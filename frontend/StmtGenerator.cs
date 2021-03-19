using System.Diagnostics;
using System.Collections.Generic;

using Antlr4.Runtime.Misc;

namespace piVC_thu
{
    partial class CFGGenerator : piBaseVisitor<Expression?>
    {
        public override Expression? VisitVarDeclStmt([NotNull] piParser.VarDeclStmtContext context)
        {
            Debug.Assert(currentBlock != null);

            // 分别依次算出类型、变量名和初始化表达式
            // 这里的顺序其实是 undefined behavior
            // 我们目前这种方式，会导致如果右边的初始化表达式里有左边正在定义的变量的话
            // 这个变量会是一个
            VarType type = CalcType(context.var().type());
            string name = context.var().IDENT().GetText();
            if (symbolTables.Peek().ContainsKey(name))
                throw new ParsingException(context, $"duplicate declared variable {name}");
            annotated = false;
            Expression? initExpr = context.expr() == null ? null : TypeConfirm(context.expr(), type);
            annotated = null;

            // 用上面算出来的类型、变量名和初始化表达式构成一个变量整体
            LocalVariable localVariable = type is StructType
                ? new StructVariable
                {
                    type = type,
                    name = counter.GetVariable(name)
                }
                : new LocalVariable
                {
                    type = type,
                    name = counter.GetVariable(name)
                };
            symbolTables.Peek().Add(name, localVariable);



            // 如果说有初始化表达式存在，那么其实就相当于一个赋值语句，所以也需要放到现在的 block 里
            if (context.expr() != null)
            {
                if (initExpr == null)
                    throw new ParsingException(context, "initial expression is mistakenly wrong. Probably a bug occurs.");

                currentBlock.AddStatement(new VariableAssignStatement
                {
                    variable = localVariable,
                    rhs = initExpr
                });
            }

            return null;
        }

        public override Expression? VisitExprStmt([NotNull] piParser.ExprStmtContext context)
        {
            Debug.Assert(currentBlock != null);

            annotated = false;
            // 这里的表达式的返回值在对象语言中是可以为 void 的，
            // 也就是在元语言中可以为 null。
            Visit(context.expr());
            annotated = null;

            return null;
        }

        public override Expression? VisitIfStmt([NotNull] piParser.IfStmtContext context)
        {
            Debug.Assert(currentBlock != null);
            Debug.Assert(currentFunction != null);

            // 先把 condition variable 算出来，如果是一个比较复杂的表达式的话，就加一个辅助变量
            // 作为 variable
            annotated = false;
            Expression conditionExpression = CompressedCondition(context.expr());
            annotated = null;

            Block prevBlock = currentBlock;

            // then-block
            BasicBlock thenBlock = new BasicBlock(currentFunction, prevBlock);
            currentBlock = thenBlock;
            thenBlock.AddStatement(new AssumeStatement
            {
                condition = conditionExpression
            });
            symbolTables.Push(new Dictionary<string, LocalVariable>());
            Visit(context.stmt()[0]);
            symbolTables.Pop();
            Block? visitedThenBlock = currentBlock;

            // else-block
            BasicBlock elseBlock = new BasicBlock(currentFunction, prevBlock);
            currentBlock = elseBlock;
            Expression notCondition = new NotExpression
            {
                type = BoolType.Get(),
                expression = conditionExpression
            };
            elseBlock.AddStatement(new AssumeStatement
            {
                condition = notCondition
            });
            if (context.stmt().Length == 2)
            {
                symbolTables.Push(new Dictionary<string, LocalVariable>());
                Visit(context.stmt()[1]);
                symbolTables.Pop();
            }
            Block? visitedElseBlock = currentBlock;

            // 在访问过之后，相应的 block 可能为空
            // 因为被 break 或者 return 了
            if (visitedThenBlock != null || visitedElseBlock != null)
            {
                currentBlock = new BasicBlock(currentFunction);
                if (thenBlock != null)
                    Block.AddEdge(thenBlock, currentBlock);
                if (elseBlock != null)
                    Block.AddEdge(elseBlock, currentBlock);
            }

            return null;
        }

        public override Expression? VisitWhileStmt([NotNull] piParser.WhileStmtContext context)
        {
            Debug.Assert(currentBlock != null);
            Debug.Assert(currentFunction != null);

            annotated = true;
            LoopHeadBlock loopheadBlock = CalcLoopHeadBlock(context.beforeBranch().annotationWithLabel(), context.beforeBranch().termination());
            annotated = null;

            annotated = false;
            Expression condition = CompressedCondition(context.expr());
            annotated = null;

            // 开一个新的作用域
            symbolTables.Push(new Dictionary<string, LocalVariable>());

            // 开一个 body block
            BasicBlock bodyBlock = new BasicBlock(currentFunction, loopheadBlock);
            bodyBlock.AddStatement(new AssumeStatement
            {
                condition = condition
            });

            // 开一个 exit loop block，里面其实只有一条语句，就是 assume notCondition
            BasicBlock exitBlock = new BasicBlock(currentFunction, loopheadBlock);
            Expression notCondition = new NotExpression
            {
                type = BoolType.Get(),
                expression = condition
            };
            exitBlock.AddStatement(new AssumeStatement
            {
                condition = notCondition
            });

            // 开一个 post loop block，接在 exit loop block 后面
            postLoopBlock = new BasicBlock(currentFunction, exitBlock);

            // 访问 body
            currentBlock = bodyBlock;
            Visit(context.stmt());
            Block.AddEdge(currentBlock, loopheadBlock);

            // 结束循环
            symbolTables.Pop();
            currentBlock = postLoopBlock;

            return null;
        }

        // for ( var := init ; cond ; iter)
        //
        // 等价于
        //
        // {
        //   var := init
        //   while (cond) {
        //     body
        //     iter
        //   }
        // }
        public override Expression? VisitForStmt([NotNull] piParser.ForStmtContext context)
        {
            Debug.Assert(currentBlock != null);
            Debug.Assert(currentFunction != null);

            // find three expressions in the for-statement
            piParser.ExprContext? initExprContext = null, condExprContext = null, iterExprContext = null;
            for (int i = 0; i < context.ChildCount; ++i)
                if (context.GetChild(i) is piParser.ExprContext exprContext)
                {
                    if (context.GetChild(i - 1).GetText() == ":=" && context.GetChild(i + 1).GetText() == ";")
                        initExprContext = exprContext;
                    else if (context.GetChild(i - 1).GetText() == ";" && context.GetChild(i + 1).GetText() == ";")
                        condExprContext = exprContext;
                    else if (context.GetChild(i - 1).GetText() == ";" && context.GetChild(i + 1).GetText() == ")")
                        iterExprContext = exprContext;
                }
            if (condExprContext == null)
                throw new ParsingException(context, "no condition in for-loop.");

            // 开作用域，但不开新的 block
            symbolTables.Push(new Dictionary<string, LocalVariable>());

            if (context.var() != null)
            { // declaration and possible initialization
                VarType type = CalcType(context.var().type());
                string name = context.var().IDENT().GetText();
                if (symbolTables.Peek().ContainsKey(name))
                    throw new ParsingException(context, $"duplicate variable {name}");

                annotated = false;
                Expression? initExpr = initExprContext != null ? TypeConfirm(initExprContext, type) : null;
                annotated = null;

                LocalVariable localVariable = type is StructType
                    ? new StructVariable
                    {
                        type = type,
                        name = counter.GetVariable(name)
                    }
                    : new LocalVariable
                    {
                        type = type,
                        name = counter.GetVariable(name)
                    };
                symbolTables.Peek().Add(name, localVariable);

                if (initExpr != null)
                { // 如果是有初始化表达式的话，就想变量声明时我们所作的那样，也是需要将其作为一条语句来处理的
                    // 注意这里是要放到 currentBlock 里
                    currentBlock.AddStatement(new VariableAssignStatement
                    {
                        variable = localVariable,
                        rhs = initExpr
                    });
                }
            }

            // loop head block
            annotated = true;
            LoopHeadBlock loopheadBlock = CalcLoopHeadBlock(context.beforeBranch().annotationWithLabel(), context.beforeBranch().termination());
            annotated = null;
            currentBlock = loopheadBlock;

            // condition
            annotated = false;
            Expression condition = CompressedCondition(condExprContext);
            annotated = null;

            // 开一个 body block
            BasicBlock bodyBlock = new BasicBlock(currentFunction, loopheadBlock);

            // 将 condition 作为 assume 放到 body block 的首端
            bodyBlock.AddStatement(new AssumeStatement
            {
                condition = condition
            });

            // 开一个 exit loop block，其中其实只有一条 assume 语句
            BasicBlock exitBlock = new BasicBlock(currentFunction, loopheadBlock);
            Expression notCondition = new NotExpression
            {
                type = BoolType.Get(),
                expression = condition
            };
            exitBlock.AddStatement(new AssumeStatement
            {
                condition = notCondition
            });

            // 开一个 post loop block，接在 exit loop block 后面
            postLoopBlock = new BasicBlock(currentFunction, exitBlock);

            // 访问 body
            currentBlock = bodyBlock;
            Visit(context.stmt());

            annotated = false;
            if (iterExprContext != null)
            { // 如果有 iterExpr 的话，需要放到 body block 的最末端
                // 我们可以无需理会它的返回表达式，因为事实上唯一有副作用的是 function call
                // 而我们会为 function call 自动生成语句
                Visit(iterExprContext);
            }
            if (context.assign() != null)
            { // 也可能放到 iteration 位置上的不是 expr，而是一个 assign
                Debug.Assert(iterExprContext == null);
                Visit(context.assign());
            }
            annotated = null;

            Block.AddEdge(currentBlock, loopheadBlock);

            // 结束循环
            symbolTables.Pop();
            currentBlock = postLoopBlock;

            return null;
        }

        public override Expression? VisitBreakStmt([NotNull] piParser.BreakStmtContext context)
        {
            Debug.Assert(currentBlock != null);

            if (postLoopBlock == null)
                throw new ParsingException(context, "a break statement is not within loop.");

            Block.AddEdge(currentBlock, postLoopBlock);
            currentBlock = null;

            return null;
        }

        public override Expression? VisitReturnStmt([NotNull] piParser.ReturnStmtContext context)
        {
            Debug.Assert(currentBlock != null);
            Debug.Assert(currentFunction != null);

            if (context.expr() == null)
            {
                // 如果没有返回值的话，函数的返回类型也必须是 void
                if (currentFunction.type.returnType is not VoidType)
                    throw new ParsingException(context, $"return-statement with no value, in function returning '{currentFunction.type.returnType}'");
            }
            else
            {
                if (currentFunction.rv == null)
                    throw new ParsingException(context, $"return-statement with a value, in function returning 'void'");
                // 这里需要一个 rv = expr 的语句
                // 注意这里的 rv 不是在函数体里（可能）定义出来的 rv
                // 而是一个编译器保留的特殊变量，其类型即是函数的返回类型
                annotated = false;
                Expression rhs = TypeConfirm(context.expr(), currentFunction.rv.type);
                annotated = null;
                currentBlock.AddStatement(new VariableAssignStatement
                {
                    variable = currentFunction.rv,
                    rhs = rhs
                });
            }

            Block.AddEdge(currentBlock, currentFunction.postconditionBlock);
            currentBlock = null;

            return null;
        }

        public override Expression? VisitAssertStmt([NotNull] piParser.AssertStmtContext context)
        {
            Debug.Assert(currentBlock != null);

            // 尽管这里的类型应该是已经被 confirm 过一遍了，但多 confirm 一次是更加保险的选择
            annotated = true;
            Expression annotation = TypeConfirm(context.annotationWithLabel(), BoolType.Get());
            annotated = null;

            currentBlock.AddStatement(new AssertStatement
            {
                annotation = annotation
            });

            return null;
        }

        public override Expression? VisitStmtBlock([NotNull] piParser.StmtBlockContext context)
        {
            foreach (var stmt in context.stmt())
            {
                Visit(stmt);
                if (currentBlock == null)
                    break;
            }
            return null;
        }

        public override Expression? VisitVarAssign([NotNull] piParser.VarAssignContext context)
        {
            Debug.Assert(currentBlock != null);

            string name = context.IDENT().GetText();
            Variable variable = FindVariable(context, name);

            annotated = false;
            Expression rhs = NotNullConfirm(context.expr());
            annotated = null;

            currentBlock.AddStatement(new VariableAssignStatement
            {
                variable = variable,
                rhs = rhs
            });
            return null;
        }

        public override Expression? VisitSubAssign([NotNull] piParser.SubAssignContext context)
        {
            Debug.Assert(currentBlock != null);

            annotated = false;
            Expression array = NotNullConfirm(context.expr()[0]);
            if (array.type is not ArrayType)
                throw new ParsingException(context, "the expression just before the subscription is not an array.");
            Expression index = TypeConfirm(context.expr()[1], IntType.Get());
            Expression rhs = TypeConfirm(context.expr()[2], ((ArrayType)(array.type)).atomicType);
            annotated = null;

            currentBlock.AddStatement(new SubscriptAssignStatement
            {
                array = array,
                index = index,
                rhs = rhs
            });
            return null;
        }

        public override Expression? VisitMemAssign([NotNull] piParser.MemAssignContext context)
        {
            Debug.Assert(currentBlock != null);

            string structName = context.IDENT()[0].GetText();
            string memberName = context.IDENT()[1].GetText();
            Variable structVariable = FindVariable(context, structName);
            if (structVariable is not StructVariable)
                throw new ParsingException(context, $"request for member '{memberName}' in '{structName}', which is of non-struct type '{structVariable.type}'.");
            Struct s = ((StructType)(structVariable.type)).structDefinition;

            // 先根据名字算出来是哪个 member
            if (!s.members.ContainsKey(memberName))
                throw new ParsingException(context, $"'struct {s.name}' has no member named '{memberName}'.");
            MemberVariable memberVariable = s.members[memberName];

            // 将 MemberVariable 转成 LocalVariable 统一处理
            LocalVariable variable = new LocalVariable
            {
                type = memberVariable.type,
                name = structVariable.name + "$" + memberName
            };
            ((StructVariable)(structVariable)).members.Add(memberName, variable);

            // 求出右边的表达式
            annotated = false;
            Expression rhs = TypeConfirm(context.expr(), variable.type);
            annotated = null;

            // 把赋值语句加到基本块里
            currentBlock.AddStatement(new VariableAssignStatement
            {
                variable = variable,
                rhs = rhs
            });
            return null;
        }

        // utils only for statement generator

        // 如果一个函数有多个 condition 的话，先把它放到后面QAQ
        Expression CompressedCondition([NotNull] piParser.ExprContext context)
        {
            Debug.Assert(currentBlock != null);
            Expression expression = TypeConfirm(context, BoolType.Get());
            if (expression is not VariableExpression)
            {
                Variable variable = new LocalVariable
                {
                    type = BoolType.Get(),
                    name = counter.GetCondition()
                };
                currentBlock.AddStatement(new VariableAssignStatement
                {
                    variable = variable,
                    rhs = expression
                });
                expression = new VariableExpression
                {
                    type = BoolType.Get(),
                    variable = variable
                };
            }
            return expression;
        }
    }
}