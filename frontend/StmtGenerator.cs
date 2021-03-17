using System;
using System.Diagnostics;
using System.Collections.Generic;

using Antlr4.Runtime.Misc;

namespace piVC_thu
{
    partial class CFGGenerator : piBaseVisitor<Expression?>
    {
        public override Expression? VisitVarDeclStmt([NotNull] piParser.VarDeclStmtContext context)
        {
            Debug.Assert(currentBasicBlock != null);

            // TODO: 这一段也许要怎么 extract 一下，和 for 的那个 decl 一起搞一下

            // 分别依次算出类型、变量名和初始化表达式
            // 这里的顺序其实是 undefined behavior
            // 我们目前这种方式，会导致如果右边的初始化表达式里有左边正在定义的变量的话
            // 这个变量会是一个
            VarType type = CalcType(context.var().type());
            string name = context.var().IDENT().GetText();
            if (symbolTables.Peek().ContainsKey(name))
                throw new ParsingException(context, $"duplicate declared variable {name}");
            Expression? initExpr = context.expr() == null ? null : TypeConfirm(context.expr(), Visit(context.expr())!, type);

            // 用上面算出来的类型、变量名和初始化表达式构成一个变量整体
            // 这里注意要做 alpha-renaming
            LocalVariable localVariable = new LocalVariable
            {
                type = type,
                name = alphaRenamed(name),
                initializer = initExpr
            };
            symbolTables.Peek().Add(name, localVariable);

            // 如果说有初始化表达式存在，那么其实就相当于一个赋值语句，所以也需要放到现在的 block 里
            if (context.expr() != null)
            {
                if (initExpr == null)
                    throw new ParsingException(context, "initial expression is mistakenly wrong. Probably a bug occurs.");

                currentBasicBlock.AddStatement(new VariableAssignStatement
                {
                    variable = localVariable,
                    rhs = initExpr
                });
            }

            return null;
        }

        public override Expression? VisitExprStmt([NotNull] piParser.ExprStmtContext context)
        {
            Debug.Assert(currentBasicBlock != null);

            Expression expression = Visit(context.expr())!;
            currentBasicBlock.AddStatement(new ExpressionStatement
            {
                expression = expression
            });
            return null;
        }

        public override Expression? VisitIfStmt([NotNull] piParser.IfStmtContext context)
        {
            Debug.Assert(currentBasicBlock != null);

            Expression condition = TypeConfirm(context, Visit(context.expr())!, BoolType.Get());

            BasicBlock prevBlock = currentBasicBlock;

            // then-block
            BasicBlock thenBlock = new BasicBlock();
            Block.AddEdge(prevBlock, thenBlock);
            currentBasicBlock = thenBlock;
            thenBlock.AddStatement(new AssumeStatement
            {
                condition = condition
            });
            Visit(context.stmt()[0]);
            BasicBlock? visitedThenBlock = currentBasicBlock;

            // else-block
            BasicBlock elseBlock = new BasicBlock();
            Block.AddEdge(prevBlock, elseBlock);
            currentBasicBlock = elseBlock;
            Expression notCondition = new NotExpression
            {
                type = condition.type,
                expression = condition
            };
            elseBlock.AddStatement(new AssumeStatement
            {
                condition = notCondition
            });
            if (context.stmt().Length == 2)
                Visit(context.stmt()[1]);
            BasicBlock? visitedElseBlock = currentBasicBlock;

            // 在访问过之后，相应的 block 可能为空
            // 因为被 break 或者 return 了
            if (visitedThenBlock != null || visitedElseBlock != null)
            {
                currentBasicBlock = new BasicBlock();
                if (thenBlock != null)
                {
                    Block.AddEdge(thenBlock, currentBasicBlock);
                }
                if (elseBlock != null)
                {
                    Block.AddEdge(elseBlock, currentBasicBlock);
                }
            }

            return null;
        }

        public override Expression? VisitWhileStmt([NotNull] piParser.WhileStmtContext context)
        {
            Debug.Assert(currentBasicBlock != null);

            LoopHeadBlock loopheadBlock = CalcLoopHeadBlock(context.beforeBranch().annotationWithLabel(), context.beforeBranch().termination());
            Block.AddEdge(currentBasicBlock, loopheadBlock);

            Expression condition = TypeConfirm(context, Visit(context.expr())!, BoolType.Get());

            // 开一个新的作用域
            symbolTables.Push(new Dictionary<string, LocalVariable>());

            // 开一个 body block
            BasicBlock bodyBlock = new BasicBlock();
            bodyBlock.AddStatement(new AssumeStatement
            {
                condition = condition
            });
            Block.AddEdge(loopheadBlock, bodyBlock);

            // 开一个 exit loop block，里面其实只有一条语句，就是 assume notCondition
            BasicBlock exitBlock = new BasicBlock();
            Expression notCondition = new NotExpression
            {
                type = BoolType.Get(),
                expression = condition
            };
            exitBlock.AddStatement(new AssumeStatement
            {
                condition = notCondition
            });
            Block.AddEdge(loopheadBlock, exitBlock);

            // 开一个 post loop block，接在 exit loop block 后面
            postLoopBlock = new BasicBlock();
            Block.AddEdge(exitBlock, postLoopBlock);

            // 访问 body
            currentBasicBlock = bodyBlock;
            Visit(context.stmt());
            Block.AddEdge(currentBasicBlock, loopheadBlock);

            // 结束循环
            symbolTables.Pop();
            currentBasicBlock = postLoopBlock;

            return null;
        }

        // for ( var := expr ; expr ; expr)
        //
        // 等价于
        //
        // {
        //   var := expr
        //   while (expr) {
        //     body
        //   }
        // }
        public override Expression? VisitForStmt([NotNull] piParser.ForStmtContext context)
        {
            Debug.Assert(currentBasicBlock != null);

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

            // 开作用域，但不开新的 block
            symbolTables.Push(new Dictionary<string, LocalVariable>());

            if (context.var() != null)
            { // declaration and possible initialization
                VarType type = CalcType(context.var().type());
                string name = context.var().IDENT().GetText();
                if (symbolTables.Peek().ContainsKey(name))
                    throw new ParsingException(context, $"duplicate variable {name}");
                Expression? initExpr = initExprContext != null ? TypeConfirm(context, Visit(initExprContext)!, type) : null;

                LocalVariable localVariable = new LocalVariable
                {
                    type = type,
                    name = alphaRenamed(name),
                    initializer = initExpr
                };
                symbolTables.Peek().Add(name, localVariable);

                if (initExpr != null)
                { // 如果是有初始化表达式的话，就想变量声明时我们所作的那样，也是需要将其作为一条语句来处理的
                    // 注意这里是要放到 currentBlock 里
                    currentBasicBlock.AddStatement(new VariableAssignStatement
                    {
                        variable = localVariable,
                        rhs = initExpr
                    });
                }
            }

            // loop head block
            LoopHeadBlock loopheadBlock = CalcLoopHeadBlock(context.beforeBranch().annotationWithLabel(), context.beforeBranch().termination());
            Block.AddEdge(currentBasicBlock, loopheadBlock);

            // condition
            Expression condition = Visit(condExprContext)!;

            // 开一个 body block
            BasicBlock bodyBlock = new BasicBlock();
            Block.AddEdge(currentBasicBlock, bodyBlock);

            // 将 condition 作为 assume 放到 body block 的首端
            currentBasicBlock.AddStatement(new AssumeStatement
            {
                condition = condition
            });

            // 开一个 exit loop block，其中其实只有一条 assume 语句
            BasicBlock exitBlock = new BasicBlock();
            Expression notCondition = new NotExpression
            {
                type = BoolType.Get(),
                expression = condition
            };
            exitBlock.AddStatement(new AssumeStatement
            {
                condition = notCondition
            });
            Block.AddEdge(loopheadBlock, exitBlock);

            // 开一个 post loop block，接在 exit loop block 后面
            postLoopBlock = new BasicBlock();
            Block.AddEdge(exitBlock, postLoopBlock);

            // 访问 body
            currentBasicBlock = bodyBlock;
            Visit(context.stmt());

            if (iterExprContext != null)
            { // 如果有 iterExpr 的话，需要放到 body block 的最末端
                Expression iterExpr = Visit(iterExprContext)!;
                currentBasicBlock.AddStatement(new ExpressionStatement
                {
                    expression = iterExpr
                });
            }
            if (context.assign() != null)
            { // 也可能放到 iteration 位置上的不是 expr，而是一个 assign
                Debug.Assert(iterExprContext == null);
                Visit(context.assign());
            }

            Block.AddEdge(currentBasicBlock, loopheadBlock);

            // 结束循环
            symbolTables.Pop();

            return null;
        }

        public override Expression? VisitBreakStmt([NotNull] piParser.BreakStmtContext context)
        {
            Debug.Assert(currentBasicBlock != null);

            if (postLoopBlock == null)
                throw new ParsingException(context, "a break statement is not within loop.");

            Block.AddEdge(currentBasicBlock, postLoopBlock);
            currentBasicBlock = null;

            return null;
        }

        public override Expression? VisitReturnStmt([NotNull] piParser.ReturnStmtContext context)
        {
            Debug.Assert(currentBasicBlock != null);
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
                Expression rhs = TypeConfirm(context, Visit(context.expr())!, currentFunction.rv.type);
                currentBasicBlock.AddStatement(new VariableAssignStatement
                {
                    variable = currentFunction.rv,
                    rhs = rhs
                });
            }

            Block.AddEdge(currentBasicBlock, currentFunction.postconditionBlock);
            currentBasicBlock = null;

            return null;
        }

        public override Expression? VisitAssertStmt([NotNull] piParser.AssertStmtContext context)
        {
            Debug.Assert(currentBasicBlock != null);

            // 尽管这里的类型应该是已经被 confirm 过一遍了，但多 confirm 一次是更加保险的选择
            Expression annotation = TypeConfirm(context, Visit(context.annotationWithLabel())!, BoolType.Get());

            currentBasicBlock.AddStatement(new AssertStatement
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
                if (currentBasicBlock == null)
                    break;
            }
            return null;
        }

        public override Expression? VisitVarAssign([NotNull] piParser.VarAssignContext context)
        {
            Debug.Assert(currentBasicBlock != null);

            string name = context.IDENT().GetText();
            LocalVariable variable = FindLocalVariable(context, name);
            Expression rhs = Visit(context.expr())!;

            currentBasicBlock.AddStatement(new VariableAssignStatement
            {
                variable = variable,
                rhs = rhs
            });
            return null;
        }

        public override Expression? VisitSubAssign([NotNull] piParser.SubAssignContext context)
        {
            Debug.Assert(currentBasicBlock != null);

            Expression array = Visit(context.expr()[0])!;
            if (array.type is not ArrayType)
                throw new ParsingException(context, "the expression just before the subscription is not an array.");
            Expression index = TypeConfirm(context, Visit(context.expr()[1])!, IntType.Get())!;
            Expression rhs = TypeConfirm(context, Visit(context.expr()[2])!, ((ArrayType)(array.type)).atomicType);

            currentBasicBlock.AddStatement(new SubscriptAssignStatement
            {
                array = array,
                index = index,
                rhs = rhs
            });
            return null;
        }

        public override Expression? VisitMemAssign([NotNull] piParser.MemAssignContext context)
        {
            Debug.Assert(currentBasicBlock != null);

            string structName = context.IDENT()[0].GetText();
            string memberName = context.IDENT()[1].GetText();
            LocalVariable structVariable = FindLocalVariable(context, structName);
            if (structVariable.type is not StructType)
                throw new ParsingException(context, $"request for member '{memberName}' in '{structName}', which is of non-struct type '{nameof(structVariable.type)}'.");
            Struct s = ((StructType)(structVariable.type)).structDefinition;

            // 先根据名字算出来是哪个 member
            if (!s.members.ContainsKey(memberName))
                throw new ParsingException(context, $"'struct {s.name}' has no member named {memberName}");
            MemberVariable memberVariable = s.members[memberName];

            // 将 MemberVariable 转成 LocalVariable 统一处理
            LocalVariable variable = new LocalVariable
            {
                type = memberVariable.type,
                name = structVariable.name + "$" + memberName
            };

            // 求出右边的表达式
            Expression rhs = TypeConfirm(context, Visit(context.expr())!, variable.type);

            // 把赋值语句加到基本块里
            currentBasicBlock.AddStatement(new VariableAssignStatement
            {
                variable = variable,
                rhs = rhs
            });
            return null;
        }

        // ==== utils just for statements ====

        public string alphaRenamed(string name)
        {
            numberOfVariable[name] = numberOfVariable.GetValueOrDefault<string, int>(name) + 1;
            return name + "$" + numberOfVariable[name];
        }
    }
}