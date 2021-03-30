using System;

using System.Collections.Generic;

using System.Diagnostics;

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

            // 用上面算出来的类型、变量名和初始化表达式构成一个变量整体
            LocalVariable localVariable;
            switch (type)
            {
                case StructType st:
                    localVariable = new StructVariable(st, counter.GetVariable(name));
                    break;
                case ArrayType at:
                    localVariable = new ArrayVariable
                    {
                        type = at,
                        name = counter.GetArray()
                    };
                    break;
                default:
                    localVariable = new LocalVariable
                    {
                        type = type,
                        name = name
                    };
                    break;
            }
            symbolTables.Peek().Add(name, localVariable);

            // 如果说有初始化表达式存在，那么其实就相当于一个赋值语句，所以也需要放到现在的 block 里
            if (context.expr() != null)
            {
                Assign(localVariable, context.expr());
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
            Expression conditionExpression = CompressedExpression(TypeConfirm(context.expr(), BoolType.Get()), counter.GetCondition);
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
            Expression notCondition = new NotExpression(conditionExpression);
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
            Expression condition = CompressedExpression(TypeConfirm(context.expr(), BoolType.Get()), counter.GetCondition);
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
            Expression notCondition = new NotExpression(condition);
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

            // 开作用域，但不开新的 block
            symbolTables.Push(new Dictionary<string, LocalVariable>());

            if (context.forInit() != null)
            { // declaration and possible initialization
                if (context.forInit().var() != null)
                {
                    VarType type = CalcType(context.forInit().var().type());
                    string name = context.forInit().var().IDENT().GetText();
                    if (symbolTables.Peek().ContainsKey(name))
                        throw new ParsingException(context, $"duplicate variable {name}");

                    LocalVariable localVariable = type is StructType structType
                        ? new StructVariable(structType, counter.GetVariable(name))
                        : new LocalVariable
                        {
                            type = type,
                            name = counter.GetVariable(name)
                        };
                    symbolTables.Peek().Add(name, localVariable);

                    if (context.forInit().expr() != null)
                        Assign(localVariable, context.forInit().expr());
                }
                else
                {
                    Debug.Assert(context.forIter().assign() != null);
                    Visit(context.forIter().assign());
                }
            }

            // loop head block
            annotated = true;
            LoopHeadBlock loopheadBlock = CalcLoopHeadBlock(context.beforeBranch().annotationWithLabel(), context.beforeBranch().termination());
            annotated = null;
            currentBlock = loopheadBlock;

            // condition
            annotated = false;
            Expression condition = CompressedExpression(TypeConfirm(context.expr(), BoolType.Get()), counter.GetCondition);
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
            Expression notCondition = new NotExpression(condition);
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
            if (context.forIter() != null)
            {
                if (context.forIter().expr() != null)
                { // 如果有 iterExpr 的话，需要放到 body block 的最末端
                  // 我们可以无需理会它的返回表达式，因为事实上唯一有副作用的是 function call
                  // 而我们会为 function call 自动生成语句
                    Visit(context.forIter());
                }
                else
                { // 也可能放到 iteration 位置上的不是 expr，而是一个 assign
                    Debug.Assert(context.forIter().assign() != null);
                    Visit(context.forIter().assign());
                }
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
                if (currentFunction.type.returnTypes.Count > 0)
                    throw new ParsingException(context, $"return-statement with no value, in function returning '{currentFunction.type.returnTypes}'");
            }
            else
            {
                if (currentFunction.rvs.Count == 0)
                    throw new ParsingException(context, $"return-statement with a value, in function returning 'void'");
                Debug.Assert(currentFunction.rvs.Count == 1);
                Assign(currentFunction.rvs[0], context.expr());
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
            symbolTables.Push(new Dictionary<string, LocalVariable>());
            foreach (var stmt in context.stmt())
            {
                Visit(stmt);
                if (currentBlock == null)
                    break;
            }
            symbolTables.Pop();
            return null;
        }

        public override Expression? VisitVarAssign([NotNull] piParser.VarAssignContext context)
        {
            Debug.Assert(currentBlock != null);

            string name = context.IDENT().GetText();
            LocalVariable variable = FindVariable(context, name);
            Assign(variable, context.expr());

            return null;
        }

        public override Expression? VisitSubAssign([NotNull] piParser.SubAssignContext context)
        {
            Debug.Assert(currentBlock != null);

            annotated = false;
            LocalVariable lv = FindVariable(context, context.IDENT().GetText());
            if (lv is ArrayVariable av)
            {
                VariableExpression subscript = CompressedExpression(TypeConfirm(context.expr()[1], IntType.Get()), counter.GetSub);
                // runtime assertion: subscript >= 0
                currentBlock.AddStatement(new AssertStatement()
                {
                    annotation = new LEExpression(new IntConstantExpression(0), subscript)
                });
                // runtime assertion: subscript < length
                if (av.length != null)
                {
                    currentBlock.AddStatement(new AssertStatement()
                    {
                        annotation = new LTExpression(subscript, new VariableExpression(av.length))
                    });
                }

                Expression rhs = TypeConfirm(context.expr()[2], ((ArrayType)(av.type)).atomicType);
                annotated = null;

                currentBlock.AddStatement(new SubscriptAssignStatement
                {
                    array = av,
                    subscript = subscript,
                    rhs = rhs
                });

                return new SubscriptExpression(new VariableExpression(av), subscript);
            }
            else
                throw new ParsingException(context, "request for an element in a non-array variable.");
        }

        public override Expression? VisitMemAssign([NotNull] piParser.MemAssignContext context)
        {
            Debug.Assert(currentBlock != null);

            string structName = context.IDENT()[0].GetText();
            string memberName = context.IDENT()[1].GetText();
            Variable structVariable = FindVariable(context, structName);
            if (structVariable is StructVariable sv)
            {
                if (!((StructType)(sv.type)).structDefinition.members.ContainsKey(memberName))
                    throw new ParsingException(context, $"'struct {structName}' has no member named '{memberName}'.");
                Debug.Assert(sv.members.ContainsKey(memberName));

                LocalVariable variable = sv.members[memberName];

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
            }
            else
                throw new ParsingException(context, $"request for member '{memberName}' in '{structName}', which is of non-struct type '{structVariable.type}'.");
            return null;
        }

        // utils only for statement generator

        void Assign(LocalVariable lhsVariable, [NotNull] piParser.ExprContext rhsContext)
        {
            Debug.Assert(currentBlock != null);

            annotated = false;
            Expression rhs = TypeConfirm(rhsContext, lhsVariable.type);
            annotated = null;

            switch (rhs.type)
            {
                case StructType st:
                    Debug.Assert(lhsVariable is StructVariable);
                    StructVariable ls = (StructVariable)lhsVariable;

                    // 如果右边的表达式的类型是一个 struct 的话，
                    // 那么它一定是 VariableExpression
                    Debug.Assert(rhs is VariableExpression);
                    Debug.Assert(((VariableExpression)rhs).variable is StructVariable);
                    StructVariable rs = (StructVariable)(((VariableExpression)rhs).variable);

                    // 为每一个成员单独赋值
                    foreach (MemberVariable mv in st.structDefinition.members.Values)
                    {
                        Debug.Assert(ls.members.ContainsKey(mv.name));
                        Debug.Assert(rs.members.ContainsKey(mv.name));
                        Debug.Assert(ls.members[mv.name].type == mv.type);
                        Debug.Assert(ls.members[mv.name].type == mv.type);

                        currentBlock.AddStatement(new VariableAssignStatement
                        {
                            variable = ls.members[mv.name],
                            rhs = new VariableExpression(rs.members[mv.name])
                        });
                    }
                    break;
                case ArrayType at:
                    Debug.Assert(lhsVariable is ArrayVariable);

                    currentBlock.AddStatement(new VariableAssignStatement
                    {
                        variable = lhsVariable,
                        rhs = rhs
                    });

                    // 右边有两种可能：
                    // 一种是 variable expression；
                    // 另一种是 array update expression
                    if (rhs is VariableExpression ve && ve.variable is ArrayVariable av)
                    {
                        Debug.Assert(ve.variable is ArrayVariable);
                        currentBlock.AddStatement(new VariableAssignStatement
                        {
                            variable = ((ArrayVariable)lhsVariable).length,
                            rhs = new VariableExpression(av.length)
                        });
                    }
                    else if (rhs is ArrayUpdateExpression aue)
                    {
                        currentBlock.AddStatement(new VariableAssignStatement
                        {
                            variable = ((ArrayVariable)lhsVariable).length,
                            rhs = aue.length
                        });
                    }
                    else
                        throw new ArgumentException(
                            message: "the expression at right hand side has an array type but it is neither single variable expression nor array update expression. Probably a bug occurs.",
                            paramName: nameof(rhs));
                    break;
                default:
                    currentBlock.AddStatement(new VariableAssignStatement
                    {
                        variable = lhsVariable,
                        rhs = rhs
                    });
                    break;
            }
        }
    }
}