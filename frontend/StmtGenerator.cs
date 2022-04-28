using System.Diagnostics;
using System.Collections.Generic;

using Antlr4.Runtime.Misc;

namespace cminor
{
    partial class CFGGenerator : CMinorParserBaseVisitor<Expression?>
    {
        public override Expression? VisitExprStmt([NotNull] CMinorParser.ExprStmtContext context)
        {
            Debug.Assert(currentBlock != null);
            Debug.Assert(currentFunction != null);

            // 这里的表达式的返回值在对象语言中是可以为 void 的，
            // 也就是在元语言中可以为 null。
            Visit(context.expr());

            return null;
        }

        public override Expression? VisitIfStmt([NotNull] CMinorParser.IfStmtContext context)
        {
            Debug.Assert(currentBlock != null);
            Debug.Assert(currentFunction != null);

            // 先把 condition variable 算出来，如果是一个比较复杂的表达式的话，就加一个辅助变量
            // 作为 variable
            Expression conditionExpression = CompressedExpression(TypeConfirm(context.expr(), BoolType.Get()), counter.GetCondition);

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
            elseBlock.AddStatement(new AssumeStatement
            {
                condition = new NotExpression(conditionExpression)
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
                if (visitedThenBlock != null)
                    Block.AddEdge(visitedThenBlock, currentBlock);
                if (visitedElseBlock != null)
                    Block.AddEdge(visitedElseBlock, currentBlock);
            }

            return null;
        }

        public override Expression? VisitWhileStmt([NotNull] CMinorParser.WhileStmtContext context)
        {
            Debug.Assert(currentBlock != null);
            Debug.Assert(currentFunction != null);

            // calculate condition
            LoopHeadBlock loopheadBlock = CalcLoopHeadBlock(context.loopAnnot());
            currentBlock = loopheadBlock;
            Block? outerContBlock = contBlock;
            contBlock = loopheadBlock;

            Expression condition = CompressedExpression(TypeConfirm(context.expr(), BoolType.Get()), counter.GetCondition);

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
            BasicBlock? outerBreakBlock = breakBlock;
            breakBlock = new BasicBlock(currentFunction, exitBlock);

            // 访问 body
            currentBlock = bodyBlock;
            Visit(context.stmt());
            if (currentBlock != null)
            {
                Block.AddEdge(currentBlock, loopheadBlock);
            }

            // 结束循环
            symbolTables.Pop();
            currentBlock = breakBlock;
            breakBlock = outerBreakBlock;
            contBlock = outerContBlock;

            return null;
        }

        /* for ( var := init ; cond ; iter)
        
              [init]
                |
     ------[loop head]------
     |          |          |
   [exit]  [loop body]   [cont]
     |          |          |
     |          -----------|
     |
     -----------|
                |
               ...
        */
        public override Expression? VisitForStmt([NotNull] CMinorParser.ForStmtContext context)
        {
            Debug.Assert(currentBlock != null);
            Debug.Assert(currentFunction != null);

            // 开作用域，但不开新的 block
            symbolTables.Push(new Dictionary<string, LocalVariable>());

            if (context.forInit() != null)
            { // declaration and possible initialization
                if (context.forInit().localVar() != null)
                {
                    LocalVariable localVariable = CalcLocalVar(context.forInit().localVar());
                    if (context.forInit().expr() != null)
                        Assign(localVariable, context.forInit().expr());
                }
                else
                {
                    Debug.Assert(context.forInit().assign() != null);
                    Visit(context.forInit().assign());
                }
            }

            // loop head block
            LoopHeadBlock loopheadBlock = CalcLoopHeadBlock(context.loopAnnot());
            currentBlock = loopheadBlock;

            // condition
            Expression condition = context.expr() == null
                ? new BoolConstantExpression(true)
                : CompressedExpression(TypeConfirm(context.expr(), BoolType.Get()), counter.GetCondition);

            // 开一个 body block
            BasicBlock bodyBlock = new BasicBlock(currentFunction, loopheadBlock);

            // 将 condition 作为 assume 放到 body block 的首端
            bodyBlock.AddStatement(new AssumeStatement
            {
                condition = condition
            });

            // 访问 body
            currentBlock = bodyBlock;
            Visit(context.stmt());

            // cont (iter) block
            Block? outerContBlock = contBlock;
            contBlock = new BasicBlock(currentFunction, currentBlock);
            Block.AddEdge(contBlock, loopheadBlock);
            currentBlock = contBlock;
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

            // 开一个 exit loop block，其中其实只有一条 assume 语句
            BasicBlock exitBlock = new BasicBlock(currentFunction, loopheadBlock);
            Expression notCondition = new NotExpression(condition);
            exitBlock.AddStatement(new AssumeStatement
            {
                condition = notCondition
            });

            // 开一个新的 break block，接在 exit loop block 后面
            BasicBlock? outerBreakBlock = breakBlock;
            breakBlock = new BasicBlock(currentFunction, exitBlock);

            // 结束循环
            symbolTables.Pop();
            currentBlock = breakBlock;
            breakBlock = outerBreakBlock;
            contBlock = outerContBlock;

            return null;
        }

        /* do { body } while (cond)
           
            [loop head] -|
                 |       |
                 |  [normal cont]
                 |       |
            [loop body] -|
                 |
            [loop exit]
                 |
         */
        public override Expression? VisitDoStmt([NotNull] CMinorParser.DoStmtContext context)
        {
            Debug.Assert(currentBlock != null);
            Debug.Assert(currentFunction != null);

            // calculate condition
            LoopHeadBlock loopheadBlock = CalcLoopHeadBlock(context.loopAnnot());
            Block? outerContBlock = contBlock;
            contBlock = loopheadBlock;

            // 开一个新的作用域
            symbolTables.Push(new Dictionary<string, LocalVariable>());

            // 开一个 body block
            BasicBlock bodyBlock = new BasicBlock(currentFunction, loopheadBlock);

            // 访问 body
            currentBlock = bodyBlock;
            Visit(context.stmt());
            Expression condition = CompressedExpression(TypeConfirm(context.expr(), BoolType.Get()), counter.GetCondition);

            // 开一个 exit loop block，里面其实只有一条语句，就是 assume condition
            BasicBlock exitBlock = new BasicBlock(currentFunction, bodyBlock);
            exitBlock.AddStatement(new AssumeStatement
            {
                condition = new NotExpression(condition)
            });

            // 就是不调 continue，正常执行地话，因为循环条件不满足，所以会走的 block
            BasicBlock normalContBlock = new BasicBlock(currentFunction, bodyBlock);
            normalContBlock.AddStatement(new AssumeStatement
            {
                condition = condition
            });
            Block.AddEdge(normalContBlock, loopheadBlock);

            // 开一个 post loop block，接在 exit loop block 后面
            BasicBlock? outerBreakBlock = breakBlock;
            breakBlock = new BasicBlock(currentFunction, exitBlock);

            // 结束循环
            symbolTables.Pop();
            currentBlock = breakBlock;
            breakBlock = outerBreakBlock;
            contBlock = outerContBlock;

            return null;
        }

        public override Expression? VisitBreakStmt([NotNull] CMinorParser.BreakStmtContext context)
        {
            Debug.Assert(currentBlock != null);

            if (breakBlock == null)
                throw new ParsingException(context, "a break statement is not within loop.");

            Block.AddEdge(currentBlock, breakBlock);
            currentBlock = null;

            return null;
        }

        public override Expression? VisitContStmt([NotNull] CMinorParser.ContStmtContext context)
        {
            Debug.Assert(currentBlock != null);

            if (contBlock == null)
                throw new ParsingException(context, "a break statement is not within loop.");

            Block.AddEdge(currentBlock, contBlock);
            currentBlock = null;

            return null;
        }

        public override Expression? VisitReturnStmt([NotNull] CMinorParser.ReturnStmtContext context)
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

        public override Expression? VisitBlockStmt([NotNull] CMinorParser.BlockStmtContext context)
        {
            symbolTables.Push(new Dictionary<string, LocalVariable>());
            foreach (var child in context.children)
                if (child is CMinorParser.StmtContext stmt)
                    Visit(stmt);
                else if (child is CMinorParser.DeclContext decl)
                    Visit(decl);
            symbolTables.Pop();
            return null;
        }

        public override Expression? VisitVarAssign([NotNull] CMinorParser.VarAssignContext context)
        {
            Debug.Assert(currentBlock != null);

            string name = context.IDENT().GetText();
            LocalVariable variable = FindVariable(context, name);
            Assign(variable, context.expr());

            return null;
        }

        public override Expression? VisitSubAssign([NotNull] CMinorParser.SubAssignContext context)
        {
            Debug.Assert(currentBlock != null);

            LocalVariable lv = FindVariable(context, context.IDENT().GetText());
            if (lv is ArrayVariable av)
            {
                VariableExpression subscript = CompressedExpression(TypeConfirm(context.expr()[0], IntType.Get()), counter.GetSub);

                // runtime assertion: subscript >= 0
                currentBlock.AddStatement(new AssertStatement()
                {
                    pred = new LEExpression(new IntConstantExpression(0), subscript)
                });
                // runtime assertion: subscript < length
                if (av.length != null)
                {
                    currentBlock.AddStatement(new AssertStatement()
                    {
                        pred = new LTExpression(subscript, new LengthExpression(new VariableExpression(av)))
                    });
                }

                Expression rhs = TypeConfirm(context.expr()[1], ((ArrayType)(av.type)).atomicType);

                currentBlock.AddStatement(new SubscriptAssignStatement
                {
                    array = av,
                    subscript = subscript,
                    rhs = rhs
                });
            }
            else
                throw new ParsingException(context, "request for an element in a non-array variable.");
            return null;
        }

        public override Expression? VisitMemAssign([NotNull] CMinorParser.MemAssignContext context)
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
                Expression rhs = TypeConfirm(context.expr(), variable.type);

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

        void Assign(LocalVariable lhsVariable, [NotNull] CMinorParser.ExprContext rhsContext)
        {
            Debug.Assert(currentBlock != null);

            Expression rhs = TypeConfirm(rhsContext, lhsVariable.type);

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