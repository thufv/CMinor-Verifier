using System.Collections.Generic;

using Antlr4.Runtime.Misc;

// TODO: rv 怎么处理还需要仔细想一想……

namespace piVC_thu
{
    partial class CFGGenerator : piBaseVisitor<Expression?>
    {
        public override Expression? VisitVarDeclStmt([NotNull] piParser.VarDeclStmtContext context)
        {
            VarType type = CalcType(context.var().type());
            string name = context.var().IDENT().GetText();
            if (symbolTables.Peek().ContainsKey(name))
                throw new ParsingException(context, $"duplicate variable {name}");
            Expression? initExpr = context.expr() == null ? null : TypeConfirm(context.expr(), Visit(context.expr())!, type);

            LocalVariable localVariable = new LocalVariable
            {
                type = type,
                name = name + "$" + numberOfName.GetValueOrDefault<string, int>(name),
                initializer = initExpr
            };
            numberOfName[name] = numberOfName.GetValueOrDefault<string, int>(name) + 1;
            symbolTables.Peek().Add(name, localVariable);

            if (context.expr() != null)
            {
                if (currentBasicBlock == null)
                    throw new ParsingException(context, "there's no current basic block. Probably a bug occurs.");
                if (initExpr == null)
                    throw new ParsingException(context, "initial expression is mistakenly wrong. Probably a bug occurs.");

                currentBasicBlock.statements.AddLast(new VariableAssignStatement
                {
                    location = ++currentLocation,
                    variable = localVariable,
                    rhs = initExpr
                });
            }

            return null;
        }

        public override Expression? VisitExprStmt([NotNull] piParser.ExprStmtContext context)
        {
            Expression expression = Visit(context.expr())!;
            if (currentBasicBlock == null)
                throw new ParsingException(context, "there's no current basic block. Probably a bug occurs.");
            currentBasicBlock.statements.AddLast(new ExpressionStatement
            {
                location = currentLocation,
                expression = expression
            });
            return null;
        }

        public override Expression? VisitVarAssignStmt([NotNull] piParser.VarAssignStmtContext context)
        {
            string name = context.IDENT().GetText();
            LocalVariable variable = FindLocalVariable(context, name);
            Expression rhs = Visit(context.expr())!;

            if (currentBasicBlock == null)
                throw new ParsingException(context, "there's no current basic block. Probably a bug occurs.");
            currentBasicBlock.statements.AddLast(new VariableAssignStatement
            {
                location = currentLocation,
                variable = variable,
                rhs = rhs
            });
            return null;
        }

        public override Expression? VisitSubAssignStmt([NotNull] piParser.SubAssignStmtContext context)
        {
            Expression array = Visit(context.expr()[0])!;
            Expression index = TypeConfirm(context, Visit(context.expr()[1])!, IntType.Get())!;
            if (array.type is not ArrayType)
                throw new ParsingException(context, "the expression just before the subscription is not an array.");
            Expression rhs = TypeConfirm(context, Visit(context.expr()[2])!, ((ArrayType)(array.type)).atomicType);

            if (currentBasicBlock == null)
                throw new ParsingException(context, "there's no current basic block. Probably a bug occurs.");
            currentBasicBlock.statements.AddLast(new SubscriptAssignStatement
            {
                location = currentLocation,
                array = array,
                index = index,
                rhs = rhs
            });
            return null;
        }

        public override Expression? VisitMemAssignStmt([NotNull] piParser.MemAssignStmtContext context)
        {
            Expression structExpr = TypeConfirm(context, Visit(context.expr()[0])!, typeof(StructType));
            Struct s = ((StructType)(structExpr.type)).structDefinition;
            string memberName = context.IDENT().GetText();


            Expression rhs = typeConfirm(context, Visit(context.expr()[1])!, variable.type);

            if (currentBasicBlock == null)
                throw new ParsingException(context, "there's no current basic block. Probably a bug occurs.");
            currentBasicBlock.statements.AddLast(new VariableAssignStatement
            {
                location = currentLocation,
                variable = variable,
                rhs = rhs
            });
            return null;
        }

        public override Expression? VisitIfStmt([NotNull] piParser.IfStmtContext context)
        {
            Expression condition = TypeConfirm(context, Visit(context.expr())!, BoolType.Get());

            if (currentBasicBlock == null)
                throw new ParsingException(context, "there's no current basic block. Probably a bug occurs.");
            BasicBlock prevBlock = currentBasicBlock;

            // then-block
            BasicBlock thenBlock = new BasicBlock();
            Block.AddEdge(prevBlock, thenBlock);
            currentBasicBlock = thenBlock;
            thenBlock.statements.AddLast(new AssumeStatement
            {
                location = currentLocation,
                condition = condition
            });
            Visit(context.stmt()[0]);

            // else-block
            BasicBlock elseBlock = new BasicBlock();
            Block.AddEdge(prevBlock, elseBlock);
            currentBasicBlock = elseBlock;
            Expression notCondition = new NotExpression
            {
                type = condition.type,
                annotated = condition.annotated,
                expression = condition
            };
            elseBlock.statements.AddLast(new AssumeStatement
            {
                location = ++currentLocation,
                condition = notCondition
            });
            if (context.stmt().Length == 2)
                Visit(context.stmt()[1]);

            // post block
            BasicBlock postBlock = new BasicBlock();
            Block.AddEdge(thenBlock, postBlock);
            Block.AddEdge(elseBlock, postBlock);

            return null;
        }

        public override Expression? VisitWhileStmt([NotNull] piParser.WhileStmtContext context)
        {
            LoopHeadBlock loopheadBlock = CalcLoopHeadBlock(context.beforeBranch().annotationWithLabel(), context.beforeBranch().termination());
            if (currentBasicBlock == null)
                throw new ParsingException(context, "there's no current basic block. Probably a bug occurs.");
            Block.AddEdge(currentBasicBlock, loopheadBlock);

            Expression condition = TypeConfirm(context, Visit(context.expr())!, BoolType.Get());

            // 开一个新的作用域
            symbolTables.Push(new Dictionary<string, LocalVariable>());
            BasicBlock bodyBlock = new BasicBlock();
            bodyBlock.AddStatement(new AssumeStatement
            {
                location = ++currentLocation,
                condition = condition
            });
            Block.AddEdge(loopheadBlock, bodyBlock);
            Block.AddEdge(bodyBlock, loopheadBlock);

            // 访问 body
            Visit(context.stmt());

            // 关闭作用域
            symbolTables.Pop();
            currentBasicBlock = new BasicBlock();
            Block.AddEdge(bodyBlock, currentBasicBlock);
            Expression notCondition = new NotExpression
            {
                type = BoolType.Get(),
                expression = condition
            };
            currentBasicBlock.AddStatement(new AssumeStatement
            {
                location = ++currentLocation,
                condition = notCondition
            });

            return null;
        }

        public override Expression? VisitForStmt([NotNull] piParser.ForStmtContext context)
        {
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

            // 开一个 outer 作用域
            symbolTables.Push(new Dictionary<string, LocalVariable>());
            BasicBlock outerBlock = new BasicBlock();
            if (currentBasicBlock == null)
                throw new ParsingException(context, "there's no current basic block. Probably a bug occurs.");
            Block.AddEdge(currentBasicBlock, outerBlock);

            // declare
            if (context.var() != null)
            {
                VarType type = CalcType(context.var().type());
                string name = context.var().IDENT().GetText();
                if (symbolTables.Peek().ContainsKey(name))
                    throw new ParsingException(context, $"duplicate variable {name}");
                Expression? initExpr = initExprContext != null ? TypeConfirm(context, Visit(initExprContext)!, type) : null;

                LocalVariable localVariable = new LocalVariable
                {
                    type = type,
                    name = name + "$" + numberOfName.GetValueOrDefault<string, int>(name),
                    initializer = initExpr
                };

                numberOfName[name] = numberOfName.GetValueOrDefault<string, int>(name) + 1;
                symbolTables.Peek().Add(name, localVariable);
            }

            if (context.expr() != null)
            {
                if (currentBasicBlock == null)
                    throw new ParsingException(context, "there's no current basic block. Probably a bug occurs.");
                if (initExpr == null)
                    throw new ParsingException(context, "initial expression is mistakenly wrong. Probably a bug occurs.");

                currentBasicBlock.statements.AddLast(new VariableAssignStatement
                {
                    location = ++currentLocation,
                    variable = localVariable,
                    rhs = initExpr
                });
            }

            // declaration


            // loop head block
            LoopHeadBlock loopheadBlock = CalcLoopHeadBlock(context.beforeBranch().annotationWithLabel(), context.beforeBranch().termination());
            if (currentBasicBlock == null)
                throw new ParsingException(context, "there's no current basic block. Probably a bug occurs.");
            Block.AddEdge(outerBlock, loopheadBlock);

            // 开一个 inner 作用域

        }

        public override Expression? VisitBreakStmt([NotNull] piParser.BreakStmtContext context)
        {
            // TODO: 退出循环的话，那么我需要知道这个循环后面的 block 在哪QAQ
        }

        public override Expression? VisitReturnStmt([NotNull] piParser.ReturnStmtContext context)
        {
            // TODO: 这里就需要处理一下 rv 的事情了……
        }

        public override Expression? VisitAssertStmt([NotNull] piParser.AssertStmtContext context)
        {
            // TODO
        }
    }
}