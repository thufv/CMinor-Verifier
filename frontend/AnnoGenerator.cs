using System.Linq;
using System.Diagnostics;
using System.Collections.Generic;

using Antlr4.Runtime.Misc;

namespace cminor
{
    partial class CFGGenerator : CMinorParserBaseVisitor<Expression?>
    {
        public override Expression? VisitAssertion([NotNull] CMinorParser.AssertionContext context)
        {
            Debug.Assert(currentBlock != null);

            // 尽管这里的类型应该是已经被 confirm 过一遍了，但多 confirm 一次是更加保险的选择
            Expression pred = TypeConfirm(context.pred(), BoolType.Get());

            currentBlock.AddStatement(new AssertStatement
            {
                pred = pred
            });

            return null;
        }

        PreconditionBlock 
        CalcPreconditionBlock([NotNull] CMinorParser.RequiresClauseContext[] requiresClauseContexts, CMinorParser.DecreasesClauseContext decreasesClauseContext)
        {
            List<Expression> conditions = new List<Expression>(requiresClauseContexts.Select(
                ctx => TypeConfirm(ctx.pred(), BoolType.Get())));
            Expression? rankingFunction =
                decreasesClauseContext != null
                    ? TypeConfirm(decreasesClauseContext.term(), IntType.Get())
                    : null;
            return new PreconditionBlock
            {
                conditions = conditions,
                rankingFunction = rankingFunction
            };
        }

        LoopHeadBlock CalcLoopHeadBlock([NotNull] CMinorParser.LoopAnnotContext context)
        {
            Debug.Assert(currentFunction != null);
            Debug.Assert(currentBlock != null);

            List<Expression> invariants = new List<Expression>(context.pred().Select(
                invariant => TypeConfirm(invariant, BoolType.Get())));
            Expression? rankingFunction =
                context.term() != null
                    ? TypeConfirm(context.term(), IntType.Get())
                    : null;
            return new LoopHeadBlock(currentFunction, currentBlock)
            {
                invariants = invariants,
                rankingFunction = rankingFunction
            };
        }

        PostconditionBlock CalcPostconditionBlock([NotNull] CMinorParser.EnsuresClauseContext[] contexts, List<LocalVariable> rvs)
        {
            // 这里我们开一个只有 rv 的假作用域
            var scope = rvs.ToDictionary(rv => rv.name, rv => rv);
            symbolTables.Push(scope);

            List<Expression> conditions = new List<Expression>(contexts.Select(
                ctx => TypeConfirm(ctx.pred(), BoolType.Get())));

            symbolTables.Pop();

            return new PostconditionBlock
            {
                conditions = conditions
            };
        }
    }
}