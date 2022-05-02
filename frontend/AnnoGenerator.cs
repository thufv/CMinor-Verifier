/*
    这里是生成 annotation 的逻辑，需要生成的 annotation 包括：
    - precondition
    - postcondition
    - ranking function
    - assertion
*/

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
            Expression pred = TypeConfirm(context.pred(), false, BoolType.Get());

            currentBlock.AddStatement(new AssertStatement
            {
                pred = pred
            });

            return null;
        }

        PreconditionBlock
        CalcPreconditionBlock([NotNull] CMinorParser.RequiresClauseContext[] requiresClauseContexts, CMinorParser.DecreasesClauseContext? decreasesClauseContext)
        {
            List<Expression> conditions = requiresClauseContexts.Select(
                        ctx => TypeConfirm(ctx.pred(), false, BoolType.Get())).ToList();
            List<Expression> rankingFunctions = decreasesClauseContext is null
                ? new List<Expression>()
                : decreasesClauseContext.arithTerm().Select(
                        arithTerm => TypeConfirm(arithTerm, false, IntType.Get())).ToList();
            return new PreconditionBlock
            {
                conditions = conditions,
                rankingFunctions = rankingFunctions
            };
        }

        LoopHeadBlock CalcLoopHeadBlock([NotNull] CMinorParser.LoopAnnotContext context)
        {
            Debug.Assert(currentFunction != null);
            Debug.Assert(currentBlock != null);

            List<Expression> invariants = new List<Expression>(
                context.pred().Select(
                    invariant => TypeConfirm(invariant, false, BoolType.Get())));
            List<Expression> rankingFunctions = new List<Expression>(
                context.arithTerm().Select(
                    arithTerm => TypeConfirm(arithTerm, false, IntType.Get())));
            return new LoopHeadBlock(currentFunction, currentBlock)
            {
                invariants = invariants,
                rankingFunctions = rankingFunctions
            };
        }

        PostconditionBlock CalcPostconditionBlock([NotNull] CMinorParser.EnsuresClauseContext[] contexts, List<LocalVariable> rvs)
        {
            // 这里我们开一个只有 \result 的假作用域
            var scope = rvs.ToDictionary(rv => rv.name, rv => rv);
            symbolTables.Push(scope);

            List<Expression> conditions = new List<Expression>(contexts.Select(
                ctx => TypeConfirm(ctx.pred(), false, BoolType.Get())));

            symbolTables.Pop();

            return new PostconditionBlock
            {
                conditions = conditions
            };
        }
    }
}