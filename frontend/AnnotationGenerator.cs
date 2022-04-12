using System;
using System.Linq;
using System.Diagnostics;
using System.Collections.Generic;

using Antlr4.Runtime.Misc;

namespace cminor
{
    partial class CFGGenerator : CMinorBaseVisitor<Expression?>
    {
        public override Expression VisitAnnotationWithLabel([NotNull] CMinorParser.AnnotationWithLabelContext context)
        {
            // To make life easier, we just ignore the identifier for the annotation here!
            // You may feel annoyed about this choice, but I feel really good!
            // Because the identifier of annotation is really hard to handle.
            // If you don't believe that, let me ask, what symbol field should the identifier
            // of loop invariant fall in? What do we do if an annotation identifier
            // conflict with a local variable, function, predicate or class? It's too tedious!
            return TypeConfirm(context.expr(), BoolType.Get());
        }

        // The following methods are out of control of visitor pattern,
        // as we need a differnt return type...
        List<Expression> CalcRankingFunction([NotNull] CMinorParser.TerminationContext context)
        {
            return new List<Expression>(context.expr().Select(exprContext => TypeConfirm(exprContext, IntType.Get())));
        }

        PreconditionBlock CalcPreconditionBlock([NotNull] CMinorParser.AnnotationPreContext annotationPreContext, CMinorParser.TerminationContext terminationContext)
        {
            Expression condition = NotNullConfirm(annotationPreContext.expr());
            List<Expression> rankingFunction =
                terminationContext != null
                    ? CalcRankingFunction(terminationContext)
                    : new List<Expression>();
            return new PreconditionBlock
            {
                condition = condition,
                rankingFunction = rankingFunction
            };
        }

        LoopHeadBlock CalcLoopHeadBlock([NotNull] CMinorParser.AnnotationWithLabelContext invariantContext, CMinorParser.TerminationContext terminationContext)
        {
            Debug.Assert(currentFunction != null);
            Debug.Assert(currentBlock != null);

            Expression invariant = NotNullConfirm(invariantContext.expr());
            List<Expression> rankingFunction =
                terminationContext != null
                    ? CalcRankingFunction(terminationContext)
                    : new List<Expression>();
            return new LoopHeadBlock(currentFunction, currentBlock)
            {
                invariant = invariant,
                rankingFunction = rankingFunction
            };
        }

        PostconditionBlock CalcPostconditionBlock([NotNull] CMinorParser.AnnotationPostContext context, List<LocalVariable> rvs)
        {
            // 这里我们开一个只有 rv 的假作用域
            var scope = new Dictionary<string, LocalVariable>();
            Debug.Assert(rvs.Count <= 1);
            foreach (LocalVariable rv in rvs)
            {
                scope.Add("rv", rv);
            }
            symbolTables.Push(scope);

            Expression condition = NotNullConfirm(context);

            symbolTables.Pop();

            return new PostconditionBlock
            {
                condition = condition
            };
        }
    }
}