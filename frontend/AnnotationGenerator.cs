using System.Linq;
using System.Collections.Generic;
using Antlr4.Runtime.Misc;

namespace piVC_thu
{
    partial class CFGGenerator : piBaseVisitor<Expression?>
    {
        public override Expression VisitAnnotationWithLabel([NotNull] piParser.AnnotationWithLabelContext context)
        {
            // To make life easier, we just ignore the identifier for the annotation here!
            // You may feel annoyed about this choice, but I feel really good!
            // Because the identifier of annotation is really hard to handle.
            // If you don't believe that, let me ask, what symbol field should the identifier
            // of loop invariant fall in? What do we do if an annotation identifier
            // conflict with a local variable, function, predicate or class? It's too tedious!
            return TypeConfirm(context, Visit(context.expr())!, BoolType.Get(annotated: true));
        }

        // The following methods are out of control of visitor pattern,
        // as we need a differnt return type...
        List<Expression> CalcRankingFunction(piParser.TerminationContext context)
        {
            return new List<Expression>(context.expr().Select(exprContext => Visit(exprContext)!));
        }

        PreconditionBlock CalcPreconditionBlock(piParser.AnnotationPreContext annotationPreContext, piParser.TerminationContext terminationContext)
        {
            Expression condition = Visit(annotationPreContext.expr())!;
            List<Expression> rankingFunction = CalcRankingFunction(terminationContext);
            return new PreconditionBlock
            {
                condition = condition,
                rankingFunction = rankingFunction
            };
        }

        LoopHeadBlock CalcLoopHeadBlock(piParser.AnnotationWithLabelContext invariantContext, piParser.TerminationContext terminationContext)
        {
            Expression invariant = Visit(invariantContext.expr())!;
            List<Expression> rankingFunction = CalcRankingFunction(terminationContext);
            return new LoopHeadBlock
            {
                invariant = invariant,
                rankingFunction = rankingFunction
            };
        }

        PostconditionBlock CalcPostconditionBlock(piParser.AnnotationPostContext context)
        {
            if (currentFunction == null)
                throw new ParsingException(context, "there's no current function. Probably a bug occurs.");

            // 这里我们开一个只有 rv 的假作用域
            if (currentFunction.rv != null)
                symbolTables.Push(new Dictionary<string, LocalVariable>() {
                    { "rv", currentFunction.rv}
                });

            Expression condition = Visit(context)!;

            if (currentFunction.rv != null)
                symbolTables.Pop();

            return new PostconditionBlock
            {
                condition = condition
            };
        }
    }
}