using System.Linq;
using System.Collections.Generic;

using Antlr4.Runtime;
using Antlr4.Runtime.Tree;

namespace piVC_thu
{
    partial class CFGGenerator : piBaseVisitor<Expression?>
    {
        string CalcDefName(ParserRuleContext context, ITerminalNode node)
        {
            string name = node.GetText();
            // check if the name is used by a previous function, struct or predicate
            if (functionTable.ContainsKey(name))
                throw new ParsingException(context, $"a function named '{name}' has already been defined");
            if (structTable.ContainsKey(name))
                throw new ParsingException(context, $"a struct named '{name}' has already been defined");
            if (predicateTable.ContainsKey(name))
                throw new ParsingException(context, $"a predicate named '{name}' has already been defined");
            return name;
        }

        // We don't override VisitType and VisitAtomicType,
        // as we directly use the following method CalcType.
        VarType CalcType(piParser.TypeContext context)
        {
            if (context.IDENT() != null)
            { // struct type
                string structName = context.IDENT().GetText();
                if (structTable.ContainsKey(structName))
                    return structTable[structName].type;
                else
                    throw new ParsingException(context, "unknown type");
            }
            else
            { // atomic type or array type
                AtomicType atomicType;
                switch (context.atomicType().GetText())
                {
                    case "int":
                        atomicType = IntType.Get();
                        break;
                    case "float":
                        atomicType = FloatType.Get();
                        break;
                    case "bool":
                        atomicType = BoolType.Get();
                        break;
                    default:
                        throw new ParsingException(context, "an atomic type that is not int, float, nor bool is found. Probably a bug occurs.");
                }
                if (context.ChildCount == 1)
                { // atomic type
                    return atomicType;
                }
                else
                { // array type
                    return ArrayType.Get(atomicType);
                }
            }
        }

        List<Expression> CalcRankingFunction(piParser.TerminationContext context)
        {
            return new List<Expression>(context.expr().Select(exprContext => Visit(exprContext)!));
        }

        PreConditionBlock CalcPreConditionBlock(piParser.AnnotationPreContext annotationPreContext, piParser.TerminationContext terminationContext)
        {
            Expression condition = Visit(annotationPreContext.expr())!;
            List<Expression> rankingFunction = CalcRankingFunction(terminationContext);
            return new PreConditionBlock
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

        PostConditionBlock CalcPostConditionBlock(piParser.AnnotationPostContext context)
        {
            Expression condition = Visit(context)!;
            return new PostConditionBlock
            {
                condition = condition
            };
        }

        Expression TypeConfirm(ParserRuleContext context, Expression expression, System.Type intendedType, bool annotated = false)
        {
            if (expression.type.GetType() != intendedType)
                throw new ParsingException(context, $"the expected type of the expression is {intendedType.Name} while the actual type is {expression.GetType().Name}.");
            if (!annotated && expression.annotated)
                throw new ParsingException(context, "quantifiers are only allowed to be used in annotations.");
            return expression;
        }

        Expression TypeConfirm(ParserRuleContext context, Expression expression, Type intendedType, bool annotated = false)
        {
            if (expression.type != intendedType)
                throw new ParsingException(context, $"the expected type of the expression is {intendedType.GetType().Name} while the actual type is {expression.GetType().Name}.");
            if (!annotated && expression.annotated)
                throw new ParsingException(context, "quantifiers are only allowed to be used in annotations.");
            return expression;
        }

        LocalVariable FindLocalVariable(ParserRuleContext context, string name)
        {
            // consider each symbol table reversely
            foreach (var symbolTable in symbolTables)
                if (symbolTable.ContainsKey(name))
                    return symbolTable[name];
            throw new ParsingException(context, $"cannot find local variable {name}.");
        }
    }
}