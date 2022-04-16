using System;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics;

using Antlr4.Runtime.Misc;

namespace cminor
{
    partial class CFGGenerator : CMinorParserBaseVisitor<Expression?>
    {
        public override Expression VisitTruePred([NotNull] CMinorParser.TruePredContext context)
        {
            return new BoolConstantExpression(true);
        }

        public override Expression VisitFalsePred([NotNull] CMinorParser.FalsePredContext context)
        {
            return new BoolConstantExpression(false);
        }

        public override Expression VisitCmpPred([NotNull] CMinorParser.CmpPredContext context)
        {
            // 所有的 term 的 type 必须相同
            var exprs = new List<Expression>();
            for (int i = 0; i < context.ChildCount; i += 2)
            {
                exprs.Add(NotNullConfirm(context.arithTerm()[i >> 1]));
                if (exprs.Last().type != exprs.First().type)
                    throw new ParsingException(context, $"The types of terms in CmpPred must be same, but there are {exprs.Last().type} and {exprs.First().type}.");
            }

            var ops = new List<String>();
            for (int i = 1; i < context.ChildCount; i += 2)
                ops.Add(context.GetChild(i).GetText());
            if (ops.Count > 1
                && !(new HashSet<String>(ops)).IsSubsetOf(new HashSet<String> { "<", "<=", "==" })
                && !(new HashSet<String>(ops)).IsSubsetOf(new HashSet<String> { ">", ">=", "==" }))
                throw new ParsingException(context, $"The directions of operators are different: {ops}");

            Expression e = BinaryExpression.FromOp(ops[0], exprs[0], exprs[1]);
            for (int i = 1; i < ops.Count; ++i)
                e = new AndExpression(e, BinaryExpression.FromOp(ops[i], exprs[i], exprs[i + 1]));
            return e;
        }

        public override Expression VisitCallPred([NotNull] CMinorParser.CallPredContext context)
        {
            string calledName = context.IDENT().GetText();
            if (LocalVariableExists(calledName))
                throw new ParsingException(context, "call a variable that is neither function nor predicate.");

            if (!predicateTable.ContainsKey(calledName))
                throw new ParsingException(context, $"no predicate named '{calledName}'");

            // 这种其实很简单，正常来就行啦QAQ
            Predicate predicate = predicateTable[calledName];

            // 把所有参数算出来！
            int paraNum = predicate.type.paraTypes.Count;
            if (paraNum != context.term().Length)
                throw new ParsingException(context, $"the number of arguments passed to function '{calledName}' is not the same as defined.");
            List<Expression> argumentExpressions = new List<Expression>();
            for (int i = 0; i < paraNum; ++i)
            {
                Expression argumentExpression = TypeConfirm(context.term()[i], predicate.type.paraTypes[i]);
                if (argumentExpression.type is StructType)
                {
                    Debug.Assert(argumentExpression is VariableExpression);
                    Debug.Assert(((VariableExpression)argumentExpression).variable is StructVariable);
                    foreach (LocalVariable member in ((StructVariable)(((VariableExpression)argumentExpression).variable)).members.Values)
                    {
                        argumentExpressions.Add(argumentExpression);
                    }
                }
                else
                {
                    argumentExpressions.Add(argumentExpression);
                }
            }

            return new PredicateCallExpression(predicate, argumentExpressions);
        }

        public override Expression? VisitParPred([NotNull] CMinorParser.ParPredContext context)
        {
            return Visit(context.pred());
        }

        public override Expression VisitConPred([NotNull] CMinorParser.ConPredContext context)
        {
            Expression le = TypeConfirm(context.pred()[0], BoolType.Get());
            Expression re = TypeConfirm(context.pred()[1], BoolType.Get());
            Expression e = new AndExpression(le, re);
            return e;
        }

        public override Expression VisitDisPred([NotNull] CMinorParser.DisPredContext context)
        {
            Expression le = TypeConfirm(context.pred()[0], BoolType.Get());
            Expression re = TypeConfirm(context.pred()[1], BoolType.Get());
            Expression e = new OrExpression(le, re);
            return e;
        }

        public override Expression VisitImpPred([NotNull] CMinorParser.ImpPredContext context)
        {
            Expression le = TypeConfirm(context.pred()[0], BoolType.Get());
            Expression re = TypeConfirm(context.pred()[1], BoolType.Get());
            Expression e = new ImplicationExpression(le, re);
            return e;
        }

        public override Expression VisitIffPred([NotNull] CMinorParser.IffPredContext context)
        {
            Expression le = TypeConfirm(context.pred()[0], BoolType.Get());
            Expression re = TypeConfirm(context.pred()[1], BoolType.Get());
            Expression e = new IffExpression(le, re);
            return e;
        }

        public override Expression VisitNegPred([NotNull] CMinorParser.NegPredContext context)
        {
            Expression expression = TypeConfirm(context.pred(), BoolType.Get());
            Expression e = new NotExpression(expression);
            return e;
        }

        public override Expression VisitXorPred([NotNull] CMinorParser.XorPredContext context)
        {
            Expression le = TypeConfirm(context.pred()[0], BoolType.Get());
            Expression re = TypeConfirm(context.pred()[1], BoolType.Get());
            Expression e = new XorExpression(le, re);
            return e;
        }

        public override Expression VisitQuantiPred([NotNull] CMinorParser.QuantiPredContext context)
        {
            // 这里我们开一个新的作用域
            // 当然 alpha-renaming 也是要做的
            symbolTables.Push(new Dictionary<string, LocalVariable>());
            Dictionary<string, QuantifiedVariable> vars = new Dictionary<string, QuantifiedVariable>();
            foreach ((AtomicType type, List<String> names) in context.binder().Select(
                ctx =>
                    (
                        AtomicType.FromString(ctx.GetChild(0).GetText()),
                        ctx.IDENT().ToArray().Select(identContext => identContext.GetText()).ToList()
                    )))
            {
                foreach (String name in names)
                {
                    if (vars.ContainsKey(name))
                        throw new ParsingException(context, $"duplicate quantified variable {name}");
                    QuantifiedVariable variable = new QuantifiedVariable
                    {
                        name = counter.GetVariable(name),
                        type = type
                    };
                    symbolTables.Peek().Add(name, variable);
                    vars.Add(name, variable);
                }
            }

            Expression expression = TypeConfirm(context.pred(), BoolType.Get());

            symbolTables.Pop();

            if (context.GetChild(0).GetText() == "\\forall")
                return new ForallQuantifiedExpression(vars, expression);
            else
            {
                Debug.Assert(context.GetChild(0).GetText() == "\\exists");
                return new ExistsQuantifiedExpression(vars, expression);
            }
        }
    }
}