using System;
using System.Diagnostics;

using Antlr4.Runtime.Misc;

namespace cminor
{
    partial class CFGGenerator : CMinorParserBaseVisitor<Expression?>
    {
        public override Expression VisitIdentTerm([NotNull] CMinorParser.IdentTermContext context)
        {
            LocalVariable variable = FindVariable(context, context.IDENT().GetText());
            return new VariableExpression(variable);
        }

        public override Expression VisitResTerm([NotNull] CMinorParser.ResTermContext context)
        {
            LocalVariable variable = FindVariable(context, "\\result");
            return new VariableExpression(variable);
        }

        public override Expression VisitConstTerm([NotNull] CMinorParser.ConstTermContext context)
        {
            return NotNullConfirm(context.logicConstant());
        }

        public override Expression? VisitParArithTerm([NotNull] CMinorParser.ParArithTermContext context)
        {
            return Visit(context.arithTerm());
        }

        public override Expression? VisitParTerm([NotNull] CMinorParser.ParTermContext context)
        {
            return Visit(context.term());
        }

        public override Expression VisitArrAccessTerm([NotNull] CMinorParser.ArrAccessTermContext context)
        {
            Expression array = NotNullConfirm(context.arithTerm()[0]);

            Expression subscript = TypeConfirm(context.arithTerm()[1], false, IntType.Get());
            return new ArrayAccessExpression(array, subscript);

            throw new ParsingException(context, $"request for an element in a non-array expression.");
        }

        public override Expression VisitMemTerm([NotNull] CMinorParser.MemTermContext context)
        {
            Expression structExpression = NotNullConfirm(context.arithTerm());
            string memberName = context.IDENT().GetText();

            // struct 只能是变量或者函数的返回值，
            // 函数的返回值会被用临时变量处理，
            // 所以这里肯定会是一个局部变量。
            if (structExpression is not VariableExpression)
                throw new ParsingException(context, $"request for member '{memberName}' in a non-variable expression. Probably a bug occurs.");

            // 从表达式得到变量
            Variable structVariable = ((VariableExpression)structExpression).variable;
            if (structVariable is not StructVariable)
                throw new ParsingException(context, $"request for member '{memberName}' in an expression of non-struct type '{structExpression.type}'");

            // 从变量得到定义
            Struct structDefinition = ((StructType)(structExpression.type)).structDefinition;
            if (!structDefinition.members.ContainsKey(memberName))
                throw new ParsingException(context, $"'struct {structDefinition.name}' has no member named '{memberName}'.");

            // 将成员变量转化成一个局部变量
            MemberVariable memberVariable = structDefinition.members[memberName];
            var members = ((StructVariable)structVariable).members;
            if (!members.ContainsKey(memberName))
            { // 如果之前已经转化过一次了，那么就得直接用之前转化出来的
                members[memberName] = new LocalVariable
                {
                    name = structVariable.name + "$" + memberName,
                    type = memberVariable.type
                };
            }

            return new VariableExpression(members[memberName]);
        }

        public override Expression VisitUnaryTerm([NotNull] CMinorParser.UnaryTermContext context)
        {
            string op = context.GetChild(0).GetText();
            switch (op)
            {
                case "!":
                    {
                        Expression expression = TypeConfirm(context.arithTerm(), false, BoolType.Get());
                        return new NotExpression(expression);
                    }
                case "-":
                    {
                        Expression expression = TypeConfirm(context.arithTerm(), false, IntType.Get(), FloatType.Get());
                        return new NegExpression(expression);
                    }
                default:
                    throw new ArgumentException(
                        message: $"operator '{op}' is neither '!' nor '-'. Probably a bug occurs.",
                        paramName: nameof(op));
            }
        }

        public override Expression VisitMulTerm([NotNull] CMinorParser.MulTermContext context)
        {
            string op = context.GetChild(1).GetText();

            switch (op)
            {
                case "*":
                    {
                        Expression le = TypeConfirm(context.arithTerm()[0], false, IntType.Get(), FloatType.Get());
                        Expression re = TypeConfirm(context.arithTerm()[1], false, IntType.Get(), FloatType.Get());
                        if (!(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType))
                            throw new ParsingException(context, "the type of expression between '*' must be both 'int' or 'float'.");
                        return new MultiExpression(le, re);
                    }
                case "/":
                    {
                        Expression le = TypeConfirm(context.arithTerm()[0], false, IntType.Get(), FloatType.Get());
                        Expression re = TypeConfirm(context.arithTerm()[1], false, IntType.Get(), FloatType.Get());
                        if (!(le.type is FloatType && re.type is FloatType || le.type is IntType && re.type is IntType))
                            throw new ParsingException(context, "the type of expression between '/' must be both 'float'.");
                        return new DivExpression(le, re);
                    }
                case "%":
                    {
                        Expression le = TypeConfirm(context.arithTerm()[0], false, IntType.Get());
                        Expression re = TypeConfirm(context.arithTerm()[1], false, IntType.Get());
                        if (!(le.type is IntType && re.type is IntType))
                            throw new ParsingException(context, "the type of expression '%' must be both 'int'.");
                        return new ModExpression(le, re);
                    }
                default:
                    throw new ArgumentException(
                        message: $"operator '{op}' is neither '*', '/', 'div' nor '%'. Probably a bug occurs.",
                        paramName: nameof(op));
            }
        }

        public override Expression VisitAddTerm([NotNull] CMinorParser.AddTermContext context)
        {
            Expression le = TypeConfirm(context.arithTerm()[0], false, IntType.Get(), FloatType.Get());
            Expression re = TypeConfirm(context.arithTerm()[1], false, IntType.Get(), FloatType.Get());

            if (!(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType))
                throw new ParsingException(context, "the type of expression between '+' or '-' must be both int or float.");

            string op = context.GetChild(1).GetText();
            Expression e = BinaryExpression.FromOp(op, le, re);
            return e;
        }

        public override Expression VisitOrdTerm([NotNull] CMinorParser.OrdTermContext context)
        {
            Expression le = TypeConfirm(context.term()[0], false, IntType.Get(), FloatType.Get());
            Expression re = TypeConfirm(context.term()[1], false, IntType.Get(), FloatType.Get());

            if (!(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType))
                throw new ParsingException(context, $"the type of expression between inequality must be both int or float, while now they are '{le.type}' and '{re.type}'.");

            string op = context.GetChild(1).GetText();
            Expression e = BinaryExpression.FromOp(op, le, re);
            return e;
        }

        public override Expression VisitEquTerm([NotNull] CMinorParser.EquTermContext context)
        {
            Expression le = NotNullConfirm(context.term()[0]);
            Expression re = NotNullConfirm(context.term()[1]);

            if (!(le.type is AtomicType && re.type is AtomicType && le.type == re.type))
                throw new ParsingException(context, $"the type of expression between '=' or '!=' must be of same atomic type, while now they are '{le.type}' and '{re.type}'.");

            string op = context.GetChild(1).GetText();
            Expression e = BinaryExpression.FromOp(op, le, re);
            return e;
        }

        public override Expression VisitAndTerm([NotNull] CMinorParser.AndTermContext context)
        {
            Expression le = TypeConfirm(context.term()[0], false, BoolType.Get());
            Expression re = TypeConfirm(context.term()[1], false, BoolType.Get());
            Expression e = new AndExpression(le, re);
            return e;
        }

        public override Expression VisitOrTerm([NotNull] CMinorParser.OrTermContext context)
        {
            Expression le = TypeConfirm(context.term()[0], false, BoolType.Get());
            Expression re = TypeConfirm(context.term()[1], false, BoolType.Get());
            Expression e = new OrExpression(le, re);
            return e;
        }

        public override Expression VisitArrUpdTerm([NotNull] CMinorParser.ArrUpdTermContext context)
        {
            Expression array = NotNullConfirm(context.arithTerm()[0]);
            if (array.type is ArrayType at)
            {
                Debug.Assert(currentBlock != null);

                VariableExpression subscript = CompressedExpression(TypeConfirm(context.arithTerm()[1], false, IntType.Get()), counter.GetSub);

                // runtime assertion: subscript >= 0
                currentBlock.AddStatement(new AssertStatement()
                {
                    pred = new LEExpression(new IntConstantExpression(0), subscript)
                });

                Expression rhs = TypeConfirm(context.arithTerm()[2], false, ((ArrayType)(array.type)).atomicType);

                // runtime assertion: subscript < length
                currentBlock.AddStatement(new AssertStatement()
                {
                    pred = new LTExpression(subscript, new LengthExpression(array))
                });

                if (array is ArrayUpdateExpression aue)
                {
                    return new ArrayUpdateExpression(array, subscript, rhs, aue.length);
                }
                else if (array is VariableExpression ve && ve.variable is ArrayVariable av)
                {
                    return new ArrayUpdateExpression(array, subscript, rhs, new VariableExpression(av.length));
                }
                else
                    throw new ArgumentException(
                        message: "the expression to update as array is neither single variable expression nor array update expression. Probably a bug occurs.",
                        paramName: nameof(array));
            }
            else
                throw new ParsingException(context, $"updating a non-array expression as it is an array.");
        }

        public override Expression VisitLogicConstant([NotNull] CMinorParser.LogicConstantContext context)
        {
            if (context.INT_CONSTANT() != null)
                return new IntConstantExpression(
                    int.Parse(context.INT_CONSTANT().GetText()));
            else if (context.FLOAT_CONSTANT() != null)
                return new FloatConstantExpression(
                    float.Parse(context.FLOAT_CONSTANT().GetText()));
            else if (context.GetText() == "\\true")
                return new BoolConstantExpression(true);
            else
            {
                Debug.Assert(context.GetText() == "\\false");
                return new BoolConstantExpression(false);
            }
        }
    }
}