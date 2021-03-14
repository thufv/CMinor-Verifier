using System.Collections.Generic;

namespace piVC_thu
{
    class Expression
    {
        public Type type;
    }

    class IdentifierExpression : Expression
    {
        public string identifier;
    }

    class ConstantExpression : Expression { }

    class IntConstantExpression : ConstantExpression
    {
        public int constant;
    }

    class CallExpression : Expression
    {
        public Function function;
        public List<Expression> arguments;
    }

    class SubscriptExpression : Expression
    {
        public Expression array, subscript;
    }

    class NewArrayExpression : Expression
    {
        public Expression length;
    }

    class MemberExpression : Expression
    {
        public Struct host;
        public MemberVariable member;
    }

    class ArrayUpdateExpression : Expression
    {
        public Expression array, index, rhs;
    }

    class UnaryExpression : Expression
    {
        public Expression expression;
        public Operator op;
    }

    class BinaryExpression : UnaryExpression
    {
        public Expression le, re;
        public Operator op;
    }

    class MultiExpression : BinaryExpression { }

    class FloatDivExpression : BinaryExpression { }

    class DivExpression : BinaryExpression { }

    class ModExpression : BinaryExpression { }

    class AddExpression : BinaryExpression { }

    class SubExpression : BinaryExpression { }

    class LTExpression : BinaryExpression { }

    class LEExpression : BinaryExpression { }

    class GTExpression : BinaryExpression { }

    class GEExpression : BinaryExpression { }

    class EQExpression : BinaryExpression { }

    class NEExpression : BinaryExpression { }

    class QuantifiedExpression : Expression
    {
        HashSet<QuantifiedVariable> vars;
        Expression expression;
    }

    class ForallQuantifiedExpression : QuantifiedExpression { }

    class ExistsQuantifiedExpression : QuantifiedExpression { }

    class AndExpression : BinaryExpression { }

    class OrExpression : BinaryExpression { }

    class ImplicationExpression : BinaryExpression { }

    class IffExpression : BinaryExpression { }

    class LengthExpression : Expression { }
}