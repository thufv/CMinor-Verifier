using System.Collections.Generic;

namespace piVC_thu
{
    abstract class Expression
    {
        public VarType type = default!;
        // "annotated" expression is the expression that contains a quantifier,
        // which indicates that the expression must be regarded in annotation.
        public bool annotated = false;
    }

    sealed class IdentifierExpression : Expression
    {
        public Variable variable;
    }

    abstract class ConstantExpression : Expression { }

    sealed class IntConstantExpression : ConstantExpression
    {
        public int constant;
    }

    sealed class FloatConstantExpression : ConstantExpression
    {
        public float constant;
    }

    sealed class BoolConstantExpression : ConstantExpression
    {
        public bool constant;
    }

    sealed class CallExpression : Expression
    {
        public Function function;
        public List<Expression> arguments;
    }

    sealed class SubscriptExpression : Expression
    {
        public Expression array, subscript;
    }

    sealed class NewArrayExpression : Expression
    {
        public Expression length;
    }

    sealed class MemberExpression : Expression
    {
        public Struct host;
        public MemberVariable member;
    }

    sealed class ArrayUpdateExpression : Expression
    {
        public Expression array, index, rhs;
    }

    abstract class UnaryExpression : Expression
    {
        public Expression expression;
    }

    sealed class NotExpression : UnaryExpression
    {
    }

    sealed class NegExpression : UnaryExpression { }

    abstract class BinaryExpression : Expression
    {
        public Expression le, re;
    }

    sealed class MultiExpression : BinaryExpression { }

    sealed class FloatDivExpression : BinaryExpression { }

    sealed class DivExpression : BinaryExpression { }

    sealed class ModExpression : BinaryExpression { }

    sealed class AddExpression : BinaryExpression { }

    sealed class SubExpression : BinaryExpression { }

    sealed class LTExpression : BinaryExpression { }

    sealed class LEExpression : BinaryExpression { }

    sealed class GTExpression : BinaryExpression { }

    sealed class GEExpression : BinaryExpression { }

    sealed class EQExpression : BinaryExpression { }

    sealed class NEExpression : BinaryExpression { }

    abstract class QuantifiedExpression : Expression
    {
        HashSet<QuantifiedVariable> vars;
        Expression expression;
    }

    sealed class ForallQuantifiedExpression : QuantifiedExpression { }

    sealed class ExistsQuantifiedExpression : QuantifiedExpression { }

    sealed class AndExpression : BinaryExpression { }

    sealed class OrExpression : BinaryExpression { }

    sealed class ImplicationExpression : BinaryExpression { }

    sealed class IffExpression : BinaryExpression { }

    sealed class LengthExpression : Expression { }
}