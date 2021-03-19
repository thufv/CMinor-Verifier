using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace piVC_thu
{
    abstract class Expression
    {
        public VarType type = default!;
    }

    sealed class VariableExpression : Expression
    {
        public Variable variable = default!;
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

    // 这是一个极为特殊的 expression，我们规定 expression 的类型不能为 void，
    // 所以 function call 不能算在常规的 expression 里面。
    // 并且，function call 只会出现在 FunctionCallStatement 这个 statement 里。
    sealed class FunctionCallExpression
    {
        public Function function = default!;
        public Variable[] argumentVariables = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(this.argumentVariables.Length == function.type.paraTypes.Length);
        }
    }

    sealed class PredicateCallExpression : Expression
    {
        public Predicate predicate = default!;
        public Expression[] argumentExpressions = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(this.argumentExpressions.Length == predicate.type.paraTypes.Length);
        }
    }

    sealed class SubscriptExpression : Expression
    {
        public Expression array = default!, subscript = default!;
    }

    sealed class NewArrayExpression : Expression
    {
        public Expression length = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(this.length.type is IntType);
        }
    }

    sealed class ArrayUpdateExpression : Expression
    {
        public Expression array = default!, index = default!, rhs = default!;
    }

    abstract class UnaryExpression : Expression
    {
        public Expression expression = default!;
    }

    sealed class NotExpression : UnaryExpression { }

    sealed class NegExpression : UnaryExpression { }

    abstract class BinaryExpression : Expression
    {
        public Expression le = default!, re = default!;
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
        public Dictionary<string, QuantifiedVariable> vars = default!;
        public Expression expression = default!;
    }

    sealed class ForallQuantifiedExpression : QuantifiedExpression { }

    sealed class ExistsQuantifiedExpression : QuantifiedExpression { }

    sealed class AndExpression : BinaryExpression { }

    sealed class OrExpression : BinaryExpression { }

    sealed class ImplicationExpression : BinaryExpression { }

    sealed class IffExpression : BinaryExpression { }

    sealed class LengthExpression : UnaryExpression { }
}