using System.IO;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace piVC_thu
{
    abstract class Expression
    {
        public VarType type = default!;

        public abstract void Print(TextWriter writer);
    }

    sealed class VariableExpression : Expression
    {
        public Variable variable = default!;

        public override void Print(TextWriter writer)
        {
            writer.Write(variable.name);
        }
    }

    abstract class ConstantExpression : Expression { }

    sealed class IntConstantExpression : ConstantExpression
    {
        public int constant;

        public override void Print(TextWriter writer)
        {
            writer.Write(constant);
        }
    }

    sealed class FloatConstantExpression : ConstantExpression
    {
        public float constant;

        public override void Print(TextWriter writer)
        {
            writer.Write(constant);
        }
    }

    sealed class BoolConstantExpression : ConstantExpression
    {
        public bool constant;

        public override void Print(TextWriter writer)
        {
            writer.Write(constant ? "true" : "false");
        }
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

        public void Print(TextWriter writer)
        {
            writer.Write($"{function.name}(");
            for (int i = 0; i < argumentVariables.Length; ++i)
            {
                if (i != 0) writer.Write(", ");
                writer.Write(argumentVariables[i].name);
            }
            writer.Write(")");
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

        public override void Print(TextWriter writer)
        {
            writer.Write($"{predicate.name}(");
            for (int i = 0; i < argumentExpressions.Length; ++i)
            {
                if (i != 0) writer.Write(", ");
                argumentExpressions[i].Print(writer);
            }
            writer.Write(")");
        }
    }

    sealed class SubscriptExpression : Expression
    {
        public Expression array = default!, subscript = default!;

        public override void Print(TextWriter writer)
        {
            array.Print(writer);
            writer.Write("[");
            subscript.Print(writer);
            writer.Write("]");
        }
    }

    sealed class NewArrayExpression : Expression
    {
        public AtomicType atomicType = default!;
        public Expression length = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(this.length.type is IntType);
        }

        public override void Print(TextWriter writer)
        {
            writer.Write($"(new {atomicType}[");
            length.Print(writer);
            writer.Write("]");
        }
    }

    sealed class ArrayUpdateExpression : Expression
    {
        public Expression array = default!, index = default!, rhs = default!;

        public override void Print(TextWriter writer)
        {
            array.Print(writer);
            writer.Write("{");
            index.Print(writer);
            writer.Write(" <- ");
            rhs.Print(writer);
            writer.Write("}");
        }
    }

    abstract class UnaryExpression : Expression
    {
        public Expression expression = default!;
    }

    sealed class NotExpression : UnaryExpression
    {
        public override void Print(TextWriter writer)
        {
            writer.Write("!");
            expression.Print(writer);
        }
    }

    sealed class NegExpression : UnaryExpression
    {
        public override void Print(TextWriter writer)
        {
            writer.Write("-");
            expression.Print(writer);
        }
    }

    abstract class BinaryExpression : Expression
    {
        public Expression le = default!, re = default!;

        // 由于我们删去了可能的括号，为了避免歧义，这里必须要强制加上括号

        public override void Print(TextWriter writer)
        {
            writer.Write("(");
            le.Print(writer);
            writer.Write(GetOperator());
            re.Print(writer);
            writer.Write(")");
        }

        protected abstract string GetOperator();
    }

    sealed class MultiExpression : BinaryExpression
    {
        protected override string GetOperator() => "*";
    }

    sealed class FloatDivExpression : BinaryExpression
    {
        protected override string GetOperator() => "/";
    }

    sealed class DivExpression : BinaryExpression
    {
        protected override string GetOperator() => "div";
    }

    sealed class ModExpression : BinaryExpression
    {
        protected override string GetOperator() => "%";
    }

    sealed class AddExpression : BinaryExpression
    {
        protected override string GetOperator() => "+";
    }

    sealed class SubExpression : BinaryExpression
    {
        protected override string GetOperator() => "-";
    }

    sealed class LTExpression : BinaryExpression
    {
        protected override string GetOperator() => "<";
    }

    sealed class LEExpression : BinaryExpression
    {
        protected override string GetOperator() => "<=";
    }

    sealed class GTExpression : BinaryExpression
    {
        protected override string GetOperator() => ">";
    }

    sealed class GEExpression : BinaryExpression
    {
        protected override string GetOperator() => ">=";
    }

    sealed class EQExpression : BinaryExpression
    {
        protected override string GetOperator() => "=";
    }

    sealed class NEExpression : BinaryExpression
    {
        protected override string GetOperator() => "!=";
    }

    abstract class QuantifiedExpression : Expression
    {
        public Dictionary<string, QuantifiedVariable> vars = default!;
        public Expression expression = default!;

        public override void Print(TextWriter writer)
        {
            writer.Write($"({GetQuantifier()} ");
            bool isFirst = true;
            foreach (var v in vars.Values)
            {
                if (isFirst) isFirst = false;
                else writer.Write(", ");
                writer.Write($"({v.name}: {v.type})");
            }
            writer.Write(". ");
            expression.Print(writer);
            writer.Write(")");
        }

        protected abstract string GetQuantifier();
    }

    sealed class ForallQuantifiedExpression : QuantifiedExpression
    {
        protected override string GetQuantifier() => "∀";
    }

    sealed class ExistsQuantifiedExpression : QuantifiedExpression
    {
        protected override string GetQuantifier() => "∃";
    }

    sealed class AndExpression : BinaryExpression
    {
        protected override string GetOperator() => "&&";
    }

    sealed class OrExpression : BinaryExpression
    {
        protected override string GetOperator() => "||";
    }

    sealed class ImplicationExpression : BinaryExpression
    {
        protected override string GetOperator() => "->";
    }

    sealed class IffExpression : BinaryExpression
    {
        protected override string GetOperator() => "<->";
    }

    sealed class LengthExpression : UnaryExpression
    {
        public override void Print(TextWriter writer)
        {
            writer.Write("|");
            expression.Print(writer);
            writer.Write("|");
        }
    }
}