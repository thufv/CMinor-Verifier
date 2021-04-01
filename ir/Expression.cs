using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;

using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace piVC_thu
{
    abstract class Expression
    {
        public VarType type = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            // 如果表达式的类型是 struct，那么它一定是一个 VariableExpression
            // 注意：FunctionCallExpression 并不是 Expression 的 subclass
            Contract.Invariant(!(type is StructType) || (this is VariableExpression));

            // 如果一个 expression 是一个 array expression，那么有且仅有两种情况：
            // 1. 它是一个 variable expression，并且其中的 variable 是一个 array variable
            // 2. 它是一个 array update expression
            Contract.Invariant(!(type is ArrayType) || (this is VariableExpression || this is ArrayUpdateExpression));
        }

        public abstract void Print(TextWriter writer);

        public abstract Expression Substitute(LocalVariable s, Expression t);

        public abstract HashSet<LocalVariable> GetFreeVariables();
    }

    sealed class VariableExpression : Expression
    {
        public LocalVariable variable;

        public VariableExpression(LocalVariable variable)
        {
            this.type = variable.type;
            this.variable = variable;
        }

        public override void Print(TextWriter writer)
        {
            writer.Write(variable.name);
        }

        public override Expression Substitute(LocalVariable s, Expression t)
        {
            if (s == variable)
                return t;
            else
            {
                Debug.Assert(s.name != variable.name);
                return this;
            }
        }

        public override HashSet<LocalVariable> GetFreeVariables()
        {
            return new HashSet<LocalVariable> { variable };
        }
    }

    abstract class ConstantExpression : Expression
    {
        public override Expression Substitute(LocalVariable s, Expression t)
        {
            return this;
        }

        public override HashSet<LocalVariable> GetFreeVariables()
        {
            return new HashSet<LocalVariable>();
        }
    }

    sealed class IntConstantExpression : ConstantExpression
    {
        public int constant;

        public IntConstantExpression(int constant)
        {
            this.type = IntType.Get();
            this.constant = constant;
        }

        public override void Print(TextWriter writer)
        {
            writer.Write(constant);
        }
    }

    sealed class FloatConstantExpression : ConstantExpression
    {
        public float constant;

        public FloatConstantExpression(float constant)
        {
            this.type = FloatType.Get();
            this.constant = constant;
        }

        public override void Print(TextWriter writer)
        {
            writer.Write(constant);
        }
    }

    sealed class BoolConstantExpression : ConstantExpression
    {
        public bool constant;

        public BoolConstantExpression(bool constant)
        {
            this.type = BoolType.Get();
            this.constant = constant;
        }

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
        public List<LocalVariable> argumentVariables = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(this.argumentVariables.Count == function.type.paraTypes.Count);
        }

        public void Print(TextWriter writer)
        {
            writer.Write($"{function.name}(");
            for (int i = 0; i < argumentVariables.Count; ++i)
            {
                if (i != 0) writer.Write(", ");
                writer.Write(argumentVariables[i].name);
            }
            writer.Write(")");
        }
    }

    sealed class PredicateCallExpression : Expression
    {
        public Predicate predicate;
        public List<Expression> argumentExpressions;

        public PredicateCallExpression(Predicate predicate, List<Expression> argumentExpressions)
        {
            this.type = BoolType.Get();
            this.predicate = predicate;
            this.argumentExpressions = argumentExpressions;
        }

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(this.argumentExpressions.Count == predicate.type.paraTypes.Count);
        }

        public override void Print(TextWriter writer)
        {
            writer.Write($"{predicate.name}(");
            for (int i = 0; i < argumentExpressions.Count; ++i)
            {
                if (i != 0) writer.Write(", ");
                argumentExpressions[i].Print(writer);
            }
            writer.Write(")");
        }

        public override Expression Substitute(LocalVariable s, Expression t)
        {
            return new PredicateCallExpression(predicate,
                new List<Expression>(
                    argumentExpressions.Select(
                        argumentExpression =>
                            argumentExpression.Substitute(s, t))));
        }

        public override HashSet<LocalVariable> GetFreeVariables()
        {
            var fvs = new HashSet<LocalVariable>();
            foreach (var ae in argumentExpressions)
                fvs.UnionWith(ae.GetFreeVariables());
            return fvs;
        }
    }

    sealed class SubscriptExpression : Expression
    {
        public Expression array;
        public Expression subscript;

        public SubscriptExpression(Expression array, Expression subscript)
        {
            Debug.Assert(array.type is ArrayType);
            Debug.Assert(subscript.type is IntType);

            this.type = ((ArrayType)(array.type)).atomicType;
            this.array = array;
            this.subscript = subscript;
        }

        public override void Print(TextWriter writer)
        {
            array.Print(writer);
            writer.Write("[");
            subscript.Print(writer);
            writer.Write("]");
        }

        public override Expression Substitute(LocalVariable s, Expression t)
        {
            return new SubscriptExpression(array.Substitute(s, t), subscript.Substitute(s, t));
        }

        public override HashSet<LocalVariable> GetFreeVariables()
        {
            var fvs = array.GetFreeVariables();
            fvs.UnionWith(subscript.GetFreeVariables());
            return fvs;
        }
    }

    sealed class ArrayUpdateExpression : Expression
    {
        public Expression array;
        public Expression subscript;
        public Expression rhs;

        // The length is not actually a part of expression,
        // but derived from the array.
        public VariableExpression length;

        public ArrayUpdateExpression(Expression array, Expression subscript, Expression rhs, VariableExpression length)
        {
            Debug.Assert(array.type is ArrayType);
            Debug.Assert(subscript.type is IntType);
            Debug.Assert(((ArrayType)(array.type)).atomicType == rhs.type);
            Debug.Assert(length.type is IntType);

            this.type = array.type;
            this.array = array;
            this.subscript = subscript;
            this.rhs = rhs;
            this.length = length;
        }

        public override void Print(TextWriter writer)
        {
            array.Print(writer);
            writer.Write("{");
            subscript.Print(writer);
            writer.Write(" <- ");
            rhs.Print(writer);
            writer.Write("}");
        }

        public override Expression Substitute(LocalVariable s, Expression t)
        {
            Expression array = this.array.Substitute(s, t);
            Expression subscript = this.subscript.Substitute(s, t);
            Expression rhs = this.rhs.Substitute(s, t);

            if (array is VariableExpression ve && ve.variable is ArrayVariable av)
            {
                return new ArrayUpdateExpression(array, subscript, rhs, new VariableExpression(av.length));
            }
            else
            {
                Debug.Assert(array is ArrayUpdateExpression);
                return new ArrayUpdateExpression(array, subscript, rhs, ((ArrayUpdateExpression)array).length);
            }
        }

        public override HashSet<LocalVariable> GetFreeVariables()
        {
            var fvs = array.GetFreeVariables();
            fvs.UnionWith(subscript.GetFreeVariables());
            fvs.UnionWith(rhs.GetFreeVariables());
            return fvs;
        }
    }

    abstract class UnaryExpression : Expression
    {
        public Expression expression = default!;

        public override HashSet<LocalVariable> GetFreeVariables()
        {
            return expression.GetFreeVariables();
        }

        public override Expression Substitute(LocalVariable s, Expression t)
        {
            Object? result = Activator.CreateInstance(this.GetType(), new object[] {
                expression.Substitute(s, t)
            });
            Debug.Assert(result != null);
            Debug.Assert(result is Expression);
            return (Expression)result;
        }
    }

    sealed class NotExpression : UnaryExpression
    {
        public NotExpression(Expression expression)
        {
            Debug.Assert(expression.type is BoolType);
            this.type = expression.type;
            this.expression = expression;
        }
        public override void Print(TextWriter writer)
        {
            writer.Write("!");
            expression.Print(writer);
        }
    }

    sealed class NegExpression : UnaryExpression
    {
        public NegExpression(Expression expression)
        {
            Debug.Assert(expression.type is IntType || expression.type is FloatType);
            this.type = expression.type;
            this.expression = expression;
        }
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
            writer.Write($" {GetOperator()} ");
            re.Print(writer);
            writer.Write(")");
        }

        protected abstract string GetOperator();

        public override Expression Substitute(LocalVariable s, Expression t)
        {
            // 调用子类的 constructor
            Object? result = Activator.CreateInstance(this.GetType(), new object[] {
                le.Substitute(s, t), re.Substitute(s, t)
            });
            Debug.Assert(result != null);
            Debug.Assert(result is Expression);
            return (Expression)result;
        }

        public override HashSet<LocalVariable> GetFreeVariables()
        {
            HashSet<LocalVariable> fvs = le.GetFreeVariables();
            fvs.UnionWith(re.GetFreeVariables());
            return fvs;
        }
    }

    sealed class MultiExpression : BinaryExpression
    {
        protected override string GetOperator() => "*";

        public MultiExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType);
            this.type = le.type;
            this.le = le;
            this.re = re;
        }
    }

    sealed class FloatDivExpression : BinaryExpression
    {
        protected override string GetOperator() => "/";

        public FloatDivExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is FloatType && re.type is FloatType);
            this.type = FloatType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class DivExpression : BinaryExpression
    {
        protected override string GetOperator() => "div";

        public DivExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType);
            this.type = IntType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class ModExpression : BinaryExpression
    {
        protected override string GetOperator() => "%";

        public ModExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType);
            this.type = IntType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class AddExpression : BinaryExpression
    {
        protected override string GetOperator() => "+";

        public AddExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType);
            this.type = le.type;
            this.le = le;
            this.re = re;
        }
    }

    sealed class SubExpression : BinaryExpression
    {
        protected override string GetOperator() => "-";

        public SubExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType);
            this.type = le.type;
            this.le = le;
            this.re = re;
        }
    }

    sealed class LTExpression : BinaryExpression
    {
        protected override string GetOperator() => "<";

        public LTExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class LEExpression : BinaryExpression
    {
        protected override string GetOperator() => "<=";

        public LEExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class GTExpression : BinaryExpression
    {
        protected override string GetOperator() => ">";

        public GTExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class GEExpression : BinaryExpression
    {
        protected override string GetOperator() => ">=";

        public GEExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class EQExpression : BinaryExpression
    {
        protected override string GetOperator() => "=";

        public EQExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType || le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class NEExpression : BinaryExpression
    {
        protected override string GetOperator() => "!=";

        public NEExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType || le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }
    }

    abstract class QuantifiedExpression : Expression
    {
        // notice: the key string is not alpha-renamed
        public Dictionary<string, QuantifiedVariable> vars;
        public Expression expression;

        public QuantifiedExpression(Dictionary<string, QuantifiedVariable> vars, Expression expression)
        {
            this.type = BoolType.Get();
            this.vars = vars;
            this.expression = expression;
        }

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

        public override Expression Substitute(LocalVariable s, Expression t)
        {
            if (vars.ContainsKey(s.name))
            {
                return this;
            }
            else
            {
                // 调用子类的 constructor
                Object? result = Activator.CreateInstance(this.GetType(), new object[] {
                    vars, expression.Substitute(s, t)
                });
                Debug.Assert(result != null);
                Debug.Assert(result is Expression);
                return (Expression)result;
            }
        }

        public override HashSet<LocalVariable> GetFreeVariables()
        {
            return new HashSet<LocalVariable>();
        }
    }

    sealed class ForallQuantifiedExpression : QuantifiedExpression
    {
        public ForallQuantifiedExpression(Dictionary<string, QuantifiedVariable> vars, Expression expression) : base(vars, expression) { }

        protected override string GetQuantifier() => "forall";
    }

    sealed class ExistsQuantifiedExpression : QuantifiedExpression
    {
        public ExistsQuantifiedExpression(Dictionary<string, QuantifiedVariable> vars, Expression expression) : base(vars, expression) { }

        protected override string GetQuantifier() => "exists";
    }

    sealed class AndExpression : BinaryExpression
    {
        public AndExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }

        protected override string GetOperator() => "&&";
    }

    sealed class OrExpression : BinaryExpression
    {
        public OrExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }

        protected override string GetOperator() => "||";
    }

    sealed class ImplicationExpression : BinaryExpression
    {
        public ImplicationExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }

        protected override string GetOperator() => "->";
    }

    sealed class IffExpression : BinaryExpression
    {
        public IffExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }

        protected override string GetOperator() => "<->";
    }

    sealed class LengthExpression : UnaryExpression
    {
        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(expression.type is ArrayType);
            Contract.Invariant(expression is VariableExpression || expression is ArrayUpdateExpression);
        }

        public LengthExpression(Expression expression)
        {
            Debug.Assert(expression.type is ArrayType);
            this.type = IntType.Get();
            this.expression = expression;
        }

        public override void Print(TextWriter writer)
        {
            writer.Write("|");
            expression.Print(writer);
            writer.Write("|");
        }

        public override Expression Substitute(LocalVariable s, Expression t)
        {
            Expression expression = this.expression.Substitute(s, t);
            if (expression is VariableExpression ve)
            {
                Debug.Assert(ve.variable is ArrayVariable);
                if (((ArrayVariable)(ve.variable)).length == s)
                {
                    return t;
                }
                else
                {
                    return new LengthExpression(expression);
                }
            }
            else
            {
                Debug.Assert(expression is ArrayUpdateExpression);
                if (((ArrayUpdateExpression)expression).length.variable == s)
                    return t;
                else
                    return new LengthExpression(expression);
            }
        }
    }
}