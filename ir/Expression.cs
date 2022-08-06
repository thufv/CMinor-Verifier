/* Copyright 2022 Xingyu Xie

This file is part of CMinor.

CMinor is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

CMinor is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with CMinor. If not, see <https://www.gnu.org/licenses/>. */

using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;

using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace cminor
{
    /**
        <summary>
        我们统一来处理表达式，既包括 C 里的表达式，也包括 ACSL 里的表达式。
        其支持三个基本功能：打印（Print）、替换（Substitute）、求表达式中的自由变量（GetFreeVariables）。
        </summary>
     */
    abstract class Expression
    {
        public VarType type { get; protected set; } = default!;

        public abstract void Print(TextWriter writer);

        public abstract Expression Substitute(LocalVariable s, Expression t);

        public abstract HashSet<LocalVariable> GetFreeVariables();

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            // 如果表达式的类型是 struct，那么它一定是一个 VariableExpression
            // 注意：FunctionCallExpression 并不是 Expression 的 subclass
            Contract.Invariant(!(type is StructType) || (this is VariableExpression));

            // 如果一个 expression 是一个 array expression，当且仅当，它是一个 variable expression，并且其中的 variable 是一个 array variable
            Contract.Invariant((type is ArrayType) == (this is VariableExpression ve && ve.variable.type is ArrayType));
        }
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
            {
                return t;
            }
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

    sealed class ArrayAccessExpression : Expression
    {
        public Expression array;
        public Expression subscript;

        public ArrayAccessExpression(Expression array, Expression subscript)
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
            return new ArrayAccessExpression(array.Substitute(s, t), subscript.Substitute(s, t));
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

    sealed class ITEExpression : Expression
    {
        public Expression cond;
        public Expression thenExpr, elseExpr;

        public ITEExpression(Expression cond, Expression thenExpr, Expression elseExpr)
        {
            Debug.Assert(cond.type is BoolType);
            Debug.Assert(thenExpr.type == elseExpr.type);

            this.cond = cond;
            this.thenExpr = thenExpr;
            this.elseExpr = elseExpr;
            this.type = thenExpr.type;
        }

        public override void Print(TextWriter writer)
        {
            cond.Print(writer);
            writer.Write(" ? ");
            thenExpr.Print(writer);
            writer.Write(" : ");
            elseExpr.Print(writer);
        }

        public override Expression Substitute(LocalVariable s, Expression t)
        {
            Expression cond = this.cond.Substitute(s, t);
            Expression thenExpr = this.thenExpr.Substitute(s, t);
            Expression elseExpr = this.elseExpr.Substitute(s, t);
            return new ITEExpression(cond, thenExpr, elseExpr);
        }

        public override HashSet<LocalVariable> GetFreeVariables()
        {
            var fvs = cond.GetFreeVariables();
            fvs.UnionWith(thenExpr.GetFreeVariables());
            fvs.UnionWith(elseExpr.GetFreeVariables());
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
            string op = (string)this.GetType().GetMethod("GetOperator")!.Invoke(null, null)!;
            writer.Write($" {op} ");
            re.Print(writer);
            writer.Write(")");
        }

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

        public static BinaryExpression FromOp(string op, Expression le, Expression re)
        {
            foreach (System.Type type in typeof(BinaryExpression).Assembly.GetTypes())
                if (type.IsSubclassOf(typeof(BinaryExpression)))
                {
                    if ((string)type.GetMethod("GetOperator")!.Invoke(null, null)! == op)
                    {
                        return (BinaryExpression)type
                                .GetConstructor(new System.Type[] { typeof(Expression), typeof(Expression) })!
                                .Invoke(new object[] { le, re });
                    }
                }
            throw new ArgumentException($"There is no binary expression of operator '{op}'.");
        }
    }

    sealed class MultiExpression : BinaryExpression
    {
        public static string GetOperator() => "*";

        public MultiExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType);
            this.type = le.type;
            this.le = le;
            this.re = re;
        }
    }

    sealed class DivExpression : BinaryExpression
    {
        public static string GetOperator() => "/";

        public DivExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is FloatType && re.type is FloatType || le.type is IntType && re.type is IntType);
            this.type = le.type;
            this.le = le;
            this.re = re;
        }
    }

    sealed class ModExpression : BinaryExpression
    {
        public static string GetOperator() => "%";

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
        public static string GetOperator() => "+";

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
        public static string GetOperator() => "-";

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
        public static string GetOperator() => "<";

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
        public static string GetOperator() => "<=";

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
        public static string GetOperator() => ">";

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
        public static string GetOperator() => ">=";

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
        public static string GetOperator() => "==";

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
        public static string GetOperator() => "!=";

        public NEExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType || le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class AndExpression : BinaryExpression
    {
        public static string GetOperator() => "&&";

        public AndExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class OrExpression : BinaryExpression
    {
        public static string GetOperator() => "||";

        public OrExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }
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
            writer.Write("\\length(");
            expression.Print(writer);
            writer.Write(")");
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
            writer.Write($"(\\{GetQuantifier()} ");
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

    sealed class ImplicationExpression : BinaryExpression
    {
        public static string GetOperator() => "==>";

        public ImplicationExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class IffExpression : BinaryExpression
    {
        public static string GetOperator() => "<==>";

        public IffExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
        }
    }

    sealed class XorExpression : BinaryExpression
    {
        public static string GetOperator() => "^^";

        public XorExpression(Expression le, Expression re)
        {
            Debug.Assert(le.type is BoolType && re.type is BoolType);
            this.type = BoolType.Get();
            this.le = le;
            this.re = re;
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
}