using System.IO;
using System.Collections.Generic;

using System.Diagnostics.Contracts;

namespace cminor
{
    abstract class Statement
    {
        // A globally unique integer
        // 主要是为了做谓词分析
        public int location { get; }
        static int currentLocation = 0;

        public Statement()
        {
            location = ++currentLocation;
        }

        // 注意这里打印的时候一定是前面带 \t，后面带 \n
        public abstract void Print(TextWriter writer);
    }

    abstract class AssignStatement : Statement
    {
        public Expression rhs = default!;

        // 为了让事情更清晰，我们在打印这种语句时总是显示地标注一下左边的变量的类型
    }

    sealed class VariableAssignStatement : AssignStatement
    {
        public LocalVariable variable = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(variable is not QuantifiedVariable);
            Contract.Invariant(variable.type == rhs.type);
        }

        public override void Print(TextWriter writer)
        {
            writer.Write($"\t({variable.name}: {variable.type}) = ");
            rhs.Print(writer);
            writer.Write("\n");
        }
    }

    sealed class SubscriptAssignStatement : AssignStatement
    {
        public ArrayVariable array = default!;
        public VariableExpression subscript = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(array.type is ArrayType);
            Contract.Invariant(subscript.type is IntType);
        }

        public override void Print(TextWriter writer)
        {
            writer.Write($"\t({array.name}[");
            subscript.Print(writer);
            writer.Write($"]: {((ArrayType)(array.type)).atomicType}) := ");
            rhs.Print(writer);
            writer.WriteLine("");
        }
    }

    sealed class FunctionCallStatement : Statement
    {
        public List<LocalVariable> lhs = new List<LocalVariable>();
        public FunctionCallExpression rhs = default!;

        public override void Print(TextWriter writer)
        {
            writer.Write("\t");
            foreach (LocalVariable lv in lhs)
            {
                writer.Write(
                    (lhs != null
                        ? $"({lv.name}: {lv.type})"
                        : "(void)")
                    + " := ");
            }
            rhs.Print(writer);
            writer.WriteLine("");
        }
    }

    sealed class AssertStatement : Statement
    {
        public Expression pred = default!;

        public override void Print(TextWriter writer)
        {
            writer.Write("\t@assert ");
            pred.Print(writer);
            writer.WriteLine("");
        }
    }

    sealed class AssumeStatement : Statement
    {
        public Expression condition = default!;

        public override void Print(TextWriter writer)
        {
            writer.Write("\tassume ");
            condition.Print(writer);
            writer.WriteLine("");
        }
    }
}