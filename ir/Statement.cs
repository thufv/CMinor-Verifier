using System.IO;
using System.Diagnostics.Contracts;

namespace piVC_thu
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
        public Variable variable = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(variable is LocalVariable || variable is StructVariable);
        }

        public override void Print(TextWriter writer)
        {
            writer.Write($"\t({variable.name}: {variable.type}) := ");
            rhs.Print(writer);
            writer.Write("\n");
        }
    }

    sealed class SubscriptAssignStatement : AssignStatement
    {
        public Expression array = default!, index = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(array.type is ArrayType);
        }

        public override void Print(TextWriter writer)
        {
            writer.Write("\t(");
            array.Print(writer);
            writer.Write("[");
            index.Print(writer);
            writer.Write($"]: {((ArrayType)(array.type)).atomicType}) := ");
            rhs.Print(writer);
            writer.WriteLine("");
        }
    }

    sealed class FunctionCallStatement : Statement
    {
        public LocalVariable? lhs = null;
        public FunctionCallExpression rhs = default!;

        public override void Print(TextWriter writer)
        {
            writer.Write("\t");
            writer.Write(
                (lhs != null
                    ? $"({lhs.name}: {lhs.type})"
                    : "(void)")
                + " := ");
            rhs.Print(writer);
            writer.WriteLine("");
        }
    }

    sealed class AssertStatement : Statement
    {
        public Expression annotation = default!;

        public override void Print(TextWriter writer)
        {
            writer.Write("\t@assert ");
            annotation.Print(writer);
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