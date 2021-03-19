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
    }

    abstract class AssignStatement : Statement
    {
        public Expression rhs = default!;
    }

    sealed class VariableAssignStatement : AssignStatement
    {
        public Variable variable = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(variable is LocalVariable || variable is StructVariable);
        }
    }

    sealed class SubscriptAssignStatement : AssignStatement
    {
        public Expression array = default!, index = default!;
    }

    sealed class FunctionCallStatement : Statement
    {
        public LocalVariable? lhs = null;
        public FunctionCallExpression rhs = default!;
    }

    sealed class AssertStatement : Statement
    {
        public Expression annotation = default!;
    }

    sealed class AssumeStatement : Statement
    {
        public Expression condition = default!;
    }
}