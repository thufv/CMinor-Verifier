using System.Collections.Generic;

namespace piVC_thu
{
    // 这里的顶层设计主要是参考了 TrivialCompiler

    class Main
    {
        public LinkedList<Function> functions = new LinkedList<Function>();
        public LinkedList<Predicate> predicates = new LinkedList<Predicate>();
        public LinkedList<Struct> structs = new LinkedList<Struct>();
    }


    class Function
    {
        public FunType type = default!;
        public string name = default!;

        public PreconditionBlock preconditionBlock = default!;
        public PostconditionBlock postconditionBlock = default!;

        // All blocks, containing precondition block and postcondition block.
        // For minimization we don't need the following one,
        // this is only for convenience.
        public LinkedList<Block> blocks = new LinkedList<Block>();

        public LocalVariable? rv;

        // public CallExpression apply(List<Expression> arguments) { TODO }
    }

    class Predicate
    {
        // a predicate can be regarded as a function,
        // of which the return value is bool and the body
        // is just one return statement.
        public FunType type = default!;
        public string name = default!;
        public Expression expression = default!;

        // public CallExpression apply(List<Expression> arguments) { TODO }
    }

    class Struct
    {
        public StructType type;
        public string name;

        public Dictionary<string, MemberVariable> members;

        public Struct(string name, Dictionary<string, MemberVariable> members)
        {
            this.name = name;
            this.members = members;
            this.type = StructType.Get(this);
        }
    }
}