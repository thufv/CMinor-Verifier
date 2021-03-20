using System.IO;
using System.Collections.Generic;

namespace piVC_thu
{
    class Main
    {
        public LinkedList<Function> functions = new LinkedList<Function>();
        public LinkedList<Predicate> predicates = new LinkedList<Predicate>();
        public LinkedList<Struct> structs = new LinkedList<Struct>();

        public void Print(TextWriter writer)
        {
            // writer.WriteLine("// structs");
            foreach (Struct s in structs)
            {
                s.Print(writer);
                writer.WriteLine("");
            }
            // writer.WriteLine("");

            // writer.WriteLine("// predicates");
            foreach (Predicate p in predicates)
            {
                p.Print(writer);
                writer.WriteLine("");
            }
            // writer.WriteLine("");

            // writer.WriteLine("// functions");
            foreach (Function f in functions)
            {
                f.Print(writer);
                writer.WriteLine("");
            }
        }
    }


    class Function
    {
        public FunType type = default!;
        public string name = default!;
        public LocalVariable[] parameters = default!;

        public PreconditionBlock preconditionBlock = default!;
        public PostconditionBlock postconditionBlock = default!;

        // All blocks, containing precondition block and postcondition block.
        // For minimization we don't need the following one,
        // this is only for convenience.
        public LinkedList<Block> blocks = new LinkedList<Block>();

        public LocalVariable? rv;

        public void Print(TextWriter writer)
        {
            writer.WriteLine($"[function] {type.returnType} {name} \n(");
            for (int i = 0; i < parameters.Length; ++i)
                writer.WriteLine($"\t({parameters[i].name}: {parameters[i].type}),");
            writer.WriteLine(")");

            preconditionBlock.Print(writer);
            writer.WriteLine("");
            foreach (Block block in blocks)
            {
                block.Print(writer);
                writer.WriteLine("");
            }
            postconditionBlock.Print(writer);
        }
    }

    class Predicate
    {
        // a predicate can be regarded as a function,
        // of which the return value is bool and the body
        // is just one return statement.
        public FunType type = default!;
        public string name = default!;
        public LocalVariable[] parameters = default!;
        public Expression expression = default!;

        public void Print(TextWriter writer)
        {
            writer.WriteLine($"[predicate] {name}\n(");
            for (int i = 0; i < parameters.Length; ++i)
                writer.WriteLine($"\t({parameters[i].name}: {parameters[i].type}),");
            writer.WriteLine(")");
            writer.Write("\t:= ");
            expression.Print(writer);
        }
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

        public void Print(TextWriter writer)
        {
            writer.WriteLine($"[struct] {name}\n{{");
            foreach (MemberVariable member in members.Values)
                writer.WriteLine($"\t{member.name}: {member.type};");
            writer.WriteLine("}}");
        }
    }
}