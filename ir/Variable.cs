namespace piVC_thu
{
    public abstract class Variable
    {
        public VarType type;
        public string name;
        public Expression? initializer;
    }

    class LocalVariable : Variable { }

    class MemberVariable : Variable
    {
        public Struct host;
        public string name;
    }

    class QuantifiedVariable : Variable { }
}