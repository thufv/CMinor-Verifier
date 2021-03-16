namespace piVC_thu
{
    abstract class Variable
    {
        public VarType type = default!;
        public string name = default!;
    }

    class LocalVariable : Variable
    {
        public Expression? initializer = null;
    }

    sealed class ParaVariable : LocalVariable { }

    sealed class MemberVariable : Variable { }

    sealed class QuantifiedVariable : Variable
    {
        // 这里搞了一个 constructor，其实仅仅是因为 quantified variable 的类型必须为 int
        public QuantifiedVariable(string name)
        {
            this.type = IntType.Get();
            this.name = name;
        }
    }
}