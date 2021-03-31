using System.Diagnostics.Contracts;

namespace piVC_thu
{
    abstract class Variable
    {
        public VarType type = default!;
        public string name = default!;
    }

    // 包括局部变量，函数参数，辅助变量
    // 额外的，成员变量也会被转成 LocalVariable 来处理
    class LocalVariable : Variable { }

    class ArrayVariable : LocalVariable
    {
        // 只有在 new array 的时候需要对 length 作一个非负性的 runtime assertion
        public LocalVariable length = default!;
    }

    sealed class QuantifiedVariable : LocalVariable
    {
        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(this.type is IntType);
        }
    }

    // MemberVariable 和其他的不太一样，它是放在结构体的定义里的，
    // 并不会实际出现在表达式里。
    sealed class MemberVariable : Variable { }
}