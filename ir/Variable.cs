namespace cminor
{
    /// <summary> 一个变量的抽象类型 </summary>
    /// <remarks>
    /// 在最终的 IR 中，所有变量都会被视作局部变量（<c>LocalVariable</c>）来处理，数组和约束变量会被视作特殊的局部变量。
    /// 不过在 IR 的生成过程中，为了方便，我们还会有成员变量和结构体变量，细节可见于 frontend/Struct.cs。
    /// </remarks>
    abstract class Variable
    {
        public VarType type = default!;
        public string name = default!;
    }

    /// <summary> 包括局部变量，函数参数，辅助变量，额外的，成员变量也会被转成 <c>LocalVariable</c> 来处理 </summary>
    class LocalVariable : Variable { }

    class ArrayVariable : LocalVariable
    {
        // 只有在 new array 的时候需要对 length 作一个非负性的 runtime assertion
        public LocalVariable length = default!;
    }

    sealed class QuantifiedVariable : LocalVariable { }

    /// <summary> 结构体的成员变量 </summary>
    /// <remarks> <c>MemberVariable</c> 和其他的 sibling class 不太一样，它是放在结构体的定义里的，并不会实际出现在表达式里。 </remarks>
    sealed class MemberVariable : Variable { }
}