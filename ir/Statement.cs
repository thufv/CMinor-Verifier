namespace piVC_thu
{
    // TODO: CFG 里需要有 declaration 嘛？我该怎么处理 declaration？

    public abstract class Statement
    {
        // A unique integer
        public int location;
    }

    // 这里我突然不知道该怎么处理了，因为 assign 也可以嵌套？
    // assign 是不允许嵌套的，那为什么语法要写成这个德性呢……

    public abstract class AssignStatement : Statement
    {
        public Expression rhs;
    }

    class VariableAssign : AssignStatement
    {
        public LocalVariable variable;
    }

    class SubscriptAssign : AssignStatement
    {
        public Expression array, subscript;
    }

    class MemberAssign : AssignStatement
    {
        public Struct host;
        public MemberVariable member;
    }

    class Assert : Statement
    {
        public Expression annotation;
    }

    class Assume : Statement
    {
        public Expression annotation;
    }
}