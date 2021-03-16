namespace piVC_thu
{
    abstract class Statement
    {
        // A globally unique integer
        // 主要是为了做谓词分析
        public int location;
    }

    // 这里我突然不知道该怎么处理了，因为 assign 也可以嵌套？
    // assign 是不允许嵌套的，那为什么语法要写成这个德性呢……

    abstract class AssignStatement : Statement
    {
        public Expression rhs = default!;
    }

    sealed class VariableAssignStatement : AssignStatement
    {
        public LocalVariable variable = default!;
    }

    sealed class SubscriptAssignStatement : AssignStatement
    {
        public Expression array = default!, index = default!;
    }

    sealed class ExpressionStatement : Statement
    {
        public Expression expression = default!;
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