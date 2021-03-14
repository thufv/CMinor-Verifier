using System.Collections.Generic;

namespace piVC_thu
{
    // 这里的顶层设计主要是参考了 Silver

    class Block
    {
    }

    class BasicBlock : Block
    {
        public LinkedList<Statement> statements;
    }

    class PreconditionBlock : Block
    {
        public Expression condition;
        public List<Expression> rankingFunctions;
    }

    class PostconditionBlock : Block
    {
        public Expression condition;
    }

    class LoopheadBlock : Block
    {
        public Expression invariant;
        public List<Expression> rankingFunctions;
    }
}
