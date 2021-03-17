using System.Collections.Generic;

namespace piVC_thu
{
    // 这里的顶层设计主要是参考了 Silver

    abstract class Block
    {
        public LinkedList<Block> predecessors = new LinkedList<Block>();
        public LinkedList<Block> successors = new LinkedList<Block>();

        static public void AddEdge(Block from, Block to)
        {
            from.successors.AddLast(to);
            to.predecessors.AddLast(from);
        }

        // 也许可以搞一两个带 predecessor 的初始化QAQ
    }

    sealed class BasicBlock : Block
    {
        // statements 里有可能没有 Statement
        private LinkedList<Statement> statements = new LinkedList<Statement>();

        public void AddStatement(Statement statement)
        {
            statements.AddLast(statement);
        }
    }

    sealed class PostconditionBlock : Block
    {
        public Expression condition = default!;
    }

    class HeadBlock : Block
    {
        public List<Expression> rankingFunction = new List<Expression>();
    }

    sealed class PreconditionBlock : HeadBlock
    {
        public Expression condition = default!;
    }

    sealed class LoopHeadBlock : HeadBlock
    {
        public Expression invariant = default!;
    }
}
