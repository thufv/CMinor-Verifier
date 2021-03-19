using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace piVC_thu
{
    abstract class Block
    {
        public LinkedList<Block> predecessors = new LinkedList<Block>();
        public LinkedList<Block> successors = new LinkedList<Block>();

        static public void AddEdge(Block from, Block to)
        {
            from.successors.AddLast(to);
            to.predecessors.AddLast(from);
        }

        // statements 里是可能没有东西的
        protected LinkedList<Statement> statements = new LinkedList<Statement>();

        public void AddStatement(Statement statement)
        {
            statements.AddLast(statement);
        }
    }

    sealed class BasicBlock : Block
    {
    }

    sealed class PostconditionBlock : Block
    {
        public Expression condition = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(statements.Count == 1);
        }
    }

    class HeadBlock : Block
    {
        public List<Expression> rankingFunction = default!;
    }

    sealed class PreconditionBlock : HeadBlock
    {
        public Expression condition = default!;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(statements.Count == 1);
        }
    }

    sealed class LoopHeadBlock : HeadBlock
    {
        public Expression invariant = default!;
    }
}
