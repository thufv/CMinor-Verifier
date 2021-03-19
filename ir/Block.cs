using System.IO;
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

        public Block() { }
        public Block(Function currentFunction, Block? predecessor)
        {
            currentFunction.blocks.AddLast(this);
            if (predecessor != null)
                AddEdge(predecessor, this);
        }

        public abstract void Print(TextWriter writer);
        protected void PrintPredecessors(TextWriter writer)
        {
            writer.Write("\tpredecessors:");
            foreach (Block predecessor in predecessors)
                writer.Write(" " + predecessor);
            writer.WriteLine("");
        }
        protected void PrintSuccessors(TextWriter writer)
        {
            writer.Write("\tsuccessors:");
            foreach (Block successor in successors)
                writer.Write(" " + successor);
            writer.WriteLine("");
        }
        protected void PrintCondition(TextWriter writer, string name, Expression condition)
        {
            writer.Write($"\t@{name} ");
            condition.Print(writer);
            writer.Write("\n");
        }

        protected void PrintStatements(TextWriter writer)
        {
            foreach (Statement statement in statements)
                statement.Print(writer);
        }
    }

    sealed class BasicBlock : Block
    {
        static int numberCounter = 0;
        public int number { get; } = ++numberCounter;

        public override void Print(TextWriter writer)
        {
            writer.WriteLine(this + ":");

            PrintPredecessors(writer);
            PrintSuccessors(writer);

            PrintStatements(writer);
        }

        public BasicBlock(Function currentFunction, Block? predecessor = null)
            : base(currentFunction, predecessor) { }

        public override string ToString() => $"_BASIC#{number}";
    }

    sealed class PostconditionBlock : Block
    {
        public Expression condition = default!;

        static int numberCounter = 0;
        public int number { get; } = ++numberCounter;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(statements.Count == 0);
            Contract.Invariant(successors.Count == 0);
        }

        public override void Print(TextWriter writer)
        {
            writer.WriteLine(this + ":");

            PrintPredecessors(writer);

            PrintCondition(writer, "post", condition);
        }

        public override string ToString() => $"_POSTCOND#{number}";
    }

    abstract class HeadBlock : Block
    {
        public List<Expression> rankingFunction = default!;

        public HeadBlock() { }
        public HeadBlock(Function currentFunction, Block? predecessor)
            : base(currentFunction, predecessor) { }

        protected void PrintRankingFunction(TextWriter writer)
        {
            writer.WriteLine("\t#rankingfunction\n\t(");
            for (int i = 0; i < rankingFunction.Count; ++i)
            {
                writer.Write("\t\t");
                rankingFunction[i].Print(writer);
                writer.Write(",\n");
            }
            writer.WriteLine("\t)");
        }
    }

    sealed class PreconditionBlock : HeadBlock
    {
        public Expression condition = default!;

        static int numberCounter = 0;
        public int number { get; } = ++numberCounter;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(statements.Count == 0);
            Contract.Invariant(predecessors.Count == 0);
        }

        public override void Print(TextWriter writer)
        {
            writer.WriteLine(this + ":");

            PrintSuccessors(writer);

            PrintCondition(writer, "pre", condition);

            PrintRankingFunction(writer);
        }

        public override string ToString() => $"_PRECOND#{number}";
    }

    sealed class LoopHeadBlock : HeadBlock
    {
        public Expression invariant = default!;

        static int numberCounter = 0;
        public int number { get; } = ++numberCounter;

        public LoopHeadBlock(Function currentFunction, Block? predecessor = null)
            : base(currentFunction, predecessor) { }

        public override void Print(TextWriter writer)
        {
            writer.WriteLine(this + ":");

            PrintPredecessors(writer);
            PrintSuccessors(writer);

            PrintCondition(writer, "invariant", invariant);

            PrintRankingFunction(writer);

            PrintStatements(writer);
        }

        public override string ToString() => $"_LOOPHEAD#{number}";
    }
}
