/* Copyright 2022 Xingyu Xie

This file is part of CMinor.

CMinor is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

CMinor is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with CMinor. If not, see <https://www.gnu.org/licenses/>. */

using System.IO;
using System.Collections.Generic;

using System.Diagnostics.Contracts;

namespace cminor
{
    /// <summary> 用于表示“程序块”的抽象类。 </summary>
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
        public LinkedList<Statement> statements = new LinkedList<Statement>();

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
            writer.Write($"\t{name} ");
            condition.Print(writer);
            writer.Write("\n");
        }

        protected void PrintStatements(TextWriter writer)
        {
            foreach (Statement statement in statements)
                statement.Print(writer);
        }
    }

    /// <summary> 基本块 </summary>
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
        public List<Expression> conditions = new List<Expression>();

        static int numberCounter = 0;
        public int number { get; } = ++numberCounter;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(statements.Count == 0);
            Contract.Invariant(predecessors.Count == 1);
            Contract.Invariant(successors.Count == 0);
        }

        public override void Print(TextWriter writer)
        {
            writer.WriteLine(this + ":");

            PrintPredecessors(writer);

            foreach (Expression condition in conditions)
                PrintCondition(writer, "ensures", condition);
        }

        public override string ToString() => $"_POSTCOND#{number}";
    }

    /// <summary> 用于表示“头”（循环头以及函数头）的程序块的抽象类。 </summary>
    abstract class HeadBlock : Block
    {
        public List<Expression> rankingFunctions = new List<Expression>();

        public HeadBlock() { }
        public HeadBlock(Function currentFunction, Block? predecessor)
            : base(currentFunction, predecessor) { }

        abstract protected void PrintRankingFunction(TextWriter writer);
    }

    /// <summary> 前置条件块，或者说函数头块，里面包括前置条件和秩函数。 </summary>
    sealed class PreconditionBlock : HeadBlock
    {
        public List<Expression> conditions = new List<Expression>();

        static int numberCounter = 0;
        public int number { get; } = ++numberCounter;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(statements.Count == 0);
            Contract.Invariant(predecessors.Count == 0);
            Contract.Invariant(successors.Count == 1);
            foreach (Expression cond in conditions)
                Contract.Invariant(cond.type is BoolType);
        }

        public override void Print(TextWriter writer)
        {
            writer.WriteLine(this + ":");

            PrintSuccessors(writer);

            foreach (Expression cond in conditions)
                PrintCondition(writer, "requires", cond);

            PrintRankingFunction(writer);
        }

        protected override void PrintRankingFunction(TextWriter writer)
        {
            writer.WriteLine("\tdecreases (");
            foreach (Expression rankingFunction in rankingFunctions)
            {
                writer.Write("\t");
                rankingFunction.Print(writer);
                writer.WriteLine("");
            }
            writer.WriteLine(")");
        }

        public override string ToString() => $"_PRECOND#{number}";
    }

    /// <summary> 循环头块，其中包括循环不变式和秩函数。 </summary>
    sealed class LoopHeadBlock : HeadBlock
    {
        // 这里的 statements 是用来算 condition 的！

        public List<Expression> invariants = new List<Expression>();

        static int numberCounter = 0;
        public int number { get; } = ++numberCounter;

        public LoopHeadBlock(Function currentFunction, Block? predecessor = null)
            : base(currentFunction, predecessor) { }

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            foreach (Expression cond in invariants)
                Contract.Invariant(cond.type is BoolType);
        }

        public override void Print(TextWriter writer)
        {
            writer.WriteLine(this + ":");

            PrintPredecessors(writer);
            PrintSuccessors(writer);

            foreach (Expression invariant in invariants)
                PrintCondition(writer, "loop invariant", invariant);

            PrintRankingFunction(writer);

            PrintStatements(writer);
        }

        protected override void PrintRankingFunction(TextWriter writer)
        {
            writer.WriteLine("\tloop variant (");
            foreach (Expression rankingFunction in rankingFunctions)
            {
                writer.Write("\t");
                rankingFunction.Print(writer);
                writer.WriteLine("");
            }
            writer.WriteLine("");
        }

        public override string ToString() => $"_LOOPHEAD#{number}";
    }
}
