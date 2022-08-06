/* Copyright 2022 Xingyu Xie

This file is part of CMinor.

CMinor is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

CMinor is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with CMinor. If not, see <https://www.gnu.org/licenses/>. */

using System.IO;
using System.Collections.Generic;

namespace cminor
{
    /// <summary> IR 的最顶层，其中包含了若干函数定义和谓词定义。 </summary>

    class IRMain
    {
        public LinkedList<Function> functions = new LinkedList<Function>();
        public LinkedList<Predicate> predicates = new LinkedList<Predicate>();

        public void Print(TextWriter writer)
        {
            // writer.WriteLine("// predicates");
            foreach (Predicate p in predicates)
            {
                p.Print(writer);
                writer.WriteLine("");
            }
            // writer.WriteLine("");

            // writer.WriteLine("// functions");
            foreach (Function f in functions)
            {
                f.Print(writer);
                writer.WriteLine("");
            }
        }
    }


    /// <summary> 函数的主体是若干个 block 构成的 CFG，入口块是 precondition block，出口块是 postcondition block。 </summary>
    class Function
    {
        // 注意，这个 type 在 CFG 中
        public FunType type = default!;

        public string name = default!;
        public List<LocalVariable> parameters = default!;

        public PreconditionBlock preconditionBlock = default!;
        public PostconditionBlock postconditionBlock = default!;

        // All blocks except precondition block and postcondition block.
        // For minimization we don't need the following one,
        // this is only for convenience.
        public LinkedList<Block> blocks = new LinkedList<Block>();

        // 如果是 void，那么就为空
        // 如果是 int, float, bool 或者 array，那么就只有一个
        // 如果是 struct 的话，就有 struct 的成员数量那么多个
        public List<LocalVariable> rvs = new List<LocalVariable>();

        public void Print(TextWriter writer)
        {
            writer.Write($"[function] (\\result: (");
            foreach (Type returnType in type.returnTypes)
                writer.Write(returnType);
            writer.WriteLine($")) {name} \n(");
            for (int i = 0; i < parameters.Count; ++i)
                writer.WriteLine($"\t({parameters[i].name}: {parameters[i].type}),");
            writer.WriteLine(")");

            preconditionBlock.Print(writer);
            writer.WriteLine("");
            foreach (Block block in blocks)
            {
                block.Print(writer);
                writer.WriteLine("");
            }
            postconditionBlock.Print(writer);
        }
    }

    /// <summary> 谓词的主体就是一个逻辑表达式。 </summary>
    class Predicate
    {
        // a predicate can be regarded as a function,
        // of which the return value is bool and the body
        // is just one return statement.
        public PredType type = default!;
        public string name = default!;
        public List<LocalVariable> parameters = default!;
        public Expression expression = default!;

        public void Print(TextWriter writer)
        {
            writer.WriteLine($"[predicate] {name}\n(");
            for (int i = 0; i < parameters.Count; ++i)
                writer.WriteLine($"\t({parameters[i].name}: {parameters[i].type}),");
            writer.WriteLine(")");
            writer.Write("\t:= ");
            expression.Print(writer);
        }
    }
}