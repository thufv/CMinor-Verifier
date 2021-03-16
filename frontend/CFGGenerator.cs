using System;
using System.Collections.Generic;

using Antlr4.Runtime.Misc;

// 需要做这么几件事：
// 1. 名称解析
// 2. 类型检查

namespace piVC_thu
{
    partial class CFGGenerator : piBaseVisitor<Expression?>
    {
        // 最终计算出来的 IR 主体
        static public Main main = default!;

        // 当前正在计算的 function
        Function? currentFuncion;
        // 当前的 location
        int currentLocation = 0;
        // block
        BasicBlock? currentBasicBlock = null;

        // 符号表
        Dictionary<string, Function> functionTable = new Dictionary<string, Function>();
        Dictionary<string, Struct> structTable = new Dictionary<string, Struct>();
        Dictionary<string, Predicate> predicateTable = new Dictionary<string, Predicate>();
        Stack<Dictionary<string, LocalVariable>> symbolTables = new Stack<Dictionary<string, LocalVariable>>();
        // 这个是用来作 alpha renaming 的
        Dictionary<string, int> numberOfName = new Dictionary<string, int>();

        public override Expression? VisitMain([NotNull] piParser.MainContext context)
        {
            main = new Main();

            foreach (var decl in context.decl())
                Visit(decl);

            // 检查：所有的 ranking function 的元组数量必须是相同的
            int rankingFunctionSize = -1;
            Action<HeadBlock> considerHeadBlock = headBlock =>
            {
                if (rankingFunctionSize == -1)
                    rankingFunctionSize = headBlock.rankingFunction.Count;
                if (headBlock.rankingFunction.Count != rankingFunctionSize)
                    throw new ParsingException(context,
                        rankingFunctionSize == 0 || headBlock.rankingFunction.Count == 0 ?
                            "some ranking functions are annotated while the others not" :
                            "the sizes of the tuple of ranking functions are different");
            };
            foreach (Function function in functionTable.Values)
            {
                considerHeadBlock(function.preConditionBlock);
                foreach (Block block in function.blocks)
                    if (block is HeadBlock headBlock)
                        considerHeadBlock(headBlock);
            }

            return null;
        }

        public override Expression? VisitFuncDef([NotNull] piParser.FuncDefContext context)
        {
            string name = CalcDefName(context, context.IDENT());

            symbolTables.Push(new Dictionary<string, LocalVariable>());

            PreConditionBlock preconditionBlock = CalcPreConditionBlock(context.beforeFunc().annotationPre(), context.beforeFunc().termination());
            PostConditionBlock postconditionBlock = CalcPostConditionBlock(context.beforeFunc().annotationPost());

            ReturnType returnType = context.type() != null ? CalcType(context.type()) : VoidType.Get();

            // calculate parameters
            VarType[] paraTypes = new VarType[context.var().Length];
            HashSet<string> paraNames = new HashSet<string>();
            for (int i = 0; i < context.var().Length; ++i)
            {
                var ctx = context.var()[i]!;
                paraTypes[i] = CalcType(ctx.type());
                string paraName = ctx.IDENT().GetText();
                if (!paraNames.Contains(paraName))
                    paraNames.Add(paraName);
                else
                    throw new ParsingException(context, $"duplicate function parameter '{paraName}'");

                if (!numberOfName.ContainsKey(paraName))
                    numberOfName.Add(paraName, 0);
                ParaVariable paraVariable = new ParaVariable
                {
                    type = paraTypes[i],
                    name = paraName + '$' + numberOfName[paraName] // alpha renaming
                };
                numberOfName[paraName] = numberOfName[paraName] + 1;

                symbolTables.Peek().Add(paraName, paraVariable);
            }

            currentFuncion = new Function
            {
                type = FunType.Get(returnType, paraTypes),
                name = name,
                preConditionBlock = preconditionBlock,
                postConditionBlock = postconditionBlock
            };
            main.functions.AddLast(currentFuncion);
            functionTable.Add(name, currentFuncion);

            // visit function body
            currentBasicBlock = new BasicBlock();
            foreach (var stmt in context.stmt())
                Visit(stmt);
            Block.AddEdge(currentBasicBlock, postconditionBlock);

            numberOfName.Clear();
            symbolTables.Pop();
            currentFuncion = null;
            return null;
        }

        public override Expression? VisitStructDef([NotNull] piParser.StructDefContext context)
        {
            string name = CalcDefName(context, context.IDENT());

            // parse member variables
            Dictionary<string, MemberVariable> members = new Dictionary<string, MemberVariable>();
            foreach (var member in context.var())
            {
                MemberVariable memberVariable = new MemberVariable
                {
                    type = CalcType(member.type()),
                    name = member.IDENT().GetText()
                };
                if (!members.ContainsKey(name))
                    members.Add(name, memberVariable);
                else
                    throw new ParsingException(member, $"duplicate member '{name}'");
            }
            Struct s = new Struct(name, members);
            structTable.Add(name, s);
            return null;
        }

        public override Expression? VisitPredDef([NotNull] piParser.PredDefContext context)
        {
            string name = CalcDefName(context, context.IDENT());

            symbolTables.Push(new Dictionary<string, LocalVariable>());

            // calculate parameters
            VarType[] paraTypes = new VarType[context.var().Length];
            HashSet<string> paraNames = new HashSet<string>();
            for (int i = 0; i < context.var().Length; ++i)
            {
                var ctx = context.var()[i]!;
                paraTypes[i] = CalcType(ctx.type());
                string paraName = ctx.IDENT().GetText();
                if (!paraNames.Contains(paraName))
                    paraNames.Add(paraName);
                else
                    throw new ParsingException(context, $"duplicate function parameter '{paraName}'");

                if (!numberOfName.ContainsKey(paraName))
                    numberOfName.Add(paraName, 0);
                ParaVariable paraVariable = new ParaVariable
                {
                    type = paraTypes[i],
                    name = paraName + '$' + numberOfName.GetValueOrDefault<string, int>(paraName) // alpha renaming
                };
                numberOfName[paraName] = numberOfName.GetValueOrDefault<string, int>(paraName) + 1;

                symbolTables.Peek().Add(paraName, paraVariable);
            }

            Expression expression = Visit(context.expr())!;

            Predicate predicate = new Predicate
            {
                type = FunType.Get(BoolType.Get(), paraTypes),
                name = name,
                expression = expression
            };
            predicateTable.Add(name, predicate);

            symbolTables.Pop();
            return null;
        }
    }
}