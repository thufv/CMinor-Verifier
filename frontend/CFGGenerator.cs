using System;
using System.Collections.Generic;

using Antlr4.Runtime;
using Antlr4.Runtime.Misc;
using Antlr4.Runtime.Tree;

namespace piVC_thu
{
    // 整个 frontend 其实都是 CFGGenerator 这一个 class，
    // 由于 class 里的实现代码太大，为了方便组织，利用 C# 的 partial class 我们将其划分成了几个文件。
    //
    // 我们的语言设计有一个绝妙的地方在于：它是没有 side effect 的。
    // 这样的话，不少 C/C++ 里的 UB 在我们这里是不存在的，比如 `a[++i] = ++i;` 这种。
    partial class CFGGenerator : piBaseVisitor<Expression?>
    {
        // 最终计算出来的 IR 主体
        Main main = default!;

        // 当前正在计算的 function
        Function? currentFunction;
        // block
        Block? currentBlock = null;
        // post block of loop (for break statement)
        BasicBlock? postLoopBlock = null;

        // 符号表
        Dictionary<string, Function> functionTable = new Dictionary<string, Function>();
        Dictionary<string, Struct> structTable = new Dictionary<string, Struct>();
        Dictionary<string, Predicate> predicateTable = new Dictionary<string, Predicate>();
        Stack<Dictionary<string, LocalVariable>> symbolTables = new Stack<Dictionary<string, LocalVariable>>();

        // 用来作 alpha renaming，以及用来生成临时变量
        Counter counter = new Counter();

        // 主要是用来帮助表达式知道自己现在是否在一个 annotation 里
        bool? annotated = null;

        // 真正的主函数
        public Main apply([NotNull] piParser.MainContext context)
        {
            main = new Main();
            Visit(context);
            return main;
        }

        public override Expression? VisitMain([NotNull] piParser.MainContext context)
        {
            foreach (var def in context.def())
                Visit(def);
            return null;
        }

        public override Expression? VisitFuncDef([NotNull] piParser.FuncDefContext context)
        {
            string name = CalcDefName(context, context.IDENT());

            symbolTables.Push(new Dictionary<string, LocalVariable>());

            // 把所有的参数加到符号表里
            int paraNum = context.var().Length;
            VarType[] paraTypes = new VarType[paraNum];
            LocalVariable[] parameters = new LocalVariable[paraNum];
            HashSet<string> paraNames = new HashSet<string>();
            for (int i = 0; i < paraNum; ++i)
            {
                var ctx = context.var()[i];
                paraTypes[i] = CalcType(ctx.type());
                string paraName = ctx.IDENT().GetText();
                if (paraName == "rv")
                    throw new ParsingException(ctx, "'rv' is not permitted as parameter name, as it's used to indicate the return value in postcondition.");
                if (!paraNames.Contains(paraName))
                    paraNames.Add(paraName);
                else
                    throw new ParsingException(ctx, $"duplicate function parameter '{paraName}'");

                LocalVariable paraVariable = new LocalVariable
                {
                    type = paraTypes[i],
                    name = counter.GetVariable(paraName)
                };
                parameters[i] = paraVariable;

                symbolTables.Peek().Add(paraName, paraVariable);
            }

            // 算出 returnType，如果其不是 void，那么就搞出一个 rv 来
            ReturnType returnType = context.type() != null ? CalcType(context.type()) : VoidType.Get();
            LocalVariable? rv = null;
            if (returnType is VarType)
            {
                rv = new LocalVariable
                {
                    type = (VarType)(returnType),
                    name = counter.GetVariable("rv")
                };
            }

            annotated = true;
            PreconditionBlock preconditionBlock = CalcPreconditionBlock(context.beforeFunc().annotationPre(), context.beforeFunc().termination());
            PostconditionBlock postconditionBlock = CalcPostconditionBlock(context.beforeFunc().annotationPost(), rv);
            annotated = null;

            currentFunction = new Function
            {
                type = FunType.Get(returnType, paraTypes),
                name = name,
                parameters = parameters,
                preconditionBlock = preconditionBlock,
                postconditionBlock = postconditionBlock,
                rv = rv
            };
            main.functions.AddLast(currentFunction);
            functionTable.Add(name, currentFunction);

            // visit function body
            currentBlock = new BasicBlock(currentFunction, preconditionBlock);
            annotated = false;
            foreach (var stmt in context.stmt())
                Visit(stmt);
            annotated = null;

            // 理想情况下，currentBasicBlock 应该是空，这表示所有的 path 都已经被 return 了
            if (currentBlock != null)
            {
                if (returnType is VoidType)
                { // 如果函数的返回值类型是 void 的话，我们是允许隐式的 return 的
                    Block.AddEdge(currentBlock, postconditionBlock);
                }
                else
                    throw new ParsingException(context, $"function {name} does not return in all paths.");
            }

            // 搞定这个函数啦~
            symbolTables.Pop();
            currentFunction = null;

            return null;
        }

        public override Expression? VisitStructDef([NotNull] piParser.StructDefContext context)
        {
            string name = CalcDefName(context, context.IDENT());

            // parse member variables
            Dictionary<string, MemberVariable> members = new Dictionary<string, MemberVariable>();
            foreach (var member in context.var())
            {
                string memberName = member.IDENT().GetText();
                MemberVariable memberVariable = new MemberVariable
                {
                    type = CalcType(member.type()),
                    name = memberName
                };
                if (!members.ContainsKey(name))
                    members.Add(memberName, memberVariable);
                else
                    throw new ParsingException(member, $"duplicate struct member '{memberName}'");
            }
            Struct s = new Struct(name, members);
            structTable.Add(name, s);
            main.structs.AddLast(s);
            return null;
        }

        public override Expression? VisitPredDef([NotNull] piParser.PredDefContext context)
        {
            string name = CalcDefName(context, context.IDENT());

            symbolTables.Push(new Dictionary<string, LocalVariable>());

            // calculate parameters
            int paraNum = context.var().Length;
            LocalVariable[] parameters = new LocalVariable[paraNum];
            VarType[] paraTypes = new VarType[paraNum];
            HashSet<string> paraNames = new HashSet<string>();
            for (int i = 0; i < paraNum; ++i)
            {
                var ctx = context.var()[i];
                paraTypes[i] = CalcType(ctx.type());
                string paraName = ctx.IDENT().GetText();
                if (!paraNames.Contains(paraName))
                    paraNames.Add(paraName);
                else
                    throw new ParsingException(ctx, $"duplicate predicate parameter '{paraName}'");

                LocalVariable paraVariable = new LocalVariable
                {
                    type = paraTypes[i],
                    name = counter.GetVariable(paraName)
                };
                parameters[i] = paraVariable;

                symbolTables.Peek().Add(paraName, paraVariable);
            }

            annotated = true;
            Expression expression = NotNullConfirm(context.expr());
            annotated = null;

            Predicate predicate = new Predicate
            {
                type = FunType.Get(BoolType.Get(), paraTypes),
                name = name,
                parameters = parameters,
                expression = expression
            };
            // 这里我们需要在表达式算完之后再将谓词名放到表里，
            // 因为函数可以递归调用自身，但是谓词是不行的
            predicateTable.Add(name, predicate);
            main.predicates.AddLast(predicate);

            symbolTables.Pop();

            return null;
        }

        // ==== utils just for top level definitions ====

        string CalcDefName(ParserRuleContext context, ITerminalNode node)
        {
            string name = node.GetText();
            // check if the name is used by a previous function, struct or predicate
            if (functionTable.ContainsKey(name))
                throw new ParsingException(context, $"a function named '{name}' has already been defined");
            if (structTable.ContainsKey(name))
                throw new ParsingException(context, $"a struct named '{name}' has already been defined");
            if (predicateTable.ContainsKey(name))
                throw new ParsingException(context, $"a predicate named '{name}' has already been defined");
            return name;
        }
    }
}