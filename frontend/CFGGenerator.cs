using System.Linq;
using System.Diagnostics;
using System.Collections.Generic;

using Antlr4.Runtime;
using Antlr4.Runtime.Misc;
using Antlr4.Runtime.Tree;

namespace cminor
{
    // 整个 frontend 其实都是 CFGGenerator 这一个 class，
    // 由于 class 里的实现代码太大，为了方便组织，利用 C# 的 partial class 我们将其划分成了几个文件。
    //
    // 目前我们考虑的语言是没有 side effect 的。
    // 这样的话，不少 C/C++ 里的 UB 在我们这里是不存在的，比如 `a[++i] = ++i;` 这种。
    partial class CFGGenerator : CMinorParserBaseVisitor<Expression?>
    {
        // 最终计算出来的 IR 主体
        IRMain main = default!;

        // 当前正在计算的 function
        Function? currentFunction;
        // block
        Block? currentBlock = null;
        // block that break statement points to
        BasicBlock? breakBlock = null;
        // block that continue statement points to
        Block? contBlock = null;

        // 符号表
        Dictionary<string, Function> functionTable = new Dictionary<string, Function>();
        Dictionary<string, Struct> structTable = new Dictionary<string, Struct>();
        Dictionary<string, Predicate> predicateTable = new Dictionary<string, Predicate>();
        Stack<Dictionary<string, LocalVariable>> symbolTables = new Stack<Dictionary<string, LocalVariable>>();

        // 用来作 alpha renaming，以及用来生成临时变量
        Counter counter = new Counter();

        // 真正的主函数
        public IRMain Apply([NotNull] CMinorParser.MainContext context)
        {
            main = new IRMain();
            Visit(context);

            // 这里我们做一个检查（约定）：ranking function 要么在每个函数头和循环头都有，要么都没有。
            int rankingFunctionExists = -1; // -1 means unkown, 0 means non-existence, 1 means existence
            foreach (Function function in functionTable.Values)
            {
                if (rankingFunctionExists == -1)
                    rankingFunctionExists = function.preconditionBlock.rankingFunction != null ? 1 : 0;
                if (rankingFunctionExists != (function.preconditionBlock.rankingFunction != null ? 1 : 0))
                    throw new ParsingException(context, "Ranking functions should exist in all function contracts and loopheads, or not exist in all function contracts and loopheads.");
                foreach (Block block in function.blocks)
                    if (block is LoopHeadBlock lhb)
                        if (rankingFunctionExists != (function.preconditionBlock.rankingFunction != null ? 1 : 0))
                            throw new ParsingException(context, "Ranking functions should exist in all function contracts and loopheads, or not exist in all function contracts and loopheads.");
            }

            // 把函数和谓词的参数、返回值和类型“拍扁”
            // 也就是说把 struct 消解成几个普通的变量
            foreach (Function function in functionTable.Values)
            {
                // 拍扁参数及其类型
                List<LocalVariable> flattenedParameters = new List<LocalVariable>();
                List<VarType> flattenedParaTypes = new List<VarType>();
                for (int i = 0; i < function.parameters.Count; ++i)
                {
                    if (function.parameters[i] is StructVariable structParameter)
                    {
                        foreach (LocalVariable member in structParameter.members.Values)
                        {
                            flattenedParameters.Add(member);
                            flattenedParaTypes.Add(member.type);
                        }
                    }
                    else
                    {
                        flattenedParameters.Add(function.parameters[i]);
                        flattenedParaTypes.Add(function.parameters[i].type);
                    }
                }
                function.parameters = flattenedParameters;

                if (function.rvs.Count > 0 && function.rvs[0] is StructVariable structRV)
                {
                    // 拍扁返回值
                    Debug.Assert(function.rvs.Count == 1);

                    List<LocalVariable> flattenedRV = new List<LocalVariable>();
                    foreach (LocalVariable member in structRV.members.Values)
                    {
                        flattenedRV.Add(member);
                    }
                    function.rvs = flattenedRV;
                }

                List<VarType> flattenedReturnTypes = new List<VarType>();
                foreach (LocalVariable rv in function.rvs)
                {
                    flattenedReturnTypes.Add(rv.type);
                }
                function.type = FunType.Get(flattenedReturnTypes, flattenedParaTypes);
            }
            foreach (Predicate predicate in predicateTable.Values)
            {
                // 拍扁参数及其类型
                List<LocalVariable> flattenedParameters = new List<LocalVariable>();
                List<VarType> flattenedParaTypes = new List<VarType>();
                for (int i = 0; i < predicate.parameters.Count; ++i)
                {
                    if (predicate.parameters[i] is StructVariable structParameter)
                    {
                        foreach (LocalVariable member in structParameter.members.Values)
                        {
                            flattenedParameters.Add(member);
                            flattenedParaTypes.Add(member.type);
                        }
                    }
                    else
                    {
                        flattenedParameters.Add(predicate.parameters[i]);
                        flattenedParaTypes.Add(predicate.parameters[i].type);
                    }
                }
                predicate.type = PredType.Get(flattenedParaTypes);
                predicate.parameters = flattenedParameters;
            }

            return main;
        }

        public override Expression? VisitMain([NotNull] CMinorParser.MainContext context)
        {
            foreach (var def in context.def())
                Visit(def);
            return null;
        }

        public override Expression? VisitFuncDef([NotNull] CMinorParser.FuncDefContext context)
        {
            string name = CalcDefName(context, context.retVar().IDENT().Last());

            // 把所有的形参加到符号表里
            symbolTables.Push(new Dictionary<string, LocalVariable>());
            var paraVars = new List<LocalVariable>(context.paraVar().Select(ctx => CalcParaVar(ctx)));
            var paraTypes = new List<VarType>(paraVars.Select(var => var.type));

            // 算出 returnType，如果其不是 void，那么就搞出一个 \result 变量来
            List<VarType> returnTypes = new List<VarType>();
            List<LocalVariable> rvs = new List<LocalVariable>();
            if (context.retVar().GetChild(0).GetText() != "void")
            {
                LocalVariable rv = CalcRetVar(context.retVar());
                returnTypes.Add(rv.type);
                rvs.Add(rv);
            }

            PreconditionBlock preconditionBlock = CalcPreconditionBlock(context.funcContract().requiresClause(), context.funcContract().decreasesClause());
            PostconditionBlock postconditionBlock = CalcPostconditionBlock(context.funcContract().ensuresClause(), rvs);

            currentFunction = new Function
            {
                type = FunType.Get(returnTypes, paraTypes),
                name = name,
                parameters = paraVars,
                preconditionBlock = preconditionBlock,
                postconditionBlock = postconditionBlock,
                rvs = rvs
            };
            main.functions.AddLast(currentFunction);
            functionTable.Add(name, currentFunction);

            // visit function body
            currentBlock = new BasicBlock(currentFunction, preconditionBlock);

            // 逐次访问函数中的每一条语句
            foreach (var child in context.children)
                if (child is CMinorParser.DeclContext decl)
                    Visit(decl);
                else if (child is CMinorParser.StmtContext stmt)
                    Visit(stmt);

            // 理想情况下，currentBasicBlock 应该是空，这表示所有的 path 都已经被 return 了
            if (currentBlock != null)
            {
                if (returnTypes.Count == 0)
                { // 如果函数的返回值类型是 void 的话，我们是允许隐式的 return 的
                    Block.AddEdge(currentBlock, postconditionBlock);
                }
                else
                    throw new ParsingException(context, $"function '{name}' does not return in all paths.");
            }

            // 搞定这个函数啦~
            symbolTables.Pop();

            currentFunction = null;

            return null;
        }

        public override Expression? VisitStructDef([NotNull] CMinorParser.StructDefContext context)
        {
            string name = CalcDefName(context, context.IDENT().First());

            // parse member variables
            var members = new SortedDictionary<string, MemberVariable>();
            for (int i = 0; i < context.atomicType().Length; ++i)
            {
                string memberName = context.IDENT()[i + 1].GetText();
                MemberVariable memberVariable = new MemberVariable
                {
                    type = AtomicType.FromString(context.atomicType()[i].GetText()),
                    name = memberName
                };
                if (!members.ContainsKey(memberName))
                    members.Add(memberName, memberVariable);
                else
                    throw new ParsingException(context, $"duplicate struct member '{memberName}'");
            }
            Struct s = new Struct(name, members);
            structTable.Add(name, s);
            return null;
        }

        public override Expression? VisitPredDef([NotNull] CMinorParser.PredDefContext context)
        {
            string name = CalcDefName(context, context.IDENT());

            // calculate parameters
            symbolTables.Push(new Dictionary<string, LocalVariable>());
            var paraVars = new List<LocalVariable>(context.logicParaVar().Select(ctx => CalcLogicParaVar(ctx)));
            var paraTypes = new List<VarType>(paraVars.Select(var => var.type));

            Expression expression = NotNullConfirm(context.pred());

            // 最后再把这个加到谓词表里，避免其表达式中有对自身的引用。

            Predicate predicate = new Predicate
            {
                type = PredType.Get(paraTypes),
                name = name,
                parameters = paraVars,
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