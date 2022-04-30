using System.Diagnostics;

using Antlr4.Runtime.Misc;

namespace cminor
{
    partial class CFGGenerator: CMinorParserBaseVisitor<Expression?>
    {
        public override Expression? VisitDecl([NotNull] CMinorParser.DeclContext context)
        {
            Debug.Assert(currentBlock != null);

            LocalVariable lv = CalcLocalVar(context.localVar());

            // 遵循 C 标准，初始化表达式中可以出现正在定义的变量，
            // 但这个变量在这个初始化表达式中的值是未定义的。
            // 如果说有初始化表达式存在，那么其实就相当于一个赋值语句，所以也需要放到现在的 block 里。
            if (context.expr() != null)
                Assign(lv, context.expr());
            
            return null;
        }
    }
}