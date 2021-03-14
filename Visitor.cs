using System;

using Antlr4.Runtime.Misc;

// TODO: rv 怎么处理还需要仔细想一想……

namespace piVC_thu
{
    class Visitor : piBaseVisitor<Expression?>
    {
        public override Expression? VisitMain([NotNull] piParser.MainContext context)
        {
            // TODO: maybe some initializations are needed here

            foreach (var decl in context.decl())
                Visit(decl);

            Console.WriteLine("visit main");

            return null;
        }
    }
}