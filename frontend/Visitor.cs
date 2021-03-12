using System;

using Antlr4.Runtime.Misc;

// TODO: rv 怎么处理还需要仔细想一想……

namespace piVC_thu {
    public class Visitor: piBaseVisitor<Type?> {
        public override Type? VisitMain([NotNull] piParser.MainContext context) {
            Console.WriteLine("visit main");
            return null;
        }
    }
}