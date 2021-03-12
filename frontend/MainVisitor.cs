using System;

using Antlr4.Runtime.Misc;

namespace piVC_thu {
    public class MainVisitor: piBaseVisitor<Type> {
        public override Type VisitMain([NotNull] piParser.MainContext context) {
            Console.WriteLine("visit main");
            return new NoType();
        }
    }
}