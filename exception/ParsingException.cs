using System;
using Antlr4.Runtime;

using Antlr4.Runtime.Misc;

namespace piVC_thu
{
    public class ParsingException : Exception
    {
        public ParsingException() { }
        public ParsingException(string message) : base(message) { }
        public ParsingException(string message, Exception inner) : base(message, inner) { }

        public ParsingException([NotNull] ParserRuleContext context, string message) : base($"({context.Start.Line}, {context.Start.Column}): {message}")
        { }
    }
}