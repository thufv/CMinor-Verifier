using System;
using System.IO;
using System.Collections.Generic;

using Antlr4.Runtime;
using Antlr4.Runtime.Misc;

namespace cminor
{
    class Program
    {
        static void Main(string[] args)
        {
            StreamReader reader = File.OpenText(args[0]);

            var stream = new AntlrInputStream(reader);
            var lexer  = new CMinorLexer(stream);
            var tokens = new CommonTokenStream(lexer);
            var parser = new CMinorParser(tokens);

            var compileUnit = parser.main();

            Console.WriteLine(compileUnit.ToStringTree());
        }
    }
}
