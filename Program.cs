using System;
using System.IO;
using System.Collections.Generic;

using Antlr4.Runtime;
using Antlr4.Runtime.Tree;

using CommandLine;
using CommandLine.Text;

namespace piVC_thu
{
    /// <summary>
    /// The main class of the whole verifying compiler.
    /// </summary>
    class Program
    {
        class Options
        {
            [Value(0, MetaName = "source", Required = true, HelpText = "The path to the source pi file.")]
            public String sourcePath { get; set; } = default!;

            [Usage(ApplicationAlias = "piVC-thu")]
            public static IEnumerable<Example> Examples
            {
                get
                {
                    return new List<Example>() {
                        new Example("piVC-thu (pi verifying compiler of Tsinghua University) takes one source file as argument", new Options { sourcePath = "<source>" })
                    };
                }
            }
        }

        /// <summary>
        /// The main method of the whole verifying compiler.
        /// </summary>
        static void Main(string[] args)
        {
            CommandLine.Parser.Default.ParseArguments<Options>(args)
                .WithParsed(RunOptions);
        }

        static void RunOptions(Options opts)
        {
            StreamReader reader = File.OpenText(opts.sourcePath);
            AntlrInputStream stream = new AntlrInputStream(reader);
            ITokenSource lexer = new piLexer(stream);
            ITokenStream tokens = new CommonTokenStream(lexer);
            piParser parser = new piParser(tokens);
            parser.BuildParseTree = true;
            IParseTree tree = parser.main();
            Visitor visitor = new Visitor();
            visitor.Visit(tree);
            Console.WriteLine("Parsed. If something goes wrong, you'll see it.");
        }
    }
}