using System;
using System.IO;
using System.Collections.Generic;

using Antlr4.Runtime;

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
            [Option("source",
                Required = true,
                HelpText = "The source file of pi language (recommended with filename extension '.pi').")]
            public string sourcePath { get; set; } = default!;

            [Option("printCFG",
                Required = false,
                HelpText = "The file ('stdout' as console) to which the control flow graph is printed.")]
            public string? CFGFile { get; set; } = null;

            [Usage(ApplicationAlias = "piVC-thu")]
            public static IEnumerable<Example> Examples
            {
                get
                {
                    return new List<Example>()
                    {
                        new Example("The simplest usage to compile and verify a pi source file", new Options
                        {
                            sourcePath = "<path>"
                        })
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
            // 生成 cfg
            StreamReader reader = File.OpenText(opts.sourcePath);
            AntlrInputStream stream = new AntlrInputStream(reader);
            ITokenSource lexer = new piLexer(stream);
            ITokenStream tokens = new CommonTokenStream(lexer);
            piParser parser = new piParser(tokens);
            parser.BuildParseTree = true;
            piParser.MainContext tree = parser.main();
            CFGGenerator generator = new CFGGenerator();
            Main cfg = generator.apply(tree);

            // 输出 cfg
            if (opts.CFGFile != null)
            {
                using (TextWriter writer = opts.CFGFile == "stdout"
                    ? Console.Out
                    : new StreamWriter(opts.CFGFile))
                {
                    cfg.Print(writer);
                }
            }
        }
    }
}