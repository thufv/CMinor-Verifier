using System;
using System.IO;
using System.Collections.Generic;

using Antlr4.Runtime;
using Antlr4.Runtime.Misc;

using CommandLine;
using CommandLine.Text;

namespace cminor
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
                HelpText = "The file (or 'console') to which the control flow graph is printed.")]
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

        // 返回码的设计是这样的：
        //  0 表示验证成功
        //  1 表示验证失败
        //  2 表示语义错误
        //  3 表示语法错误
        static void RunOptions(Options opts)
        {
            try
            {
                // 首先，我们要生成 cfg！

                StreamReader reader = File.OpenText(opts.sourcePath);

                AntlrInputStream stream = new AntlrInputStream(reader);

                ITokenSource lexer = new CMinorLexer(stream);

                ITokenStream tokens = new CommonTokenStream(lexer);

                CMinorParser parser = new CMinorParser(tokens);

                // 由于现有的 error listener 或者 handler，
                // 要么不会终止 parse，要么连行号都不会打印出来……
                // 所以我们需要写一个新的 listener！
                parser.RemoveErrorListeners();
                parser.AddErrorListener(new ThrowingErrorListener());

                CMinorParser.MainContext tree = parser.main();
                CFGGenerator generator = new CFGGenerator();
                IRMain cfg = generator.Apply(tree);

                if (opts.CFGFile != null)
                {
                    // 输出 cfg
                    using (TextWriter writer = opts.CFGFile == "console"
                        ? Console.Out
                        : new StreamWriter(opts.CFGFile))
                    {
                        cfg.Print(writer);
                    }
                }

                Verifier verifier = new Verifier(Console.Out);
                int result = verifier.Apply(cfg);
                if (result > 0) Console.WriteLine("VERIFIED");
                else if (result == 0) Console.WriteLine("UNKNOWN");
                else if (result < 0) Console.WriteLine("UNVERIFIED");
                Environment.Exit(0);
            }
            catch (ParsingException e)
            {
                Console.Error.WriteLine($"semantic error: {e.Message}");
                Environment.Exit(1);
            }
            catch (ParseCanceledException e)
            {
                Console.Error.WriteLine($"syntax error: {e.Message}");
                Environment.Exit(1);
            }
        }
    }
}
