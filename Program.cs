using System;
using System.Collections.Generic;

using Antlr4.Runtime;
using Antlr4.Runtime.Tree;

using CommandLine;
using CommandLine.Text;

/// <summary>
/// The main class of the whole verifying compiler.
/// </summary>
class Program
{
    class Options {
        [Value(0, MetaName = "source", Required = true, HelpText = "The path to the source pi file.")]
        public String sourcePath { get; set; }

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

    static void RunOptions(Options opts) {
        ICharStream stream = CharStreams.fromPath(opts.sourcePath);
        ITokenSource lexer = new piLexer(stream);
        ITokenStream tokens = new CommonTokenStream(lexer);
        piParser parser = new piParser(tokens);
        parser.BuildParseTree = true;
        IParseTree tree = parser.main();
        Console.WriteLine("Parsed. If something goes wrong, you'll see it.");
    }
}