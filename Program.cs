using System;

using Antlr4.Runtime;
using Antlr4.Runtime.Tree;

class Program
{
    static void Main(string[] args)
    {
        String input = @"
@pre  0 <= l && u < |a|
@post rv <-> exists ix. (l <= ix && ix <= u && a[ix] = e)
bool LinearSearch(int[] a, int l, int u, int e) {
    for
        @L: l <= i
        (int i := l; i <= u; i := i + 1)
    {
        if (a[i] = e)
            return true;
    }
    return false;
}
";
        ICharStream stream = CharStreams.fromString(input);
        ITokenSource lexer = new piLexer(stream);
        ITokenStream tokens = new CommonTokenStream(lexer);
        piParser parser = new piParser(tokens);
        parser.BuildParseTree = true;
        IParseTree tree = parser.main();

        Console.WriteLine("Parsed. If something goes wrong, you'll see it.");
    }
}