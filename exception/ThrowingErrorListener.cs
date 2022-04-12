using Antlr4.Runtime;
using Antlr4.Runtime.Misc;

namespace cminor
{
    public class ThrowingErrorListener : BaseErrorListener
    {
        public override void SyntaxError([NotNull] IRecognizer recognizer, [Nullable] IToken offendingSymbol, int line, int charPositionInLine, [NotNull] string msg, [Nullable] RecognitionException e)
        {
            throw new ParseCanceledException($"({line}, {charPositionInLine}): {msg}");
        }
    }
}