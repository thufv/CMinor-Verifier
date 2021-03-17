using Antlr4.Runtime;

namespace piVC_thu
{
    // 如果是专属于某一部分的 util method，就放到直接放到它的那个文件里吧QAQ
    partial class CFGGenerator : piBaseVisitor<Expression?>
    {
        // We don't override VisitType and VisitAtomicType,
        // as we directly use the following method CalcType.
        VarType CalcType(piParser.TypeContext context)
        {
            if (context.IDENT() != null)
            { // struct type
                string structName = context.IDENT().GetText();
                if (structTable.ContainsKey(structName))
                    return structTable[structName].type;
                else
                    throw new ParsingException(context, "unknown type");
            }
            else
            { // atomic type or array type
                AtomicType atomicType;
                switch (context.atomicType().GetText())
                {
                    case "int":
                        atomicType = IntType.Get();
                        break;
                    case "float":
                        atomicType = FloatType.Get();
                        break;
                    case "bool":
                        atomicType = BoolType.Get();
                        break;
                    default:
                        throw new ParsingException(context, "an atomic type that is not int, float, nor bool is found. Probably a bug occurs.");
                }
                if (context.ChildCount == 1)
                { // atomic type
                    return atomicType;
                }
                else
                { // array type
                    return ArrayType.Get(atomicType);
                }
            }
        }

        Expression TypeConfirm(ParserRuleContext context, Expression expression, Type intendedType, bool annotated = false)
        {
            if (expression.type != intendedType)
                throw new ParsingException(context, $"the expected type of the expression is {intendedType.GetType().Name} while the actual type is {expression.GetType().Name}.");
            if (!annotated && expression.annotated)
                throw new ParsingException(context, "quantifiers are only allowed to be used in annotations.");
            return expression;
        }

        LocalVariable FindLocalVariable(ParserRuleContext context, string name)
        {
            // consider each symbol table reversely
            foreach (var symbolTable in symbolTables)
                if (symbolTable.ContainsKey(name))
                    return symbolTable[name];
            throw new ParsingException(context, $"cannot find local variable {name}.");
        }
        bool LocalVariableExists(string name)
        {
            // consider each symbol table reversely
            foreach (var symbolTable in symbolTables)
                if (symbolTable.ContainsKey(name))
                    return true;
            return false;
        }
    }
}