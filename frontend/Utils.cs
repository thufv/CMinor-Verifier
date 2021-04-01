using System;
using System.Collections.Generic;

using System.Diagnostics;

using Antlr4.Runtime;
using Antlr4.Runtime.Misc;

namespace piVC_thu
{
    // 如果是专属于某一部分的 util method，就放到直接放到它的那个文件里吧QAQ
    partial class CFGGenerator : piBaseVisitor<Expression?>
    {
        // We don't override VisitType and VisitAtomicType,
        // as we directly use the following method CalcType.
        VarType CalcType([NotNull] piParser.TypeContext context)
        {
            if (context.IDENT() != null)
            { // struct type
                string structName = context.IDENT().GetText();
                if (structTable.ContainsKey(structName))
                    return structTable[structName].type;
                else
                    throw new ParsingException(context, $"unknown type '{structName}'.");
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

        Expression TypeConfirm([NotNull] ParserRuleContext context, Type intendedType)
        {
            Expression? expression = Visit(context);
            if (expression == null)
                throw new ParsingException(context, $"try to use an expression of type 'void'.");
            if (expression.type != intendedType)
                throw new ParsingException(context, $"the expected type of the expression is '{intendedType}' while the actual type is '{expression.type}'.");
            return expression;
        }

        LocalVariable FindVariable([NotNull] ParserRuleContext context, string name)
        {
            // consider each symbol table reversely
            foreach (var symbolTable in symbolTables)
                if (symbolTable.ContainsKey(name))
                {
                    // Console.WriteLine($"Found variable ({symbolTable[name].name}: {symbolTable[name].type}) of name {name}.");

                    return symbolTable[name];
                }
            throw new ParsingException(context, $"cannot find local variable '{name}'.");
        }
        bool LocalVariableExists(string name)
        {
            // consider each symbol table reversely
            foreach (var symbolTable in symbolTables)
                if (symbolTable.ContainsKey(name))
                    return true;
            return false;
        }

        Expression NotNullConfirm([NotNull] ParserRuleContext context)
        {
            Expression? expression = Visit(context);
            if (expression != null)
                return expression;
            else
                throw new ParsingException(context, $"try to use a void expression.");
        }

        // 把一个表达式压缩成一个变量。
        // 也就是说，添加一个辅助变量用来表示这个表达式，
        // 然后传回一个只有一个变量的表达式。
        VariableExpression CompressedExpression(Expression expression, Func<string> getName)
        {
            if (expression is VariableExpression ve)
                return ve;
            else
            {
                Debug.Assert(currentBlock != null);
                LocalVariable variable = new LocalVariable
                {
                    type = expression.type,
                    name = getName()
                };
                currentBlock.AddStatement(new VariableAssignStatement
                {
                    variable = variable,
                    rhs = expression
                });
                return new VariableExpression(variable);
            }
        }

        // 从 Counter 里得到的所有数字都是全局唯一的
        public class Counter
        {
            // 这个是用来作 alpha renaming 的，每个 function 会清空一次
            // 局部变量作 alpha-renaming 会变成：{name}${number}
            // 成员变量作 alpha-renaming 会变成：{structName}${number}${memberName}
            Dictionary<string, int> variableCounter = new Dictionary<string, int>();
            public string GetVariable(string variable)
            {
                int number = variableCounter.GetValueOrDefault<string, int>(variable) + 1;
                variableCounter[variable] = number;
                return variable + "$" + number;
            }

            // 我们需要为每一个函数调用搞一个临时变量
            // 这个临时变量的名字是：_call_{variable}${number}
            Dictionary<string, int> callCounter = new Dictionary<string, int>();
            public string GetCall(string variable)
            {
                int number = callCounter.GetValueOrDefault<string, int>(variable) + 1;
                callCounter[variable] = number;
                return "_call_" + variable + "$" + number;
            }

            // 如果一个 condition 不是只有一个变量组成的，
            // 那么我们需要为这个 condition 搞一个临时变量
            // 这个临时变量的名字是：_condition${number}
            int conditionCounter = 0;
            public string GetCondition()
            {
                return "_condition" + "$" + ++conditionCounter;
            }

            // 我们也需要为每一个新数组搞一个临时变量：_array${number}
            // 注意：这个仅用于 new 出来的数组。
            // 有名字的数组，包括局部变量、参数或返回值，还是会被视为变量来处理。
            int newArrayCounter = 0;
            public string GetArray()
            {
                return "_array" + "$" + ++newArrayCounter;
            }

            // 我们其实也需要为每一个参数搞一个临时变量：_arg${number}
            int newArgNumber = 0;
            public string GetArg()
            {
                return "_arg" + "$" + ++newArgNumber;
            }

            // 为数组下标搞一个临时变量：_sub${number}
            // 这是为了方便 assert 其合法性（runtime assertion）
            int subCounter = 0;
            public string GetSub()
            {
                return "_sub" + "$" + ++subCounter;
            }

            // 为数组长度搞一个临时变量：_length${name}
            // 因为我们已知数组的变量名便是全局 unique 的，
            // 所以长度的变量名也是全局 unique 的。
            public static string GetLength(string variable)
            {
                return "_length" + "$" + variable;
            }

            // 为除数搞一个临时变量：_divisor${number}
            // 这是为了方便 assert 其非零性
            // 方便起见，这里我们统一考虑 /, div 和 %
            int divisorCounter = 0;
            public string GetDivisor()
            {
                return "_divisor" + "$" + ++divisorCounter;
            }
        }
    }
}