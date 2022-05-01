using System;
using System.Linq;
using System.Collections.Generic;

using System.Diagnostics;

using Antlr4.Runtime;
using Antlr4.Runtime.Misc;

namespace cminor
{
    // 如果是专属于某一部分的 util method，就放到直接放到它的那个文件里吧QAQ
    partial class CFGGenerator : CMinorParserBaseVisitor<Expression?>
    {
        VarType CalcType(string type, bool isArray)
        {
            if (AtomicType.availableNames.Contains(type))
            { // atomic type or array type
                AtomicType atomicType = AtomicType.FromString(type);
                if (isArray)
                { // array type
                    return ArrayType.Get(atomicType);
                }
                else
                { // atomic type
                    return atomicType;
                }
            }
            else
            { // struct type
                Debug.Assert(!isArray);
                if (structTable.ContainsKey(type))
                    return structTable[type].type;
                else
                    throw new ArgumentException($"unknown type '{type}'.");
            }
        }

        LocalVariable CalcVar([NotNull] ParserRuleContext context, string name, VarType type)
        {
            if (symbolTables.Peek().ContainsKey(name))
                throw new ParsingException(context, $"duplicate declared variable {name}");
            string varname = counter.GetVariable(name);
            
            LocalVariable variable;
            if (type is StructType st)
            {
                variable = new StructVariable(st, varname);
            }
            else if (type is ArrayType at)
            {
                variable = new ArrayVariable
                {
                    type = at,
                    name = varname,
                    length = new LocalVariable
                    {
                        type = IntType.Get(),
                        name = Counter.GetLength(name)
                    }
                };
            }
            else
            {
                Debug.Assert(type is AtomicType);
                variable = new LocalVariable
                {
                    type = type,
                    name = varname
                };
            }

            // 把新建出来的变量放到符号表里并返回
            symbolTables.Peek().Add(name, variable);
            return variable;
        }

        LocalVariable CalcLocalVar([NotNull] CMinorParser.LocalVarContext context)
        {
            Debug.Assert(currentBlock != null);

            string name = context.IDENT().Last().GetText();
            VarType type = CalcType(context.children[
                    context.children.IndexOf(context.IDENT().Last()) - 1
                ].GetText(), context.ChildCount > 3);
            LocalVariable lv = CalcVar(context, name, type);

            // 对于数组来说，在声明时我们会要求指定一个 literal 作为长度。
            if (context.INT_CONSTANT() != null)
            {
                Debug.Assert(lv is ArrayVariable);
                Debug.Assert(type is ArrayType);

                currentBlock.AddStatement(new VariableAssignStatement
                {
                    variable = ((ArrayVariable)lv).length,
                    rhs = new IntConstantExpression(int.Parse(context.INT_CONSTANT().GetText()))
                });
            }

            return lv;
        }

        LocalVariable CalcParaVar([NotNull] CMinorParser.ParaVarContext context)
        {
            string name = context.IDENT().Last().GetText();
            VarType type = CalcType(context.children[
                    context.children.IndexOf(context.IDENT().Last()) - 1
                ].GetText(), context.ChildCount > 3);
            return CalcVar(context, name, type);
        }

        LocalVariable CalcLogicParaVar([NotNull] CMinorParser.LogicParaVarContext context)
        {
            string name = context.IDENT().Last().GetText();
            VarType type = CalcType(context.children[
                    context.children.IndexOf(context.IDENT().Last()) - 1
                ].GetText(), context.ChildCount > 3);
            return CalcVar(context, name, type);
        }

        LocalVariable CalcRetVar([NotNull] CMinorParser.RetVarContext context)
        {
            VarType type = CalcType(context.children[
                    context.children.IndexOf(context.IDENT().Last()) - 1
                ].GetText(), false);
            return CalcVar(context, "\\result", type);
        }

        Expression TypeConfirm([NotNull] ParserRuleContext context, bool boolAsInt, params Type[] intendedTypes)
        {
            Expression? expression = Visit(context);
            if (expression == null)
                throw new ParsingException(context, $"try to use an expression of type 'void'.");
            foreach (Type intendedType in intendedTypes)
                if (expression.type == intendedType)
                    return expression;
            if (boolAsInt)
            {
                if (expression.type is BoolType && intendedTypes.Contains(IntType.Get()))
                    return new ITEExpression(expression, new IntConstantExpression(1), new IntConstantExpression(0));
                if (expression.type is IntType && intendedTypes.Contains(BoolType.Get()))
                    return new NEExpression(expression, new IntConstantExpression(0));
            }
            throw new ParsingException(context, $"the expected types of the expression are {intendedTypes}, while the actual type is '{expression.type}'.");
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
            // 这个临时变量的名字是：_cond${number}
            int conditionCounter = 0;
            public string GetCondition()
            {
                return "_cond" + "$" + ++conditionCounter;
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