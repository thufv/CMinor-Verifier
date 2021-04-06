/*
    这里有生成表达式的逻辑。
*/

using System;
using System.Linq;
using System.Diagnostics;
using System.Collections.Generic;

using Antlr4.Runtime.Misc;

namespace piVC_thu
{
    partial class CFGGenerator : piBaseVisitor<Expression?>
    {
        public override Expression VisitIdentExpr([NotNull] piParser.IdentExprContext context)
        {
            LocalVariable variable = FindVariable(context, context.IDENT().GetText());
            return new VariableExpression(variable);
        }

        public override Expression VisitConstExpr([NotNull] piParser.ConstExprContext context)
        {
            return NotNullConfirm(context.constant());
        }

        public override Expression? VisitCallExpr([NotNull] piParser.CallExprContext context)
        {
            string calledName = context.IDENT().GetText();
            if (LocalVariableExists(calledName))
                throw new ParsingException(context, "call a variable that is neither function nor predicate.");

            Debug.Assert(annotated.HasValue);
            if (!annotated.Value)
            {
                if (!functionTable.ContainsKey(calledName))
                    throw new ParsingException(context, $"no function named '{calledName}'");

                Debug.Assert(!predicateTable.ContainsKey(calledName));
                Debug.Assert(currentBlock != null);

                Function function = functionTable[calledName];

                // 先算出参数来
                int paraNum = function.type.paraTypes.Count;
                if (paraNum != context.expr().Length)
                    throw new ParsingException(context, $"the number of arguments passed to function '{calledName}' is not the same as defined.");
                List<LocalVariable> argumentVariables = new List<LocalVariable>();
                for (int i = 0; i < paraNum; ++i)
                {
                    Expression argumentExpression = TypeConfirm(context.expr()[i], function.type.paraTypes[i]);
                    if (argumentExpression is VariableExpression variableExpression)
                    {
                        // 如果参数是一个 struct 的话，就把它拍扁，每个成员作为一个参数
                        if (variableExpression.variable is StructVariable sv)
                        {
                            foreach (LocalVariable memberVariable in sv.members.Values)
                            {
                                argumentVariables.Add(memberVariable);
                            }
                        }
                        else
                        {
                            argumentVariables.Add(variableExpression.variable);
                        }
                    }
                    else
                    { // 如果说表达式不只是由单个变量构成的话，我们就需要为它搞一个新的临时变量。
                        argumentVariables.Add(CompressedExpression(argumentExpression, counter.GetArg).variable);
                    }
                    Debug.Assert(argumentVariables[i] is not QuantifiedVariable);
                }

                // 把一条 function call 的 statement 加到当前的基本块里
                FunctionCallExpression expression = new FunctionCallExpression
                {
                    function = function,
                    argumentVariables = argumentVariables
                };
                if (function.type.returnTypes.Count == 0)
                {
                    currentBlock.AddStatement(new FunctionCallStatement
                    {
                        rhs = expression
                    });
                    // 如果返回值是 void 的话，那么就没有返回表达式。
                    // 这里其实是所有的 expression visit method 中唯一一个会返回 null 的地方。
                    return null;
                }
                else
                {
                    Debug.Assert(function.type.returnTypes.Count == 1);

                    // 如果返回值不是 void，那么这里其实是需要添加一个 assign statement，
                    // 然后把装有函数的返回值的临时变量回传。
                    string callName = counter.GetCall(function.name);
                    List<LocalVariable> lhs = new List<LocalVariable>();
                    LocalVariable variable;
                    switch (function.type.returnTypes[0])
                    {
                        case StructType st:
                            // 如果返回值类型是一个 struct type，那么需要把它“拍扁”
                            variable = new StructVariable(st, callName);

                            foreach (LocalVariable member in ((StructVariable)variable).members.Values)
                            {
                                lhs.Add(member);
                            }
                            break;
                        case ArrayType at:
                            // 如果返回值类型是一个 array type，那么需要把长度 havoc
                            variable = new ArrayVariable
                            {
                                type = at,
                                name = callName,
                                length = new LocalVariable
                                {
                                    type = IntType.Get(),
                                    name = Counter.GetLength(callName)
                                }
                            };

                            lhs.Add(variable);
                            break;
                        default:
                            Debug.Assert(function.type.returnTypes[0] is VarType);
                            variable = new LocalVariable
                            {
                                type = (VarType)(function.type.returnTypes[0]),
                                name = callName
                            };
                            lhs.Add(variable);
                            break;
                    }
                    currentBlock.AddStatement(new FunctionCallStatement
                    {
                        lhs = lhs,
                        rhs = expression
                    });

                    return new VariableExpression(variable);
                }
            }
            else
            {
                if (!predicateTable.ContainsKey(calledName))
                    throw new ParsingException(context, $"no predicate named '{calledName}'");

                // 这种其实很简单，正常来就行啦QAQ
                Predicate predicate = predicateTable[calledName];

                // 把所有参数算出来！
                int paraNum = predicate.type.paraTypes.Count;
                if (paraNum != context.expr().Length)
                    throw new ParsingException(context, $"the number of arguments passed to function '{calledName}' is not the same as defined.");
                List<Expression> argumentExpressions = new List<Expression>();
                for (int i = 0; i < paraNum; ++i)
                {
                    Expression argumentExpression = TypeConfirm(context.expr()[i], predicate.type.paraTypes[i]);
                    if (argumentExpression.type is StructType)
                    {
                        Debug.Assert(argumentExpression is VariableExpression);
                        Debug.Assert(((VariableExpression)argumentExpression).variable is StructVariable);
                        foreach (LocalVariable member in ((StructVariable)(((VariableExpression)argumentExpression).variable)).members.Values)
                        {
                            argumentExpressions.Add(argumentExpression);
                        }
                    }
                    else
                    {
                        argumentExpressions.Add(argumentExpression);
                    }
                }

                return new PredicateCallExpression(predicate, argumentExpressions);
            }
            throw new ParsingException(context, "an undefined symbol is called.");
        }

        public override Expression? VisitParExpr([NotNull] piParser.ParExprContext context)
        {
            return Visit(context.expr());
        }

        public override Expression VisitSubExpr([NotNull] piParser.SubExprContext context)
        {
            Expression array = NotNullConfirm(context.expr()[0]);

            Debug.Assert(annotated != null);
            if (annotated == false)
            {
                Debug.Assert(currentBlock != null);

                VariableExpression subscript = CompressedExpression(TypeConfirm(context.expr()[1], IntType.Get()), counter.GetSub);

                // runtime assertion: subscript >= 0
                currentBlock.AddStatement(new AssertStatement()
                {
                    annotation = new LEExpression(new IntConstantExpression(0), subscript)
                });

                // runtime assertion: subscript < length
                Debug.Assert(currentBlock != null);
                currentBlock.AddStatement(new AssertStatement()
                {
                    annotation = new LTExpression(subscript, new LengthExpression(array))
                });

                return new SubscriptExpression(array, subscript);
            }
            else
            {
                Expression subscript = TypeConfirm(context.expr()[1], IntType.Get());
                return new SubscriptExpression(array, subscript);
            }
            throw new ParsingException(context, $"request for an element in a non-array expression.");
        }

        public override Expression VisitNewArrayExpr([NotNull] piParser.NewArrayExprContext context)
        {
            Debug.Assert(annotated.HasValue);
            if (annotated.Value)
                throw new ParsingException(context, "new array are not allowed in annotation.");
            Debug.Assert(currentBlock != null);

            string atomicTypeString = context.atomicType().GetText();
            AtomicType atomicType;
            switch (atomicTypeString)
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
                    throw new ParsingException(context, "an atomic type that is neither int, float not bool. Probably a bug occurs.");
            }

            string arrayName = counter.GetArray();
            VariableExpression length = CompressedExpression(TypeConfirm(context.expr(), IntType.Get()), () => Counter.GetLength(arrayName));
            // runtime assertion: length of array >= 0
            currentBlock.AddStatement(new AssertStatement
            {
                annotation = new GEExpression(length, new IntConstantExpression(0))
            });
            ArrayVariable arrayVariable = new ArrayVariable
            {
                type = ArrayType.Get(atomicType),
                name = arrayName,
                length = length.variable
            };
            return new VariableExpression(arrayVariable);
        }

        public override Expression VisitMemExpr([NotNull] piParser.MemExprContext context)
        {
            Expression structExpression = NotNullConfirm(context.expr());
            string memberName = context.IDENT().GetText();

            // struct 只能是变量或者函数的返回值，
            // 函数的返回值会被用临时变量处理，
            // 所以这里肯定会是一个局部变量。
            if (structExpression is not VariableExpression)
                throw new ParsingException(context, $"request for member '{memberName}' in a non-variable expression. Probably a bug occurs.");

            // 从表达式得到变量
            Variable structVariable = ((VariableExpression)structExpression).variable;
            if (structVariable is not StructVariable)
                throw new ParsingException(context, $"request for member '{memberName}' in an expression of non-struct type '{structExpression.type}'");

            // 从变量得到定义
            Struct structDefinition = ((StructType)(structExpression.type)).structDefinition;
            if (!structDefinition.members.ContainsKey(memberName))
                throw new ParsingException(context, $"'struct {structDefinition.name}' has no member named '{memberName}'.");

            // 将成员变量转化成一个局部变量
            MemberVariable memberVariable = structDefinition.members[memberName];
            var members = ((StructVariable)structVariable).members;
            if (!members.ContainsKey(memberName))
            { // 如果之前已经转化过一次了，那么就得直接用之前转化出来的
                members[memberName] = new LocalVariable
                {
                    name = structVariable.name + "$" + memberName,
                    type = memberVariable.type
                };
            }

            return new VariableExpression(members[memberName]);
        }

        public override Expression VisitArrUpdExpr([NotNull] piParser.ArrUpdExprContext context)
        {
            Expression array = NotNullConfirm(context.expr()[0]);
            if (array.type is ArrayType at)
            {
                Debug.Assert(annotated.HasValue);
                if (annotated.Value)
                {
                    Expression subscript = TypeConfirm(context.expr()[1], IntType.Get());
                    Expression rhs = TypeConfirm(context.expr()[2], ((ArrayType)(array.type)).atomicType);
                    if (array is ArrayUpdateExpression aue)
                    {
                        return new ArrayUpdateExpression(array, subscript, rhs, aue.length);
                    }
                    else if (array is VariableExpression ve && ve.variable is ArrayVariable av)
                    {
                        return new ArrayUpdateExpression(array, subscript, rhs, new VariableExpression(av.length));
                    }
                    else
                        throw new ArgumentException(
                            message: "the expression to update as array is neither single variable expression nor array update expression. Probably a bug occurs.",
                            paramName: nameof(array));
                }
                else
                {
                    Debug.Assert(currentBlock != null);

                    VariableExpression subscript = CompressedExpression(TypeConfirm(context.expr()[1], IntType.Get()), counter.GetSub);

                    // runtime assertion: subscript >= 0
                    currentBlock.AddStatement(new AssertStatement()
                    {
                        annotation = new LEExpression(new IntConstantExpression(0), subscript)
                    });

                    Expression rhs = TypeConfirm(context.expr()[2], ((ArrayType)(array.type)).atomicType);

                    // runtime assertion: subscript < length
                    currentBlock.AddStatement(new AssertStatement()
                    {
                        annotation = new LTExpression(subscript, new LengthExpression(array))
                    });

                    if (array is ArrayUpdateExpression aue)
                    {
                        return new ArrayUpdateExpression(array, subscript, rhs, aue.length);
                    }
                    else if (array is VariableExpression ve && ve.variable is ArrayVariable av)
                    {
                        return new ArrayUpdateExpression(array, subscript, rhs, new VariableExpression(av.length));
                    }
                    else
                        throw new ArgumentException(
                            message: "the expression to update as array is neither single variable expression nor array update expression. Probably a bug occurs.",
                            paramName: nameof(array));
                }
            }
            else
                throw new ParsingException(context, $"updating a non-array expression as it is an array.");
        }

        public override Expression VisitUnaryExpr([NotNull] piParser.UnaryExprContext context)
        {
            Expression expression = NotNullConfirm(context.expr());
            string op = context.GetChild(0).GetText();
            switch (op)
            {
                case "!":
                    if (!(expression.type is BoolType))
                        throw new ParsingException(context, "the type of expression just after '!' must be bool.");
                    return new NotExpression(expression);
                case "-":
                    if (!(expression.type is IntType || expression.type is FloatType))
                        throw new ParsingException(context, "the type of expression just after '-' must be int or float.");
                    return new NegExpression(expression);
                default:
                    throw new ArgumentException(
                        message: $"operator '{op}' is neither '!' nor '-'. Probably a bug occurs.",
                        paramName: nameof(op));
            }
        }

        public override Expression VisitMulExpr([NotNull] piParser.MulExprContext context)
        {
            Expression le = NotNullConfirm(context.expr()[0]);
            Expression re = NotNullConfirm(context.expr()[1]);
            string op = context.GetChild(1).GetText();

            switch (op)
            {
                case "*":
                    if (!(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType))
                        throw new ParsingException(context, "the type of expression between '*' must be both 'int' or 'float'.");
                    return new MultiExpression(le, re);
                case "/":
                    if (!(le.type is FloatType && re.type is FloatType))
                        throw new ParsingException(context, "the type of expression between '/' must be both 'float'.");
                    if (annotated == false)
                    {
                        Debug.Assert(currentBlock != null);
                        re = CompressedExpression(re, counter.GetDivisor);
                        currentBlock.AddStatement(new AssertStatement()
                        {
                            annotation = new NEExpression(re, new FloatConstantExpression(0))
                        });
                    }
                    return new FloatDivExpression(le, re);
                case "div":
                    if (!(le.type is IntType && re.type is IntType))
                        throw new ParsingException(context, "the type of expression between 'div' must be both 'int'.");
                    if (annotated == false)
                    {
                        Debug.Assert(currentBlock != null);
                        re = CompressedExpression(re, counter.GetDivisor);
                        currentBlock.AddStatement(new AssertStatement()
                        {
                            annotation = new NEExpression(re, new IntConstantExpression(0))
                        });
                    }
                    return new DivExpression(le, re);
                case "%":
                    if (!(le.type is IntType && re.type is IntType))
                        throw new ParsingException(context, "the type of expression '%' must be both 'int'.");
                    if (annotated == false)
                    {
                        Debug.Assert(currentBlock != null);
                        re = CompressedExpression(re, counter.GetDivisor);
                        currentBlock.AddStatement(new AssertStatement()
                        {
                            annotation = new NEExpression(re, new IntConstantExpression(0))
                        });
                    }
                    return new ModExpression(le, re);
                default:
                    throw new ArgumentException(
                        message: $"operator '{op}' is neither '*', '/', 'div' nor '%'. Probably a bug occurs.",
                        paramName: nameof(op));
            }
        }

        public override Expression VisitAddExpr([NotNull] piParser.AddExprContext context)
        {
            Expression le = NotNullConfirm(context.expr()[0]);
            Expression re = NotNullConfirm(context.expr()[1]);
            string op = context.GetChild(1).GetText();

            if (!(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType))
                throw new ParsingException(context, "the type of expression between '+' or '-' must be both int or float.");

            switch (op)
            {
                case "+":
                    return new AddExpression(le, re);
                case "-":
                    return new SubExpression(le, re);
                default:
                    throw new ArgumentException(
                        message: $"operator '{op}' is neither '+' nor '-'. Probably a bug occurs.",
                        paramName: nameof(op));
            }
        }

        public override Expression VisitInequExpr([NotNull] piParser.InequExprContext context)
        {
            Expression le = NotNullConfirm(context.expr()[0]);
            Expression re = NotNullConfirm(context.expr()[1]);
            string op = context.GetChild(1).GetText();

            if (!(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType))
                throw new ParsingException(context, $"the type of expression between inequality must be both int or float, while now they are '{le.type}' and '{re.type}'.");

            switch (op)
            {
                case "<":
                    return new LTExpression(le, re);
                case "<=":
                    return new LEExpression(le, re);
                case ">":
                    return new GTExpression(le, re);
                case ">=":
                    return new GEExpression(le, re);
                default:
                    throw new ArgumentException(
                        message: $"operator '{op}' is neither '<', '<=', '>' nor '>='. Probably a bug occurs.",
                        paramName: nameof(op));
            }
        }

        public override Expression VisitEquExpr([NotNull] piParser.EquExprContext context)
        {
            Expression le = NotNullConfirm(context.expr()[0]);
            Expression re = NotNullConfirm(context.expr()[1]);
            string op = context.GetChild(1).GetText();

            if (!(le.type is AtomicType && re.type is AtomicType && le.type == re.type))
                throw new ParsingException(context, $"the type of expression between '=' or '!=' must be of same atomic type, while now they are '{le.type}' and '{re.type}'.");

            switch (op)
            {
                case "=":
                    return new EQExpression(le, re);
                case "!=":
                    return new NEExpression(le, re);
                default:
                    throw new ArgumentException(
                        message: $"operator '{op}' is neither '<', '<=', '>' nor '>='. Probably a bug occurs.",
                        paramName: nameof(op));
            }
        }

        public override Expression VisitQuantifiedExpr([NotNull] piParser.QuantifiedExprContext context)
        {
            Debug.Assert(annotated.HasValue);
            if (!annotated.Value)
                throw new ParsingException(context, "quantifiers are only allowed in annotation.");

            // 这里我们开一个新的作用域
            // 当然 alhpa-renaming 也是要做的
            symbolTables.Push(new Dictionary<string, LocalVariable>());
            Dictionary<string, QuantifiedVariable> vars = new Dictionary<string, QuantifiedVariable>();
            foreach (string name in context.IDENT().Select(node => node.GetText()))
            {
                if (vars.ContainsKey(name))
                    throw new ParsingException(context, $"duplicate quantified variable {name}");
                QuantifiedVariable variable = new QuantifiedVariable
                {
                    name = counter.GetVariable(name),
                    type = IntType.Get()
                };
                symbolTables.Peek().Add(name, variable);
                vars.Add(name, variable);
            }

            Expression expression = NotNullConfirm(context.expr());

            symbolTables.Pop();

            if (context.GetChild(0).GetText() == "forall")
                return new ForallQuantifiedExpression(vars, expression);
            else
                return new ExistsQuantifiedExpression(vars, expression);
        }

        public override Expression VisitAndExpr([NotNull] piParser.AndExprContext context)
        {
            Expression le = TypeConfirm(context.expr()[0], BoolType.Get());
            Expression re = TypeConfirm(context.expr()[1], BoolType.Get());
            Expression e = new AndExpression(le, re);
            return e;
        }

        public override Expression VisitOrExpr([NotNull] piParser.OrExprContext context)
        {
            Expression le = TypeConfirm(context.expr()[0], BoolType.Get());
            Expression re = TypeConfirm(context.expr()[1], BoolType.Get());
            Expression e = new OrExpression(le, re);
            return e;
        }

        public override Expression VisitArrowExpr([NotNull] piParser.ArrowExprContext context)
        {
            Debug.Assert(annotated.HasValue);
            if (!annotated.Value)
                throw new ParsingException(context, "'->' and '<->' are only allowed in annotation.");

            Expression le = TypeConfirm(context.expr()[0], BoolType.Get());
            Expression re = TypeConfirm(context.expr()[1], BoolType.Get());
            string op = context.GetChild(1).GetText();
            switch (op)
            {
                case "->":
                    return new ImplicationExpression(le, re);
                case "<->":
                    return new IffExpression(le, re);
                default:
                    throw new ArgumentException(
                        message: $"operator '{op}' is neither '->' nor '<->'. Probably a bug occurs.",
                        paramName: nameof(op));
            }
        }

        public override Expression VisitLengthExpr([NotNull] piParser.LengthExprContext context)
        {
            Expression arrayExpr = NotNullConfirm(context.expr());
            if (arrayExpr.type is ArrayType)
                return new LengthExpression(arrayExpr);
            else
                throw new ParsingException(context, "try calculating the length of a non-array expression.");
        }

        public override Expression VisitConstant([NotNull] piParser.ConstantContext context)
        {
            if (context.INT_CONSTANT() != null)
                return new IntConstantExpression(int.Parse(context.INT_CONSTANT().GetText()));
            else if (context.FLOAT_CONSTANT() != null)
                return new FloatConstantExpression(float.Parse(context.FLOAT_CONSTANT().GetText()));
            else if (context.GetText() == "true")
                return new BoolConstantExpression(true);
            else
            {
                Debug.Assert(context.GetText() == "false");
                return new BoolConstantExpression(false);
            }
        }
    }
}