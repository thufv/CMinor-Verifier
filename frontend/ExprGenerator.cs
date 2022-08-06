/* Copyright 2022 Xingyu Xie

This file is part of CMinor.

CMinor is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

CMinor is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with CMinor. If not, see <https://www.gnu.org/licenses/>. */

using System;
using System.Diagnostics;
using System.Collections.Generic;

using Antlr4.Runtime.Misc;

namespace cminor
{
    partial class CFGGenerator : CMinorParserBaseVisitor<Expression?>
    {
        public override Expression VisitIdentExpr([NotNull] CMinorParser.IdentExprContext context)
        {
            LocalVariable variable = FindVariable(context, context.IDENT().GetText());
            return new VariableExpression(variable);
        }

        public override Expression VisitConstExpr([NotNull] CMinorParser.ConstExprContext context)
        {
            return NotNullConfirm(context.constant());
        }

        public override Expression? VisitCallExpr([NotNull] CMinorParser.CallExprContext context)
        {
            string calledName = context.IDENT().GetText();
            if (LocalVariableExists(calledName))
                throw new ParsingException(context, "call a variable that is neither function nor predicate.");

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
                Expression argumentExpression = TypeConfirm(context.expr()[i], true, function.type.paraTypes[i]);
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

            throw new ParsingException(context, "an undefined symbol is called.");
        }

        public override Expression? VisitParExpr([NotNull] CMinorParser.ParExprContext context)
        {
            return Visit(context.expr());
        }

        public override Expression VisitArrAccessExpr([NotNull] CMinorParser.ArrAccessExprContext context)
        {
            Expression array = NotNullConfirm(context.expr()[0]);

            Debug.Assert(currentBlock != null);

            VariableExpression subscript = CompressedExpression(TypeConfirm(context.expr()[1], true, IntType.Get()), counter.GetSub);

            // runtime assertion: subscript >= 0
            currentBlock.AddStatement(new AssertStatement()
            {
                pred = new LEExpression(new IntConstantExpression(0), subscript)
            });

            // runtime assertion: subscript < length
            Debug.Assert(currentBlock != null);
            currentBlock.AddStatement(new AssertStatement()
            {
                pred = new LTExpression(subscript, new LengthExpression(array))
            });

            return new ArrayAccessExpression(array, subscript);

            throw new ParsingException(context, $"request for an element in a non-array expression.");
        }

        public override Expression VisitMemExpr([NotNull] CMinorParser.MemExprContext context)
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

        public override Expression VisitUnaryExpr([NotNull] CMinorParser.UnaryExprContext context)
        {
            string op = context.GetChild(0).GetText();
            switch (op)
            {
                case "!":
                    {
                        Expression expression = TypeConfirm(context.expr(), true, BoolType.Get());
                        return new NotExpression(expression);
                    }
                case "-":
                    {
                        Expression expression = TypeConfirm(context.expr(), true, IntType.Get(), FloatType.Get());
                        return new NegExpression(expression);
                    }
                default:
                    throw new ArgumentException(
                        message: $"operator '{op}' is neither '!' nor '-'. Probably a bug occurs.",
                        paramName: nameof(op));
            }
        }

        public override Expression VisitMulExpr([NotNull] CMinorParser.MulExprContext context)
        {
            string op = context.GetChild(1).GetText();

            switch (op)
            {
                case "*":
                    {
                        Expression le = TypeConfirm(context.expr()[0], true, IntType.Get(), FloatType.Get());
                        Expression re = TypeConfirm(context.expr()[1], true, IntType.Get(), FloatType.Get());
                        if (!(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType))
                            throw new ParsingException(context, "the type of expression between '*' must be both 'int' or 'float'.");
                        return new MultiExpression(le, re);
                    }
                case "/":
                    {
                        Expression le = TypeConfirm(context.expr()[0], true, IntType.Get(), FloatType.Get());
                        Expression re = TypeConfirm(context.expr()[1], true, IntType.Get(), FloatType.Get());
                        if (!(le.type is FloatType && re.type is FloatType || le.type is IntType && re.type is IntType))
                            throw new ParsingException(context, "the type of expression between '/' must be both 'float'.");

                        Debug.Assert(currentBlock != null);
                        re = CompressedExpression(re, counter.GetDivisor);
                        currentBlock.AddStatement(new AssertStatement()
                        {
                            pred = new NEExpression(re,
                                le.type is IntType ? new IntConstantExpression(0) : new FloatConstantExpression(0))
                        });
                        return new DivExpression(le, re);
                    }
                case "%":
                    {
                        Expression le = TypeConfirm(context.expr()[0], true, IntType.Get());
                        Expression re = TypeConfirm(context.expr()[1], true, IntType.Get());

                        Debug.Assert(currentBlock != null);
                        re = CompressedExpression(re, counter.GetDivisor);
                        currentBlock.AddStatement(new AssertStatement()
                        {
                            pred = new NEExpression(re, new IntConstantExpression(0))
                        });
                        return new ModExpression(le, re);
                    }
                default:
                    throw new ArgumentException(
                        message: $"operator '{op}' is neither '*', '/', 'div' nor '%'. Probably a bug occurs.",
                        paramName: nameof(op));
            }
        }

        public override Expression VisitAddExpr([NotNull] CMinorParser.AddExprContext context)
        {
            Expression le = TypeConfirm(context.expr()[0], true, IntType.Get(), FloatType.Get());
            Expression re = TypeConfirm(context.expr()[1], true, IntType.Get(), FloatType.Get());
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

        public override Expression VisitOrdExpr([NotNull] CMinorParser.OrdExprContext context)
        {
            Expression le = TypeConfirm(context.expr()[0], true, IntType.Get(), FloatType.Get());
            Expression re = TypeConfirm(context.expr()[1], true, IntType.Get(), FloatType.Get());

            if (!(le.type is IntType && re.type is IntType || le.type is FloatType && re.type is FloatType))
                throw new ParsingException(context, $"the type of expression between inequality must be both int or float, while now they are '{le.type}' and '{re.type}'.");

            string op = context.GetChild(1).GetText();
            Expression e = BinaryExpression.FromOp(op, le, re);
            return e;
        }

        public override Expression VisitEquExpr([NotNull] CMinorParser.EquExprContext context)
        {
            Expression le = NotNullConfirm(context.expr()[0]);
            Expression re = NotNullConfirm(context.expr()[1]);

            if (le.type is BoolType && re.type is IntType)
                le = new ITEExpression(le, new IntConstantExpression(1), new IntConstantExpression(0));
            else if (le.type is IntType && re.type is BoolType)
                re = new ITEExpression(re, new IntConstantExpression(1), new IntConstantExpression(0));

            if (!(le.type is AtomicType && re.type is AtomicType && le.type == re.type))
                throw new ParsingException(context, $"the type of expression between '=' or '!=' must be of same atomic type, while now they are '{le.type}' and '{re.type}'.");

            string op = context.GetChild(1).GetText();
            Expression e = BinaryExpression.FromOp(op, le, re);
            return e;
        }

        public override Expression VisitAndExpr([NotNull] CMinorParser.AndExprContext context)
        {
            Expression le = TypeConfirm(context.expr()[0], true, BoolType.Get());
            Expression re = TypeConfirm(context.expr()[1], true, BoolType.Get());
            Expression e = new AndExpression(le, re);
            return e;
        }

        public override Expression VisitOrExpr([NotNull] CMinorParser.OrExprContext context)
        {
            Expression le = TypeConfirm(context.expr()[0], true, BoolType.Get());
            Expression re = TypeConfirm(context.expr()[1], true, BoolType.Get());
            Expression e = new OrExpression(le, re);
            return e;
        }

        public override Expression VisitConstant([NotNull] CMinorParser.ConstantContext context)
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