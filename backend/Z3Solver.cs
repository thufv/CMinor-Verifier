/* Copyright 2022 Xingyu Xie, Jiangyi Liu

This file is part of CMinor.

CMinor is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

CMinor is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with CMinor. If not, see <https://www.gnu.org/licenses/>. */

using System;
using System.Linq;
using System.Diagnostics;
using System.Collections.Generic;

using Microsoft.Z3;

namespace cminor
{
    /// <summary> 对 Z3 求解器的一层封装 </summary>
    class Z3Solver
    {
        Context ctx = new Context(new Dictionary<string, string>() {
            { "model", "true" }
        });

        public Z3Solver()
        {
            Microsoft.Z3.Global.SetParameter("parallel.enable", "false");
        }

        /// <summary> 对逻辑表达式的有效性的检查。 </summary>
        /// <param name="expression"> 待检查有效性的逻辑表达式 </param>
        /// <returns> 如果表达式有效，那么就返回 null；否则的话，返回一个反例模型。</returns>
        public CounterModel? CheckValid(Expression expression)
        {
            Solver solver = ctx.MkSolver();

            Expr expr = ExpressionToZ3Expr(expression).Simplify();
            Debug.Assert(expr is BoolExpr);

            // Z3 默认求解的是 satisfiable
            // 为了判断 valid，我们需要先取反
            solver.Assert(ctx.MkNot((BoolExpr)expr));
            Status status = solver.Check();
            if (status == Status.UNSATISFIABLE)
            {
                return null;
            }
            else
            {
                Dictionary<string, string> assignments = new Dictionary<string, string>();
                foreach ((FuncDecl decl, Expr valueExpr) in solver.Model.Consts)
                {
                    assignments.Add(decl.Name.ToString(), valueExpr.ToString());
                }
                return new CounterModel(assignments);
            }
        }

        /// <summary> 把我们的 IR 里的表达式转成 Z3 里的表达式 </summary>
        /// <remarks> 注意我们的 constant 其实需要对应到 z3 里的 numeral，我们的 variable 需要对应到 z3 里的 const。</remarks>
        Expr ExpressionToZ3Expr(Expression e)
        {
            switch (e)
            {
                case VariableExpression ve:
                    {
                        string name = ve.variable.name;
                        switch (ve.variable.type)
                        {
                            case IntType:
                                return ctx.MkIntConst(name);
                            case FloatType:
                                return ctx.MkRealConst(name);
                            case BoolType:
                                return ctx.MkBoolConst(name);
                            case ArrayType at:
                                switch (at.atomicType)
                                {
                                    case IntType:
                                        return ctx.MkArrayConst(name, ctx.IntSort, ctx.IntSort);
                                    case FloatType:
                                        return ctx.MkArrayConst(name, ctx.IntSort, ctx.RealSort);
                                    case BoolType:
                                        return ctx.MkArrayConst(name, ctx.IntSort, ctx.BoolSort);
                                    default:
                                        throw new ArgumentException("there's an atomic type that is neither 'int', 'float' or 'bool'. Probably a bug occurs.");
                                }
                        }
                        break;
                    }
                case IntConstantExpression ice:
                    return ctx.MkNumeral(ice.constant, ctx.IntSort);
                case FloatConstantExpression fce:
                    return ctx.MkReal(fce.constant.ToString());
                case BoolConstantExpression bce:
                    return ctx.MkBool(bce.constant);
                case PredicateCallExpression pce:
                    // 里面的 predicate 应该是已经被预先声明好了
                    Debug.Assert(predicates.ContainsKey(pce.predicate));

                    return predicates[pce.predicate].Item1.Substitute(
                        from: predicates[pce.predicate].Item2,
                        to: pce.argumentExpressions.Select(
                            expression => ExpressionToZ3Expr(expression)).ToArray());
                case ArrayAccessExpression aae:
                    {
                        Expr array = ExpressionToZ3Expr(aae.array);
                        Expr subscript = ExpressionToZ3Expr(aae.subscript);

                        Debug.Assert(array is ArrayExpr);

                        return ctx.MkSelect((ArrayExpr)array, subscript);
                    }
                case ArrayUpdateExpression aue:
                    {
                        Expr array = ExpressionToZ3Expr(aue.array);
                        Expr subscript = ExpressionToZ3Expr(aue.subscript);
                        Expr rhs = ExpressionToZ3Expr(aue.rhs);

                        Debug.Assert(array is ArrayExpr);

                        return ctx.MkStore((ArrayExpr)array, subscript, rhs);
                    }
                case ITEExpression itee:
                    {
                        Expr cond = ExpressionToZ3Expr(itee.cond);
                        Expr thenExpr = ExpressionToZ3Expr(itee.thenExpr);
                        Expr elseExpr = ExpressionToZ3Expr(itee.elseExpr);

                        Debug.Assert(cond is BoolExpr);

                        return ctx.MkITE((BoolExpr)cond, thenExpr, elseExpr);
                    }
                case NotExpression ne:
                    {
                        Expr expr = ExpressionToZ3Expr(ne.expression);
                        Debug.Assert(expr is BoolExpr);
                        return ctx.MkNot((BoolExpr)expr);
                    }
                case NegExpression ne:
                    {
                        Expr expr = ExpressionToZ3Expr(ne.expression);
                        Debug.Assert(expr is ArithExpr);
                        return ctx.MkUnaryMinus((ArithExpr)expr);
                    }
                case BinaryExpression be:
                    {
                        Expr le = ExpressionToZ3Expr(be.le);
                        Expr re = ExpressionToZ3Expr(be.re);

                        switch (be)
                        {
                            case MultiExpression:
                                Debug.Assert(le is ArithExpr);
                                Debug.Assert(re is ArithExpr);

                                return ctx.MkMul(new ArithExpr[] {
                                    (ArithExpr)le,
                                    (ArithExpr)re
                                });
                            case DivExpression:
                                if (le is IntExpr li)
                                {
                                    if (re is IntExpr ri)
                                    {
                                        //             5 / 3   5 / -3   -5 / -3   -5 / 3
                                        // C        :    1       -1        1        -1
                                        // Euclidean:    1       -1        2        -2

                                        //  (le div re) + (le >= 0 || le % re == 0 ? 0: (re > 0 ? - 1: 1))
                                        return ctx.MkAdd(
                                            ctx.MkDiv(li, ri),
                                            (IntExpr)ctx.MkITE(
                                                ctx.MkOr(
                                                    ctx.MkGe(li, ctx.MkInt(0)),
                                                    ctx.MkEq(ctx.MkMod(li, ri), ctx.MkInt(0))
                                                ),
                                                ctx.MkInt(0),
                                                ctx.MkITE(
                                                    ctx.MkGt(ri, ctx.MkInt(0)),
                                                    ctx.MkInt(-1),
                                                    ctx.MkInt(1)
                                                )
                                            )
                                        );
                                    }
                                }
                                else
                                {
                                    if (le is RealExpr lr)
                                        if (re is RealExpr rr)
                                            return ctx.MkDiv(lr, rr);
                                }
                                throw new ArgumentException("The type between '/' must be both 'int' or both 'real'.");
                            case ModExpression:
                                Debug.Assert(le is IntExpr);
                                Debug.Assert(re is IntExpr);

                                //             5 % 3    5 % -3   -5 % -3   -5 % 3
                                // C        :    2        2        -2        -2
                                // Euclidean:    2        2         1         1

                                // le > 0 ? (re > 0 ? (le mod re): (le mod -re) : (re > 0 ? -(le mod re): -(le mod -re))
                                return ctx.MkITE(
                                    ctx.MkGt((IntExpr)le, ctx.MkInt(0)),
                                    (IntExpr)ctx.MkITE(
                                        ctx.MkGt((IntExpr)re, ctx.MkInt(0)),
                                        ctx.MkMod((IntExpr)le, (IntExpr)re),
                                        ctx.MkMod((IntExpr)le, (IntExpr)ctx.MkUnaryMinus((IntExpr)re))
                                    ),
                                    (IntExpr)ctx.MkITE(
                                        ctx.MkGt((IntExpr)re, ctx.MkInt(0)),
                                        ctx.MkUnaryMinus(ctx.MkMod((IntExpr)le, (IntExpr)re)),
                                        ctx.MkUnaryMinus(ctx.MkMod((IntExpr)le, (IntExpr)ctx.MkUnaryMinus((IntExpr)re)))
                                    )
                                );
                            case AddExpression:
                                Debug.Assert(le is ArithExpr);
                                Debug.Assert(re is ArithExpr);

                                return ctx.MkAdd(new ArithExpr[] {
                                    (ArithExpr)le,
                                    (ArithExpr)re
                                });
                            case SubExpression:
                                Debug.Assert(le is ArithExpr);
                                Debug.Assert(re is ArithExpr);

                                return ctx.MkSub(new ArithExpr[] {
                                    (ArithExpr)le,
                                    (ArithExpr)re
                                });
                            case LTExpression:
                                Debug.Assert(le is ArithExpr);
                                Debug.Assert(re is ArithExpr);

                                return ctx.MkLt((ArithExpr)le, (ArithExpr)re);
                            case LEExpression:
                                Debug.Assert(le is ArithExpr);
                                Debug.Assert(re is ArithExpr);

                                return ctx.MkLe((ArithExpr)le, (ArithExpr)re);
                            case GTExpression:
                                Debug.Assert(le is ArithExpr);
                                Debug.Assert(re is ArithExpr);

                                return ctx.MkGt((ArithExpr)le, (ArithExpr)re);
                            case GEExpression:
                                Debug.Assert(le is ArithExpr);
                                Debug.Assert(re is ArithExpr);

                                return ctx.MkGe((ArithExpr)le, (ArithExpr)re);
                            case EQExpression:
                                Debug.Assert(le is ArithExpr);
                                Debug.Assert(re is ArithExpr);

                                return ctx.MkEq((ArithExpr)le, (ArithExpr)re);
                            case NEExpression:
                                Debug.Assert(le is ArithExpr);
                                Debug.Assert(re is ArithExpr);

                                return ctx.MkNot(ctx.MkEq((ArithExpr)le, (ArithExpr)re));
                            case AndExpression:
                                Debug.Assert(le is BoolExpr);
                                Debug.Assert(re is BoolExpr);

                                return ctx.MkAnd(new BoolExpr[] {
                                    (BoolExpr)le,
                                    (BoolExpr)re
                                });
                            case OrExpression:
                                Debug.Assert(le is BoolExpr);
                                Debug.Assert(re is BoolExpr);

                                return ctx.MkOr(new BoolExpr[] {
                                    (BoolExpr)le,
                                    (BoolExpr)re
                                });
                            case ImplicationExpression:
                                Debug.Assert(le is BoolExpr);
                                Debug.Assert(re is BoolExpr);

                                return ctx.MkImplies((BoolExpr)le, (BoolExpr)re);
                            case IffExpression:
                                Debug.Assert(le is BoolExpr);
                                Debug.Assert(re is BoolExpr);

                                return ctx.MkIff((BoolExpr)le, (BoolExpr)re);
                            case XorExpression:
                                Debug.Assert(le is BoolExpr);
                                Debug.Assert(re is BoolExpr);

                                return ctx.MkXor((BoolExpr)le, (BoolExpr)re);
                        }

                        Debug.Assert(false);
                        break;
                    }
                case QuantifiedExpression qe:
                    Expr[] boundConstants = qe.vars.Values.Select<QuantifiedVariable, Expr>(
                        variable =>
                        {
                            switch (variable.type)
                            {
                                case IntType:
                                    return ctx.MkIntConst(variable.name);
                                case FloatType:
                                    return ctx.MkRealConst(variable.name);
                                case BoolType:
                                    return ctx.MkBoolConst(variable.name);
                                default:
                                    throw new ArgumentException($"there is a type of quantified variable that is not atomic type: {variable.type}");
                            }
                        }
                    ).ToArray();
                    Expr body = ExpressionToZ3Expr(qe.expression);
                    if (qe is ForallQuantifiedExpression)
                    {
                        return ctx.MkForall(boundConstants, body);
                    }
                    else
                    {
                        Debug.Assert(qe is ExistsQuantifiedExpression);
                        return ctx.MkExists(boundConstants, body);
                    }
                case LengthExpression le:
                    {
                        if (le.expression is VariableExpression ve)
                        {
                            Debug.Assert(ve.variable is ArrayVariable);
                            ArrayVariable av = (ArrayVariable)(ve.variable);
                            return ctx.MkIntConst(av.length.name);
                        }
                        else
                        {
                            Debug.Assert(le.expression is ArrayUpdateExpression);
                            LocalVariable variable = ((ArrayUpdateExpression)(le.expression)).length.variable;
                            Debug.Assert(variable.type is IntType);
                            return ctx.MkIntConst(variable.name);
                        }
                    }
            }
            Debug.Assert(false);
            return null;
        }

        Dictionary<Predicate, Tuple<Expr, Expr[]>> predicates = new Dictionary<Predicate, Tuple<Expr, Expr[]>>();

        public void definePredicate(Predicate predicate)
        {
            Expr expr = ExpressionToZ3Expr(predicate.expression);
            Expr[] paraExprs = predicate.parameters.Select<LocalVariable, Expr>(
                (parameter) =>
                {
                    switch (parameter.type)
                    {
                        case IntType:
                            return ctx.MkIntConst(parameter.name);
                        case FloatType:
                            return ctx.MkRealConst(parameter.name);
                        case BoolType:
                            return ctx.MkBoolConst(parameter.name);
                        case ArrayType at:
                            switch (at.atomicType)
                            {
                                case IntType:
                                    return ctx.MkArrayConst(parameter.name, ctx.IntSort, ctx.IntSort);
                                case FloatType:
                                    return ctx.MkArrayConst(parameter.name, ctx.IntSort, ctx.RealSort);
                                case BoolType:
                                    return ctx.MkArrayConst(parameter.name, ctx.IntSort, ctx.BoolSort);
                                default:
                                    throw new ArgumentException("there's an atomic type that is neither 'int', 'float' or 'bool'. Probably a bug occurs.");
                            }
                        default:
                            throw new ArgumentException($"the type of parameter of {predicate.name} is neither int, float nor bool.");
                    }
                }
            ).ToArray();

            predicates.Add(predicate, Tuple.Create(expr, paraExprs));
        }
    }
}