using System.Linq;
using System.Collections.Generic;

namespace piVC_thu
{
    // 这是对真正的 SMT Solver 的一层封装
    class SMTSolver
    {
        Dictionary<string, Expression> predicates = new Dictionary<string, Expression>();

        Z3Solver z3Solver = new Z3Solver();
        

        // 为 null 的话就表示 valid，
        // 否则返回Counter一个 counter model
        public CounterModel? CheckValid(Expression expression)
        {
            // introduce the knowledge that the length of array must be non-negative
            Expression lengthKnowledge = expression.GetFreeVariables().Aggregate<LocalVariable, Expression>(
                new BoolConstantExpression(true),
                (expression, variable) =>
                {
                    if (variable is ArrayVariable av)
                    {
                        return new AndExpression(
                            le: expression,
                            re: new GEExpression(
                                le: new VariableExpression(av.length),
                                re: new IntConstantExpression(0)
                            )
                        );
                    }
                    else
                    {
                        return expression;
                    }
                });
            
            expression = new ImplicationExpression(
                le: lengthKnowledge,
                re: expression
            );

            return z3Solver.CheckValid(expression);
        }

        public void definePredicate(Predicate predicate)
        {
            z3Solver.definePredicate(predicate);
        }

        // TODO: 这个有可能需要用其他的 SMT Solver 或者是低版本的 Z3，之后再说吧
        // public List<Expression> interpolate(List<Expression> expressions) {}
    }
}