using System.Collections.Generic;

namespace cminor
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
            return z3Solver.CheckValid(expression);
        }

        public void definePredicate(Predicate predicate)
        {
            z3Solver.definePredicate(predicate);
        }
    }
}