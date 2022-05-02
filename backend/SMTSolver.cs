using System.Collections.Generic;

namespace cminor
{
    /// <summary> 对真正的 SMT Solver 的一层封装 </summary>
    /// <remarks> 
    /// 不过我们目前还只支持 z3。。。
    /// 之后会考虑支持 cvc5，以及把这一层封装也换成更成熟的封装。
    /// </remarks>
    class SMTSolver
    {
        Dictionary<string, Expression> predicates = new Dictionary<string, Expression>();

        Z3Solver z3Solver = new Z3Solver();


        /// <summary> 检查逻辑表达式的有效性 </summary>
        /// <param name="expression"> 待检查的逻辑表达式 </param>
        /// <returns> 为 null 的话就表示 valid，否则返回一个反例模型。 </returns>
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