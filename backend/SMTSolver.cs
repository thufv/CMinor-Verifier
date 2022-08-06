/* Copyright 2022 Xingyu Xie

This file is part of CMinor.

CMinor is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

CMinor is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with CMinor. If not, see <https://www.gnu.org/licenses/>. */

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

        /// <summary> 在 SMT solver 中定义谓词 </summary>
        /// <param name="predicate"> 待定义的谓词 </param>
        /// <remarks> 目前我们只允许一个表达式作为谓词，而且谓词不允许递归调用。 </remarks>
        public void definePredicate(Predicate predicate)
        {
            z3Solver.definePredicate(predicate);
        }
    }
}