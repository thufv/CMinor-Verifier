using System.Diagnostics.Contracts;
using System.Collections.Generic;

namespace cminor
{
    class BasicPath
    {
        public List<Expression> headConditions = new List<Expression>();
        public Expression? headRankingFunction = default;

        // only assumement, assignment are allowed
        public List<Statement> statements = new List<Statement>();

        public List<Expression> tailConditions = new List<Expression>();

        // null 表示没有啦
        public Expression? tailRankingFunction = null;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            foreach (Expression headCondition in headConditions)
                Contract.Invariant(headCondition.type is BoolType);
        }
    }
}