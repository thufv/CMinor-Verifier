using System.Diagnostics.Contracts;
using System.Collections.Generic;

namespace cminor
{
    class BasicPath
    {
        public List<Expression> headConditions = new List<Expression>();
        public List<Expression> headRankingFunctions = new List<Expression>();

        // only assumement, assignment are allowed
        public List<Statement> statements = new List<Statement>();

        public List<Expression> tailConditions = new List<Expression>();

        public List<Expression> tailRankingFunctions = new List<Expression>();

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            foreach (Expression headCondition in headConditions)
                Contract.Invariant(headCondition.type is BoolType);
        }
    }
}