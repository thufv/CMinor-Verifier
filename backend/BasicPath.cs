/* Copyright 2022 Xingyu Xie

This file is part of CMinor.

CMinor is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

CMinor is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with CMinor. If not, see <https://www.gnu.org/licenses/>. */

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