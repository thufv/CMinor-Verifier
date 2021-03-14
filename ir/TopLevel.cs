using System.Collections.Generic;

namespace piVC_thu
{
    // 这里的顶层设计主要是参考了 TrivialCompiler

    class Main
    {
        LinkedList<Function> functions = new LinkedList<Function>();
        LinkedList<Predicate> predicates = new LinkedList<Predicate>();
        LinkedList<Struct> structs = new LinkedList<Struct>();
    }


    class Function
    {
        FunType type;
        string name;

        BasicBlock statementBlock;
        PreconditionBlock preconditionBlock;
        PostconditionBlock postconditionBlock;
        LoopheadBlock loopheadBlock;

        LinkedList<Block> blocks;

        // for verification
        int rankingFunctionSize;
    }

    class Predicate
    {
        string name;
        Expression expression;
    }

    class Struct
    {
        string name;
        LinkedList<MemberVariable> members;
        Dictionary<string, MemberVariable> symbolTable;
    }
}