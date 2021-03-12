using System.Collections.Generic;

namespace piVC_thu {
    // 这里的顶层设计主要是参考了 TrivialCompiler

    public class Main {
        LinkedList<Function> functions = new LinkedList<Function>();
        LinkedList<GlobalVar> globalVars = new LinkedList<GlobalVar>();
        LinkedList<Predicate> predicates = new LinkedList<Predicate>();
        LinkedList<Class> classes = new LinkedList<Class>();
    }


    public class Function {
        FunType type;
        string name;

        BasicBlock statementBlock;
        PreconditionBlock preconditionBlock;
        PostconditionBlock postconditionBlock;
        LoopheadBlock loopheadBlock;

        LinkedList<Block> blocks;
    }

    // 是需要有 global variable 的，但我不确定是不是应该把它放到这里。。。
    public class GlobalVar {
        // TODO
        
    }

    public class Predicate {
        // TODO
    }

    public class Class {
        // TODO
    }
}