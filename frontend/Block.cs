using System.Collections.Generic;

namespace piVC_thu {
    // 这里的顶层设计主要是参考了 Silver

    public class Block {
        public LinkedList<Instruction> instructions;
    }

    public class BasicBlock : Block {
        // TODO
    }

    public class PreconditionBlock : Block {
        // TODO: nullable ranking function
    }

    public class PostconditionBlock : Block {
        // TODO
    }

    public class LoopheadBlock : Block {
        // TODO
    }
}
