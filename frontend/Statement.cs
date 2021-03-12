namespace piVC_thu {
    // TODO: CFG 里需要有 declare 嘛？我该怎么处理 declare？

    public abstract class Instruction {
    }

    public abstract class Assign : Instruction {
    }

    public class VarAssign : Assign {
    }

    public class SubAssign : Assign {
    }

    public class MemAssign : Assign {
    }

    public class Assert : Instruction {
    }

    public class Assume : Instruction {
    }
}