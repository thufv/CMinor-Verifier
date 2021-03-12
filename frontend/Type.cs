/**
 * To be honest,
 * I really don't know how to design a type system...
 * There seems to be a lot other things that are needed to consider.
 */

public class Type {
}

public class VarType : Type {
}

public class IntType : VarType {
}

public class FloatType : VarType {
}

public class BoolType : VarType {
}

public class ArrayType : VarType {
    public Type baseType;
    public int size;

    public ArrayType(Type baseType, int size) {
        this.baseType = baseType;
        this.size = size;
    }
}

public class NoType : Type {
}

public class VoidType : Type {
}

public class FunType : Type {
    public Type returnType; // I want VarType or VoidType, is it possible?
    public VarType[] argTypes;

    public FunType(Type returnType, VarType[] argTypes) {
        this.returnType = returnType;
        this.argTypes = argTypes;
    }
}