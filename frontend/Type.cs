using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;

/**
 * To be honest,
 * I really don't know how to design a type system...
 * There seems to be a lot other things that are needed to consider.
 */

namespace piVC_thu {
    // 这里我们尝试拿 singleton design pattern 来简化繁琐的比较
    public class Type {
    }

    public class VarType : Type, ReturnType{}

    public sealed class IntType : VarType {
        private static IntType singleton = new IntType();

        private IntType() {}

        public static IntType Get() {
            return singleton;
        }
    }

    public sealed class FloatType : VarType {
        private static FloatType singleton = new FloatType();

        private FloatType() {}

        public static FloatType Get() {
            return singleton;
        }
    }

    public class BoolType : VarType {
        private static BoolType singleton = new BoolType();

        private BoolType() {}

        public static BoolType Get() {
            return singleton;
        }
    }

    public class ArrayType : VarType {
        public VarType baseType;
        public int size;

        private static Dictionary<Tuple<VarType, int>, ArrayType> singletons =
            new Dictionary<Tuple<VarType, int>, ArrayType>();

        private ArrayType(VarType baseType, int size) {
            this.baseType = baseType;
            this.size = size;
        }

        public static ArrayType Get(VarType baseType, int size) {
            var t = new Tuple<VarType, int>(baseType, size);
            if (!singletons.ContainsKey(t)) {
                singletons.Add(t, new ArrayType(baseType, size));
            }
            return singletons[t];
        }
    }

    public class VoidType : ReturnType {
        private static VoidType singleton = new VoidType();
        
        private VoidType() {}

        public static VoidType Get() {
            return singleton;
        }
    }

    // 这里是用了一个 interface 配合 implement 来实现了一个 "sum type"
    public interface ReturnType {}

    public class FunType : Type {
        public ReturnType returnType;
        public VarType[] argTypes;

        private static LinkedList<FunType> singletons = new LinkedList<FunType>();

        private FunType(ReturnType returnType, VarType[] argTypes) {
            this.returnType = returnType;
            this.argTypes = argTypes;
        }

        public static FunType Get(ReturnType returnType, VarType[] argTypes) {
            Func<FunType, bool> Equals = (FunType funType) => {
                if (returnType != funType.returnType) return false;
                if (argTypes.Length != funType.argTypes.Length) return false;
                for (int i = 0; i < funType.argTypes.Length; ++i)
                    if (argTypes[i] != funType.argTypes[i])
                        return false;
                return true;
            };
            foreach (FunType funType in singletons)
                if (Equals(funType))
                    return funType;
            
            // if there is no equal FunType to be find
            FunType newFunType = new FunType(returnType, argTypes);
            singletons.AddLast(newFunType);
            return newFunType;
        }
    }
}