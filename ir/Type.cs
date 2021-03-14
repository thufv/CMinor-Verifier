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
    class Type {
    }

    class VarType : Type, ReturnType{}

    class AtomicType : VarType {}

    public sealed class IntType : AtomicType {
        private static IntType singleton = new IntType();

        private IntType() {}

        public static IntType Get() {
            return singleton;
        }
    }

    public sealed class FloatType : AtomicType {
        private static FloatType singleton = new FloatType();

        private FloatType() {}

        public static FloatType Get() {
            return singleton;
        }
    }

    class BoolType : AtomicType {
        public bool annotated;

        private static BoolType nonAnnotatedSingleton = new BoolType();
        private static BoolType annotatedSingleton = new BoolType(true);

        private BoolType(bool annotated = false) {
            this.annotated = annotated;
        }

        public static BoolType Get(bool annotated = false) {
            return annotated ? annotatedSingleton : nonAnnotatedSingleton;
        }
    }

    class ArrayType : VarType {
        public AtomicType atomicType;
        public int size;

        private static Dictionary<Tuple<AtomicType, int>, ArrayType> singletons =
            new Dictionary<Tuple<AtomicType, int>, ArrayType>();

        private ArrayType(AtomicType atomicType, int size) {
            this.atomicType = atomicType;
            this.size = size;
        }

        public static ArrayType Get(AtomicType atomicType, int size) {
            var t = new Tuple<AtomicType, int>(atomicType, size);
            if (!singletons.ContainsKey(t)) {
                singletons.Add(t, new ArrayType(atomicType, size));
            }
            return singletons[t];
        }
    }

    class VoidType : ReturnType {
        private static VoidType singleton = new VoidType();
        
        private VoidType() {}

        public static VoidType Get() {
            return singleton;
        }
    }

    class StructType : VarType {
        public Struct structDefinition;

        private static Dictionary<Struct, StructType> singletons = new Dictionary<Struct, StructType>();

        private StructType(Struct structDefinition) {
            this.structDefinition = structDefinition;
        }

        public static StructType Get(Struct structDefinition) {
            if (!singletons.ContainsKey(structDefinition)) {
                singletons.Add(structDefinition, new StructType(structDefinition));
            }
            return singletons[structDefinition];
        }
    }

    // 这里是用了一个 interface 配合 implement 来实现了一个 "sum type"
    public interface ReturnType {}

    class FunType : Type {
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