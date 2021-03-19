using System;
using System.Collections.Generic;

/**
 * To be honest,
 * I really don't know how to design a type system...
 * There seems to be a lot other things that are needed to consider.
 */

namespace piVC_thu
{
    // 这里我们尝试拿 singleton design pattern 来简化繁琐的比较
    abstract class Type { }

    abstract class VarType : Type, ReturnType { }

    abstract class AtomicType : VarType { }

    sealed class IntType : AtomicType
    {
        private static IntType singleton = new IntType();

        private IntType() { }

        public static IntType Get()
        {
            return singleton;
        }

        public override string ToString()
        {
            return "int";
        }
    }

    sealed class FloatType : AtomicType
    {
        private static FloatType singleton = new FloatType();

        private FloatType() { }

        public static FloatType Get()
        {
            return singleton;
        }

        public override string ToString()
        {
            return "float";
        }
    }

    sealed class BoolType : AtomicType
    {
        private static BoolType singleton = new BoolType();

        private BoolType() { }

        public static BoolType Get()
        {
            return singleton;
        }

        public override string ToString()
        {
            return "bool";
        }
    }

    sealed class ArrayType : VarType
    {
        public AtomicType atomicType;

        private static ArrayType intArraySingleton = new ArrayType(IntType.Get());
        private static ArrayType boolArraySingleton = new ArrayType(BoolType.Get());
        private static ArrayType floatArraySingleton = new ArrayType(FloatType.Get());

        private ArrayType(AtomicType atomicType)
        {
            this.atomicType = atomicType;
        }

        public static ArrayType Get(AtomicType atomicType)
        {
            switch (atomicType)
            {
                case IntType:
                    return intArraySingleton;
                case BoolType:
                    return boolArraySingleton;
                case FloatType:
                    return floatArraySingleton;
                default:
                    throw new ArgumentException(
                        message: "an atomic type that is not int, float, nor bool is found when constructing an array type. Probably a bug occurs.",
                        paramName: nameof(atomicType));
            }
        }

        public override string ToString()
        {
            return $"{atomicType}[]";
        }
    }

    sealed class VoidType : ReturnType
    {
        private static VoidType singleton = new VoidType();

        private VoidType() { }

        public static VoidType Get()
        {
            return singleton;
        }

        public override string ToString()
        {
            return "void";
        }
    }

    sealed class StructType : VarType
    {
        public Struct structDefinition;

        private static Dictionary<Struct, StructType> singletons = new Dictionary<Struct, StructType>();

        private StructType(Struct structDefinition)
        {
            this.structDefinition = structDefinition;
        }

        public static StructType Get(Struct structDefinition)
        {
            if (!singletons.ContainsKey(structDefinition))
            {
                singletons.Add(structDefinition, new StructType(structDefinition));
            }
            return singletons[structDefinition];
        }

        public override string ToString()
        {
            return $"struct {structDefinition.name}";
        }
    }

    // 这里是用了一个 interface 配合 implement 来实现了一个 "sum type"
    interface ReturnType { }

    sealed class FunType : Type
    {
        public ReturnType returnType;
        public VarType[] paraTypes;

        private static LinkedList<FunType> singletons = new LinkedList<FunType>();

        private FunType(ReturnType returnType, VarType[] paraTypes)
        {
            this.returnType = returnType;
            this.paraTypes = paraTypes;
        }

        public static FunType Get(ReturnType returnType, VarType[] paraTypes)
        {
            Func<FunType, bool> Equals = (FunType funType) =>
            {
                if (returnType != funType.returnType) return false;
                if (paraTypes.Length != funType.paraTypes.Length) return false;
                for (int i = 0; i < funType.paraTypes.Length; ++i)
                    if (paraTypes[i] != funType.paraTypes[i])
                        return false;
                return true;
            };
            foreach (FunType funType in singletons)
                if (Equals(funType))
                    return funType;

            // if there is no equal FunType to be find
            FunType newFunType = new FunType(returnType, paraTypes);
            singletons.AddLast(newFunType);
            return newFunType;
        }

        public override string ToString()
        {
            string s = returnType.ToString()!;
            s += "(";
            for (int i = 0; i < paraTypes.Length; ++i)
            {
                if (i > 0) s += ",";
                s += paraTypes[i].ToString();
            }
            s += ")";
            return s;
        }
    }
}