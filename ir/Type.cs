using System;
using System.Collections.Generic;

/**
 * To be honest,
 * I really don't know how to design a type system...
 * There seems to be a lot other things that are needed to consider.
 */

namespace cminor
{
    // 这里我们尝试拿 singleton design pattern 来简化繁琐的比较
    abstract class Type { }

    abstract class VarType : Type { }

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

    class FunType : Type
    {
        public List<VarType> returnTypes;
        public List<VarType> paraTypes;

        private static LinkedList<FunType> singletons = new LinkedList<FunType>();

        private FunType(List<VarType> returnTypes, List<VarType> paraTypes)
        {
            this.returnTypes = returnTypes;
            this.paraTypes = paraTypes;
        }

        public static FunType Get(List<VarType> returnTypes, List<VarType> paraTypes)
        {
            Func<FunType, bool> Equals = (FunType funType) =>
            {
                if (returnTypes.Count != funType.returnTypes.Count)
                    return false;
                for (int i = 0; i < funType.returnTypes.Count; ++i)
                    if (returnTypes[i] != funType.returnTypes[i])
                        return false;

                if (paraTypes.Count != funType.paraTypes.Count)
                    return false;
                for (int i = 0; i < funType.paraTypes.Count; ++i)
                    if (paraTypes[i] != funType.paraTypes[i])
                        return false;

                return true;
            };
            foreach (FunType funType in singletons)
                if (Equals(funType))
                    return funType;

            // if there is no equal FunType to be find
            FunType newFunType = new FunType(returnTypes, paraTypes);
            singletons.AddLast(newFunType);
            return newFunType;
        }

        public override string ToString()
        {
            string s = "";
            for (int i = 0; i < returnTypes.Count; ++i)
            {
                if (i > 0) s += ",";
                s += paraTypes[i].ToString();
            }
            s += "(";
            for (int i = 0; i < paraTypes.Count; ++i)
            {
                if (i > 0) s += ",";
                s += paraTypes[i].ToString();
            }
            s += ")";
            return s;
        }
    }

    // 尽管 PredType 和 FunType 似乎有一点类似，
    // 但我们还是应该将其分开处理。
    // 毕竟在我们的设计里，谓词只能在 annotation 里调用，
    // 它不能被视为一个 function，不是嘛？
    sealed class PredType : Type
    {
        public List<VarType> paraTypes;

        private static LinkedList<PredType> singletons = new LinkedList<PredType>();

        private PredType(List<VarType> paraTypes)
        {
            this.paraTypes = paraTypes;
        }

        public static PredType Get(List<VarType> paraTypes)
        {
            Func<PredType, bool> Equals = (PredType predType) =>
            {
                if (paraTypes.Count != predType.paraTypes.Count)
                    return false;
                for (int i = 0; i < predType.paraTypes.Count; ++i)
                    if (paraTypes[i] != predType.paraTypes[i])
                        return false;

                return true;
            };
            foreach (PredType predType in singletons)
                if (Equals(predType))
                    return predType;

            // if there is no equal PredType to be find
            PredType newPredType = new PredType(paraTypes);
            singletons.AddLast(newPredType);
            return newPredType;
        }

        public override string ToString()
        {
            string s = "predicate(";
            for (int i = 0; i < paraTypes.Count; ++i)
            {
                if (i > 0) s += ",";
                s += paraTypes[i].ToString();
            }
            s += ")";
            return s;
        }
    }
}