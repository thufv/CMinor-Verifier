/* Copyright 2022 Xingyu Xie

This file is part of CMinor.

CMinor is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

CMinor is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with CMinor. If not, see <https://www.gnu.org/licenses/>. */

/*
    CMinor 的类型系统最核心的设计如下：

    Type：最抽象的类型
        VarType：变量类型
            AtomicType：原子类型
                IntType：整数类型
                FloatType：浮点类型
                BoolType：布尔类型（仅用于标注中）
            ArrayType：数组类型，是一个复合类型，会带一个原子类型
        FunType：函数类型，可以携带若干参数类型，并且返回若干参数类型（之所以允许返回多个，是因为我们会将结构体“拍扁”成“tuple”）
        PredType：谓词类型，可以携带若干参数类型
    
    注意：在 CMinor 中不允许（隐式和显式的）类型转换
*/

using System;
using System.Collections.Generic;

namespace cminor
{
    abstract class Type { }

    abstract class VarType : Type { }

    /// <summary> 原子类型，包括整数、浮点数和布尔 </summary>
    /// <remarks> 这里我们尝试拿 singleton design pattern 来简化繁琐的比较。 </remarks>
    abstract class AtomicType : VarType
    {
        public static AtomicType FromString(string s)
        {
            switch (s)
            {
                case "int":
                case "integer":
                    return IntType.Get();
                case "float":
                case "real":
                    return FloatType.Get();
                case "bool":
                case "boolean":
                    return BoolType.Get();
                default:
                    throw new ArgumentException($"Failed to parse {s} as an atomic type, which is neither int/integer, float/real nor bool/boolean.");
            }
        }

        public static HashSet<String> availableNames = new HashSet<String>()
        {
            "int", "integer", "float", "real", "bool", "boolean"
        };
    }

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

    /// <summary> 谓词类型（可以近似理解为一个 inline logic function） </summary>
    /// <remarks>
    /// 尽管 <c>PredType</c> 和 <c>FunType</c> 似乎有一点类似，但我们还是应该将其分开处理。
    /// 毕竟在我们的设计里，谓词只能在 annotation 里调用，它不能被视为一个 function，不是嘛？
    /// </remarks>
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