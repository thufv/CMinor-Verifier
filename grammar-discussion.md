注释这个事情还是挺麻烦的，需要解决一下qwq

## 新增支持的特性

- for 循环的条件表达式可以为空
- bound variable 可以指定类型，包括 integer / boolean / real 三种。

\old(e) can be used only in ensures, assigns , allocates and frees clauses, since the other
clauses already refer to only one state, the pre-state. 

## 不支持的特性

- 全局变量
- 变长数组
- 高维数组
- 对数组的初始化
- 复杂类型的嵌套
    - 结构体套数组
    - 数组套结构体
    - 结构体套结构体
    - 结构体套数组
- 数组传参时不支持指定大小
- 连等 `a = b = c`
- 动态内存分配
- `div`
- logic function & predication
- 函数声明和函数定义的分离
- 传参时指定数组长度
- 位运算
