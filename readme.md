## 计划

### 重要

- [ ] 修改文法
- [ ] 支持 float
- [ ] 测例
- [ ] 重写 readme 和 taskdoc
- [ ] API doc

### 不重要

- [ ] logic function
- [ ] visualizer 

## 简介

这是清华版的 piVC (pi Verifying Compiler)，受 Stanford 的[同名项目](https://cs.stanford.edu/people/jasonaue/pivc/)启发所作。pi 是一个面向教学的验证中间语言，类似于带有验证标注的 C 语言的子集；piVC 即是 pi 这个语言的验证编译器。

本次大作业你需要实现 piVC 中的核心验证算法部分，具体的说明请见 [任务说明文档](task-doc.md)。

本项目使用 [git submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) 来集成公开测例仓库，在 clone 时你需要使用 `--recursive`。

## 安装

本项目依赖于 .NET 6，你可以从[这里](https://dotnet.microsoft.com/download)下载其最新的 SDK。

你可以使用任意你喜欢的 IDE，我们推荐：
- [Visual Studio 2019 (>= 16.8)](https://visualstudio.microsoft.com/zh-hans/)
- [Visual Studio Code](https://code.visualstudio.com/)：配合 [C# 插件](https://marketplace.visualstudio.com/items?itemName=ms-dotnettools.csharp)
- [Rider](https://www.jetbrains.com/rider/)

> 注意：建议不要通过 `homebrew` 或 `apt` 直接安装，因为其软件源中的 dotnet 的版本很有可能是过时的。建议从[这里](https://dotnet.microsoft.com/download)下载最新版。

> 注意：如果你遇到了错误 `Unhandled exception. System.DllNotFoundException: Unable to load shared library 'libz3' or one of its dependencies.`，那么你需要从[这里](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.10)单独安装 Z3 4.8.10。

## 使用

本项目基本的使用方法是：

```bash
piVC-thu --source <path>
```

你可以在本项目的根目录下运行以下指令：

```bash
dotnet run -- --source <path>
```

你可以使用 `--printCFG` 来打印出得到的 CFG，各选项的具体含义为：

```bash
--source      Required. The source file of pi language (recommended with filename extension '.pi').

--printCFG    The file (or 'console') to which the control flow graph is printed.

--help        Display this help screen.

--version     Display version information.
```

## 结构

该编译器的设计可以分为三个部分：

 * 前端（frontend）：使用由 [ANTLR](https://www.antlr.org/) 自动生成的 parser 将源文件解析为 CST (concrete syntax tree，具体语法树)，再遍历 CST，生成 CFG（control flow graph，控制流图）；
 * 中间表示（ir）：面向验证来设计的控制流图；
 * 后端（backend）：使用 deductive verification 的方法从 CFG 中生成验证条件（verification condition），再将其喂给 SMT Solver 来求解。
   * 这部分是你需要来实现的。

你唯一被允许修改、并且你也必须要修改的文件是 `Verifier.cs`，你需要在其中实现 deductive verification 的算法主体。
