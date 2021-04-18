这是清华版的 piVC，受 Stanford 的[同名项目](https://cs.stanford.edu/people/jasonaue/pivc/)启发所作，是一个以教学为目的的验证语言。

## 结构

该编译器的设计可以分为三个部分：

 * 前端（frontend）：使用由 [ANTLR](https://www.antlr.org/) 自动生成的 parser 将源文件解析为 CST (concrete syntax tree，具体语法树)，再遍历 CST，生成 CFG；
 * CFG（control flow graph，控制流图）：一个以验证为目标设计的控制流图，作为中间表示；
 * 后端（backend）：使用 deductive verification 的方法从 CFG 中生成验证条件（verification condition），再将其喂给 SMT Solver 来求解。

你唯一被允许修改、并且你也必须要修改的文件是 `Verifier.cs`，你需要在其中实现 deductive verification 的算法主体。

## 安装

本项目依赖于 .NET 5.0，你可以从[这里](https://dotnet.microsoft.com/download)下载其最新的 SDK。

你可以使用任意你喜欢的 IDE，我们推荐：
- [Visual Studio](https://visualstudio.microsoft.com/zh-hans/)
- [Visual Studio Code](https://code.visualstudio.com/)：配合 [C# 插件](https://marketplace.visualstudio.com/items?itemName=ms-dotnettools.csharp)。

> 注意：建议不要通过 homebrew 或 apt 直接安装，因为其软件源中的 `dotnet` 的版本很有可能是过时的。建议从[这里](https://dotnet.microsoft.com/download)下载最新版。

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

## 分值分配

占总评 30 分

分值分配
- 报告：6
- 基本要求一（partial correctness）：21
- 基本要求二（termination）：3

bonus 有 0~5 分的加分，推荐 BMC 和谓词抽象，也可以自主选题，需要与助教交流。

如果被检查出雷同，则直接以 0 分处理。

考虑：完成基本要求就有接近 27 分，只要再写完 termination 就只会被扣 1.5 分，再写个 BMC 就有满分，再写个谓词抽象就能加 6 分，我觉得还算是比较宽松也比较合情的

有隐藏测例，分数上的占比 20%。

隐藏测例是公开测例的“变体”。
TODO：具体是怎样的变体需要讲清楚。
