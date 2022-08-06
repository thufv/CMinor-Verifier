![Error when building and testing](https://byob.yarr.is/thufv/CMinor/score)

> 注：请在 fork 后将上面的 URL 中的 `thufv` 替换为你的 username。以上显示的得分需要等待每次 push 所触发的 GitHub Action 执行完毕后才会被更新。

## 简介

本项目为 2022 年春季学期清华大学《软件分析与验证》课程的大作业，作业平台提供了一个 CMinor 的验证框架，你需要在其中实现核心的验证算法。CMinor 是一个面向验证的教学语言，其包括源程序和验证标注两部分，其中源程序部分大致是 C 语言的子集，验证标注部分大致是 [ACSL (ANSI/ISO C Specification Language)](https://frama-c.com/html/acsl.html) 的子集。从 C 语言的角度来看，验证标注是写在注释中的，不会影响 C 代码通常的编译和运行。

本次大作业你需要实现本工具中的核心验证算法部分，具体的说明请见[任务说明文档](task-doc.md)。

本项目使用 [git submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) 来集成公开测例仓库，在 clone 后可以使用 `git submodule update --remote` 来更新测例仓库。

## 安装

本项目依赖于 .NET 6，你可以从[这里](https://dotnet.microsoft.com/download)下载其最新的 SDK。

你可以使用任意你喜欢的 IDE，我们推荐：
- [Visual Studio 2022 (>= 17.0.0)](https://visualstudio.microsoft.com/)：可以在安装的时候打包安装 .NET 的 SDK，不需要再单独下载
- [Visual Studio Code](https://code.visualstudio.com/)：配合 [C# 插件](https://marketplace.visualstudio.com/items?itemName=ms-dotnettools.csharp)
- [Rider](https://www.jetbrains.com/rider/)

> 注意：建议不要通过 `homebrew` 或 `apt` 直接安装，因为其软件源中的 dotnet 的版本很有可能是过时的。建议从[这里](https://dotnet.microsoft.com/download)下载最新版。

> 注意：如果你遇到了错误 `Unhandled exception. System.DllNotFoundException: Unable to load shared library 'libz3' or one of its dependencies.`，那么你需要从[这里](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.16)单独安装 Z3 4.8.16。

## 使用

本项目基本的使用方法是：

```bash
cminor --source <path>
```

你可以在本项目的根目录下运行以下指令：

```bash
dotnet run -- --source <path>
```

你可以使用 `--printCFG` 来打印出得到的 CFG。

所支持的各命令行选项的具体含义为：

```bash
--source      Required. The source file of CMinor language (recommended with filename extension '.c').

--printCFG    The file (or 'console') to which the control flow graph is printed.

--help        Display this help screen.

--version     Display version information.
```

## 自动测试

我们不再使用传统的 OJ 来提交代码，而是用 [GitHub Actions](https://github.com/features/actions) 将自动化测试直接集成进项目中。
简而言之，你的每一次 push 都相当于自动提交了代码，会触发一个名为 `Build and Test` 的 job，其会构建项目并评测所有测例，并将得分（百分制）显示在 readme 开头。

## 结构

该编译器的设计可以分为三个部分：

 * 前端（frontend）：使用由 [ANTLR](https://www.antlr.org/) 自动生成的 parser 将源文件解析为 CST (concrete syntax tree，具体语法树)，再遍历 CST，生成 CFG（control flow graph，控制流图）；
 * 中间表示（ir）：面向验证来设计的控制流图；
 * 后端（backend）：使用 deductive verification 的方法从 CFG 中生成验证条件（verification condition），再将其喂给 SMT Solver 来求解。
   * 这部分是你需要来实现的。

你唯一被允许修改、并且你也必须要修改的文件是 `Verifier.cs`，你需要在其中实现演绎验证的算法主体。

## API 文档

API 文档在 `./api-doc/`，打开 `./api-doc/index.html` 即可浏览。

如果想要更新 API 文档的话，你需要使用 [doxygen](https://www.doxygen.nl/index.html)，并在本项目根目录下运行 `doxygen`。

## 贡献者

 * [谢兴宇](https://github.com/namasikanam)
 * [陈建辉](https://www.zhihu.com/people/yan-jing-ye-35)
 * [徐荣琛](https://xurongchen.github.io/)
 * [刘江宜](https://github.com/panda2134)
 * [孙志航](https://github.com/Misasasa)
 * [贺飞](https://feihe.github.io/)

## 参考

CMinor 语言大致是以下语言标准的子集：

- Standard C: [ISO/IEC 9899:2018, aka C17 or C18](https://web.archive.org/web/20181230041359if_/http://www.open-std.org/jtc1/sc22/wg14/www/abq/c17_updated_proposed_fdis.pdf)
- ANSI/ISO C Speicication Language: [ACSL v1.17](https://frama-c.com/download/acsl-1.17.pdf)
