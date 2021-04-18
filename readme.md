This is the THU version compiler of [piVC](https://cs.stanford.edu/people/jasonaue/pivc/), an education purposed verification language.

## Structure

The whole project are split into three parts:

 * frontend: CFG generation from concrete syntax tree, which is calculated by ANTLR
 * CFG: a verification-aimed designed CFG
 * backend: deductive verification of generated CFG, which will call SMT solver to check the validity of verification conditions.

You are allowed to modify ONLY ONE file `Verifier.cs`, in which you need to implement the main algorithm of deductive verification.

## Install

You need to install .net 5.0. [Download Link](https://dotnet.microsoft.com/download/dotnet/5.0)

Then install C# Plugin in Visual Studio Code, and open this folder using VSCode.

Mac OS Notes:
1. DO NOT install `dotnet` via Homebrew directly, since the homebrew formula contains an outdated version. use the package installer provided by Microsoft.
2. You need to install `libz3`. Install homebrew and then run:
```bash
brew install z3
```

To check for you environment, run

```bash
dotnet run
```

in the project folder.

## Usage

The basic usage is

```bash
piVC-thu --source <path> --printCFG console
```

You could run the following command in the root directory of this project:

```bash
dotnet run -- --source <path> --printCFG console
```

The details about options are:

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
