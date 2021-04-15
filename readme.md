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

## To-Do

A lot of work needs to do, include the followings and something other.

### Level I: You have to do

- [x] The grammar is not totally correct and sufficiently tested.
- [x] The design and implementation of CFG.
  - [x] runtime assertion
    - [x] divided by 0：`/` `div`
    - [x] the length of array > 0: 
- [x] The framework of verification algorithm and a baseline implementation.
  - [x] SMT solver abstraction
  - [x] substitution
  - [x] runtime assertion in annotation
- [ ] printer
  - [x] control flow graph
  - [x] basic path
  - [x] counter model
  - [ ] label of annotation
- [ ] The documentation for code, task and environments.
- [ ] The testcases and judging system.

### Level II: Make things better

- [ ] more beautiful printer
  - [ ] label of annotation: now I just omit it for simplicity
  - [ ] the row and column of the beginning of each block
- [ ] Target code (assembly) generator
- [x] Find a student to test

### Level III: Bonus for fun

- [ ] VS Code syntax highlighter