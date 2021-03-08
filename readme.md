This is the THU version compiler of [piVC](https://cs.stanford.edu/people/jasonaue/pivc/), an education purposed verification language.

## Usage

So far we just use a stupid way to update generated parser, if you update the grammar file, you have to update generated parser source files manually.

In `/parsing`, you need to run command like the following:

```bash
java -jar </path/to/antlr/jar> piVC.g4 -Dlanguage=CSharp
```

## To-Do

A lot of work needs to do, include the followings and something other.

### Level I: You have to do

- [ ] The grammar is not totally correct and sufficiently tested.
- [ ] The design and implementation of CFG.
- [ ] The framework of verification algorithm and a baseline implementation.
- [ ] The documentation for code, task and environments.
- [ ] The testcases and judging system.

### Level II: Make things better

- [ ] Target code (assembly) generator
- [ ] Find a student to test

### Level III: Bonus for fun

- [ ] VS Code syntax highlighter
