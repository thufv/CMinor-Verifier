This is the THU version compiler of [piVC](https://cs.stanford.edu/people/jasonaue/pivc/), an education purposed verification language.

## Usage

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
