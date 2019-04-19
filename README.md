# A Verified Bounded Model Checker in Coq

## Requirements

- [Coq](https://coq.inria.fr) (checked with 8.6.1)
- [coq2smt](https://github.com/wangjwchn/coq2smt) (checked with commit `604f72a`)

## Usage

### Compilation

```.sh
$ make
```

### Usage

Invoke the IDE
```.sh
$ coqide Basic_example.v
```
and play with an interactive proof.

## File Structure

The following diagram represents the dependencies among the vernacular files and their contents.

```
.
+-- Logic.v: Some auxiliary lemmas.
    |
    +-- Core.v: Definitions of transition systems etc.;
        |       a thery of state sequences and paths.
        |
        +-- Basic.v: Basic BMC methods.
        |   +-- Basic_example.v
        |
        +-- Sheeran1.v: Sheeran et al.'s first algorithm.
        |   +-- Sheeran1_example.v
        |
        +-- KInduction.v: A k-induction method.
            +-- KInduction_example.v
```            

<!-- EOF -->
