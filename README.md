# A Verified Bounded Model Checker in Coq

## Requirements

- [Coq](https://coq.inria.fr) (checked with 8.6.1)
- [coq2smt](https://github.com/wangjwchn/coq2smt) (checked with the commit `604f72a`)
- [coq-plugin-utils](https://github.com/gmalecha/coq-plugin-utils) (required by coq2smt)
- SMT solvers (e.g. CVC4 and Z3)

## Usage

### Compilation

```.sh
$ make
```

### Usage

Invoke the IDE
```.sh
$ coqide src/Basic_example.v
```
and play with an interactive proof.

## Modules

The following diagram represents the contents of the modules and the dependencies among them.

```
.
+-- Logic: Some auxiliary lemmas.
    |
    +-- Core: Definitions of transition systems, etc.;
        |       A thery of state sequences and paths.
        |
        +-- Basic: Basic BMC methods.
        |   +-- Basic_example
        |
        +-- Forward: Sheeran et al.'s forward method.
        |   +-- Forward_example
        |
        +-- Backward: Sheeran et al.'s backward method.
        |   +-- Backward_example
        |
        +-- KInduction.v: A k-induction method.
            +-- KInduction_example
```            
