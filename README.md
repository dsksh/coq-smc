# SAT-based Model Checking in Coq

Specification of SMT-based model checking methods in Coq.
We aim to verify the correctness of the methods.
Currently formal soundness proofs are included.

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
+-- LoopFree: Lemmas for relating looped and loop-free paths.
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
        |   +-- KInduction_example
        |
        +-- PDR.v: An IC3/PDR method.
            +-- PDR_example
```            
