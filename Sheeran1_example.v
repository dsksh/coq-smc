Require Import Sheeran1.
Require Import Examples.
Require Import SMTC.Tactic.
Require Import SMTC.Integers.

Set SMT Solver "z3".
Set SMT Debug.

Axiom by_smt : forall P : Prop, P.


Example algorithm1_test1 :
  algorithm1_post ex1_I ex1_T ex1_P 1.
Proof.
  unfold ex1_I, ex1_T, ex1_P.
  unfold algorithm1_post, lasso, violate_loop_free, safety_k;
  split;
  unfold loop_free, prop_k_init_lf, prop_k_init;
  unfold state;
  simpl.

  (right; intros; smt solve; apply by_smt) ||
  (left; intros; smt solve; apply by_smt).

  repeat tryif split then split
    else smt solve; apply by_smt.
Qed.

Example algorithm1_test2 :
  algorithm1_post ex2_I ex2_T ex2_P 1.
Proof.
  unfold ex2_I, ex2_T, ex2_P.
  unfold algorithm1_post, lasso, violate_loop_free, safety_k;
  split;
  unfold loop_free, prop_k_init_lf, prop_k_init;
  unfold state;
  simpl.

  (right; intros; smt solve; apply by_smt) ||
  (left; intros; smt solve; apply by_smt).

  repeat tryif split then split
    else smt solve; apply by_smt.
Qed.

(* eof *)