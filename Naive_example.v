Require Import Naive.
Require Import Examples.
Require Import SMTC.Tactic.
Require Import SMTC.Integers.

Set SMT Solver "z3".
Set SMT Debug.

Axiom by_smt : forall P : Prop, P.


Example naive_method1 :
  naive_post ex1_I ex1_T ex1_P 2.
Proof.
  unfold naive_post.
  simpl.
  unfold ex1_I; unfold ex1_T; unfold ex1_P.
  simpl.
  intros.
  unfold state in *.
  smt solve; apply by_smt.
Qed.

Example naive_method2 :
  naive_post ex2_I ex2_T ex2_P 3.
Proof.
  unfold naive_post.
  simpl.
  unfold ex2_I; unfold ex2_T; unfold ex2_P.
  simpl.
  intros.
  unfold state in *.
  smt solve; apply by_smt.
Qed.

Example naive_method3 :
  naive_post ex3_I ex3_T ex3_P 3.
Proof.
  unfold naive_post.
  simpl.
  unfold ex3_I; unfold ex3_T; unfold ex3_P.
  simpl.
  intros.
  unfold state in *.
  smt solve; apply by_smt.
Qed.

(* eof *)