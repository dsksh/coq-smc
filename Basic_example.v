Require Import Basic.
Require Import Example.
Require Import SMTC.Tactic.
Require Import SMTC.Integers.

Set SMT Solver "z3".
Set SMT Debug.
(*Unset SMT Debug.*)

Axiom by_smt : forall P : Prop, P.


Goal naive_post ex1_I ex1_T ex1_P 1.
Proof.
  unfold ex1_I; unfold ex1_T; unfold ex1_P.
  unfold naive_post.
  unfold safety_k.
  unfold prop_k_init.
  unfold path.
  unfold nth.
  unfold sseq.
  unfold state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  split.
  - intros.
    smt solve; apply by_smt.
  - intros.
    smt solve; apply by_smt.
Qed.

Goal naive_post ex2_I ex2_T ex2_P 1.
Proof.
  unfold ex2_I; unfold ex2_T; unfold ex2_P.
  unfold naive_post, safety_k, prop_k_init, path, nth, sseq, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  repeat split; intros; smt solve; apply by_smt.
Qed.

Goal naive_post ex3_I ex3_T ex3_P 6.
Proof.
  unfold ex3_I; unfold ex3_T; unfold ex3_P.
  unfold naive_post, safety_k, prop_k_init, path, nth, sseq, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  repeat split; intros; smt solve; apply by_smt.
Qed.

(* eof *)