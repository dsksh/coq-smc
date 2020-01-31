Require Import Bmc.Core.
Require Import Bmc.Example.
Require Import SMTC.Tactic.
Require Import SMTC.Integers.

Set SMT Solver "z3".
Set SMT Debug.

Axiom by_smt : forall P : Prop, P.


Definition backward_post (I : prop) (T : trans) (P : prop) (k: nat) : Prop :=
  lasso_bwd_ni T P  k /\ safety_k_ni I T P k.


Goal backward_post ex1_I ex1_T ex1_P 1.
Proof.
  unfold ex1_I, ex1_T, ex1_P.
  unfold backward_post.
  unfold lasso_bwd_ni.
  unfold safety_k_ni.
  unfold prop_k_init_ni.
  unfold loop_free.
  unfold path.
  unfold no_loop.
  unfold no_loop'.
  unfold sseq.
  unfold nth.
  unfold state.
  repeat rewrite -> Nat.add_0_l.
  repeat rewrite -> Nat.add_0_r.

  split.
  - intros.
    smt solve; apply by_smt.

  - repeat split.
    + intros.
      smt solve; apply by_smt.
    + intros.
      smt solve; apply by_smt.
Qed.

Goal backward_post ex2_I ex2_T ex2_P 3.
Proof.
  unfold ex2_I, ex2_T, ex2_P.
  unfold backward_post, lasso_bwd_ni, safety_k_ni, prop_k_init_ni, loop_free, path, no_loop, no_loop', sseq, nth, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  split.
  intros; smt solve; apply by_smt.
  repeat split; intros; smt solve; apply by_smt.
Qed.

Goal backward_post ex3_I ex3_T ex3_P 10.
Proof.
  unfold ex3_I, ex3_T, ex3_P.
  unfold backward_post, lasso_bwd_ni, safety_k_ni, prop_k_init_ni, loop_free, path, no_loop, no_loop', sseq, nth, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  split.
(*
  intros; smt solve; apply by_smt.
  repeat split; intros; smt solve; apply by_smt.
*)
Admitted.

(* eof *)