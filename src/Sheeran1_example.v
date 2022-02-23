Require Import Bmc.Forward.
Require Import Bmc.Backward.
Require Import Bmc.Example.

Require Import SMTC.Tactic.
Require Import SMTC.Integers.


(* First algorithm of [Sheeran+ 2000]. *)
Definition sheeran1_post (I : prop) (T : trans) (P : prop) (k: nat) : Prop :=
  safety_nth_conj I T P k /\
  (lasso_fwd_conj I T k \/ lasso_bwd_conj T P k).


Set SMT Solver "z3".
Set SMT Debug.

Axiom by_smt : forall P : Prop, P.


Goal sheeran1_post ex1_I ex1_T ex1_P 2.
Proof.
  unfold ex1_I, ex1_T, ex1_P.
  unfold sheeran1_post.
  unfold lasso_fwd_conj.
  unfold lasso_bwd_conj.
  unfold safety_nth_conj.
  unfold prop_nth_init_conj.
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
  - repeat split.
    + intros.
      smt solve; apply by_smt.
    + intros.
      smt solve; apply by_smt.
    + intros.
      smt solve; apply by_smt.
  - (right; intros; smt solve; apply by_smt) ||
    (left; intros; smt solve; apply by_smt).
Qed.

Goal sheeran1_post ex2_I ex2_T ex2_P 2.
Proof.
  unfold ex2_I, ex2_T, ex2_P.
  unfold sheeran1_post, lasso_fwd_conj, lasso_bwd_conj, safety_nth_conj, prop_nth_init_conj, loop_free, path, no_loop, no_loop', sseq, nth, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  split.
  repeat split; intros; smt solve; apply by_smt.
  (right; intros; smt solve; apply by_smt) ||
  (left; intros; smt solve; apply by_smt).
Qed.

Goal sheeran1_post ex3_I ex3_T ex3_P 6.
Proof.
  unfold ex3_I, ex3_T, ex3_P.
  unfold sheeran1_post, lasso_fwd_conj, lasso_bwd_conj, safety_nth_conj, prop_nth_init_conj, loop_free, path, no_loop, no_loop', sseq, nth, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  split.
  repeat split; intros; smt solve; apply by_smt.
  (right; intros; smt solve; apply by_smt) ||
  (left; intros; smt solve; apply by_smt).
Qed.

(* eof *)