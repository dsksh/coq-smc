Require Import Bmc.Backward.
Require Import Bmc.Example.

Require Import SMTC.Tactic.
Require Import SMTC.Integers.

Set SMT Solver "z3".
Set SMT Debug.

Axiom by_smt : forall P : Prop, P.


(*Definition backward_post (I : prop) (T : trans) (P : prop) (k: nat) : Prop :=
  lasso_bwd_conj T P (S k) /\ safety_nth_ni I T P (S k).
*)


Goal backward_post_conj ex1_I ex1_T ex1_P 1.
Proof.
  unfold ex1_I, ex1_T, ex1_P.
  unfold backward_post_conj.
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
  - intros.
    smt solve; apply by_smt.

  - repeat split.
    + intros.
      smt solve; apply by_smt.
    + intros.
      smt solve; apply by_smt.
    + intros.
      smt solve; apply by_smt.
Qed.

Goal backward_post_conj ex1_I ex1_T ex1_P 0.
Proof.
  unfold ex1_I, ex1_T, ex1_P.
  unfold backward_post_conj, lasso_bwd_conj, safety_nth_conj, prop_nth_init_conj, loop_free, path, no_loop, no_loop', sseq, nth, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  repeat split; intros; smt solve; apply by_smt.
Qed.

Goal backward_post_conj ex2_I ex2_T ex2_P 1.
Proof.
  unfold ex2_I, ex2_T, ex2_P.
  unfold backward_post_conj, lasso_bwd_conj, safety_nth_conj, prop_nth_init_conj, loop_free, path, no_loop, no_loop', sseq, nth, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  repeat split; intros; smt solve; apply by_smt.
Qed.

Goal backward_post_conj ex3_I ex3_T ex3_P 9.
Proof.
  unfold ex3_I, ex3_T, ex3_P.
  unfold backward_post_conj, lasso_bwd_conj, safety_nth_conj, prop_nth_init_conj, loop_free, path, no_loop, no_loop', sseq, nth, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  split.
(*
  intros; smt solve; apply by_smt.
  repeat split; intros; smt solve; apply by_smt.
*)
Admitted.

(* eof *)