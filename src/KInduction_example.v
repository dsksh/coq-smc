Require Import Bmc.Core.
Require Import Bmc.Example.
Require Import SMTC.Tactic.
Require Import SMTC.Integers.


Definition k_ind_step_ni (T : trans)
  (P : prop) (k: nat) : Prop :=
  forall ss : sseq,
  ~(loop_free T ss 0 k /\ safety_k_offset P ss 0 k /\ ~P ss.[k]).

Definition k_induction_post_ni (I : prop) (T : trans) (P : prop) (k: nat) : Prop :=
  k_ind_step_ni T P k /\ safety_k_ni I T P k.


Set SMT Solver "z3".
Set SMT Debug.

Axiom by_smt : forall P : Prop, P.


Goal k_induction_post_ni ex1_I ex1_T ex1_P 4.
Proof.
  unfold ex1_I, ex1_T, ex1_P.
  unfold k_induction_post_ni.
  unfold k_ind_step_ni.
  unfold safety_k_offset.
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
    + intros.
      smt solve; apply by_smt.
    + intros.
      smt solve; apply by_smt.
    + intros.
      smt solve; apply by_smt.
Qed.

Goal k_induction_post_ni ex2_I ex2_T ex2_P 3.
Proof.
  unfold ex2_I, ex2_T, ex2_P.
  unfold k_induction_post_ni, k_ind_step_ni, safety_k_offset, safety_k_ni, prop_k_init_ni, loop_free, path, no_loop, no_loop', sseq, nth, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  split.
  intros; smt solve; apply by_smt.
  repeat split; intros; smt solve; apply by_smt.
Qed.

Goal k_induction_post_ni ex3_I ex3_T ex3_P 6.
Proof.
  unfold ex3_I, ex3_T, ex3_P.
  unfold k_induction_post_ni, k_ind_step_ni, safety_k_offset, safety_k_ni, prop_k_init_ni, loop_free, path, no_loop, no_loop', sseq, nth, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  split.
  intros; smt solve; apply by_smt.
  repeat split; intros; smt solve; apply by_smt.
Qed.

(* eof *)
