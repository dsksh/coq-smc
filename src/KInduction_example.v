Require Import Bmc.KInduction.
Require Import Bmc.Example.

Require Import SMTC.Tactic.
Require Import SMTC.Integers.


(*Definition k_ind_step_ni (T : trans)
  (P : prop) (k: nat) : Prop :=
  forall ss : sseq,
  ~(loop_free T ss 0 k /\ safety_nth_offset P ss 0 k /\ ~P ss.[k]).

Definition k_induction_post_ni (I : prop) (T : trans) (P : prop) (k: nat) : Prop :=
  k_ind_step_ni T P k /\ safety_nth_ni I T P k.
*)


Set SMT Solver "z3".
Set SMT Debug.

Axiom by_smt : forall P : Prop, P.


Goal k_induction_post_conj ex1_I ex1_T ex1_P 3.
Proof.
  unfold ex1_I, ex1_T, ex1_P.
  unfold k_induction_post_conj.
  unfold k_ind_step_conj.
  unfold safety_nth_offset.
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
    + intros.
      smt solve; apply by_smt.
    + intros.
      smt solve; apply by_smt.
Qed.

Goal k_induction_post_conj ex2_I ex2_T ex2_P 2.
Proof.
  unfold ex2_I, ex2_T, ex2_P.
  unfold k_induction_post_conj, k_ind_step_conj, safety_nth_offset, safety_nth_conj, prop_nth_init_conj, loop_free, path, no_loop, no_loop', sseq, nth, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  split.
  intros; smt solve; apply by_smt.
  repeat split; intros; smt solve; apply by_smt.
Qed.

Goal k_induction_post_conj ex3_I ex3_T ex3_P 5.
Proof.
  unfold ex3_I, ex3_T, ex3_P.
  unfold k_induction_post_conj, k_ind_step_conj, safety_nth_offset, safety_nth_conj, prop_nth_init_conj, loop_free, path, no_loop, no_loop', sseq, nth, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  split.
  intros; smt solve; apply by_smt.
  repeat split; intros; smt solve; apply by_smt.
Qed.

(* eof *)
