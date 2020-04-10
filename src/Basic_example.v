Require Import Bmc.Basic.
Require Import Bmc.Example.

Require Import SMTC.Tactic.
Require Import SMTC.Integers.

Set SMT Solver "z3".
Set SMT Debug.
(*Unset SMT Debug.*)

Axiom by_smt : forall P : Prop, P.


(*Definition naive_post_conj (I : prop) (T : trans) (P : prop) (k : nat) : Prop :=
  safety_k_conj I T P (S k).
*)

Goal naive_post_conj ex1_I ex1_T ex1_P 0.
Proof.
  unfold ex1_I; unfold ex1_T; unfold ex1_P.
  unfold naive_post_conj.
  unfold safety_k_conj.
  unfold prop_k_init_conj.
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

Goal naive_post_conj ex2_I ex2_T ex2_P 1.
Proof.
  unfold ex2_I; unfold ex2_T; unfold ex2_P.
  unfold naive_post_conj, safety_k_conj, prop_k_init_conj, path, nth, sseq, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  repeat split; intros; smt solve; apply by_smt.
Qed.

Goal naive_post_conj ex3_I ex3_T ex3_P 6.
Proof.
  unfold ex3_I; unfold ex3_T; unfold ex3_P.
  unfold naive_post_conj, safety_k_conj, prop_k_init_conj, path, nth, sseq, state.
  repeat rewrite -> Nat.add_0_l;
  repeat rewrite -> Nat.add_0_r.
  repeat split; intros; smt solve; apply by_smt.
Qed.

(* eof *)
