Require Export Bmc.Core.
Require Import Omega.


Definition forward_post (I : prop) (T : trans) (P : prop) (k: nat) : Prop :=
  lasso_fwd I T (S k) /\ safety_nth I T P (S k).

(* *)

Local Theorem case1 :
  forall (I : prop) (T : trans) (P : prop) (k : nat),
  forward_post I T P k -> 
    forall (i : nat), (i <= S k) -> prop_nth_init_lf I T P i.
Proof.
  intros * H * H0.
  unfold forward_post in H.
  destruct H as [H H'].
  apply (bounded_safety I T P) in H0.
  firstorder.
  auto.
Qed.

Local Lemma case2_1 :
  forall (I : prop) (T : trans) (P : prop) (i k : nat),
  i > k -> lasso_fwd I T k -> prop_nth_init_lf I T P i.
Proof.
  unfold lasso_fwd, prop_nth_init_lf in *.
  intros * H H0 * H1 H2.
  assert (A : i = k + (i - k)) by omega.
  rewrite -> A in H2.
  apply split_loop_free in H2.
  destruct H2.
  contradict H2.
  apply H0.
  apply H1.
Qed.

Local Lemma case2 :
  forall (I : prop) (T : trans) (P : prop) (k : nat),
  forward_post I T P k -> 
  forall (i : nat), (i > (S k)) -> prop_nth_init_lf I T P i.
Proof.
  intros * H * H0.
  unfold forward_post in H.
  destruct H as [H H1].
  apply case2_1 with (k := S k).
  apply H0.
  apply H.
Qed.

(**)

Theorem soundness_forward' :
  forall (I : prop) (T : trans) (P : prop) (k : nat),
  forward_post I T P k -> 
  forall (i : nat), prop_nth_init_lf I T P i.
Proof.
  intros * H *.
  destruct (Nat.le_gt_cases i (S k)) as [H0|H0].
  - revert H0.
    now apply case1.
  - revert H0.
    now apply case2.
Qed.

Require Export Bmc.LoopFree.

Theorem soundness_forward :
  forall (I : prop) (T : trans) (P : prop) (k : nat),
  forward_post I T P k -> 
  forall (i : nat), prop_nth_init I T P i.
Proof.
  intros * H.
  apply safety_lf_path.
  apply soundness_forward' with (k := k).
  apply H.
Qed.

Theorem soundness_forward1 :
  forall (I : prop) (T : trans) (P : prop),
  ( exists k, forward_post I T P k ) -> 
  forall (i : nat), prop_nth_init I T P i.
Proof.
  intros * H.
  destruct H as [k].
  apply soundness_forward with (k:=k).
  apply H.
Qed.

(**)

Require Export Bmc.CoreConj.

Definition forward_post_conj (I : prop) (T : trans) (P : prop) (k: nat) : Prop :=
  lasso_fwd_conj I T (S k) /\ safety_nth_conj I T P (S k).

Lemma foreward_post_conj_eq :
  forall (I:prop) (T:trans) (P:prop) (k:nat),
  forward_post I T P k <-> forward_post_conj I T P k.
Proof.
  intros *.
  unfold forward_post, forward_post_conj.
  rewrite -> safety_nth_conj_eq.
  rewrite -> lasso_fwd_conj_eq.
  tauto.
Qed.

(* eof *)