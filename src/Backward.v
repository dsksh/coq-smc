Require Export Bmc.Core.
Require Import Omega.


Definition backward_post (I : prop) (T : trans) (P : prop) (k: nat) : Prop :=
  lasso_bwd T P (S k) /\ safety_k I T P (S k).

(* *)

Local Theorem case1 :
  forall (I : prop) (T : trans) (P : prop) (k : nat),
  backward_post I T P k -> 
    forall (i : nat), (i <= S k) -> prop_k_init_lf I T P i.
Proof.
  intros * H * H0 *.
  unfold backward_post in H.
  destruct H as [H H'].
  apply (bounded_safety I T P) in H0.
  firstorder.
  auto.
Qed.

Local Lemma case2_2' : forall (T : trans) (P : prop) (i k : nat),
  i > k -> 
  ( forall ss : sseq, (loop_free T ss 0 k -> P ss.[k]) ) -> 
    forall ss : sseq, (loop_free T ss (i-k) k -> P ss.[i]).
Proof.
  intros.
  unfold loop_free in *.
  destruct H1 as [H1 H2].
  apply skipn_path in H1.
  apply skipn_no_loop in H2.
  assert (i-k+k = i) by omega.
  rewrite <- H3.
  rewrite <- skipn_nth.
  apply H0.
  split.
  apply H1.
  apply H2.
Qed.

Local Lemma case2_2 : forall (I : prop) (T : trans) (P : prop) (i k : nat),
  i > k -> 
  lasso_bwd T P k -> 
  prop_k_init_lf I T P i.
Proof.
  unfold lasso_bwd, prop_k_init_lf.
  intros * H H0 * H1 H2.

  assert (A : i = (i - k) + k) by omega.
  rewrite A in H2.
  apply split_loop_free in H2.
  destruct H2 as [H2 H3].
  revert H3.
  apply case2_2' with (i := i) (k := k) (ss := ss).
  apply H.
  apply H0.
Qed.

Local Lemma case2 :
  forall (I : prop) (T : trans) (P : prop) (k : nat),
  backward_post I T P k -> 
  forall (i : nat), (i > S k) -> prop_k_init_lf I T P i.
Proof.
  intros * H * H0.
  unfold backward_post in H.
  destruct H as [H H1].
  now apply case2_2 with (k := S k).
Qed.

(**)

Theorem soundness_backward' :
  forall (I : prop) (T : trans) (P : prop) (k : nat),
  backward_post I T P k -> 
  forall (i : nat), prop_k_init_lf I T P i.
Proof.
  intros * H *.
  destruct (Nat.le_gt_cases i (S k)) as [H0|H0].
  - revert H0.
    now apply case1.
  - revert H0.
    now apply case2.
Qed.

Require Export Bmc.LoopFree.

Theorem soundness_backward :
  forall (I : prop) (T : trans) (P : prop) (k : nat),
  backward_post I T P k -> 
  forall (i : nat), prop_k_init I T P i.
Proof.
  intros * H.
  apply safety_lf_path.
  apply soundness_backward' with (k := k).
  apply H.
Qed.

Theorem soundness_backward1 :
  forall (I : prop) (T : trans) (P : prop),
  ( exists k, backward_post I T P k ) -> 
  forall (i : nat), prop_k_init I T P i.
Proof.
  intros * H.
  destruct H as [k].
  apply soundness_backward with (k:=k).
  apply H.
Qed.

(**)

Require Export Bmc.CoreConj.

Definition backward_post_conj (I : prop) (T : trans) (P : prop) (k: nat) : Prop :=
  lasso_bwd_conj T P (S k) /\ safety_k_conj I T P (S k).

Lemma backward_post_conj_eq :
  forall (I:prop) (T:trans) (P:prop) (k:nat),
  backward_post I T P k <-> backward_post_conj I T P k.
Proof.
  intros *.
  unfold backward_post, backward_post_conj.
  rewrite -> safety_k_conj_eq.
  rewrite -> lasso_bwd_conj_eq.
  tauto.
Qed.

(* eof *)
