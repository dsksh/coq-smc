Require Export Bmc.Core.
Require Import Omega.


Definition backward_post (I : init) (T : trans) (P : prop) (k: nat) : Prop :=
  lasso_bwd T P  k /\ safety_k I T P k.

(* *)

Local Theorem case1 :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  backward_post I T P k -> 
    forall (i : nat), (i <= k) -> prop_k_init_lf I T P i.
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
  ( forall ss : sseq, ~ (loop_free T ss 0 k /\ ~ P ss.[k]) ) -> 
    forall ss : sseq, ~ (loop_free T ss (i-k) k /\ ~ P ss.[i]).
Proof.
  intros * H H0 *.
  apply neg_false.
  split.
  - unfold loop_free in *.
    intros H1.
    destruct H1 as [H1 H3].
    destruct H1 as [H1 H2].
    apply skipn_no_loop in H2.
    apply skipn_prop with (k:= k) in H3.
    apply skipn_path in H1.
    firstorder.
    omega.
  - tauto.
Qed.

Local Lemma case2_2 : forall (I : init) (T : trans) (P : prop) (i k : nat),
  i > k -> 
  lasso_bwd T P k -> 
  prop_k_init_lf I T P i.
Proof.
  unfold lasso_bwd, prop_k_init_lf.
  intros * H H0 *.
  apply neg_false.
  split.
  - intros H1.
    destruct H1 as [H1 H2].
    destruct H2 as [H2 H3].
    assert (A : i = (i - k) + k) by omega.
    rewrite A in H2.
    apply split_loop_free in H2.
    apply case2_2' with (i := i) (k := k) (ss := ss) in H0.
    firstorder.
    apply H.
  - tauto.
Qed.

Local Lemma case2 :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  backward_post I T P k -> 
  forall (i : nat), (i > k) -> prop_k_init_lf I T P i.
Proof.
  intros * H * H0.
  unfold backward_post in H.
  destruct H as [H H1].
  now apply case2_2 with (k := k).
Qed.

(**)

Theorem soundness_backward' :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  backward_post I T P k -> 
  forall (i : nat), prop_k_init_lf I T P i.
Proof.
  intros * H *.
  destruct (Nat.le_gt_cases i k) as [H0|H0].
  - revert H0.
    now apply case1.
  - revert H0.
    now apply case2.
Qed.

Theorem soundness_backward :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  backward_post I T P k -> 
  forall (i : nat), prop_k_init I T P i.
Proof.
  intros * H.
  apply safety_lf_path.
  apply soundness_backward' with (k := k).
  apply H.
Qed.

(* eof *)
