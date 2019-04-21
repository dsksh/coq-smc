Require Export Bmc.Core.
Require Import Omega.


Definition forward_post (I : init) (T : trans) (P : prop) (k: nat) : Prop :=
  lasso_fwd I T P k /\ safety_k I T P k.

(* *)

Local Theorem case1 :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  forward_post I T P k -> 
    forall (i : nat), (i <= k) -> prop_k_init_lf I T P i.
Proof.
  intros * H * H0 *.
  unfold forward_post in H.
  destruct H as [H H'].
  apply (bounded_safety I T P) in H0.
  firstorder.
  auto.
Qed.

Local Lemma case2_1 :
  forall (I : init) (T : trans) (P : prop) (i k : nat),
  i > k -> lasso_fwd I T P k -> prop_k_init_lf I T P i.
Proof.
  unfold lasso_fwd, prop_k_init_lf in *.
  intros * H H0 *.
  apply neg_false.
  split.
  - intros H1.
    destruct H1 as [H1 H2].
    destruct H2 as [H2 H3].
    assert (A : i = k + (i - k)) by omega.
    rewrite A in H2.
    apply split_loop_free in H2.
    firstorder.
  - firstorder.
Qed.

Local Lemma case2 :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  forward_post I T P k -> 
  forall (i : nat), (i > k) -> prop_k_init_lf I T P i.
Proof.
  intros * H * H0.
  unfold forward_post in H.
  destruct H as [H H1].
  now apply case2_1 with (k := k).
Qed.

(**)

Theorem soundness_forward' :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  forward_post I T P k -> 
  forall (i : nat), prop_k_init_lf I T P i.
Proof.
  intros * H *.
  destruct (Nat.le_gt_cases i k) as [H0|H0].
  - revert H0.
    now apply case1.
  - revert H0.
    now apply case2.
Qed.

Theorem soundness_forward :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  forward_post I T P k -> 
  forall (i : nat), prop_k_init I T P i.
Proof.
  intros * H.
  apply safety_lf_path.
  apply soundness_forward' with (k := k).
  apply H.
Qed.

(* eof *)
