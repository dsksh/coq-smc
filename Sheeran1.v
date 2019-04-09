Require Export Core.
Require Import Omega.


Definition algorithm1_post (I : init) (T : trans) (P : prop) (k: nat) : Prop :=
  (lasso I T P k \/ violate_loop_free I T P  k) /\ 
  safety_k I T P k.

(*
Tactic Notation "algorithm1_solve1" :=
 unfold algorithm1_post;
 unfold state, lasso, violate_loop_free, safety;
 unfold loop_free, P_state1;
 simpl;
 repeat tryif split then try split else
     tryif right; intros; smt solve then apply by_smt
     else  left; intros; smt solve; apply by_smt.
*)

(* *)

Local Theorem case1 :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  algorithm1_post I T P k -> 
    forall (i : nat), (i <= k) -> prop_k_init_lf I T P i.
Proof.
  intros * H * H0 *.
  unfold algorithm1_post in H.
  destruct H as [H H'].
  apply (le_safety_relation I T P) in H0.
  firstorder.
  auto.
Qed.

Local Lemma case2_1 :
  forall (I : init) (T : trans) (P : prop) (i k : nat),
  i > k -> lasso I T P k -> prop_k_init_lf I T P i.
Proof.
  unfold lasso, prop_k_init_lf in *.
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
  violate_loop_free I T P k -> 
  prop_k_init_lf I T P i.
Proof.
  unfold violate_loop_free, prop_k_init_lf.
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
  algorithm1_post I T P k -> 
  forall (i : nat), (i > k) -> prop_k_init_lf I T P i.
Proof.
  intros * H * H0.
  unfold algorithm1_post in H.
  destruct H as [H H1].
  destruct H.
  - now apply case2_1 with (k := k).
  - now apply case2_2 with (k := k).
Qed.

(**)

Theorem soundness_algorithm1 :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  algorithm1_post I T P k -> 
  forall (i : nat), prop_k_init_lf I T P i.
Proof.
  intros * H *.
  destruct (Nat.le_gt_cases i k) as [H0|H0].
  - revert H0.
    now apply case1.
  - revert H0.
    now apply case2.
Qed.

(* eof *)