Require Import common.
Require Import Omega.


Definition algorithm1_post (I : init) (T : trans) (P : prop) (size k: nat) : Prop :=
  ((lasso I T P size k) \/
   (violate_loop_free I T P size k)) /\ safety_k I T P k.

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

(*Example algorithm1_test1 :
  Sheeran_method1 ex_I ex_T ex_P 3 4.
Proof.
  unfold ex_I, ex_T, ex_P.
  unfold algorithm1_post, lasso, violate_loop_free, safety;
  split;
  unfold loop_free, P_state1;
  unfold state;
  simpl;
  unfold neq_state.

  (right; intros; smt solve; apply by_smt) ||
  (left; intros; smt solve; apply by_smt).

  repeat tryif split then split
    else smt solve; apply by_smt.
Qed.
*)

(* *)

Local Theorem case1 :
  forall (I : init) (T : trans) (P : prop) (size k : nat),
  algorithm1_post I T P size k -> 
    (forall (i : nat), (i <= k) -> safety_k_init_lf I T P size i).
Proof.
  intros.
  unfold algorithm1_post in H.
  destruct H.
  apply (le_safety_relation I T P) in H0.
  firstorder.
  auto.
Qed.


Local Lemma case2_1 :
  forall (I : init) (T : trans) (P : prop) (size i k : nat),
  i > k -> lasso I T P size k -> safety_k_init_lf I T P size i.
Proof.
  unfold lasso, safety_k_init_lf in *.
  intros.
  apply neg_false.
  split.
  intros.
  destruct H1.
  destruct H2.
  assert (H4 : i = k + (i - k)) by omega.
  rewrite H4 in H2.
  apply split_loop_free in H2.
  firstorder.
  firstorder.
Qed.

Local Lemma case2_2' : forall (T : trans) (P : prop) (size i k : nat),
  i > k -> 
  (forall ss : sseq, ~ (loop_free T ss size 0 k /\ ~ P ss.[k])) -> 
  forall ss : sseq, ~ (loop_free T ss size (i-k) k /\ ~ P ss.[i]).
Proof.
  intros.
  apply neg_false.
  split.
  unfold loop_free in *.
  intros.
  destruct H1.
  destruct H1.
  apply no_loop_skipn in H3.
  apply prop_skipn with (k:= k) in H2.
  apply path_skipn in H1.
  firstorder.
  omega.
  tauto.
Qed.

Local Lemma case2_2 : forall (I : init) (T : trans) (P : prop) (size i k : nat),
  i > k -> 
  violate_loop_free I T P size k -> 
  safety_k_init_lf I T P size i.
Proof.
  unfold violate_loop_free, safety_k_init_lf.
  intros.
  apply neg_false.
  split.
  intros.
  destruct H1.
  destruct H2.
  assert (i = (i - k) + k) by omega.
  rewrite H4 in H2.
  apply split_loop_free in H2.
  apply case2_2' with (i := i) (k := k) (ss := ss) in H0.
  firstorder.
  apply H.
  tauto.
Qed.

Local Lemma case2 :
  forall (I : init) (T : trans) (P : prop) (size k : nat),
  algorithm1_post I T P size k -> 
  forall (i : nat), (i > k) -> safety_k_init_lf I T P size i.
Proof.
  intros.
  unfold algorithm1_post in H.
  destruct H.

  destruct H.
  - now apply case2_1 with (k := k).

  - now apply case2_2 with (k := k).
Qed.

(**)

Theorem soundness_algorithm1 :
  forall (I : init) (T : trans) (P : prop) (size k : nat),
  algorithm1_post I T P size k -> 
  forall (i : nat), safety_k_init_lf I T P size i.
Proof.
  intros.
  destruct (Nat.le_gt_cases i k).
  - revert H0.
    now apply case1.
  - revert H0.
    now apply case2.
Qed.

(* eof *)