Require Import common.
Require Import Omega.

Set SMT Solver "z3".
Set SMT Debug.


Definition Sheeran_method1 (I : init) (T : trans) (P : prop) (size k: nat) : Prop :=
  ((lasso I T P size k) \/
   (violate_loop_free I T P size k)) /\ safety I T P k.

(*
Tactic Notation "Sheeran_smt_solve1" :=
 unfold Sheeran_method1;
 unfold state, lasso, violate_loop_free, safety;
 unfold loop_free, P_state1;
 simpl;
 repeat tryif split then try split else
     tryif right; intros; smt solve then apply by_smt
     else  left; intros; smt solve; apply by_smt.
*)

(*Example Sheeran_method1_test1 :
  Sheeran_method1 ex_I ex_T ex_P 3 4.
Proof.
  unfold ex_I, ex_T, ex_P.
  unfold Sheeran_method1, lasso, violate_loop_free, safety;
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

Theorem Sheeran_method_soundness_case1 :
  forall (I : init) (T : trans) (P : prop) (size k : nat),
  Sheeran_method1 I T P size k -> 
    (forall (i : nat), (i <= k) -> P_state2 I T P size i).
Proof.
  intros.
  unfold Sheeran_method1 in H.
  destruct H.
  apply (le_safety_relation I T P) in H0.
  firstorder.
  auto.
Qed.


Lemma case2_1 :
  forall (I : init) (T : trans) (P : prop) (size i k : nat),
  i > k -> lasso I T P size k -> P_state2 I T P size i.
Proof.
  unfold lasso, P_state2 in *.
  intros.
  apply neg_false.
  split.
  intros.
  destruct H1.
  destruct H2.
  assert (H4 : i = k + (i - k)) by omega.
  rewrite H4 in H2.
  apply divide_loop_free in H2.
  firstorder.
  firstorder.
Qed.

Theorem case2_2' : forall (T : trans) (P : prop) (size i k : nat),
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
  apply no_loop_skipn_relation in H3.
  apply P_skipn_relation with (k:= k) in H2.
  apply path_skipn_relation in H1.
  firstorder.
  omega.
  tauto.
Qed.

Theorem case2_2 : forall (I : init) (T : trans) (P : prop) (size i k : nat),
  i > k -> 
  violate_loop_free I T P size k -> 
  P_state2 I T P size i.
Proof.
  unfold violate_loop_free, P_state2.
  intros.
  apply neg_false.
  split.
  intros.
  destruct H1.
  destruct H2.
  assert (i = (i - k) + k) by omega.
  rewrite H4 in H2.
  apply divide_loop_free in H2.
  apply case2_2' with (i := i) (k := k) (ss := ss) in H0.
  firstorder.
  apply H.
  tauto.
Qed.

Theorem Sheeran_method_soundness_case2 :
  forall (I : init) (T : trans) (P : prop) (size k : nat),
  Sheeran_method1 I T P size k -> 
  forall (i : nat), (i > k) -> P_state2 I T P size i.
Proof.
  intros.
  unfold Sheeran_method1 in H.
  destruct H.

  destruct H.
  - now apply case2_1 with (k := k).

  - now apply case2_2 with (k := k).
Qed.

Theorem Sheeran_method_soundness :
  forall (I : init) (T : trans) (P : prop) (size k : nat),
  Sheeran_method1 I T P size k -> 
  forall (i : nat), P_state2 I T P size i.
Proof.
  intros.
  destruct (Nat.le_gt_cases i k).
  - revert H0.
    now apply Sheeran_method_soundness_case1.
  - revert H0.
    now apply Sheeran_method_soundness_case2.
Qed.

(* eof *)