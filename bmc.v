Require Import Coq.Strings.String.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Export Coq.fourier.Fourier.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.omega.Omega.
Require Import Compare_dec.
Require Export Coq.Lists.List.
Require Export Arith.
Require Export Arith.EqNat. 
Require Import SMTC.Tactic.
Require Import SMTC.Integers.

Open Scope string_scope.

Set SMT Solver "z3".
Set SMT Debug.

Local Open Scope nat_scope.
Local Axiom by_smt : forall P : Prop, P.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(*
Definition state : Type := nat -> Z.
Definition ss : Type := nat -> nat -> state.
Definition sub_trans : Type := state -> state -> state -> state -> Prop.
Definition sub_init : Type := state -> state -> Prop.
Definition trans : Type :=  (nat -> state) -> (nat -> state) -> Prop.
Definition init : Type := (nat -> state) -> Prop.
Definition property : Type := (nat -> state) -> Prop.*)

Set Implicit Arguments.

Definition state : Type :=  Z.
Definition default := 99999%Z.

Definition init : Type := state -> Prop.
Definition trans : Type := state -> state -> Prop.
Definition property : Type := state -> Prop.

Fixpoint ss A (f : list A -> init -> trans -> property -> nat -> Prop)
         (l : list A) (I : init) (T : trans) (P : property)
         (n : nat) : Prop :=
  match n with
  | 0 => forall s0 : A, f (l++[s0]) I T P (length l)
  | S n' => forall s0 : A, ss f (l++[s0]) I T P n'
  end.

Fixpoint path (l : list state) (T : trans) (len : nat) : Prop :=
  match len with
  | O => True
  | S O => T (nth 0 l default) (nth 1 l default)
  | S len' => path l T len' /\ T (nth len' l default) (nth len l default)
  end.


Fixpoint violate_P (l : list state) (P : property) (k : nat) : Prop :=
  match k with
  | O =>  P (nth 0 l default)
  | S k' => violate_P l P k' /\  P (nth k l default)
  end.

Definition Naive_method_body (l : list state) (I : init)
           (T : trans) (P : property) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ path l T k /\ ~ violate_P l P k).

Definition Naive_method (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  ss Naive_method_body [] I T P k.

Module test1.
  Local Open Scope Z_scope.
  
  Definition ex_I (s : state) : Prop :=
    s = 0%Z.

  Definition ex_T (si sj : state) : Prop :=
    sj = (si + 1)%Z.
 
  Definition ex_P (s : state) : Prop :=
    ~ (s = -1)%Z.

  Example naive_method_test1 :
    Naive_method ex_I ex_T ex_P 5.
  Proof.
    unfold Naive_method; unfold Naive_method_body.
    simpl.
    unfold ex_I; unfold ex_T; unfold  ex_P.
    intros.
    unfold state.
    smt solve; apply by_smt.
  Qed.
End test1.


Definition neq_nth_mth(si sj : state) : Prop :=
 ~ (si = sj).

Fixpoint loop_check' (l : list state) (n m : nat) : Prop :=
  match m with
  | O => neq_nth_mth (nth n l default) (nth m l default)
  | S m' => neq_nth_mth (nth n l default) (nth m l default) /\
            loop_check' l n m'
  end.

Fixpoint loop_check (l : list state) (k : nat) : Prop :=
  match k with
  | O => True
  | 1 => loop_check' l 1 0
  | S k' => loop_check' l k k' /\ loop_check l k'
  end.

    
Definition loop_free (l : list state) (T : trans) (k : nat) : Prop :=
  (path l T k /\  loop_check l k). 

Definition lasso (l : list state)
           (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ loop_free l T k).

Definition violate_loop_free (l : list state)
           (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  ~ (loop_free l T k /\ ~ P (nth k l default)).


Definition P_state (l : list state) (I : init) (T : trans)
           (P : property) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ path l T k /\ ~ P (nth k l default)).

Fixpoint safety_by_k (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  match k with
  | O => ss P_state [] I T P 0
  | S k' => safety_by_k I T P k' /\ ss P_state [] I T P k
  end.


Definition Sheeran_method1 (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  ((ss lasso [] I T P k) \/
   (ss violate_loop_free [] I T P k)) /\ safety_by_k I T P k.


Lemma case1_t1 : forall (i k : nat) (I : init) (T : trans) (P : property),
    (i < k) /\ safety_by_k I T P k -> ss P_state [] I T P i.
Proof.
  intros.
  induction k.
  - easy.
    
  - destruct H.
    destruct (Nat.lt_ge_cases i k).
    + assert (safety_by_k I T P k /\ ss P_state [] I T P k)
        by (destruct k; firstorder; now rewrite <- plus_n_O in *).
      now apply IHk.
    + apply gt_S_le in H.
      assert (i = k) by omega.      
      destruct k; rewrite H2; firstorder.
Qed.

Theorem Proof_Sheeran_method_case1 :
  forall (I : init) (T : trans) (P : property) (k : nat),
    Sheeran_method1 I T P k
    -> (forall (i : nat), (i < k) -> ss P_state [] I T P i).
Proof.
  intros.
  unfold Sheeran_method1 in H.
  destruct H.
  apply case1_t1 with (k := k).
  tauto.
Qed.


Theorem Proof_Sheeran_method_case2 :
  forall (I : init) (T : trans) (P : property) (k : nat),
    Sheeran_method1 I T P k
    -> (forall (i : nat), (i >= k) ->  ss P_state [] I T P i).
Proof. Admitted.

  
Theorem Proof_Sheeran_method :
  forall (I : init) (T : trans) (P : property) (k : nat),
    Sheeran_method1 I T P k
    -> (forall (i : nat), ss P_state [] I T P i).
Proof.
  intros.
  destruct (Nat.lt_ge_cases i k).
  - revert H0.
    apply Proof_Sheeran_method_case1.
    easy.
  - revert H0.
    apply Proof_Sheeran_method_case2.
    easy.
Qed.