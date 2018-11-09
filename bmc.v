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

Definition Naive_method (l : list state) (I : init)
           (T : trans) (P : property) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ path l T k /\ ~ violate_P l P k).



Module test1.
  Local Open Scope Z_scope.
  
  Goal forall x y, x + y = y + x.
  Proof.
    intros.
    smt solve.
  Abort.
  
  Definition ex_I (s : state) : Prop :=
    s = 0%Z.

  Definition ex_T (si sj : state) : Prop :=
    sj = (si + 1)%Z.
 
  Definition ex_P (s : state) : Prop :=
    ~ (s = -1)%Z.

  Example naive_method_test1 :
    ss Naive_method [] ex_I ex_T ex_P 5.
  Proof.
    unfold Naive_method.
    simpl.
    unfold ex_I; unfold ex_T; unfold  ex_P.
    intros.
    unfold state.
    smt solve; apply by_smt.
  Qed.
End test1.









