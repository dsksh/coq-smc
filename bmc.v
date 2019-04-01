Require Import common.
Require Import SMTC.Tactic.
Require Import SMTC.Integers.

Set SMT Solver "z3".
Set SMT Debug.


Definition naive_method (I : init) (T : trans) (P : prop) (k : nat) : Prop :=
  forall ss : sseq,
    ~(I ss.[0] /\ path T ss 0 k /\ ~invariance P ss k).


(* ex1: nat sequence. *)

Definition ex_I (s : state) : Prop :=
  s 0 = 0%Z.

Definition ex_T (si sj : state) : Prop :=
  sj 0 = ((si 0%nat) + 1)%Z.

Definition ex_P (s : state) : Prop :=
  (*~ (Z.eq s (-1)).*)
  ((s 0%nat) >= 0)%Z.

(*
(* ex2: 3-bit register. *)

Definition ex_I (s : state) : Prop :=
  s 0 = 4%Z.

Definition ex_T (si sj : state) : Prop :=
  (((si 0%nat) * 2 + 1) mod 8 = (sj 0%nat))%Z.
 
Definition ex_P (s : state) : Prop :=
  ~ ((s 0%nat) = 0)%Z.


(* ex2: 3-bit register version 2. *)

Definition ex_I (s : state) : Prop :=
  s 2 = 1%Z /\ s 1 = 0%Z /\ s 0 = 0%Z.

Definition ex_T (si sj : state) : Prop :=
  sj 2 = 1%Z /\ sj 1 = si 2 /\ sj 0 = si 1.
 
Definition ex_P (s : state) : Prop :=
  ~ (s 2 = 0%Z /\ s 1 = 0%Z /\ s 0 = 0%Z).
*)

(**)

Example naive_method_test1 :
  naive_method ex_I ex_T ex_P 2.
Proof.
  unfold naive_method.
  simpl.
  unfold ex_I; unfold ex_T; unfold ex_P.
  simpl.
  intros.
  unfold state in *.
  smt solve; apply by_smt.
Qed.

(* eof *)