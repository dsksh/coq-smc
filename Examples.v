Require Import Core.


(* ex1: 3-bit register. *)

Definition ex1_I (s : state) : Prop :=
  s = 4%Z.

Definition ex1_T (si sj : state) : Prop :=
  (*((si * 2) mod 8 = sj)%Z.*)
  ((si * 2 + 1) mod 8 = sj)%Z.

Definition ex1_P (s : state) : Prop :=
  ~ (s = 0)%Z.


(* ex2: 1-0 sequence. *)

Definition ex2_I (s : state) : Prop :=
  s = 1%Z.

Definition ex2_T (si sj : state) : Prop :=
  sj = (1 - si)%Z.

Definition ex2_P (s : state) : Prop :=
  (*~ (Z.eq s (-1)).*)
  ~ (s = 2)%Z.


(* ex3: nat sequence. *)

Definition ex3_I (s : state) : Prop :=
  s = 0%Z.

Definition ex3_T (si sj : state) : Prop :=
  sj = (si + 1)%Z.

Definition ex3_P (s : state) : Prop :=
  (*~ (Z.eq s (-1)).*)
  (s >= 0)%Z.

(* eof *)