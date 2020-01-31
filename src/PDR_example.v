Require Import Bmc.Core.
Require Import Bmc.PDR.
Require Import Bmc.Example.
Require Import SMTC.Tactic.
Require Import SMTC.Integers.

Definition r1 (i:nat) (s:state) :=
  match i with
  | O => ex1_I s
  | _ => (s >= 1)%Z
  end.

Axiom a1 : forall s:state, (s >= 4)%Z -> ((s*2+1) mod 8 >= 1)%Z.

Axiom a2 : forall s:state, (s >= 1)%Z -> ((s*2+1) mod 8 >= 1)%Z.

Goal pdr_post_t ex1_I ex1_T ex1_P r1 1.
Proof.
  unfold pdr_post_t.
  repeat split; intros.
  - destruct i; simpl.
    + apply H.
    + unfold ex1_I in H.
      omega.
  - unfold ex1_P.
    destruct i; 
    simpl in H; unfold ex1_I in H;
    contradict H;
    rewrite -> H;
    omega.
  - destruct i;
    simpl in *;
    unfold ex1_I in H;
    omega.
  - destruct H0.
    simpl.
    destruct i;
    unfold ex1_T in H1;
    rewrite <- H1;
    simpl in H0; unfold ex1_I in H0.
    + apply a1. omega.
    + apply a2. omega.
  - simpl in *. apply H.
  - simpl in *. apply H.
Qed.