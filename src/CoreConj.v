Require Import Bmc.Core.
Require Export Bmc.Logic.

Definition lasso_fwd_conj (I : prop) (T : trans) (k : nat) : Prop :=
  forall ss : sseq,
  ~(I ss.[0] /\ loop_free T ss 0 k).

Lemma lasso_fwd_conj_eq :
  forall (I:prop) (T:trans) (k:nat),
  lasso_fwd I T k <-> lasso_fwd_conj I T k.
Proof.
  intros *.
  unfold lasso_fwd, lasso_fwd_conj.
  split.
  - intros H *.
    apply or_not_and.
    apply imply_to_or.
    apply H.
  - intros H *.
    specialize (H ss).
    apply not_and_or in H.
    apply or_to_imply.
    apply H.
Qed.


Definition lasso_bwd_conj (T : trans) (P : prop) (k: nat) : Prop :=
  forall ss : sseq,
  ~(loop_free T ss 0 k /\ ~P ss.[k]).

Lemma lasso_bwd_conj_eq :
  forall (T:trans) (P:prop) (k:nat),
  lasso_bwd T P k <-> lasso_bwd_conj T P k.
Proof.
  intros *.
  unfold lasso_bwd, lasso_bwd_conj.
  split.
  - intros H *.
    specialize (H ss).
    apply imply_to_or in H.
    contradict H.
    apply and_not_or.
    split.
    + unfold not.
      intros.
      apply H0.
      apply H.
    + apply H.
  - intros H *.
    specialize (H ss).
    apply or_to_imply.
    apply not_and_or in H.
    firstorder.
    apply NNPP in H.
    right.
    apply H.
Qed.



Definition prop_nth_init_conj (I : prop) (T : trans) (P : prop) (k : nat) : Prop :=
  forall ss : sseq,
  ~(I ss.[0] /\ path T ss 0 k /\ ~P ss.[k]).

Lemma prop_nth_init_conj_eq :
  forall (I:prop) (T:trans) (P:prop) (k:nat),
  prop_nth_init I T P k <-> prop_nth_init_conj I T P k.
Proof.
  intros *.
  unfold prop_nth_init, prop_nth_init_conj.
  split.
  - intros H *.
    apply not_and_imply3.
    apply and_imply_premise.
    apply H.
  - intros H ss.
    apply and_imply_premise.
    apply not_and_imply3.
    apply H.
Qed.


Fixpoint safety_nth_conj (I : prop) (T : trans) (P : prop) (k : nat) : Prop :=
  match k with
  | O => prop_nth_init_conj I T P k
  | S k' => safety_nth_conj I T P k' /\ prop_nth_init_conj I T P k
  end.


Lemma safety_nth_conj_eq :
  forall (I:prop) (T:trans) (P:prop) (k:nat),
  safety_nth I T P k <-> safety_nth_conj I T P k.
Proof.
  intros *.
  induction k.
  - unfold safety_nth, safety_nth_conj.
    apply prop_nth_init_conj_eq.
  - simpl.
    rewrite -> IHk.
    rewrite -> prop_nth_init_conj_eq.
    tauto.
Qed.

(* eof *)