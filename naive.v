Require Import common.
Require Import Coq.Logic.Classical_Prop.


Definition naive_post (I : init) (T : trans) (P : prop) : Prop :=
  (forall (s:state), ~(I s /\ ~P s)) /\
  (forall (s s':state), ~(P s /\ T s s' /\ ~P s')).

(**)

Lemma not_and_imply3 :
  forall (p1 p2 p3:Prop), 
  ~(p1 /\ p2 /\ ~p3) -> (p1 /\ p2 -> p3).
Proof.
  intros. revert H0.
  apply or_to_imply.
  apply not_and_or in H.
  destruct H.
  - left. apply or_not_and. auto.
  - apply not_and_or in H.
    destruct H.
    + left. apply or_not_and. auto.
    + right. apply NNPP in H. apply H.
Qed.

Lemma imply_to_not_and3 :
  forall (p1 p2 p3:Prop), 
  (p1 /\ p2 -> p3) -> ~(p1 /\ p2 /\ ~p3).
Proof.
  intros.
  apply or_not_and.
  apply imply_to_or in H.
  destruct H. 
  - apply not_and_or in H.
    destruct H. 
    + left. apply H.
    + right. apply or_not_and. auto.
  - right. apply or_not_and. auto.
Qed.

Lemma and_to_imply_premise :
  forall (p1 p2 p3:Prop),
  (p1 /\ p2 -> p3) -> (p1 -> p2 -> p3).
Proof.
  intros.
  apply imply_to_or in H.
  destruct H.
  - apply not_and_or in H.
    firstorder.
  - apply H.
Qed.

Lemma not_ntq_not_pq :
  forall (p q:Prop),
    ~(p /\ True /\ q) -> ~(p /\ q).
Proof.
  firstorder.
Qed.

(**)

Theorem soundness_naive :
  forall (I:init) (T:trans) (P:prop),
  naive_post I T P ->
    forall (i:nat) (ss:sseq), 
    ~(I ss.[0] /\ path T ss 0 i /\ ~P ss.[i]).
Proof.
  intros.
  unfold naive_post in H.
  decompose [and] H.
  induction i.
  - firstorder.
  - apply imply_to_not_and3.
    intros.
    rewrite -> snoc_path in H2.
    decompose [and] H2.
    apply not_and_imply3 in IHi.
    revert H6. revert IHi.
    apply and_to_imply_premise.
    apply not_and_imply3.
    apply H1. firstorder.
Qed.

Theorem completeness_naive_basecase :
  forall (I:init) (T:trans) (P:prop),
  (forall (i:nat) (ss:sseq), 
  ~(I ss.[0] /\ path T ss 0 i /\ ~P ss.[i])) ->
    forall (s:state), ~(I s /\ ~P s).
Proof.
  intros.
  assert (forall (ss:sseq), ~(I ss.[0] /\ path T ss 0 0 /\ ~P ss.[0])) by apply H.
  simpl in H0.
  revert s. apply prop_state_sseq.
  intros.
  apply not_ntq_not_pq.
  apply H0.
Qed.

(* eof *)