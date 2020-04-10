Require Export Coq.Logic.Classical_Prop.

Lemma not_and_imply3 :
  forall (p1 p2 p3:Prop), 
  ~(p1 /\ p2 /\ ~p3) <-> (p1 /\ p2 -> p3).
Proof.
  intros. tauto.
Qed.

Lemma and_imply_not_and3 :
  forall (p1 p2 p3:Prop), 
  (p1 /\ p2 -> p3) <-> ~(p1 /\ p2 /\ ~p3).
Proof.
  intros. tauto.
Qed.

Lemma imply_not_and3 :
  forall (p1 p2 p3:Prop), 
  (p1 -> p2 -> p3) <-> ~(p1 /\ p2 /\ ~p3).
Proof.
  intros. tauto.
Qed.

Lemma not_and_or3 :
  forall (p1 p2 p3:Prop), 
  ~(p1 /\ p2 /\ p3) <-> (~p1 \/ ~p2 \/ ~p3).
Proof.
  intros. tauto.
Qed.

Lemma not_or_and3 :
  forall (p1 p2 p3:Prop), 
  ~(p1 \/ p2 \/ p3) <-> (~p1 /\ ~p2 /\ ~p3).
Proof.
  intros. tauto.
Qed.

Lemma and_imply_premise :
  forall (p1 p2 p3:Prop),
  (p1 /\ p2 -> p3) <-> (p1 -> p2 -> p3).
Proof.
  intros. tauto.
Qed.

Lemma not_ntq_not_pq :
  forall (p q:Prop),
    ~(p /\ True /\ q) <-> ~(p /\ q).
Proof.
  firstorder.
Qed.

Lemma not_and_or' :
  forall (p q:Prop), ~(p /\ ~q) <-> (~p \/ q).
Proof.
  intros. tauto.
Qed.

(* eof *)