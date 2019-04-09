Require Export Core.


Definition naive_post (I : init) (T : trans) (P : prop) (k : nat) : Prop :=
  forall ss : sseq,
    ~(I ss.[0] /\ path T ss 0 k /\ ~invariance P ss k).

Definition induction_post (I : init) (T : trans) (P : prop) : Prop :=
  (forall (s:state), ~(I s /\ ~P s)) /\
  (forall (s s':state), ~(P s /\ T s s' /\ ~P s')).

(**)

Theorem soundness_induction :
  forall (I:init) (T:trans) (P:prop),
  induction_post I T P ->
    forall (i:nat) (ss:sseq), 
    ~(I ss.[0] /\ path T ss 0 i /\ ~P ss.[i]).
Proof.
  intros * H *.
  unfold induction_post in H.
  destruct H as [H H0].
  induction i as [|i IHi].
  - firstorder.
  - apply imply_not_and3.
    intros H1 H2.
    rewrite -> snoc_path in H2.
    destruct H2 as [H2 H3].
    rewrite -> Nat.add_0_l in H3.
    apply not_and_imply3 in IHi.
    revert IHi H3.
    apply imply_not_and3.
    apply H0.
    tauto.
Qed.

Theorem completeness_naive :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  ( forall (i:nat) (ss:sseq), 
    ~(I ss.[0] /\ path T ss 0 i /\ ~P ss.[i]) ) ->
      naive_post I T P k.
Proof.
  unfold naive_post.
  intros * H.
  induction k as [|k IHk].
  - apply H with (i:=0).
  - intros.
    assert (A : ~(I (ss).[0] /\ path T ss 0 (S k) /\ ~ P (ss).[S k])) by apply H.
    simpl.
    apply imply_not_and3.
    intros H0 H1.
    destruct H1 as [H1 H2].
    split.
    + revert H0 H1.
      apply imply_not_and3.
      apply IHk.
    + assert (A0 : path T ss 0 (S k)) by (simpl; tauto).
      revert H0 A0.
      apply imply_not_and3.
      apply H.
Qed.

Theorem completeness_naive_basecase :
  forall (I:init) (T:trans) (P:prop),
  ( forall (i:nat) (ss:sseq), 
    ~(I ss.[0] /\ path T ss 0 i /\ ~P ss.[i]) ) ->
      forall (s:state), ~(I s /\ ~P s).
Proof.
  intros * H *.
  assert (forall (ss:sseq), 
    ~(I ss.[0] /\ path T ss 0 0 /\ ~P ss.[0])) as A 
    by apply H.
  simpl in A.
  revert s. apply prop_state_sseq.
  intros ss.
  apply not_ntq_not_pq.
  apply A.
Qed.

(* eof *)