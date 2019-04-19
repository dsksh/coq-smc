Require Export Bmc.Core.


Definition naive_post (I : init) (T : trans) (P : prop) (k : nat) : Prop :=
  (*forall ss : sseq,
  ~(I ss.[0] /\ path T ss 0 k /\ ~invariance P ss k).*)
  safety_k I T P k.

Definition induction_post (I : init) (T : trans) (P : prop) : Prop :=
  (forall (s:state), ~(I s /\ ~P s)) /\
  (forall (s s':state), ~(P s /\ T s s' /\ ~P s')).

(**)

Theorem soundness_naive :
  forall (I:init) (T:trans) (P:prop) (k:nat),
  naive_post I T P k ->
  forall (i:nat) (ss:sseq), i <= k ->
  ~(I ss.[0] /\ path T ss 0 i /\ ~P ss.[i]).
Proof.
  intros * H i ss H0.
  unfold naive_post in H.
  induction k.
  - assert (i = 0) by omega.
    simpl in H.
    unfold prop_k_init in H.
    rewrite -> H1.
    apply H.
  - destruct (Nat.le_gt_cases i k).
    + apply IHk.
      { apply H. }
      { apply H1. }
    + assert (i = S k) by omega.
      destruct k; rewrite H2; firstorder.
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
  - firstorder.
  - simpl.
    split.
    + apply IHk.
    + unfold prop_k_init.
      intros ss.
      firstorder.
Qed.

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
