Require Export Bmc.Core.
Require Import Omega.

Open Scope nat_scope.

Definition spseq : Type := nat -> prop.


Definition pdr_post_t (I:prop) (T:trans) (P:prop) (r:spseq) (k:nat) : Prop :=
  (forall i s, I s -> r i s) /\
  (forall i s, r i s -> P s) /\
  (forall i s, r i s -> r (S i) s) /\
  (forall i s s', i <= k -> r i s /\ T s s' -> r (S i) s') /\
  (forall s, r k s <-> r (S k) s).

Lemma pdr_bounded_r :
  forall (I:prop) (T:trans) (P:prop),
  forall r:spseq,
  forall k,
  pdr_post_t I T P r k ->
  forall i, i <= k+1 -> prop_nth_init I T (r i) i.
Proof.
  unfold pdr_post_t, prop_nth_init.
  intros * PC' * H * I0 T0.
  do 4 destruct PC' as [?PC PC'].
  induction i.
  - apply PC. apply I0.
  - rewrite <- Nat.add_1_r in T0.
    apply split_path in T0. destruct T0 as [T0 T1].
    unfold path in T1. destruct T1 as [_ T1].
    rewrite -> Nat.add_0_r in T1.
    rewrite -> Nat.add_1_r in T1.
    assert (r i ss.[i]) as H1 by firstorder.
    apply PC2 with (s:=ss.[i]) (s':=ss.[S i]). omega.
    split.
    + apply H1.
    + apply T1.
Qed.

Lemma pdr_bounded :
  forall (I:prop) (T:trans) (P:prop),
  forall r:spseq,
  forall k,
  pdr_post_t I T P r k ->
  forall i, i <= k+1 -> prop_nth_init I T P i.
Proof.
  unfold pdr_post_t, prop_nth_init.
  intros * PC' * H * I0 T0.
  do 4 destruct PC' as [?PC PC'].
  apply PC0 with (i:=i).
  revert I0 T0. revert ss.
  fold (prop_nth_init I T (r i) i).
  apply pdr_bounded_r with (P:=P) (k:=k).
  firstorder.
  apply H.
Qed.

Lemma pdr_unbounded :
  forall (I:prop) (T:trans) (P:prop),
  forall r:spseq,
  forall i k,
  pdr_post_t I T P r k ->
  i > S k -> prop_nth_init I T P i.
Proof.
  intros * PC' H.
  assert (pdr_post_t I T P r k) as PC'' by auto.
  unfold pdr_post_t in PC''.
  do 4 destruct PC'' as [?PC PC''].
  unfold prop_nth_init.
  intros * I0 T0.
  apply PC0 with (i:=S k).
  clear PC PC0 PC1 PC2 PC''.

  revert T0; revert I0; revert ss.
  revert H; revert PC'; revert k.

  induction i; intros;
    unfold pdr_post_t in PC'; 
    do 4 destruct PC' as [?PC PC'] in PC'.
  - contradict H. omega.
  - rewrite <- Nat.add_1_r in T0.
    apply split_path in T0; destruct T0 as [T0 T1].
    apply skipn_path in T1.
    replace (S i) with (i+1) by omega.
    rewrite <- skipn_nth.
    apply PC2 with (i:=k) (s:=(skipn i ss).[0]) (s':=(skipn i ss).[1]).
    auto.

    split.
    + rewrite -> skipn_nth.
      apply PC'.
      rewrite <- Nat.add_1_r.
      rewrite -> Nat.add_0_r.
      clear T1.
      destruct (Nat.le_gt_cases i (k+1)) as [H0|H0].
      { assert (i=k+1) as H2. omega.
        revert T0; revert I0; revert ss.
        rewrite -> H2.
        fold (prop_nth_init I T (r (k+1)) (k+1)).
        rewrite -> Nat.add_1_r.
        apply pdr_bounded_r with (P:=P) (r:=r) (k:=k).
        { firstorder. }
        { omega. } }
      { intros.
        assert (pdr_post_t I T P r k) as H2 by firstorder.
        apply IHi with (ss:=ss) in H2.
        rewrite -> Nat.add_1_r.
        apply H2.
        omega.
        apply I0.
        apply T0. }
  + apply T1.
Qed.

Theorem pdr_soundness_t :
  forall (I:prop) (T:trans) (P:prop) (k:nat),
  forall r:spseq,
  pdr_post_t I T P r k ->
  forall i, prop_nth_init I T P i.
Proof.
  intros.
  destruct (Nat.le_gt_cases i (k+1)).
  - apply pdr_bounded with (r:=r) (k:=k).
    apply H. apply H0.
  - apply pdr_unbounded with (r:=r) (k:=k).
    apply H.
    rewrite <- Nat.add_1_r. apply H0.
Qed.

Theorem pdr_soundness_t1 :
  forall (I:prop) (T:trans) (P:prop),
  ( exists (k:nat) (r:spseq), pdr_post_t I T P r k ) ->
  forall i, prop_nth_init I T P i.
Proof.
  intros * H *.
  destruct H as [k]; destruct H as [r].
  apply pdr_soundness_t with (k:=k) (r:=r).
  apply H.
Qed.

(**)

Fixpoint spseq_sseq (I:prop) (T:trans) (r:spseq) (ss:sseq) (i:nat) :=
  match i with
  | O => I ss.[0]
  | S j => spseq_sseq I T r ss j /\ r j ss.[j] /\ T ss.[j] ss.[i]
  end.

(**)

Lemma spseq_sseq_path' :
  forall (I:prop) (T:trans) (P:prop),
  forall r:spseq,
  forall ss: sseq,
  (*(forall s, I s <-> r 0 s) ->*)
  forall k, spseq_sseq I T r ss k -> 
    I ss.[0] /\ forall i, i < k -> path T ss 0 (S i) /\ r i ss.[i].
Proof.
  induction k.
  - unfold spseq_sseq.
    intros.
    split.
    apply H.
    intros.
    contradict H0. omega.
  - unfold spseq_sseq; fold spseq_sseq.
    unfold path; fold path.
    intros.
    do 2 destruct H as [?H H].
    split.
    + apply IHk in H0. apply H0.
    + destruct (Nat.le_gt_cases k 0).
      { intros.
        assert (i = 0) by omega.
        rewrite -> H4.
        rewrite -> Nat.add_0_l.
        unfold path.
        rewrite -> Nat.add_0_l.
        assert (k = 0) by omega.
        rewrite -> H5 in H1.
        rewrite -> H5 in H.
        (*rewrite -> Nat.add_0_l in H.*)
        firstorder. }
      { intros.
        destruct i.
        { apply IHk with (i:=0) in H0.
          apply H0.
          apply H2. }
        { destruct (Nat.lt_ge_cases (S i) k).
          { apply IHk with (i:=S i) in H0.
            apply H0.
            omega. }
          { assert (k = S i) by omega. 
            apply IHk with (i:=i) in H0.
            (*assert (S i+1=S (S i)) by omega.
            rewrite -> H6.*)
            unfold path; fold path.
            do 2 rewrite -> Nat.add_0_l.
            (*rewrite <- H6.*)
            (*rewrite -> Nat.add_1_r at 2 3.*)
            rewrite -> H5 in H1.
            rewrite -> H5 in H.
            firstorder.
            omega. } } }
Qed.

Lemma spseq_sseq_path'' :
  forall (I:prop) (T:trans) (P:prop),
  forall r:spseq,
  forall ss: sseq,
  (*(forall s, I s <-> r 0 s) ->*)
  forall k,
  I ss.[0] /\ 
  (forall i, i < k -> path T ss 0 (i+1) /\ r i ss.[i]) ->
  spseq_sseq I T r ss k.
Proof.
  induction k.
  - unfold spseq_sseq.
    intros.
    apply H.
  - unfold spseq_sseq; fold spseq_sseq.
    intros.

    split.
    + apply IHk.
      split.
      { apply H. }
      { destruct H.
        intros.
        apply H0. omega. }
    + assert (path T ss 0 (k+1) /\ r k ss.[k]) by (apply H; omega).
      destruct H0.
      rewrite -> Nat.add_1_r in H0.
      unfold path in H0; fold path in H0; destruct H0.
      do 2 rewrite -> Nat.add_0_l in H2.
      (*rewrite <- Nat.add_1_r in H2.*)
      firstorder.
Qed.

(**)

Definition pdr_post_f (I:prop) (T:trans) (P:prop) (k:nat) : Prop :=
  (forall ss, I ss.[0] ->P ss.[0]) /\
  (forall ss, I ss.[0] -> T ss.[0] ss.[1] -> P ss.[1]) /\
  (forall (r:spseq) (ss:sseq),
    r k ss.[k] -> T ss.[k] ss.[S k] -> spseq_sseq I T r ss k -> P ss.[S k] ).

Theorem pdr_soundness_f :
  forall (I:prop) (T:trans) (P:prop),
  (exists k, ~pdr_post_f I T P k) ->
    ~(forall (i:nat), prop_nth_init I T P i).
Proof.
  intros.
  unfold pdr_post_f in H.
  destruct H as [k].
  (*apply or_not_and3 in H.*)
  contradict H.
  repeat split.
  - intros * H0.
    apply H.
    apply H0.
    simpl; auto.
  - intros * H0 H1.
    apply H.
    apply H0.
    simpl.
    split; auto.
  - intros * H0 H1 H2.
    apply spseq_sseq_path' in H2.
    destruct H2.
    apply H.
    apply H2.
    destruct k.
    + simpl.
      split; auto.
    + simpl.
      split.
      assert (k < S k) as A by omega.
      apply H3 in A.
      destruct A as [H4 H5].
      simpl in H4.
      apply H4.
      apply H1.
    + auto.
Qed.

Definition of_sseq (ss:sseq) (i:nat) (s:state) : Prop :=
  ss.[i] = s.

Theorem pdr_completeness_f :
  forall (I:prop) (T:trans) (P:prop),
  ~(forall (i:nat), prop_nth_init I T P i) ->
    (*exists k, ~pdr_post_f I T P k.*)
    ~forall k, pdr_post_f I T P k.
Proof.
  unfold prop_nth_init.
  unfold pdr_post_f.
  intros * H.
  contradict H.
  intros * H2 H3.
  destruct i.
  specialize H with 0.
  apply H; apply H2.
  specialize H with i.
  do 2 destruct H as [?H H].
  remember (of_sseq ss) as r.
  (*assert (~(r i ss.[i] /\ T ss.[i] ss.[i+1] /\ ~P ss.[i+1] /\ spseq_sseq I T r ss i)) by apply H.*)
  apply H with (r:=r).
  - rewrite -> Heqr.
    unfold of_sseq.
    reflexivity.
  - simpl in H3.
    apply H3.
  - apply spseq_sseq_path''.
    auto.
    repeat split.
    + apply H2.
    + assert (i0+(i-i0)=i) as A by omega.
      rewrite <- A in H3; clear A.
      assert (S (i0+(i-i0))=i0+1+(i-i0)) as A by omega.
      rewrite -> A in H3.
      apply split_path in H3.
      apply H3.
    + rewrite -> Heqr.
      unfold of_sseq.
      reflexivity.
Qed.

(* eof *)