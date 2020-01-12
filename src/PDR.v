Require Export Bmc.Core.
Require Import Omega.

Open Scope nat_scope.

Definition sprop : Type := state -> Prop.
Definition spseq : Type := nat -> state -> Prop.


Definition pdr_post_t (I:init) (T:trans) (P:prop) (r:spseq) (k:nat) : Prop :=
  (*(forall s, I s <-> r 0 s) /\*)
  (forall i s, I s -> r i s) /\
  (forall i s, r i s -> P s) /\
  (forall i s, r i s -> r (i+1) s) /\
  (forall i s s', i <= k+1 -> r i s /\ T s s' -> r (i+1) s') /\
  (forall s, r k s <-> r (k+1) s).

Lemma pdr_bounded :
  forall (I:init) (T:trans) (P:prop),
  forall r:spseq,
  forall k,
  pdr_post_t I T P r k ->
  forall i, i <= k+1 -> prop_k_init' I T P i.
Proof.
  unfold pdr_post_t, prop_k_init'.
  intros * PC' * H.
  do 4 destruct PC' as [?PC PC'].
  intros * I0 T0.
  apply PC0 with (i:=i).
  induction i.
  - apply PC. apply I0.
  - rewrite <- Nat.add_1_r in T0.
    apply split_path in T0. destruct T0 as [T0 T1].
    unfold path in T1. destruct T1 as [_ T1].
    assert (i <= k+1) as H0 by omega.
    assert (r i ss.[i]) as H1 by auto.
    rewrite <- Nat.add_1_r.
    apply PC2 with (s:=ss.[i+0]) (s':=ss.[i+1]). omega.
    split.
    + rewrite -> Nat.add_0_r. apply H1.
    + apply T1.
Qed.

Lemma pdr_bounded_r :
  forall (I:init) (T:trans) (P:prop),
  forall r:spseq,
  forall k,
  pdr_post_t I T P r k ->
  forall i, i <= k+1 -> prop_k_init' I T (r i) i.
Proof.
  unfold pdr_post_t, prop_k_init'.
  intros * PC' * H * I0 T0.
  do 4 destruct PC' as [?PC PC'].
  induction i.
  - apply PC. apply I0.
  - rewrite <- Nat.add_1_r in T0.
    apply split_path in T0. destruct T0 as [T0 T1].
    unfold path in T1. destruct T1 as [_ T1].
    assert (r i ss.[i]) as H1 by firstorder.
    rewrite <- Nat.add_1_r.
    apply PC2 with (s:=ss.[i]) (s':=ss.[i+1]). omega.
    split.
    + apply H1.
    + rewrite -> Nat.add_0_r in T1. apply T1.
Qed.

Lemma pdr_unbounded :
  forall (I:init) (T:trans) (P:prop),
  forall r:spseq,
  forall i k,
  pdr_post_t I T P r k ->
  i > k+1 -> prop_k_init' I T P i.
Proof.
  intros * PC' H.
  assert (pdr_post_t I T P r k) as PC'' by auto.
  unfold pdr_post_t in PC''.
  do 4 destruct PC'' as [?PC PC''].
  unfold prop_k_init'.
  intros * I0 T0.
  apply PC0 with (i:=k+1).
  clear PC PC0 PC1 PC2 PC''.

  revert T0; revert I0; revert ss.
  revert H; revert PC'; revert k.

  induction i; intros;
    unfold pdr_post_t in PC'; 
    do 4 destruct PC' as [?PC PC'] in PC'.
  - contradict H. omega.
  - destruct (Nat.le_gt_cases i k) as [H1|H1];
      rewrite <- Nat.add_1_r in T0;
      apply split_path in T0; destruct T0 as [T0 T1];
      apply skipn_path in T1.
    + assert (i=k) as H2. omega.
      replace (S i) with (i+1) by omega.
      rewrite <- skipn_nth.
      rewrite -> H2.
      apply PC2 with (i:=k) (s:=(skipn k ss).[0]) (s':=(skipn k ss).[1]). omega.
      split.
      { rewrite -> skipn_nth.
        rewrite -> Nat.add_0_r.
        revert T0; revert I0.
        clear T1 IHi. revert ss.
        rewrite -> H2.
        fold (prop_k_init' I T (r k) k).
        apply pdr_bounded_r with (P:=P) (r:=r) (k:=k).
        { firstorder. }
        { omega. } }
      { rewrite <- H2. apply T1. }
    + destruct (Nat.le_gt_cases i (k+1)) as [H0|H0].
      { assert (i=k+1) as H2. omega.
        replace (S i) with (i+1) by omega.
        rewrite <- skipn_nth.
        rewrite -> H2.
        apply PC2 with (i:=k) (s:=(skipn (k+1) ss).[0]) (s':=(skipn (k+1) ss).[1]). omega.
        split.
        { rewrite -> skipn_nth.
          apply PC'.
          rewrite -> Nat.add_0_r.
          revert T0; revert I0.
          clear T1 IHi; revert ss.
          rewrite -> H2.
          fold (prop_k_init' I T (r (k+1)) (k+1)).
          apply pdr_bounded_r with (P:=P) (r:=r) (k:=k).
          { firstorder. }
          { omega. } }
        { rewrite <- H2. apply T1. } }
      { assert (pdr_post_t I T P r k) as H2 by firstorder.
        apply IHi with (ss:=ss) in H2.
        replace (S i) with (i+1) by omega.
        rewrite <- skipn_nth.
        apply PC2 with (i:=k) (s:=(skipn i ss).[0]) (s':=(skipn i ss).[1]). omega.
        split.
        { rewrite -> skipn_nth.
          assert (r (k+1) ss.[i]).
          apply H2. apply PC'. 
          replace (i+0) with i by auto. apply H2. }
        { apply T1. }
        apply H0.
        apply I0.
        apply T0. }
Qed.

Theorem pdr_soundness_t :
  forall (I:init) (T:trans) (P:prop) (k:nat),
  forall r:spseq,
  pdr_post_t I T P r k ->
  forall i, prop_k_init' I T P i.
Proof.
  intros.
  destruct (Nat.le_gt_cases i (k+1)).
  - apply pdr_bounded with (r:=r) (k:=k).
    apply H. apply H0.
  - apply pdr_unbounded with (r:=r) (k:=k).
    apply H. apply H0.
Qed.

(**)

(*
Definition pdr_post_f' (I:init) (T:trans) (P:prop) (f1:sprop) : Prop :=
  (exists ss, I ss.[0] /\ ~P ss.[0]) \/
  (exists ss, I ss.[0] /\ T ss.[0] ss.[1] /\ ~P ss.[1]) \/
  (exists ss, (f1 ss.[1] /\ T ss.[1] ss.[2] /\ ~P ss.[2]) /\
    I ss.[0] /\ T ss.[0] ss.[1] /\ ss.[0] <> ss.[1]).

Theorem pdr_soundness_f' :
  forall (I:init) (T:trans) (P:prop),
  forall r1:sprop,
  ( forall (i:nat) (ss:sseq), 
    ~(I ss.[0] /\ path T ss 0 i /\ ~P ss.[i]) ) ->
      ~(pdr_post_f' I T P r1).
Proof.
  intros * H.
  unfold pdr_post_f'.
  rewrite -> not_or_and3.
  assert (forall p q r, ((p /\ p) /\ (q /\ r)) -> (p /\ q /\ r)) as A by tauto.
  apply A; clear A.
  split; split;
  unfold not at 1;
  intros H0;
  destruct H0 as [ss];
  assert (~(I ss.[0] /\ path T ss 0 0 /\ ~P ss.[0])) as H1 by apply H;
  contradict H1.
  - firstorder.
  - firstorder.
  - assert (~(I ss.[0] /\ path T ss 0 1 /\ ~P ss.[1])) as H2 by apply H.
    contradict H2.
    firstorder.
  - assert (~(I ss.[0] /\ path T ss 0 2 /\ ~P ss.[2])) as H2 by apply H.
    contradict H2.
    firstorder.
Qed.
*)

(**)

Fixpoint spseq_sseq (I:init) (T:trans) (r:spseq) (ss:sseq) (i:nat) :=
  match i with
  | O => I ss.[0]
  | S i => spseq_sseq I T r ss i /\ r i ss.[i] /\ T ss.[i] ss.[i+1]
  end.

(*
Lemma spseq_sseq_path :
  forall (I:init) (T:trans) (P:prop),
  forall r:spseq,
  forall ss: sseq,
  forall i, spseq_sseq I T r ss i -> I ss.[0] /\ path T ss 0 i.
Proof.
  induction i.
  - firstorder.
  - unfold spseq_sseq; fold spseq_sseq.
    unfold path; fold path.
    split.
    + apply IHi; apply H.
    + split.
      { apply IHi; apply H. }
      { do 2 rewrite -> Nat.add_0_l.
        rewrite <- Nat.add_1_r.
        apply H. }
Qed.
*)

(*
Definition pdr_post_f (I:init) (T:trans) (P:prop) (r:spseq) : Prop :=
  (exists ss, I ss.[0] /\ ~P ss.[0]) \/
  (exists ss, I ss.[0] /\ T ss.[0] ss.[1] /\ ~P ss.[1]) \/
  ( (*(forall s, I s <-> r 0 s) /\
    (forall i s, I s -> r i s) /\
    (forall i s, r i s -> P s) /\
    (forall i s, r i s -> r (i+1) s) /\*)
    (exists (i:nat) ss,
      r i ss.[i] /\ T ss.[i] ss.[i+1] /\ ~P ss.[i+1] /\
      spseq_sseq I T r ss i) ).

Theorem pdr_soundness_f :
  forall (I:init) (T:trans) (P:prop),
  forall r:spseq,
  pdr_post_f I T P r ->
    ~(forall (i:nat) (ss:sseq), 
      ~(I ss.[0] /\ path T ss 0 i /\ ~P ss.[i])).
Proof.
  intros * H.
  contradict H.
  unfold pdr_post_f.
  rewrite -> not_or_and3.
  assert (forall p q r, ((p /\ q) /\ r) -> (p /\ q /\ r)) as A by tauto.
  apply A; clear A.
  split.
  - split;
    unfold not at 1;
    intros H0;
    destruct H0 as [ss];
    assert (~(I ss.[0] /\ path T ss 0 0 /\ ~P ss.[0])) as H1 by apply H;
    contradict H1.
    + firstorder.
    + firstorder.

  - unfold not at 1.
    intros.
    (*do 1 destruct H0 as [?H H0].*)
    destruct H0 as [i].
    destruct H0 as [ss].

    assert (~(I ss.[0] /\ path T ss 0 (i+1) /\ ~P ss.[i+1])) by apply H.
    contradict H1.

    do 3 destruct H0 as [?H H0].
    assert (spseq_sseq I T r ss i) by apply H0.
    apply spseq_sseq_path in H4.
    rewrite -> Nat.add_1_r at 1.
    unfold path; fold path.
    do 2 rewrite -> Nat.add_0_l.
    rewrite <- Nat.add_1_r at 1.
    firstorder.
    auto.
Qed.
*)

(**)

Lemma spseq_sseq_path' :
  forall (I:init) (T:trans) (P:prop),
  forall r:spseq,
  forall ss: sseq,
  (*(forall s, I s <-> r 0 s) ->*)
  forall k, spseq_sseq I T r ss k -> 
    I ss.[0] /\ forall i, i < k -> path T ss 0 (i+1) /\ r i ss.[i].
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
        do 2 rewrite -> Nat.add_0_l.
        assert (k = 0) by omega.
        rewrite -> H5 in H1.
        rewrite -> H5 in H.
        rewrite -> Nat.add_0_l in H.
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
            assert (S i+1=S (i+1)) by omega.
            rewrite -> H6.
            unfold path; fold path.
            do 2 rewrite -> Nat.add_0_l.
            rewrite <- H6.
            rewrite -> Nat.add_1_r at 2.
            rewrite -> H5 in H1.
            rewrite -> H5 in H.
            firstorder.
            omega. } } }
Qed.

Lemma spseq_sseq_path'' :
  forall (I:init) (T:trans) (P:prop),
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
      rewrite <- Nat.add_1_r in H2.
      firstorder.
Qed.

(*
Theorem pdr_soundness_f'' :
  forall (I:init) (T:trans) (P:prop),
  forall r:spseq,
  pdr_post_f I T P r ->
    ~(forall (i:nat) (ss:sseq), 
      ~(I ss.[0] /\ path T ss 0 i /\ ~P ss.[i])).
Proof.
  intros * H.
  contradict H.
  unfold pdr_post_f.
  rewrite -> not_or_and3.
  assert (forall p q r, ((p /\ q) /\ r) -> (p /\ q /\ r)) as A by tauto.
  apply A; clear A.
  split.
  - split;
    unfold not at 1;
    intros H0;
    destruct H0 as [ss];
    assert (~(I ss.[0] /\ path T ss 0 0 /\ ~P ss.[0])) as H1 by apply H;
    contradict H1.
    + firstorder.
    + firstorder.

  - unfold not at 1.
    intros.
    (*do 1 destruct H0 as [?H H0].*)
    destruct H0 as [i].
    destruct H0 as [ss].

    do 3 destruct H0 as [?H H0].

    assert (~(I ss.[0] /\ path T ss 0 (i+1) /\ ~P ss.[i+1])) by apply H.
    contradict H4.
    apply spseq_sseq_path' in H0.
    destruct H0.
    destruct i.
    + split.
      apply H0.
      rewrite -> Nat.add_0_l.
      unfold path.
      rewrite -> Nat.add_0_l.
      firstorder.
    + split.
      apply H0.
      assert (path T ss 0 (i+1) /\ r i ss.[i]).
      apply H4; omega.
      destruct H5.
      split.
      assert (S i+1 = S (i+1)) by omega.
      rewrite -> H7.
      unfold path; fold path.
      split.
      apply H5.
      do 2 rewrite -> Nat.add_0_l.
      rewrite <- H7.
      rewrite -> Nat.add_1_r.
      apply H2.
      apply H3.
    + auto.
Qed.
*)

Definition pdr_post_f'' (I:init) (T:trans) (P:prop) : Prop :=
  ~(forall ss, ~(I ss.[0] /\ ~P ss.[0])) \/
  ~(forall ss, ~(I ss.[0] /\ T ss.[0] ss.[1] /\ ~P ss.[1])) \/
  (*(forall s, I s -> P s) ->*)
  ~(forall (i:nat) (r:spseq) (ss:sseq),
    ~( r i ss.[i] /\ T ss.[i] ss.[i+1] /\ ~P ss.[i+1] /\
       spseq_sseq I T r ss i ) ).

Theorem pdr_soundness_f1 :
  forall (I:init) (T:trans) (P:prop),
  forall r:spseq,
  pdr_post_f'' I T P ->
    ~(forall (i:nat) (ss:sseq), 
      ~(I ss.[0] /\ path T ss 0 i /\ ~P ss.[i])).
Proof.
  unfold not at 1.
  intros.
  unfold pdr_post_f'' in H.
  apply not_and_or3 in H.
  contradict H.
  split.
  { intros.
    assert (~ (I ss.[0] /\ path T ss 0 0 /\ ~ P ss.[0])) by apply H0.
    firstorder. }
  split.
  { intros.
    assert (~ (I ss.[0] /\ path T ss 0 1 /\ ~ P ss.[1])) by apply H0.
    firstorder. }
  intros.
  assert (~ (I (ss) .[ 0] /\ path T ss 0 (i+1) /\ ~ P ss.[i+1])) by apply H0.
  contradict H.
  do 3 destruct H as [?H H] in H.
  apply spseq_sseq_path' in H.
  destruct H.
  destruct i.
  - split.
    apply H.
    rewrite -> Nat.add_0_l.
    unfold path.
    rewrite -> Nat.add_0_l.
    firstorder.
  - split.
    apply H.
    assert (path T ss 0 (i+1) /\ r0 i ss.[i]).
    apply H4; omega.
    destruct H5.
    split.
    assert (S i+1 = S (i+1)) by omega.
    rewrite -> H7.
    unfold path; fold path.
    split.
    apply H5.
    do 2 rewrite -> Nat.add_0_l.
    rewrite <- H7.
    rewrite -> Nat.add_1_r.
    apply H2.
    apply H3.
  - auto.
Qed.

Definition of_sseq (ss:sseq) (i:nat) (s:state) : Prop :=
  ss.[i] = s.

Theorem pdr_completeness_f :
  forall (I:init) (T:trans) (P:prop),
  ~(forall (i:nat) (ss:sseq), 
    ~(I ss.[0] /\ path T ss 0 (i+1) /\ ~P ss.[i+1])) ->
    pdr_post_f'' I T P.
Proof.
  unfold pdr_post_f''.
  intros.
  apply not_and_or3.
  contradict H.
  do 2 destruct H as [?H' H].
  intros.
  remember (of_sseq ss) as r.
  assert (
    ~( r i (ss) .[ i] /\
       T (ss) .[ i] (ss) .[ i + 1] /\
       ~ P (ss) .[ i + 1] /\ spseq_sseq I T r ss i )
  ) as H1 by apply H.
  contradict H1.
  (*split.
  { rewrite -> Heqr.
    unfold init_spseq.
    firstorder. }
  split.
  { intros.
    rewrite -> Heqr.
    destruct i0; unfold init_spseq.
    - apply H2.
    - apply H0. apply H2. }
  split.
  { intros.
    rewrite -> Heqr in H2.
    destruct i0; unfold init_spseq in H2.
    - apply H0. apply H2.
    - apply H2. }
  split.
  { intros.
    rewrite -> Heqr.
    rewrite -> Nat.add_1_r.
    rewrite -> Heqr in H2.
    destruct i0; unfold init_spseq; unfold init_spseq in H2.
    - apply H0. apply H2.
    - apply H2. }*)
  split.
  { rewrite -> Heqr.
    unfold of_sseq.
    reflexivity. }
  split.
  { rewrite -> Nat.add_1_r in H1.
    unfold path in H1; fold path in H1.
    do 2 rewrite -> Nat.add_0_l in H1.
    rewrite <- Nat.add_1_r in H1.
    apply H1. }
  split.
  { apply H1. }
  { apply spseq_sseq_path''.
    auto.
    split.
    { apply H1. }
    { intros.
      split.
      { remember (i - i0) as j.
        assert (i+1=i0+1+j) by omega.
        rewrite -> H2 in H1.
        do 2 destruct H1 as [?H H1] in H1.
        apply split_path in H4; destruct H4.
        apply H4. }
      { rewrite -> Heqr.
        unfold of_sseq.
        reflexivity. } } }
Qed.

(* eof *)