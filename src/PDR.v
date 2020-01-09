Require Export Bmc.Core.
Require Import Omega.

Open Scope nat_scope.

Definition sprop : Type := state -> Prop.
Definition spseq : Type := nat -> state -> Prop.


Definition pdr_post_t (I:init) (T:trans) (P:prop) (f:spseq) (k:nat) : Prop :=
  (forall i s, i <= k+1 -> I s -> f i s) /\
  (forall i s, i <= k+1 -> f i s -> P s) /\
  (forall i s, i <= k+1 -> f i s -> f (i+1) s) /\
  (forall i s s', i <= k+1 -> f i s /\ T s s' -> f (i+1) s') /\
  (forall s, f k s <-> f (k+1) s).

Lemma pdr_bounded' :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  pdr_post_t I T P f 1 ->
  forall s s', I s -> T s s' -> P s'.
Proof.
  unfold pdr_post_t.
  intros * PC3 * I0 T0.
  do 4 destruct PC3 as [?PC PC3].
  apply PC0 with (i:=1); auto.
  rewrite <- Nat.add_1_r.
  apply PC2 with (s:=s); auto.
Qed.

Lemma pdr_bounded'' :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  pdr_post_t I T P f 1 ->
  prop_k_init' I T P 1.
Proof.
  unfold pdr_post_t.
  unfold prop_k_init'.
  unfold path.
  intros * PC3.
  do 4 destruct PC3 as [?PC PC3].
  intros * I0 T0.
  destruct T0 as [_ T0].
  apply PC0 with (i:=1); auto.
  rewrite <- Nat.add_1_r.
  apply PC2 with (i:=0) (s:=ss.[0]) (s':=ss.[0+1]); auto.
Qed.

Lemma pdr_bounded :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  forall k,
  pdr_post_t I T P f k ->
  forall i, i <= k+1 -> prop_k_init' I T P i.
Proof.
  unfold pdr_post_t, prop_k_init'.
  intros * PC3 * H.
  do 4 destruct PC3 as [?PC PC3].
  intros * I0 T0.
  apply PC0 with (i:=i). omega.
  induction i.
  - apply PC. omega. apply I0.
  - rewrite <- Nat.add_1_r in T0.
    apply split_path in T0. destruct T0 as [T0 T1].
    unfold path in T1. destruct T1 as [_ T1].
    assert (i <= k+1) as H0 by omega.
    assert (f i ss.[i]) as H1 by auto.
    rewrite <- Nat.add_1_r.
    apply PC2 with (s:=ss.[i+0]) (s':=ss.[i+1]). omega.
    split.
    + rewrite -> Nat.add_0_r. apply H1.
    + apply T1.
Qed.

Lemma pdr_bound_f :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  forall k,
  pdr_post_t I T P f k ->
  forall i, i <= k+1 -> prop_k_init' I T (f i) i.
Proof.
  unfold pdr_post_t, prop_k_init'.
  intros * PC3 * H * I0 T0.
  do 4 destruct PC3 as [?PC PC3].
  induction i.
  - apply PC. omega. apply I0.
  - rewrite <- Nat.add_1_r in T0.
    apply split_path in T0. destruct T0 as [T0 T1].
    unfold path in T1. destruct T1 as [_ T1].
    assert (f i ss.[i]) as H1 by firstorder.
    rewrite <- Nat.add_1_r.
    apply PC2 with (s:=ss.[i]) (s':=ss.[i+1]). omega.
    split.
    + apply H1.
    + rewrite -> Nat.add_0_r in T1. apply T1.
Qed.

Lemma pdr_unbounded' :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  pdr_post_t I T P f 0 ->
  prop_k_init' I T P 2.
Proof.
  unfold pdr_post_t, prop_k_init'.
  intros * PC3 * I0.
  do 4 destruct PC3 as [?PC PC3].
  rewrite <- Nat.add_1_r.
  rewrite <- skipn_nth.
  intros T0.
  apply split_path in T0; destruct T0 as [T0 T1].
  apply skipn_path in T1.
  unfold path in T1. destruct T1 as [_ T1].
  apply PC0 with (i:=1); auto.
  rewrite <- Nat.add_1_r.
  apply PC2 with (i:=0) (s:=(skipn 1 ss).[0+0]) (s':=(skipn (0+1) ss).[0+1]). omega.
  split.
  - rewrite -> Nat.add_0_r. rewrite -> skipn_nth.
    rewrite -> Nat.add_0_r.
    apply PC3.
    unfold path in T0; destruct T0 as [_ T0].
    rewrite -> Nat.add_1_r. rewrite <- Nat.add_1_r.
    apply PC2 with (i:=0) (s:=ss.[0]) (s':=ss.[0+1]). omega.
    split.
    + apply PC. omega. apply I0.
    + auto.
  - auto.
Qed.

Lemma pdr_unbounded :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  forall i k,
  pdr_post_t I T P f k ->
  i > k+1 -> prop_k_init' I T P i.
Proof.
  intros * PC3 H.
  assert (pdr_post_t I T P f k) as PC3' by auto.
  unfold pdr_post_t in PC3'.
  do 4 destruct PC3' as [?PC PC3'].
  unfold prop_k_init'.
  intros * I0 T0.
  apply PC0 with (i:=k+1). omega.
  clear PC PC0 PC1 PC2 PC3'.

  revert T0; revert I0; revert ss.
  revert H; revert PC3; revert k.

  induction i; intros;
    unfold pdr_post_t in PC3; 
    do 4 destruct PC3 as [?PC PC3] in PC3.
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
        fold (prop_k_init' I T (f k) k).
        apply pdr_bound_f with (P:=P) (f:=f) (k:=k).
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
          apply PC3.
          rewrite -> Nat.add_0_r.
          revert T0; revert I0.
          clear T1 IHi; revert ss.
          rewrite -> H2.
          fold (prop_k_init' I T (f (k+1)) (k+1)).
          apply pdr_bound_f with (P:=P) (f:=f) (k:=k).
          { firstorder. }
          { omega. } }
        { rewrite <- H2. apply T1. } }
      { assert (pdr_post_t I T P f k) as H2 by firstorder.
        apply IHi with (ss:=ss) in H2.
        replace (S i) with (i+1) by omega.
        rewrite <- skipn_nth.
        apply PC2 with (i:=k) (s:=(skipn i ss).[0]) (s':=(skipn i ss).[1]). omega.
        split.
        { rewrite -> skipn_nth.
          assert (f (k+1) ss.[i]).
          apply H2. apply PC3. 
          replace (i+0) with i by auto. apply H2. }
        { apply T1. }
        apply H0.
        apply I0.
        apply T0. }
Qed.

Theorem pdr_soundness :
  forall (I:init) (T:trans) (P:prop) (k:nat),
  forall f:spseq,
  pdr_post_t I T P f k ->
  forall i, prop_k_init' I T P i.
Proof.
  intros.
  destruct (Nat.le_gt_cases i (k+1)).
  - apply pdr_bounded with (f:=f) (k:=k).
    apply H. apply H0.
  - apply pdr_unbounded with (f:=f) (k:=k).
    apply H. apply H0.
Qed.

(**)

Definition pdr_post_f (I:init) (T:trans) (P:prop) (f1:sprop) : Prop :=
  (exists ss, I ss.[0] /\ ~P ss.[0]) \/
  (exists ss, I ss.[0] /\ T ss.[0] ss.[1] /\ ~P ss.[1]) \/
  (exists ss, (f1 ss.[1] /\ T ss.[1] ss.[2] /\ ~P ss.[2]) /\
    I ss.[0] /\ T ss.[0] ss.[1] /\ ss.[0] <> ss.[1]).

Theorem pdr_completeness :
  forall (I:init) (T:trans) (P:prop),
  forall f1:sprop,
  ( forall (i:nat) (ss:sseq), 
    ~(I ss.[0] /\ path T ss 0 i /\ ~P ss.[i]) ) ->
      ~(pdr_post_f I T P f1).
Proof.
  intros * H.
  unfold pdr_post_f.
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

(* eof *)