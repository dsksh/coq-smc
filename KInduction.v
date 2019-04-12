Require Export Core.
Require Import Omega.


Definition k_violate_loop_free (I : init) (T : trans)
  (P : prop) (k: nat) : Prop :=
  forall ss : sseq,
  ~ (loop_free T ss 0 k /\ safety_k_offset P ss 0 k /\ ~ P ss.[k]).


Definition k_induction_post (I : init) (T : trans) (P : prop) (k: nat) : Prop :=
  (lasso I T P k \/ k_violate_loop_free I T P k) /\
  safety_k I T P k.

(**)

Lemma safety_prop_k_init : 
  forall (i k : nat) (I : init) (T : trans) (P : prop),
  (i < k) -> safety_k I T P k -> prop_k_init I T P i.
Proof.
  intros * H H0.
  induction k.
  - easy.
  - destruct (Nat.lt_ge_cases i k) as [H1|H1].
    + assert (safety_k I T P k /\ prop_k_init I T P k) as A
      by (destruct k; firstorder; now rewrite <- plus_n_O in H0).
      now apply (IHk H1). 
    + apply gt_S_le in H.
      assert (i = k) as A by omega.
      destruct k; rewrite A; firstorder.
Qed.

Lemma skipn_safety_k_offset : 
  forall (P : prop) (i j : nat) (ss : sseq),
  safety_k_offset P ss j i -> 
  safety_k_offset P (skipn j ss) 0 i.
Proof.
  intros * H.
  induction i as [|i IHi].
  - auto.
  - assert (safety_k_offset P (skipn j ss) 0 i /\ 
      P (skipn j ss).[i] -> 
      safety_k_offset P (skipn j ss) 0 (S i)) as A.
    { intros H0.
      destruct i; firstorder. }
    apply A; clear A.
    split.
    * apply IHi.
      destruct i; firstorder.
    * rewrite skipn_nth.
      destruct i; firstorder.
Qed.

Lemma shift_violate_loop_free : 
  forall (T : trans) (P : prop) (i k : nat),
  S k <= i ->
  ( forall ss : sseq,
     ~ ( loop_free T ss 0 (S k) /\ 
         safety_k_offset P ss 0 (S k) /\ ~ P ss.[S k] )) ->
  forall ss : sseq,
  ~ ( loop_free T ss (i-k-1) (S k) /\ 
    safety_k_offset P ss (i-k-1) (S k) /\ ~ (P (ss.[i])) ).
Proof.
  intros * H H0 *.
  apply neg_false.
  split.
  - unfold loop_free in *.
    intros H1.
    destruct H1 as [H1 H2].
    destruct H1 as [H1 H1'].
    destruct H2 as [H2 H2'].
    apply skipn_no_loop in H1'.
    apply skipn_prop with (k := S k) in H2'.
    apply skipn_path in H1.
    apply skipn_safety_k_offset in H2.
    replace (i - S k) with (i - k - 1) in H2'.

    assert (( path T (skipn (i - k - 1) ss) 0 (S k) /\
      no_loop (skipn (i - k - 1) ss) 0 (S k) ) /\
      safety_k_offset P (skipn (i - k - 1) ss) 0 (S k) /\ 
      ~ P (skipn (i - k - 1) ss).[S k] ) as A
      by firstorder.

    apply H0 in A.
    contradiction.
    omega.
    omega.
  - tauto.
Qed.

Lemma divide_hd_all_prop : forall (P : prop) (ss : sseq) (i j : nat),
  P ss.[i] /\ safety_k_offset P ss (S i) j <->
  safety_k_offset P ss i (S j).
Proof.
  destruct j.
  - unfold safety_k_offset.
    rewrite -> Nat.add_0_r.
    tauto.
  - induction j as [|j IHj].
    + simpl.
      rewrite Nat.add_0_r.
      rewrite Nat.add_1_r.
      tauto.
    + firstorder; now rewrite Nat.add_succ_comm in *.
Qed.

Lemma lt_wf_ind_incl_prop : 
  forall (I : init) (T : trans) (P : prop) (ss : sseq) (i k : nat),
  k < i -> I ss.[0] /\ loop_free T ss 0 i ->
  ( forall m : nat, m < i -> I ss.[0] /\ 
    loop_free T ss 0 m -> P ss.[m] ) -> 
      safety_k_offset P ss (i-k-1) (S k).
Proof.
  intros * H H0 H1.
  induction k as [|k IHk].
  - unfold safety_k_offset.
    split; auto.
    rewrite -> Nat.sub_0_r.
    rewrite -> Nat.add_0_r.
    apply H1.
    omega.
    destruct i as [|i].
    + firstorder.
    + replace (S i - 1) with i.
      destruct i; firstorder.
      omega.
  - apply divide_hd_all_prop.
    replace (S (i - S k - 1)) with (i - k - 1).
    split.
    + apply H1.
      omega.
      split.
      * tauto.
      * destruct H0 as [H0 H0'].
        unfold loop_free in *.
        assert (i = (i - S k - 1) + (k + 2)) as A by omega.
        rewrite A in H0'.
        destruct H0' as [H2 H3].
        apply split_path in H2.
        apply split_no_loop in H3.
        tauto.
    + apply IHk.
      omega.
    + omega.
Qed.

Lemma univ_init_prop : forall (P : prop) (i : nat) (ss : sseq),
  (forall ss',  ~~ P ss'.[ 0]) -> ~~ P ss.[i].
Proof.
  intros * H.
  assert (forall p : Prop, p -> ~~ p) as A by tauto.
  apply A.
  assert (i = i + 0) as A0 by omega.
  rewrite A0.
  rewrite <- skipn_nth.
  apply NNPP.
  auto.
Qed.

(**)

Theorem soundness_k_induction' :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  k_induction_post I T P k -> 
  forall (i : nat), prop_k_init_lf I T P i.
Proof.
  unfold prop_k_init_lf.
  intros * H *.
  assert (forall A B C : Prop, (A /\ B -> C) <->  ~ (A /\ B /\ ~ C)) as A by (split; tauto).
  apply A.
  intros.

  induction i as [* H1] using lt_wf_ind.
  unfold k_induction_post in H.
  destruct (Nat.lt_ge_cases i k) as [H2|H2].
  - apply safety_prop_k_init with (I:=I) (T:=T) (P:=P) in H2.
    unfold prop_k_init in H2.
    assert (~ (I ss.[0] /\ path T ss 0 i /\ ~ P ss.[i])) as A0 by auto.
    clear H2.
    apply <- A in A0.
    tauto.
    firstorder.
    tauto.
  - destruct H as [H H3].
    destruct H.
    + assert (i = k + (i - k)) as A0 by omega.
      rewrite A0 in H0.
      destruct H0 as [H0 H0'].
      apply split_loop_free in H0'.
      firstorder.
    + unfold k_violate_loop_free in H.
      destruct k.
      * unfold loop_free in H.
        simpl in *.
        assert (forall ss, ~~ P ss.[0]) as A0 by firstorder.
        apply univ_init_prop with (i:=i) (ss:=ss) in A0.
        tauto.
      * destruct H0 as [H0 H0'].
        assert (i = (i - k - 1) + (k + 1)) as A0 by omega.

        assert (loop_free T ss 0 i) as A1 by auto.
        rewrite A0 in A1; clear A0.
        apply split_loop_free in A1.
        destruct A1 as [A1 A1'].
        assert (k < i) as A2 by omega.
        apply shift_violate_loop_free with
          (T:=T) (P:=P) (ss:=ss) in H2.
        apply lt_wf_ind_incl_prop with
          (I:=I) (T:=T) (P:=P) (ss:=ss) in A2.
        apply A in H2.
        auto.
        rewrite Nat.add_1_r in A1'.
        auto.
        auto.
        auto.
        auto.
Qed.

Theorem soundness_k_induction :
  forall (I : init) (T : trans) (P : prop) (k : nat),
  k_induction_post I T P k -> 
  forall (i : nat), prop_k_init I T P i.
Proof.
  intros * H.
  apply safety_lf_path.
  apply soundness_k_induction' with (k := k).
  apply H.
Qed.

(* eof *)