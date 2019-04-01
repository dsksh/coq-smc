Require Import common.
Require Import Omega.
Require Import Coq.Logic.Classical_Prop.


(*Fixpoint all_P (P : prop) (ss : sseq) (o num: nat) : Prop :=
  match num with
  | O => True
  | S 0  => P ss.[o]
  | S num' => all_P P ss o num' /\ P ss.[o+num']
  end.
*)

(**)

Definition k_violate_loop_free (I : init) (T : trans)
  (P : prop) (size k: nat) : Prop :=
  forall ss : sseq,
  ~ (loop_free T ss size 0 k /\ safety_k_offset P ss 0 k /\ ~ P ss.[k]).


Definition k_induction (I : init) (T : trans) (P : prop) (size k: nat) : Prop :=
  (lasso I T P size k \/ k_violate_loop_free I T P size k) /\
  safety_k I T P k.

(**)

Lemma lt_safety_relation : forall (i k : nat) (I : init) (T : trans) (P : prop),
  (i < k) -> safety_k I T P k -> safety_k_init I T P i.
Proof.
  intros.
  induction k.
  - easy.
  - destruct (Nat.lt_ge_cases i k).
    + assert (H2 : safety_k I T P k /\ safety_k_init I T P k)
      by (destruct k; firstorder; now rewrite <- plus_n_O in H0).
      now apply (IHk H1). 
    + apply gt_S_le in H.
      assert (i = k) by omega.      
      destruct k; rewrite H2; firstorder.
Qed.

Lemma all_P_skipn_relation : forall (P : prop) (i j : nat),
    forall ss : sseq,
    safety_k_offset P ss j i  -> safety_k_offset P (skipn j ss) 0 i.
Proof.
  intros.
  induction i.
  - auto.

  - assert (H0 : safety_k_offset P (skipn j ss) 0 i /\ P (skipn j ss).[i]
                 -> safety_k_offset P (skipn j ss) 0 (S i)).
    intros.
    destruct i; firstorder.
    apply H0.
    clear H0.
    split.
    apply IHi.
    destruct i; firstorder.
    rewrite skipn_nth.
    destruct i; firstorder.
    auto.
    simpl in *. rewrite <- plus_n_O.
    auto.
Qed.

Lemma shift_violate_loop_free : 
  forall (T : trans) (P : prop) (size i k : nat),
  S k <= i ->
  ( forall ss : sseq,
     ~ ( loop_free T ss size 0 (S k) /\ 
         safety_k_offset P ss 0 (S k) /\ ~ P ss.[S k] )) ->
  forall ss : sseq,
  ~ ( loop_free T ss size (i-k-1) (S k) /\ 
    safety_k_offset P ss (i-k-1) (S k) /\ ~ (P (ss.[i])) ).
Proof.
  intros.
  apply neg_false.
  split.
  unfold loop_free in *.
  intros.
  destruct H1.
  destruct H1.
  destruct H2.
  apply no_loop_skipn in H3.
  apply prop_skipn with (k:= S k) in H4.
  apply path_skipn in H1.
  apply all_P_skipn_relation in H2.
  replace (i - S k) with (i - k - 1) in H4.
  assert (( path T (skipn (i - k - 1) ss) 0 (S k) /\
    no_loop (skipn (i - k - 1) ss) size 0 (S k) ) /\
    safety_k_offset P (skipn (i - k - 1) ss) 0 (S k) /\ 
    ~ P (skipn (i - k - 1) ss) .[ S k] )
    by firstorder.
  apply H0 in H5.
  contradiction.
  omega.
  omega.
  tauto.
Qed.

Lemma divide_hd_all_P : forall (P : prop) (ss : sseq) (i j : nat),
  P ss.[i] /\ safety_k_offset P ss (S i) j <->
  safety_k_offset P ss i (S j).
Proof.
  destruct j.
  - unfold safety_k_offset. simpl.
    tauto.
  - induction j. simpl. 
    rewrite Nat.add_1_r.
    tauto.
    firstorder; now rewrite Nat.add_succ_comm in *.
Qed.

Lemma lt_wf_ind_incl_P : 
  forall (I : init) (T : trans) (P : prop) (ss : sseq)
    (i k size : nat),
  k < i -> I ss.[0] /\ loop_free T ss size 0 i ->
  (forall m : nat, m < i -> I ss.[0] /\ 
     loop_free T ss size 0 m -> P ss.[m]) -> 
  safety_k_offset P ss (i-k-1) (S k).
Proof.
  intros.
  induction k.
  - simpl in *.
    rewrite <- minus_n_O in *.
    apply H1.
    omega.
    auto.
    destruct i. firstorder.
    replace (S i - 1) with i.
    destruct i; firstorder. omega.
  - apply divide_hd_all_P.
    replace (S (i - S k - 1)) with (i - k - 1).
    split.
    apply H1.
    omega.
    split.
    tauto.
    destruct H0.
    unfold loop_free in *.
    assert (H3 : i = (i - S k - 1) + (k + 2)) by omega.
    rewrite H3 in H2.
    destruct H2.
    apply split_path in H2.
    apply split_no_loop in H4.
    tauto.
    apply IHk.
    omega.
    omega.
Qed.

Lemma univ_init_prop : forall (P : prop) (i : nat) (ss : sseq),
  (forall ss',  ~~ P ss'.[ 0]) -> ~~ P ss.[i].
Proof.
  intros.
  assert (H1 : forall A : Prop, A -> ~~ A) by tauto.
  apply H1.
  
  assert (H2 : i = i + 0) by omega.
  rewrite H2.
  rewrite <- skipn_nth.
  apply NNPP.
  auto.
Qed.

(**)

Theorem soundness_k_induction :
  forall (I : init) (T : trans) (P : prop) (size k : nat),
  k_induction I T P size k -> 
  forall (i : nat), safety_k_init_lf I T P size i.
Proof.
  unfold safety_k_init_lf.
  intros.
  assert (H0 : forall A B C : Prop, (A /\ B -> C) <->  ~ (A /\ B /\ ~ C)) by (split; tauto).
  apply H0. 
  intros.

  induction i using lt_wf_ind.
  unfold k_induction in H.
  destruct (Nat.lt_ge_cases i k).
  - apply lt_safety_relation with (I:=I) (T:=T) (P:=P) in H3.
    unfold safety_k_init in H3.
    assert (H4 : ~ (I ss.[0] /\ path T ss 0 i /\ ~ P ss.[i])) by auto.
    clear H3.
    apply <- H0 in H4.
    tauto.
    firstorder.
    tauto.
  - destruct H.
    destruct H.
    + assert (H5 : i = k + (i - k)) by omega.
      rewrite H5 in H1.
      destruct H1.
      apply split_loop_free in H6.
      firstorder.
    + unfold k_violate_loop_free in H.
      destruct k.
      * unfold loop_free in H.
        simpl in *.
        assert (H5 : forall ss, ~~ P ss.[0]) by firstorder.
        apply univ_init_prop with (i:=i) (ss:=ss) in H5.
        tauto.
      * destruct H1.
        assert (H6 : i = (i - k - 1) + (k + 1)) by omega.
        assert (H7 : loop_free T ss size 0 i) by auto.
        rewrite H6 in H5.
        apply split_loop_free in H5.
        destruct H5.
        assert (H9 : k < i) by omega.
        apply shift_violate_loop_free with
          (T:=T) (P:=P) (size:=size) (ss:=ss) in H3.
        apply lt_wf_ind_incl_P with
          (I:=I) (T:=T)(P:=P)(size:=size) (ss:=ss) in H9.
        assert (H10 :loop_free T ss size (i - k - 1) (k + 1) /\
                safety_k_offset P ss (i - k - 1) (S k)) 
          by tauto.
        apply H0 in H3.
        auto.
        rewrite Nat.add_1_r in H8.
        auto.
        auto.
        auto.
        auto.
Qed.

(* eof *)