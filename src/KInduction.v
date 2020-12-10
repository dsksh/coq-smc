Require Export Bmc.Core.
Require Import Omega.


Definition k_ind_step (T : trans)
  (P : prop) (i: nat) : Prop :=
  forall ss : sseq,
  path T ss 0 i -> safety_nth_offset P ss 0 i -> P ss.[i].

Definition k_induction_post (I : prop) (T : trans) (P : prop) (k: nat) : Prop :=
  k_ind_step T P (S k) /\ safety_nth I T P (S k).

(**)

Lemma skipn_safety_nth_offset : 
  forall (P : prop) (i j : nat) (ss : sseq),
  safety_nth_offset P ss j i -> 
  safety_nth_offset P (skipn j ss) 0 i.
Proof.
  intros * H.
  induction i as [|i IHi].
  - auto.
  - assert (safety_nth_offset P (skipn j ss) 0 i /\ 
      P (skipn j ss).[i] -> 
      safety_nth_offset P (skipn j ss) 0 (S i)) as A.
    { intros H0.
      destruct i; firstorder. }
    apply A; clear A.
    split.
    * apply IHi.
      destruct i; firstorder.
    * rewrite skipn_nth.
      destruct i; firstorder.
Qed.

Lemma shift_k_ind_step : 
  forall (T : trans) (P : prop) (i k : nat),
  k < i ->
  ( forall ss : sseq,
     path T ss 0 k -> safety_nth_offset P ss 0 k -> P ss.[k] ) ->
  forall ss : sseq,
  path T ss (i-k) k -> safety_nth_offset P ss (i-k) k -> P ss.[i].
Proof.
  intros.
  apply skipn_path in H1.
  apply skipn_safety_nth_offset in H2.
  assert (i-k+k=i) as A by omega.
  rewrite <- A.
  rewrite <- skipn_nth.
  apply H0.
  firstorder.
  apply H2.
Qed.

Lemma cons_safety_nth_offset : forall (P : prop) (ss : sseq) (i j : nat),
  P ss.[i] /\ safety_nth_offset P ss (S i) j <->
  safety_nth_offset P ss i (S j).
Proof.
  destruct j.
  - unfold safety_nth_offset.
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
  forall (I : prop) (T : trans) (P : prop) (ss : sseq) (i k : nat),
  S k < i -> I ss.[0] /\ path T ss 0 i ->
  ( forall m : nat,
    m < i -> I ss.[0] /\ path T ss 0 m ->
    P ss.[m] ) -> 
      safety_nth_offset P ss (i - S k) (S k).
Proof.
  intros * H H0 H1.
  induction (S k) as [|k' IHk].
  - unfold safety_nth_offset.
    easy.
  - apply cons_safety_nth_offset.
    replace (i - S k') with (i - k' - 1).
    split.
    + apply H1.
      omega.
      split.
      * tauto.
      * destruct H0 as [H0 H0'].
        assert (i = (i - k' - 1) + (k' + 1)) as A by omega.
        rewrite A in H0'.
        apply split_path in H0'.
        tauto.
    + replace (S (i-k'-1)) with (i-k').
      apply IHk.
      omega.
      omega.
    + omega.
Qed.

(**)

Theorem soundness_k_induction :
  forall (I : prop) (T : trans) (P : prop) (k : nat),
  k_induction_post I T P k -> 
  forall (i : nat), prop_nth_init I T P i.
Proof.
  unfold prop_nth_init.
  intros * H *.
  intros H0 H0'.

  induction i as [* H1] using lt_wf_ind.
  unfold k_induction_post in H.

  destruct (Nat.le_gt_cases i (S k)) as [H2|H2].
  - apply bounded_safety with (I:=I) (T:=T) (P:=P) in H2.
    unfold prop_nth_init in H2.
    apply H2.
    apply H0.
    apply H0'.
    simpl in H.
    apply H.
  - destruct H as [H H3].
    unfold k_ind_step in H.
    assert (i = (i - S k) + S k) as A0 by omega.
    assert (path T ss 0 i) as A1 by auto.
    rewrite A0 in A1; clear A0.
    apply split_path in A1.
    destruct A1 as [A1 A1'].
    assert (S k < i) as A2 by omega.
    apply shift_k_ind_step with (T:=T) (P:=P) (ss:=ss) in H2.
    apply H2.
    apply H.
    apply A1'.
    apply lt_wf_ind_incl_prop with (I:=I) (T:=T) (P:=P) (ss:=ss) in A2.
    apply A2.
    auto.
    intros.
    apply H1.
    apply H4.
    apply H5.
Qed.

Theorem soundness_k_induction1 :
  forall (I : prop) (T : trans) (P : prop),
  ( exists k, k_induction_post I T P k ) ->
  forall (i : nat), prop_nth_init I T P i.
Proof.
  intros * H.
  destruct H as [k].
  apply soundness_k_induction with (k:=k).
  apply H.
Qed.

(**)

Require Export Bmc.CoreConj.

Definition k_ind_step_conj (T : trans)
  (P : prop) (k: nat) : Prop :=
  forall ss : sseq,
  ~(path T ss 0 k /\ safety_nth_offset P ss 0 k /\ ~P ss.[k]).

Lemma k_ind_step_conj_eq :
  forall (T:trans) (P:prop) (k:nat),
  k_ind_step T P k <-> k_ind_step_conj T P k.
Proof.
  intros *.
  unfold k_ind_step, k_ind_step_conj.
  split; intros H *; apply imply_not_and3; apply H.
Qed.


Definition k_induction_post_conj (I : prop) (T : trans) (P : prop) (k: nat) : Prop :=
  k_ind_step_conj T P (S k) /\ safety_nth_conj I T P (S k).

Lemma k_induction_post_conj_eq :
  forall (I:prop) (T:trans) (P:prop) (k:nat),
  k_induction_post I T P k <-> k_induction_post_conj I T P k.
Proof.
  intros *.
  unfold k_induction_post, k_induction_post_conj.
  rewrite safety_nth_conj_eq.
  rewrite k_ind_step_conj_eq.
  tauto.
Qed.

(* eof *)
