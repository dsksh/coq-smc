Require Export bmc.
Require Import Omega.
Require Import Coq.Logic.Classical_Prop.
Local Open Scope nat_scope.
Local Axiom by_smt : forall P : Prop, P.

Fixpoint all_P (P : property) (l : list state) (o num: nat) : Prop :=
  match num with
  | O => True
  | S 0  => P (l _[o])
  | S num' => all_P P l o num' /\ P (l _[o+num'])
  end.

(*
Definition safety2 (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  forall l : list state,
   not (I (l _[0]) /\ path T l 0 k /\ all_P P l 0 k).
 *)

Definition k_violate_loop_free (I : init) (T : trans)
           (P : property) (size k: nat) : Prop :=
  forall l : list state,
  ~ (loop_free T l size 0 k /\ all_P P l 0 k /\ ~ P (l _[k])).


Definition k_Induction (I : init) (T : trans) (P : property) (size k: nat) : Prop :=
  ((lasso I T P size k) \/
   (k_violate_loop_free I T P size k)) /\ safety I T P k.



Lemma lt_safety_relation : forall (i k : nat) (I : init) (T : trans) (P : property),
    (i < k) -> safety I T P k -> P_state1 I T P i.
Proof.
  intros.
  induction k.
  - easy.
    
  - destruct (Nat.lt_ge_cases i k).
    + assert (H2 : safety I T P k /\ P_state1 I T P k) 
        by (destruct k; firstorder; now rewrite <- plus_n_O in H0).
      now apply (IHk H1). 
    + apply gt_S_le in H.
      assert (i = k) by omega.      
      destruct k; rewrite H2; firstorder.
Qed.


Lemma all_P_itl_relation : forall (P : property) (i j : nat),
    forall l : list state,
    all_P P l j i  -> all_P P (itl l j) 0 i.
Proof.
  intros.
  induction i.
  - auto.

  - assert (H0 : all_P P (itl l j) 0 i /\ P ((itl l j) _[i])
                 -> all_P P (itl l j) 0 (S i)).
    intros.
    destruct i; firstorder.
    apply H0.
    clear H0.
    split.
    apply IHi.
    destruct i; firstorder.
    rewrite <- itl_relation.
    destruct i; firstorder.
    replace (S i + j) with (j + S i).
    auto.
    omega.
Qed.


Lemma shift_violate_loop_free : forall (T : trans) (P : property) (size i k : nat),
    S k <= i -> 
    (forall l : list state,
        ~ (loop_free T l size 0 (S k) /\ all_P P l 0 (S k) /\ ~ P (l _[S k])))
    -> forall l : list state,
        ~ (loop_free T l size (i-k-1) (S k) /\ all_P P l (i-k-1) (S k) /\
           ~ P (l _[i])).
Proof.
  intros.
  apply neg_false.
  split.
  unfold loop_free in *.
  intros.
  destruct H1.
  destruct H1.
  destruct H2.
  apply no_loop_itl_relation in H3.
  apply P_itl_relation with (k:= S k) in H4.
  apply path_itl_relation in H1.
  apply all_P_itl_relation in H2.
  assert (i - S k = i - k - 1) by omega.
  rewrite H5 in H4.
  firstorder.
  omega.
  tauto.
Qed.



Lemma divide_hd_all_P : forall (P : property)(l : list state) (i j : nat),
    P (l _[i]) /\ all_P P l (S i) j <-> all_P P l i (S j).
Proof.
  destruct j.
  - unfold all_P. simpl.
    tauto.
   
  - induction j. simpl. 
    rewrite Nat.add_1_r.
    tauto.
    firstorder; now rewrite Nat.add_succ_comm in *.
Qed.


Lemma lt_wf_ind_incl_P : forall (I : init) (T : trans) (P : property)
                 (l : list state) (i k size : nat),
   k < i ->  I (l _[ 0]) /\ loop_free T l size 0 i ->
   (forall m : nat, m < i -> I (l _[0]) /\ loop_free T l size 0 m -> P (l _[m]))
   -> all_P P l (i-k-1) (S k).
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
    apply divide_path in H2.
    apply divide_no_loop in H4.
    tauto.
    apply IHk.
    omega.
    omega.
Qed.

Lemma xxxx : forall (P : property) (i : nat) (l : list state),
    (forall l',  ~ ~ P (l' _[ 0])) -> ~~ P (l _[i]).
Proof.
  intros.
  assert (H1 : forall A : Prop, A -> ~~ A) by tauto.
  apply H1.
  
  assert (H2 : i = 0 + i) by omega.
  rewrite H2.
  rewrite itl_relation.
  apply NNPP.
  firstorder.
Qed.


Theorem Proof_k_Induction :
  forall (I : init) (T : trans) (P : property) (size k : nat),
    k_Induction I T P size k
    -> (forall (i : nat), P_state2 I T P size i).
Proof.
  unfold P_state2.
  intros.
  
  assert (H0 : forall A B C : Prop, (A /\ B -> C) <->  ~ (A /\ B /\ ~ C)) by (split; tauto).
  apply H0. 
  intros.

  induction i using lt_wf_ind.
  unfold k_Induction in H.
  destruct (Nat.lt_ge_cases i k).
  - apply lt_safety_relation with (I:=I) (T:=T) (P:=P) in H3.
    unfold P_state1 in H3.
    assert (H4 : ~ (I (l _[ 0]) /\ path T l 0 i /\ ~ P (l _[ i]))) by auto.
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
      apply divide_loop_free in H6.
      firstorder.
    + unfold k_violate_loop_free in H.
      
      destruct k.
      * unfold loop_free in H.
        simpl in *.
        assert (H5 : forall l, ~~ P (l _[0])) by firstorder.
        apply xxxx with (i:=i) (l:=l) in H5.
        tauto.
      * destruct H1.
        assert (H6 : i = (i - k - 1) + (k + 1)) by omega.
        assert (H7 : loop_free T l size 0 i) by auto.
        rewrite H6 in H5.
        apply divide_loop_free in H5.
        destruct H5.
        assert (H9 : k < i) by omega.
        apply itl_violate_loop_free with
          (T:=T) (P:=P) (size:=size) (l:=l) in H3.
        apply lt_wf_ind_incl_P with
          (I:=I) (T:=T)(P:=P)(size:=size) (l:=l) in H9.
        assert (H10 :loop_free T l size (i - k - 1) (k + 1) /\
                all_P P l (i - k - 1) (S k)) by tauto.
        apply H0 in H3.
        auto.
        rewrite Nat.add_1_r in H8.
        auto.
        auto.
        auto.
        auto.
Qed.
