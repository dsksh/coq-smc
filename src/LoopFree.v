Require Import Bmc.Core.
Require Import Classical_Prop.
Require Import Omega.

Definition shorter_ss_l (ss1 ss2 : sseq) (o i: nat) : Prop :=
  forall (j : nat), j <= i-o -> ss1.[i-j] = ss2.[i-j].

Definition shorter_ss_u (ss1 ss2 : sseq) (i d: nat) : Prop :=
  forall (j : nat), ss1.[i+j+d] = ss2.[i+j].

Definition shorter_ss (ss1 ss2 : sseq) (o i d: nat) : Prop :=
  shorter_ss_l ss1 ss2 o i /\ shorter_ss_u ss1 ss2 i d.

Lemma skipn_shorter_ss_l :
  forall (i j o : nat) (ss1 ss2 : sseq),
  shorter_ss_l ss1 ss2 o (i+j) -> o <= i ->
  shorter_ss_l (skipn i ss1) (skipn i ss2) 0 j.
Proof.
  unfold shorter_ss_l.
  intros.
  do 2 rewrite -> skipn_nth.
  replace (i+(j-j0)) with (i+j-j0).
  apply H.
  omega.
  omega.
Qed.

Lemma skipn_shorter_ss_l' :
  forall (i j : nat) (ss1 ss2 : sseq),
  shorter_ss_l (skipn i ss1) (skipn i ss2) 0 j ->
  shorter_ss_l ss1 ss2 i (i+j).
Proof.
  unfold shorter_ss_l.
  intros.
  replace (i+j-j0) with (i+(j-j0)).
  do 2 rewrite <- skipn_nth.
  apply H.
  omega.
  omega.
Qed.

Lemma skipn_shorter_ss_u :
  forall (i j d : nat) (ss1 ss2 : sseq),
  shorter_ss_u ss1 ss2 (i+j) d <->
  shorter_ss_u (skipn i ss1) (skipn i ss2) j d.
Proof.
  unfold shorter_ss_u.
  split.
  - intros.
    do 2 rewrite -> skipn_nth.
    replace (i+(j+j0)) with (i+j+j0).
    replace (i+(j+j0+d)) with (i+j+j0+d).
    apply H.
    omega.
    omega.
  - intros.
    replace (i+j+j0) with (i+(j+j0)).
    replace (i+(j+j0)+d) with (i+(j+j0+d)).
    do 2 rewrite <- skipn_nth with (n:=i).
    apply H.
    omega.
    omega.
Qed.

Lemma skipn_shorter_ss :
  forall (i j o d : nat) (ss1 ss2 : sseq),
  shorter_ss ss1 ss2 o (i+j) d -> o <= i ->
  shorter_ss (skipn i ss1) (skipn i ss2) 0 j d.
Proof.
  unfold shorter_ss.
  intros.
  destruct H.
  split.
  - apply skipn_shorter_ss_l with (o:=o).
    apply H.
    apply H0.
  - apply skipn_shorter_ss_u.
    apply H1.
Qed.

Lemma skipn_shorter_ss' :
  forall (i j d : nat) (ss1 ss2 : sseq),
  shorter_ss (skipn i ss1) (skipn i ss2) 0 j d ->
  shorter_ss ss1 ss2 i (i+j) d.
Proof.
  unfold shorter_ss.
  intros.
  destruct H.
  split.
  - apply skipn_shorter_ss_l'.
    apply H.
  - apply skipn_shorter_ss_u.
    apply H0.
Qed.

Lemma shorter_ss_prop :
  forall (P : prop) (i d : nat) (ss1 ss2 : sseq),
  P ss1.[i] /\ shorter_ss ss1 ss2 0 i d ->
  P ss2.[i].
Proof.
  unfold shorter_ss.
  unfold shorter_ss_l.
  intros.
  assert (ss1.[i-0] = ss2.[i-0])
  by (apply H; omega).
  rewrite -> Nat.sub_0_r in H0.
  rewrite <- H0.
  apply H.
Qed.

Lemma shorter_ss_prop0 :
  forall (P : prop) (i d : nat) (ss1 ss2 : sseq),
  P ss1.[i+d+d] /\ shorter_ss ss1 ss2 0 i d ->
  P ss2.[i+d].
Proof.
  unfold shorter_ss.
  unfold shorter_ss_u.
  intros.
  destruct H. destruct H0.
  assert (ss1.[i+d+d] = ss2.[i+d])
  by apply H1.
  rewrite <- H2.
  apply H.
Qed.

Lemma shorter_ss_prop1 :
  forall (T : trans) (len i d : nat) (ss1 ss2 : sseq),
  path T ss1 0 len -> ss1.[i] = ss1.[i+d] ->
  shorter_ss ss1 ss2 0 i d ->
  path T ss2 0 (len-d).
Proof.
  unfold shorter_ss.
  unfold shorter_ss_l.
  unfold shorter_ss_u.
  intros.
  destruct H1.
  induction len.
  - auto.
  - destruct (Nat.le_gt_cases (S len) d).
    + assert (S len - d = 0) as A by omega.
      rewrite -> A; clear A. 
      simpl. intuition.
    + destruct (Nat.le_gt_cases len d).
      * assert (len = d) by omega.
        assert (S len - d = 1) as A by omega.
        rewrite -> A; clear A.
        simpl.
        destruct (Nat.le_gt_cases 1 i).
        { split.
          { auto. }
          { 
            rewrite <- Nat.add_1_l in H.
            apply split_path in H; destruct H.
            simpl in H.

            assert (0 = i-i) as A1 by omega.
            rewrite -> A1.
            assert (S (i-i) = i-(pred i)) as A2 by omega.
            rewrite -> A2.
            rewrite <- H1.
            rewrite <- H1.
            rewrite <- A2.
            rewrite <- A1.
            apply H.
            omega. omega. } }
        { split.
          { auto. }
          { assert (i = 0) by omega.
            assert (0 = i+0) as A1 by omega.
            rewrite -> A1.
            assert (S (i+0) = i+1) as A2 by omega.
            rewrite -> A2.
            rewrite <- H2.
            rewrite <- H2.
            rewrite <- A2.
            rewrite <- A1.
            rewrite -> Nat.add_0_l.
            rewrite -> Nat.add_1_l.

            simpl in H.
            rewrite <- H5.
            apply H. } }
      * clear H3.
        assert (S len - d = S (len - d)) as A by omega.
        rewrite -> A; clear A.
        simpl.
        split.
        { apply IHlen.
          rewrite <- Nat.add_1_r in H.
          apply split_path in H; destruct H.
          apply H. }
        { 
          destruct (Nat.lt_ge_cases (len - d) i).
          { remember (i-(len-d)) as j.
            assert (len-d = i-j) as A0 by omega.
            rewrite -> A0.
            assert (S (i-j) = i - pred j) as A1 by omega.
            rewrite -> A1.
            rewrite <- H1.
            rewrite <- H1.
            rewrite <- A1; clear A1.
            rewrite <- A0; clear A0.

            assert (S len = S (len-d) + d) as A2 by omega.
            rewrite -> A2 in H; clear A2.
            apply split_path in H; destruct H.
            simpl in H; destruct H.
            apply H6.
            omega.
            omega. }
          { remember ((len-d)-i) as j.
            assert (len-d = i+j) as A0 by omega.
            rewrite -> A0.
            assert (S (i+j) = i + S j) as A1 by omega.
            rewrite -> A1.
            rewrite <- H2.
            rewrite <- H2.
            rewrite <- A1; clear A1.
            rewrite <- A0; clear A0.
            replace (len-d+d) with len.
            replace (S (len-d)+d) with (S len).
            simpl in H; destruct H.
            apply H5.
            omega.
            omega. } }
Qed.

Lemma not_no_loop'_eq_states :
  forall (j o i:nat) (ss:sseq),
  ~ no_loop' ss o i j ->
  (*
  exists (k:nat), k <= j /\ ss.[o+i] = ss.[o+k].
  *)
  ~(forall (k:nat), k > j \/ ss.[o+i] <> ss.[o+k]).
Proof.
  induction j.
  - intros.
    contradict H.
    assert (0 > 0 \/ ss.[o+i] <> ss.[o+0]) by easy.
    destruct H0.
    + contradict H0. omega.
    + simpl.
      rewrite -> Nat.add_0_r in H0.
      apply H0.
  - intros.
    simpl in H.
    apply not_and_or in H.
    destruct H.
    + apply IHj in H.
      contradict H.
      intros.
      assert (k > S j \/ ss.[o+i] <> ss.[o+k]) by easy.
      destruct H0.
      * left. omega.
      * right. apply H0.
    + contradict H.
      assert (S j > S j \/ ss.[o+i] <> ss.[o+S j]) by easy.
      destruct H0.
      * contradict H0. omega.
      * apply H0.
Qed.

Definition shorten_ss (ss : sseq) (li d i : nat) : state :=
  match i-li with
  | 0 => ss.[i]
  | _ => ss.[i+d]
  end.

Lemma shorten_ss_shorter_ss :
  forall (ss  : sseq) (i d : nat),
  ss.[i] = ss.[i+d] ->
  shorter_ss ss (shorten_ss ss i d) 0 i d.
Proof.
  unfold shorter_ss.
  unfold shorter_ss_l.
  unfold shorter_ss_u.
  unfold shorten_ss.
  unfold nth.
  split.
  - intros.
    assert (i - j - i = 0) as A by omega.
    rewrite -> A.
    reflexivity.
  - intros.
    unfold shorten_ss.
    unfold nth.
    assert (i + j - i = j) as A by omega.
    rewrite -> A.
    destruct j.
    + simpl.
      rewrite -> Nat.add_0_r.
      rewrite <- H.
      reflexivity.
    + reflexivity.
Qed.

Lemma not_no_loop_eq_states :
  forall (i:nat) (ss:sseq),
  ~ no_loop ss 0 i ->
  (*
  exists (ss':sseq) (j d:nat), 
    j+d <= i /\ d > 0 /\ shorter_ss ss ss' 0 j d /\ ss.[i] = ss'.[i-d].
  *)
  ~(forall (ss':sseq) (j d:nat), 
    d <= 0 \/ ~ shorter_ss ss ss' 0 j d \/ ss.[i] <> ss'.[i-d]
    \/ j+d > i).
Proof.
  intros.
  induction i.
  - contradict H. easy.
  - simpl in H.
    apply not_and_or in H.
    destruct H.
    * apply not_no_loop'_eq_states in H.
      contradict H.
      intros.
      destruct (Nat.le_gt_cases (S i) k).
      { left. omega. }
      { right.
        remember (shorten_ss ss k (S i - k)) as ss'.
        assert (S i - k <= 0 \/ 
          ~ shorter_ss ss ss' 0 k (S i - k) \/ ss.[S i] <> ss'.[S i - (S i - k)] \/ k + (S i - k) > S i) by apply H.
        destruct H1.
        { contradict H1. omega. }
        { contradict H1.
          do 2 rewrite -> Nat.add_0_l in H1.
          apply and_not_or.
          split.
          { rewrite -> Heqss'.
            assert (forall (p:Prop), p -> ~~p) as A by tauto.
            apply A; clear A.
            apply shorten_ss_shorter_ss.
            assert (k + (S i - k) = S i) as A by omega.
            rewrite -> A.
            symmetry.
            apply H1. }
          { apply and_not_or.
            split.
            { assert (S i - (S i - k) = k) as A by omega.
              rewrite -> A.
              rewrite -> Heqss'.
              unfold shorten_ss.
              unfold nth.
              replace (k-k) with 0.
              assert (~ ss (S i) <> ss k <-> ss.[S i] = ss.[k]) as A0 by tauto.
              rewrite -> A0.
              apply H1.
              omega. }
            { assert (k + (S i - k) = S i) as A by omega.
              rewrite -> A. 
              omega. } } } }
    * apply IHi in H.
      contradict H.
      intros.
      (*remember (shorten_ss ss j d) as ss'.*)
      assert (d <= 0 \/ 
        ~ shorter_ss ss ss' 0 j d \/ ss.[S i] <> ss'.[S i - d] \/
        j + d > S i) by apply H.
      destruct H0.
      { left. apply H0. }
      { destruct H0.
        { right; left.
          apply H0. }
        { 
          destruct (Nat.lt_ge_cases (S i) (j+d)).
          { right; right; right.
            omega. }
          {
            right; left.
            contradict H0.
            apply and_not_or.
            split.
            { 
              unfold shorter_ss in H0.
              unfold shorter_ss_u in H0.
              destruct H0.
              destruct (Nat.le_gt_cases (j+d) (S i)).
              { assert (ss.[j + (S i - j - d) + d] = ss'.[j + (S i - j - d)]) as A by apply H2.
                assert (j + (S i - j - d) + d = S i) as A0 by omega.
                assert (j + (S i - j - d) = S i - d) as A1 by omega.
                rewrite -> A0 in A.
                rewrite -> A1 in A.
                assert (~ ss.[S i] <> ss'.[S i - d] <-> ss.[S i] = ss'.[S i - d]) as A2 by tauto.
                apply A2.
                apply A. }
            { assert (ss.[j + (S i - j - d) + d] = ss'.[j + (S i - j - d)]) as A by apply H2.
              assert (j + (S i - j - d) + d = S i) as A0 by omega.
              assert (j + (S i - j - d) = S i - d) as A1 by omega.
              rewrite -> A0 in A.
              rewrite -> A1 in A.
              assert (~ ss.[S i] <> ss'.[S i - d] <-> ss.[S i] = ss'.[S i - d]) as A2 by tauto.
              apply A2.
              apply A. } }
          { omega. } } } }
Qed.

Lemma eq_states_no_loop :
  forall (i:nat) (ss:sseq),
   (forall (ss':sseq) (j d:nat), 
    d <= 0 \/ ~ shorter_ss ss ss' 0 j d \/ ss.[i] <> ss'.[i-d]
    \/ j+d > i) ->
      no_loop ss 0 i.
Proof.
  intros.
  apply NNPP.
  contradict H.
  apply not_no_loop_eq_states in H.
  apply H.
Qed.

(*
Lemma not_ntq_not_pq :
  forall (p q:Prop),
    ~(p /\ True /\ q) <-> ~(p /\ q).
Proof.
  firstorder.
Qed.
*)

Lemma not_imply_imply :
  forall (p q:Prop), (~q -> ~p) <-> (p -> q).
Proof.
  intros. tauto.
Qed.


Lemma safety_lf_path'' :
  forall (I:prop) (T:trans) (P:prop) (k:nat),
  ( forall (j:nat), j < k -> prop_k_init I T P j ) ->
    prop_k_init_lf I T P k ->
    prop_k_init I T P k.
Proof.
  unfold prop_k_init.
  intros.
  (*assert ((forall (p1 p2 p3:Prop), ((p1 /\ p3 -> ~p2) <-> ~(p1 /\ p2 /\ p3)))) as A by tauto.
  apply A.
  intros; destruct H1.*)

  revert H2.
  apply not_imply_imply.
  intros.

  assert (~loop_free T ss 0 k) as A0.
  { unfold prop_k_init_lf in H0.
    contradict H2.
    revert H1 H2.
    apply H0. }


  unfold loop_free in A0.
  apply not_and_or in A0.
  destruct A0.
  apply H3.

  contradict H3.

  apply eq_states_no_loop.
  intros.
  assert (d <= 0 <-> ~ d > 0) as A2 by omega.
  rewrite -> A2; clear A2.
  do 3 (apply imply_to_or; intros).

  rewrite -> H6 in H2.
  unfold shorter_ss in H5; destruct H5.
  unfold shorter_ss_l in H5.
  assert (j <= j-0) as A3 by omega.
  apply H5 in A3.
  assert (j-j = 0) as A4 by omega.
  rewrite -> A4 in A3; clear A4.
  rewrite -> A3 in H1; clear A3.

  destruct k.
  - omega.
  - assert (S k - d < S k) as A3 by omega.
    apply H with (ss:=ss') in A3.
    { assert (~ j+d <= S k -> j+d > S k) as A4 by omega.
      apply A4; clear A4.
      contradict A3.
      apply H2. }
    { apply H1. }
    { apply shorter_ss_prop1 with (i:=j) (ss1:=ss).
      { apply H3. }
      { unfold shorter_ss_u in H7.
        symmetry.
        replace j with (j+0).
        rewrite -> H7.
        replace (j+0) with (j-0).
        rewrite H5.
        reflexivity.
        omega. omega. omega. }
      { easy. } }
Qed.

Lemma safety_lf_path' :
  forall (I:prop) (T:trans) (P:prop) (k : nat),
  ( forall (i : nat), i <= k -> prop_k_init_lf I T P i ) ->
    forall (j : nat), j <= k -> prop_k_init I T P j.
Proof.
  intros. revert j H0.
  induction k.
  - intros.
    apply safety_lf_path''.
    intros.
    contradict H1. omega.
    apply H. omega.
  - intros.
    apply safety_lf_path''.
    intros.
    assert (j0 <= k) by omega.
    apply IHk.
    intros.
    apply H.
    omega.
    omega.
    apply H.
    omega.
Qed.

Lemma safety_lf_path :
  forall (I:prop) (T:trans) (P:prop),
  ( forall (i : nat), prop_k_init_lf I T P i ) ->
    forall (j : nat), prop_k_init I T P j.
Proof.
  intros * H.
  induction j as [|j IHj].
  - apply safety_lf_path''.
    intros j H0.
    contradict H0. omega.
    apply H.
  - apply safety_lf_path''.
    intros j0 _H0.
    assert (j0 <= S j) as A by omega.
    apply safety_lf_path' with (k := S j).
    intros i _H1.
    apply H.
    apply A.
    apply H.
Qed.