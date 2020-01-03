Require Export Bmc.Core.
Require Export Bmc.Logic.
Require Import Omega.

Open Scope nat_scope.

Definition sprop : Type := state -> Prop.
Definition spseq : Type := nat -> state -> Prop.

Definition oa1 (I:init) (T:trans) (f0 f1:sprop) : Prop :=
  (forall s0:state, I s0 <-> f0 s0) /\
  (forall (s0:state), I s0 -> f1 s0) /\
  (forall (s0:state) (s1:state), I s0 -> T s0 s1 -> f1 s1).

Lemma oa1_prop :
  forall (I:init) (T:trans),
  forall (f0 f1:sprop),
  forall s s1:state,
  oa1 I T f0 f1 ->
    (f0 s -> I s) /\ (f0 s -> f1 s).
Proof.
  unfold oa1.
  intros.
  destruct H; destruct H0.
  split. 
  - apply H.
  - rewrite <- H. apply H0.
Qed.

(* testing w/ length 2/3 spseq. *)

Definition ic3_post_2 (I:init) (T:trans) (P:prop) (f0 f1 f2:sprop) : Prop :=
  (forall s, I s -> f0 s) /\
  (forall s, I s -> f1 s) /\
  (forall s, I s -> f2 s) /\
  (forall s, f0 s -> P s) /\
  (forall s, f1 s -> P s) /\
  (forall s, f2 s -> P s) /\
  (forall s, f0 s -> f1 s) /\
  (forall s, f1 s -> f2 s) /\
  (forall s s', f0 s /\ T s s' -> f1 s') /\
  (forall s s', f1 s /\ T s s' -> f2 s') /\
  (forall s, f2 s) /\
  (forall s, f0 s <-> f1 s).

Lemma ic3_2 :
  forall (I:init) (T:trans) (P:prop),
  forall f0 f1 f2:sprop,
  ic3_post_2 I T P f0 f1 f2 ->
  forall s, I s -> P s.
Proof.
  unfold ic3_post_2.
  intros.
  do 11 destruct H as [?H H].
  apply H4.
  apply H1.
  apply H0.
Qed.

Lemma ic3_2' :
  forall (I:init) (T:trans) (P:prop),
  forall f0 f1 f2:sprop,
  ic3_post_2 I T P f0 f1 f2 ->
  forall s s', I s -> T s s' -> P s'.
Proof.
  unfold ic3_post_2.
  intros.
  do 11 destruct H as [?H H].
  apply H6.
  apply H10 with (s:=s).
  split.
  - apply H2. apply H0.
  - apply H1.
Qed.

Lemma ic3_2'' :
  forall (I:init) (T:trans) (P:prop),
  forall f0 f1 f2:sprop,
  ic3_post_2 I T P f0 f1 f2 ->
  forall s s1 s2 s3, I s -> T s s1 -> T s1 s2 -> T s2 s3 -> P s3.
Proof.
  unfold ic3_post_2.
  intros.
  do 11 destruct H as [?H H].
  apply H9.
  apply H13 with (s:=s2).
  split.
  - apply H12 with (s:=s1).
    split.
    + rewrite -> H. apply H12 with (s:=s).
      split.
      { apply H4. apply H0. }
      { apply H1. }
    + apply H2.
  - apply H3.
Qed.

(* *)

Definition ic3_post (I:init) (T:trans) (P:prop) (f:spseq) (k:nat) : Prop :=
  (forall i s, i <= k+1 -> I s -> f i s) /\
  (forall i s, i <= k+1 -> f i s -> P s) /\
  (forall i s, i <= k+1 -> f i s -> f (i+1) s) /\
  (forall i s s', i <= k+1 -> f i s /\ T s s' -> f (i+1) s') /\
  (forall s, f k s <-> f (k+1) s).

Lemma ic3_bounded' :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  ic3_post I T P f 1 ->
  forall s s', I s -> T s s' -> P s'.
Proof.
  unfold ic3_post.
  intros.
  do 4 destruct H as [?H H].
  apply H3 with (i:=1); auto.
  rewrite <- Nat.add_1_r.
  apply H5 with (s:=s); auto.
Qed.

Lemma ic3_bounded'' :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  ic3_post I T P f 1 ->
  prop_k_init I T P 1.
Proof.
  unfold ic3_post.
  unfold prop_k_init.
  unfold path.
  intros.
  do 4 destruct H as [?H H].
  rewrite <- imply_not_and3.
  intros.
  destruct H5.
  destruct H5.
  apply H1 with (i:=1); auto.
  rewrite <- Nat.add_1_r.
  apply H3 with (i:=0) (s:=ss.[0]) (s':=ss.[0+1]); auto.
Qed.

Lemma ic3_bounded :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  forall k,
  ic3_post I T P f k ->
  forall i, i <= k+1 -> prop_k_init I T P i.
Proof.
  unfold ic3_post.
  unfold prop_k_init.
  intros.
  do 4 destruct H as [?H H].
  rewrite <- imply_not_and3.
  revert ss.
  intros. apply H2 with (i:=i). omega.
  revert H6. revert H5. revert ss.
  induction i.
  - intros. apply H1. omega. apply H5.
  - intros.
    rewrite <- Nat.add_1_r in H6.
    apply split_path in H6. destruct H6.
    unfold path in H7. destruct H7 as [_ H7].
    assert (i <= k+1) by omega.
    assert (f i ss.[i]) by auto.
    rewrite <- Nat.add_1_r.
    apply H4 with (s:=ss.[i+0]) (s':=ss.[i+1]). omega.
    split.
    + rewrite -> Nat.add_0_r. apply H9.
    + apply H7.
Qed.

Lemma ic3_bound_f :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  forall k,
  ic3_post I T P f k ->
  forall i, i <= k+1 -> prop_k_init I T (f i) i.
Proof.
  unfold ic3_post.
  unfold prop_k_init.
  intros.
  do 4 destruct H as [?H H].
  rewrite <- imply_not_and3.
  revert ss.
  intros. (*apply H2 with (i:=i). omega.*)
  revert H6. revert H5. revert ss.
  induction i.
  - intros. apply H1. omega. apply H5.
  - intros.
    rewrite <- Nat.add_1_r in H6.
    apply split_path in H6. destruct H6.
    unfold path in H7. destruct H7 as [_ H7].
    assert (f i ss.[i]) by firstorder.
    rewrite <- Nat.add_1_r.
    rewrite -> Nat.add_1_r. rewrite <- Nat.add_1_r.
    apply H4 with (s:=ss.[i]) (s':=ss.[i+1]). omega.
    split.
    + apply H8.
    + rewrite -> Nat.add_0_r in H7. apply H7.
Qed.

Lemma ic3_unbounded' :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  ic3_post I T P f 0 ->
  prop_k_init I T P 2.
Proof.
  unfold ic3_post.
  unfold prop_k_init.
  intros.
  do 4 destruct H as [?H H].
  rewrite <- imply_not_and3.
  rewrite <- Nat.add_1_r.
  rewrite <- skipn_nth.
  intros.
  apply split_path in H5; destruct H5.
  apply skipn_path in H6.
  apply H1 with (i:=1); auto.
  unfold path in H6.
  destruct H6 as [_ H6].
  rewrite <- Nat.add_1_r.
  apply H3 with (i:=0) (s:=(skipn 1 ss).[0+0]) (s':=(skipn (0+1) ss).[0+1]). omega.
  split.
  - rewrite -> Nat.add_0_r. rewrite -> skipn_nth.
    rewrite -> Nat.add_0_r.
    apply H.
    unfold path in H5; destruct H5 as [_ H5].
    rewrite -> Nat.add_1_r. rewrite <- Nat.add_1_r.
    apply H3 with (i:=0) (s:=ss.[0]) (s':=ss.[0+1]). omega.
    split.
    + apply H0. omega. apply H4.
    + auto.
  - auto.
Qed.

Lemma ic3_unbounded :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  forall i k,
  ic3_post I T P f k ->
  i > k+1 -> prop_k_init I T P i.
Proof.
  intros.
  assert (ic3_post I T P f k) by auto.
  revert H.
  unfold ic3_post.
  unfold prop_k_init.
  intros.
  do 4 destruct H as [?H H].
  rewrite <- imply_not_and3.
  intros.
  apply H3 with (i:=k+1). omega.
  clear H2 H3 H4 H5 H.

  revert H7. revert H6.
  rewrite -> imply_not_and3. revert ss.
  fold (prop_k_init I T (f (k+1)) i).
  revert H0. revert H1. revert k.

  induction i.
  - intros. contradict H0. omega.
  - intros.
    destruct (Nat.le_gt_cases i k).
    + assert (i=k). omega.
      revert H.
      unfold ic3_post.
      unfold prop_k_init.
      intros.
      do 4 destruct H1 as [?H H1].
      rewrite <- imply_not_and3.
      intros.
      replace (S i) with (i+1) by omega.
      rewrite <- skipn_nth.
      rewrite <- Nat.add_1_r in H8.
      apply split_path in H8. destruct H8.
      apply skipn_path in H9.
      rewrite -> H2.
      apply H6 with (i:=k) (s:=(skipn k ss).[0]) (s':=(skipn k ss).[1]). omega.
      split.
      { rewrite -> skipn_nth.
        rewrite -> Nat.add_0_r.
        revert H8. revert H7.
        rewrite -> imply_not_and3.
        clear H9. revert ss.
        rewrite -> H2.
        fold (prop_k_init I T (f k) k).
        apply ic3_bound_f with (P:=P) (f:=f) (k:=k).
        { firstorder. }
        { omega. } }
      { rewrite <- H2. apply H9. }
    + destruct (Nat.le_gt_cases i (k+1)).
      { assert (i=k+1). omega.
        revert H1.
        unfold ic3_post.
        unfold prop_k_init.
        intros.
        do 4 destruct H1 as [?H H1].
        rewrite <- imply_not_and3.
        intros.
        replace (S i) with (i+1) by omega.
        rewrite <- skipn_nth.
        rewrite <- Nat.add_1_r in H9.
        apply split_path in H9. destruct H9.
        apply skipn_path in H10.
        rewrite -> H3.
        apply H7 with (i:=k) (s:=(skipn (k+1) ss).[0]) (s':=(skipn (k+1) ss).[1]). omega.
        split.
        { rewrite -> skipn_nth.
          apply H1.
          rewrite -> Nat.add_0_r.
          revert H9. revert H8.
          rewrite -> imply_not_and3.
          clear H10. revert ss.
          rewrite -> H3.
          fold (prop_k_init I T (f (k+1)) (k+1)).
          apply ic3_bound_f with (P:=P) (f:=f) (k:=k).
          { firstorder. }
          { omega. } }
        { rewrite <- H3. apply H10. } }
      { assert (ic3_post I T P f k) by auto.
        apply IHi in H3.
        revert H1.
        unfold ic3_post.
        unfold prop_k_init.
        intros.
        do 4 destruct H1 as [?H H1].
        rewrite <- imply_not_and3.
        intros.
        replace (S i) with (i+1) by omega.
        rewrite <- skipn_nth.
        rewrite <- Nat.add_1_r in H9.
        apply split_path in H9. destruct H9.
        apply skipn_path in H10.
        apply H7 with (i:=k) (s:=(skipn i ss).[0]) (s':=(skipn i ss).[1]). omega.
        split.
        { rewrite -> skipn_nth.

          unfold prop_k_init in H3.
          assert (~(I ss.[0] /\ path T ss 0 i /\ ~ f (k+1) ss.[i])) by auto.
          rewrite <- imply_not_and3 in H11.
          assert (f (k+1) ss.[i]).
          apply H11. apply H8. apply H9.

          apply H1.
          replace (i+0) with i by auto. apply H12. }
        { apply H10. }
        { apply H2. } }
Qed.

(*
Lemma ic3_unbounded'' :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  forall i k,
  ic3_post I T P f k ->
  i > k+1 -> prop_k_init I T P i.
Proof.
  induction i.
  - intros. contradict H0. omega.
  - intros.
    destruct (Nat.le_gt_cases i k).
    + assert (i=k). omega.
      revert H.
      unfold ic3_post.
      unfold prop_k_init.
      intros.
      do 4 destruct H as [?H H].
      rewrite <- imply_not_and3.
      intros.

      rewrite <- Nat.add_1_r.
      rewrite <- skipn_nth.
      rewrite <- Nat.add_1_r in H8.
      apply split_path in H8. destruct H8.
      apply skipn_path in H9.
      apply H4 with (i:=i+1). omega.
      apply H6 with (i:=i) (s:=(skipn i ss).[0]) (s':=(skipn i ss).[1]). omega.
      split.
      { rewrite -> skipn_nth.
        rewrite -> H2.
        (*apply H.*)
        rewrite -> Nat.add_0_r.
        revert H8. revert H7.
        rewrite -> imply_not_and3.
        clear H9. revert ss.
        rewrite -> H2.
        fold (prop_k_init I T (f k) k).
        apply ic3_bound_f with (P:=P) (f:=f) (k:=k).
        { firstorder. }
        { omega. } }
      { apply H9. }
    + destruct (Nat.le_gt_cases i (k+1)).
      { assert (i=k+1). omega.
        revert H.
        unfold ic3_post.
        unfold prop_k_init.
        intros.
        do 4 destruct H as [?H H].
        rewrite <- imply_not_and3.
        intros.
        rewrite <- Nat.add_1_r.
        rewrite <- skipn_nth.
        rewrite <- Nat.add_1_r in H9.
        apply split_path in H9. destruct H9.
        apply skipn_path in H10.
        apply H5 with (i:=i). omega.
        rewrite -> H3.
        apply H7 with (i:=k) (s:=(skipn (k+1) ss).[0]) (s':=(skipn (k+1) ss).[1]). omega.
        split.
        { rewrite -> skipn_nth.
          apply H.
          rewrite -> Nat.add_0_r.
          revert H9. revert H8.
          rewrite -> imply_not_and3.
          clear H10. revert ss.
          rewrite -> H3.
          fold (prop_k_init I T (f (k+1)) (k+1)).
          apply ic3_bound_f with (P:=P) (f:=f) (k:=k).
          { firstorder. }
          { omega. } }
        { rewrite <- H3. apply H10. } }
      { assert (ic3_post I T P f k) by auto.
        apply IHi in H3.
        revert H.
        unfold ic3_post.
        unfold prop_k_init.
        intros.
        do 4 destruct H as [?H H].
        rewrite <- imply_not_and3.
        intros.
        rewrite <- Nat.add_1_r.
        rewrite <- skipn_nth.
        rewrite <- Nat.add_1_r in H9.
        apply split_path in H9. destruct H9.
        apply skipn_path in H10.
        apply H5 with (i:=0+1). omega.
        apply H7 with (i:=0) (s:=(skipn i ss).[0]) (s':=(skipn i ss).[1]). omega.
        split.
        { rewrite -> skipn_nth.

          unfold prop_k_init in H3.
          assert (~ (I (ss) .[ 0] /\ path T ss 0 i /\ ~ P (ss) .[ i])) by auto.
          rewrite <- imply_not_and3 in H11.
          assert (P ss.[i]).
          apply H11. apply H8. apply H9.

          apply H.
          rewrite -> Nat.add_0_r.
          revert H9. revert H8.
          rewrite -> imply_not_and3.
          clear H10. revert ss.
          fold (prop_k_init I T (f (k+1)) i).
          apply ic3_bound_f with (P:=P) (f:=f) (k:=i).
          { firstorder. }
          { omega. } }



    destruct i.
    + intros. apply H2 with (i:=0). omega.
      apply H1. omega. apply H5.
    + rewrite <- Nat.add_1_r.
      intros.
      rewrite <- skipn_nth.
      apply split_path in H6. destruct H6.
      apply skipn_path in H7.
      apply H2 with (i:=i); auto.
      apply H4 with (i:=0) (s:=(skipn i ss).[0]) (s':=(skipn i ss).[1]). omega.
      split.
      { rewrite -> skipn_nth.
        apply H.
        rewrite -> Nat.add_0_r.
        revert H6. revert H5.
        rewrite -> imply_not_and3.
        clear H7. revert ss.
        fold (prop_k_init I T (f (0+1)) i).
        apply ic3_bound_f with (P:=P) (f:=f) (k:=i).
      { firstorder. }
      { omega. }
    + apply H7.



Lemma ic3_unbounded :
  forall (I:init) (T:trans) (P:prop),
  forall f:spseq,
  forall k,
  ic3_post I T P f k ->
  forall i, i > k+1 -> prop_k_init I T P i.
Proof.
  unfold ic3_post.
  unfold prop_k_init.
  intros.
  do 4 destruct H as [?H H].
  rewrite <- imply_not_and3.
  revert ss.

  (*
  destruct i.
  - intros. apply H2 with (i:=0). omega.
    apply H1. omega. apply H5.
  - intros.

    assert (S i=k+(S i-k)). omega.
    rewrite -> H7.
    rewrite <- skipn_nth.
    rewrite -> H7 in H6.
    apply split_path in H6. destruct H6.
    apply skipn_path in H8.
    apply H2 with (i:=k+1); auto.
    apply H4 with (i:=k) (s:=(skipn k ss).[S i-k-1]) (s':=(skipn k ss).[S i-k]). omega.
    split.
    + rewrite -> skipn_nth.
      apply H.
      rewrite -> Nat.add_0_r.
      revert H6. revert H5. 
      rewrite -> imply_not_and3.
      clear H7. revert ss.
      fold (prop_k_init I T (f (k+1)) i).
      apply ic3_bound_f with (P:=P) (f:=f) (k:=k).
      { firstorder. }
      { omega. }

    rewrite <- Nat.add_1_r.
    rewrite <- skipn_nth.
    rewrite <- Nat.add_1_r in H6.
    apply split_path in H6. destruct H6.
    apply skipn_path in H7.
    apply H2 with (i:=k+1). apply.
    apply H4 with (i:=i) (s:=(skipn i ss).[0]) (s':=(skipn i ss).[1]). omega.
    split.
    + rewrite -> skipn_nth.
      apply H.
      rewrite -> Nat.add_0_r.
      revert H6. revert H5. 
      rewrite -> imply_not_and3.
      clear H7. revert ss.
      fold (prop_k_init I T (f (k+1)) i).
      apply ic3_bound_f with (P:=P) (f:=f) (k:=k).
      { firstorder. }
      { omega. }
*)


  remember (i-k-2) as j.
  replace i with (j+k+2).
  induction j.
  - assert (0+k+2 = k+1+1) by omega. rewrite -> H5. clear H5.
    intros.
    rewrite <- skipn_nth.
    apply split_path in H6. destruct H6.
    apply skipn_path in H7.
    apply H2 with (i:=k+1); auto.
    apply H4 with (i:=k) (s:=(skipn (k+1) ss).[0]) (s':=(skipn (k+1) ss).[1]). omega.
    split.
    + rewrite -> skipn_nth.
      apply H.

      (*
      rewrite -> Nat.add_0_r.
      revert H6. revert H5. clear H7. revert ss.
      replace (k+1) with (i-1).
      { induction i.
        { contradict H0. omega. }
        { intros.
      *)

      rewrite -> Nat.add_0_r.
      revert H6. revert H5. 
      rewrite -> imply_not_and3.
      clear H7. revert ss.
      fold (prop_k_init I T (f (k+1)) (k+1)).

      apply ic3_bound_f with (P:=P) (f:=f) (k:=k).
      { firstorder. }
      { omega. }
    + apply H7.
  - intros.
    assert (j=i-k-2). omega.

      apply ic3_bounded with (f:=f) (k:=k).
      { unfold ic3_post. firstorder.
        remember (i0-k) as j.
        replace i0 with (j+k) in H5.
        replace i0 with (j+k) in H6.
        revert H6. revert H5.
        induction j.
        { apply H3. }
        { 

        replace 


      induction k.
      { rewrite -> Nat.add_1_r in H6. 
        unfold path in H6; destruct H6 as [_ H6].
        rewrite -> Nat.add_0_r.
        apply H4 with (i:=0) (s:=ss.[0+0]) (s':=ss.[0+1]). omega.
        split.
        { apply H1. omega. apply H5. }
        { apply H6. } }
      { 

    unfold path in H6.

  - 

  rewrite <- skipn_nth.
  intros.
*)