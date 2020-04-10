Require Export Bmc.Core.


Definition naive_post (I : prop) (T : trans) (P : prop) (k : nat) : Prop :=
  safety_nth I T P (S k).

Definition induction_post (I : prop) (T : trans) (P : prop) : Prop :=
  (forall (s:state), I s -> P s) /\
  (forall (s s':state), P s -> T s s' -> P s').

(**)

Theorem soundness_naive_bounded :
  forall (I:prop) (T:trans) (P:prop) (k:nat),
  naive_post I T P k ->
  forall (i:nat), i <= (S k) ->
  prop_nth_init I T P i.
Proof.
  intros * H i H0 ss.
  unfold naive_post in H.
  induction (S k) as [|k' IHk].
  - assert (i = 0) as A by omega.
    simpl in H.
    unfold prop_nth_init in H.
    rewrite -> A.
    apply H.
  - destruct (Nat.le_gt_cases i k').
    + apply IHk.
      { apply H. }
      { apply H1. }
    + assert (i = S k') by omega.
      destruct k'; rewrite H2; firstorder.
Qed.

Theorem soundness_naive_f :
  forall (I : prop) (T : trans) (P : prop),
  (exists k, ~naive_post I T P k) ->
  ~( forall (i:nat), prop_nth_init I T P i ).
Proof.
  intros * H.
  destruct H as [k].
  contradict H.
  unfold naive_post.
  induction (S k) as [|k' IHk].
  - unfold safety_nth, prop_nth_init.
    intros *.
    apply H.
  - simpl.
    split.
    + apply IHk.
    + unfold prop_nth_init.
      intros *.
      apply H.
Qed.

Theorem completeness_naive_f :
  forall (I : prop) (T : trans) (P : prop),
  ~( forall (i:nat), prop_nth_init I T P i ) ->
  (*exists k, ~naive_post I T P k.*)
  ~( forall k, naive_post I T P k ).
Proof.
  intros * H.
  contradict H.
  unfold prop_nth_init.
  intros *.
  destruct i.
  - specialize (H 0).
    unfold safety_nth, prop_nth_init in H.
    apply H.
  - specialize (H i).
    unfold naive_post, safety_nth in H.
    destruct H as [_ H].
    unfold prop_nth_init in H.
    apply H.
Qed.

Theorem soundness_induction :
  forall (I:prop) (T:trans) (P:prop),
  induction_post I T P ->
    forall (i:nat), prop_nth_init I T P i.
Proof.
  unfold prop_nth_init.
  intros * H *.
  unfold induction_post in H.
  destruct H as [H H0].
  induction i as [|i IHi].
  - firstorder.
  - intros H1 H2.
    rewrite -> snoc_path in H2.
    destruct H2 as [H2 H3].
    rewrite -> Nat.add_0_l in H3.
    apply H0 with (s:=ss.[i]).
    apply IHi.
    apply H1.
    apply H2.
    apply H3.
Qed.

Theorem completeness_naive_basecase :
  forall (I:prop) (T:trans) (P:prop),
  ( forall (i:nat), prop_nth_init I T P i ) ->
      forall (ss:sseq), I ss.[0] -> P ss.[0].
Proof.
  intros * H *.
  assert (forall (ss:sseq), 
    I ss.[0] -> path T ss 0 0 -> P ss.[0]) as A 
    by apply H.
  simpl in A.
  firstorder.
Qed.

(**)

Require Export Bmc.CoreConj.

Definition naive_post_conj (I : prop) (T : trans) (P : prop) (k : nat) : Prop :=
  safety_nth_conj I T P (S k).

Theorem naive_post_conj_eq :
  forall (I:prop) (T:trans) (P:prop) (k:nat),
  naive_post I T P k <-> naive_post_conj I T P k.
Proof.
  intros *.
  unfold naive_post, naive_post_conj.
  apply safety_nth_conj_eq.
Qed.

(* eof *)
