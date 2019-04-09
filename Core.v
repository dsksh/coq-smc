Require Export ZArith.
Require Export Logic.

Open Scope nat_scope.

Set Implicit Arguments.

(**)

Definition state : Type := Z.
Definition sseq : Type := nat -> state.

Definition nth (n : nat) (ss : sseq) : state :=
  ss n.

Notation "ss .[ n ] " := (nth n ss)
                         (at level 0).

Definition skipn (n : nat) (ss : sseq) : sseq :=
  fun i => ss (i+n).

Lemma skipn_nth: forall (ss : sseq) (n m : nat),
  (skipn n ss).[m] = ss.[n+m].
Proof.
  intros.
  unfold skipn.
  rewrite plus_comm.
  reflexivity.
Qed.

Lemma state_sseq :
  forall (s:state), (fun _ => s).[0] = s.
Proof.
  intros. unfold nth. reflexivity.
Qed.

Lemma prop_state_sseq :
  forall (p : state -> Prop),
    (forall (ss:sseq), p ss.[0]) ->
    (forall (s:state), p s).
Proof.
  intros.
  rewrite <- state_sseq. apply H.
Qed.

(**)

Definition init : Type := state -> Prop.
Definition trans : Type := state -> state -> Prop.
Definition prop : Type := state -> Prop.

Fixpoint path (T : trans) (ss : sseq) (o len : nat) : Prop :=
  match len with
  | O => True
  | S len' => path T ss o len' /\ T ss.[o+len'] ss.[o+len]
  end.

Fixpoint invariance (P : prop) (ss : sseq) (len : nat) : Prop :=
  match len with
  | O => P ss.[0]
  | S len' => invariance P ss len' /\ P ss.[len]
  end.

Fixpoint no_loop' (ss : sseq) (o m n: nat) : Prop :=
  match n with
  | O => ss.[o+m] <> ss.[o]
  | S n' => no_loop' ss o m n' /\ ss.[o+m] <> ss.[o+n]
  end.

Fixpoint no_loop (ss : sseq) (o k : nat) : Prop :=
  match k with
  | O => True
  | S k' => no_loop' ss o k k' /\ no_loop ss o k'
  end.

Definition loop_free (T : trans) (ss : sseq) (o k: nat) : Prop :=
  path T ss o k /\ no_loop ss o k.

Definition lasso (I : init) (T : trans) (P : prop) (k : nat) : Prop :=
  forall ss : sseq,
  ~ (I ss.[0] /\ loop_free T ss 0 k).

Definition violate_loop_free (I : init) (T : trans)
           (P : prop) (k: nat) : Prop :=
  forall ss : sseq,
  ~ (loop_free T ss 0 k /\ ~ P ss.[k ]).


Definition prop_k_init (I : init) (T : trans) (P : prop) (k : nat) : Prop :=
  forall ss : sseq,
  ~ (I ss.[0] /\ path T ss 0 k /\ ~ P ss.[k]).

Fixpoint safety_k (I : init) (T : trans) (P : prop) (k : nat) : Prop :=
  match k with
  | O => prop_k_init I T P k
  | S k' => safety_k I T P k' /\ prop_k_init I T P k
  end.

Definition prop_k_init_lf  (I : init) (T : trans) (P : prop) (k : nat) : Prop :=
  forall ss : sseq,
  ~ (I ss.[0] /\ loop_free T ss 0 k /\ ~ P ss.[k]).

Fixpoint safety_k_offset (P : prop) (ss : sseq) (o k: nat) : Prop :=
  match k with
  | O => True
  | S k' => safety_k_offset P ss o k' /\ P ss.[o+k']
  end.

(**)

Lemma safety_path_lf :
  forall (I:init) (T:trans) (P:prop),
  forall (i:nat),
    prop_k_init I T P i ->
    prop_k_init_lf I T P i.
Proof.
  intros.
  unfold prop_k_init in H.
  unfold prop_k_init_lf.
  unfold loop_free.
  intros.
  assert (forall (p1 p2 p3 p4:Prop), (p1 /\ p2 /\ p3 -> p4) -> (~(p1 /\ (p2 /\ p3) /\ ~p4))) by firstorder.
  apply H0; clear H0.
  intros.
  decompose [and] H0; clear H0.
  revert H3; revert H1.
  apply and_imply_premise.
  apply or_to_imply.
  apply not_and_or'. 
  assert (forall (p1 p2 p3:Prop), ~(p1 /\ p2 /\ p3) -> ~((p1 /\ p2) /\ p3)) by firstorder.
  apply H0; clear H0.
  apply H.
Qed.

(**)

Lemma skipn_path : forall (T : trans) (i j : nat),
  forall ss : sseq,
  path T ss j i  -> path T (skipn j ss) 0 i.
Proof.
  intros.
  induction i.
  - auto.
  - assert ( path T (skipn j ss) 0 (S i) <->
      path T (skipn j ss) 0 i /\
        T (skipn j ss).[i] (skipn j ss).[S i] ).
    {
      destruct i. firstorder.
      unfold path; fold path.
      simpl.
      (*rewrite <- plus_n_O.*)
      tauto.
    }
    apply H0.
    clear H0.

    split.
    apply IHi.
    destruct i; firstorder.
    + clear IHi.
      rewrite skipn_nth.
      rewrite skipn_nth.
      simpl in *.
      decompose [and] H. clear H.
      destruct i.
      * simpl in *.
        auto.
      * auto.
Qed.

Lemma skipn_no_loop' : forall (i j k : nat),
  forall ss : sseq,
  no_loop' ss j k i ->
  no_loop' (skipn j ss) 0 k i.
Proof.
  intros.
  destruct i.
  - simpl in *.
    do 2 rewrite skipn_nth.
    rewrite -> Nat.add_0_r.
    apply H.
  - induction i.
    + simpl in *.
      do 3 rewrite skipn_nth.
      rewrite -> Nat.add_0_r.
      apply H.
    + simpl.
      split.
      * do 2 rewrite skipn_nth.
        firstorder.
      * simpl in H.
        do 2 rewrite skipn_nth.
        tauto.
Qed.

Lemma skipn_no_loop : forall (i j : nat),
  forall ss : sseq,
  no_loop ss j i -> no_loop (skipn j ss) 0 i.
Proof.
  intros.
  induction i.
  - auto.

  - assert (H1 : no_loop ss j i /\ no_loop' ss j (S i) i)
      by ( destruct i; firstorder; rewrite <- plus_n_O in *).
    clear H.

    assert ( H :no_loop (skipn j ss) 0 i /\
      no_loop' (skipn j ss) 0 (S i) i -> 
      no_loop (skipn j ss) 0 (S i) ).
    intros.
    destruct i; firstorder; rewrite <- plus_n_O in *.
    apply H.
    clear H.
    split.
    apply IHi.
    tauto.
    destruct H1.
    clear H.
    apply skipn_no_loop' in H0.
    tauto.
Qed.

Lemma skipn_prop : forall (P : prop) (i k : nat),
  forall ss : sseq,
  i >= k -> ~ P ss.[i] -> ~ P (skipn (i - k) ss).[k].
Proof.
  intros.
  rewrite skipn_nth.
  replace (i - k + k) with i.
  auto.
  omega.
Qed.

(**)

Lemma le_safety_relation : 
  forall (i k : nat) (I : init) (T : trans) (P : prop),
  i <= k -> safety_k I T P k -> prop_k_init I T P i.
Proof.
  intros.
  apply Nat.lt_eq_cases in H. 
  destruct H.
  - induction k.  
    + easy.
    + destruct (Nat.lt_ge_cases i k).
      * assert (H2 : safety_k I T P k /\ prop_k_init I T P k).
        destruct k; firstorder; now rewrite <- plus_n_O in H0.
        apply IHk.
        auto.
        tauto.
      * apply gt_S_le in H.
        assert (H2 : i = k) by omega.
        destruct k ;rewrite H2; firstorder.
  - subst.
    destruct k; firstorder.
Qed.

(**)

Lemma split_no_loop' : forall (ss:sseq) (o i k j:nat),
  no_loop' ss o i (j+k) -> no_loop' ss o i j.
Proof.
  induction k.
  - intros.
    rewrite -> plus_0_r in H.
    apply H.
  - intros.
    rewrite <- Nat.add_succ_comm in H.
    apply IHk in H.
    simpl in H.
    destruct H.
    apply H.
Qed.

Lemma split_no_loop_former : forall (ss : sseq) (j i : nat),
  no_loop ss 0 (i+j) -> no_loop ss 0 i.
Proof.
  induction j.
  - intros.
    now rewrite <- plus_n_O in H.
  - intros.
    rewrite <- Nat.add_succ_comm in H.
    apply IHj in H.
    simpl in H.
    destruct H.
    apply H0.
Qed.


Local Lemma split_no_loop_latter'' : 
  forall (ss : sseq) (i j k : nat),
  no_loop' ss i (S k) (S j) <->
    ss.[(i + (S k))] <> ss.[i] /\
    no_loop' ss (S i) k j.
Proof.
  destruct j.
  - simpl. 
    intros.
    now rewrite <- Nat.add_succ_l;
      rewrite Nat.add_succ_comm; rewrite Nat.add_1_r.
  - induction j.
    + simpl.
      intros.
      do 2 rewrite <- Nat.add_succ_r.
      do 1 rewrite ->  Nat.add_1_r.
      tauto.
    + intros.
      simpl in *.
      assert (forall (p1 p2 p3 p4 p5:Prop),
        (p1 <-> (p2 /\ p3 /\ p4) /\ p5) <->
        (p1 <-> p2 /\ (p3 /\ p4) /\ p5)) by tauto.
      rewrite <- H.
      rewrite <- IHj.
      do 2 rewrite <- Nat.add_succ_r.
      tauto.
Qed.

Local Lemma split_no_loop_latter' : forall (ss : sseq) (j i : nat),
  no_loop ss i (S j) -> no_loop ss (S i) j.
Proof.
  induction j.
  intros.
  - destruct i; firstorder.
  - intros.
    assert (no_loop ss (S i) (S j) <->
      no_loop' ss (S i) (S j) j /\ no_loop ss (S i) j)
      by (destruct j; firstorder).
    apply H0.
    assert (no_loop ss i (S (S j)) <->
      no_loop' ss i (S (S j)) (S j) /\ 
      no_loop ss i (S j))
      by (destruct j; firstorder).
    apply -> H1 in H.
    destruct H.
    split.
    now apply split_no_loop_latter'' in H.
    now apply IHj in H2.
Qed.

Lemma split_no_loop_latter : forall (ss : sseq) (i j : nat),
  no_loop ss 0 (i+j) -> no_loop ss i j.
Proof.
  induction i.
  - easy.
  - intros.
    rewrite Nat.add_succ_comm in H.
    apply IHi in H.
    now apply split_no_loop_latter' in H.
Qed.

Lemma split_no_loop : forall (ss : sseq) (i j: nat),
    no_loop ss 0 (i+j) ->
    no_loop ss 0 i /\ no_loop ss i j.
Proof.
  intros.
  split.
  - now apply split_no_loop_former in H.
  - now apply split_no_loop_latter in H.
Qed.

Lemma cons_path : forall (ss : sseq) (T : trans) (i j : nat),
  T ss.[i] ss.[S i] /\ path T ss (S i) j <->
  path T ss i (S j).
Proof.
  destruct j.
  - unfold path.
    rewrite Nat.add_0_r.
    rewrite Nat.add_1_r.
    tauto.
  - induction j. 
    + simpl.
      rewrite Nat.add_1_r.
      do 2 rewrite Nat.add_succ_r.
      rewrite Nat.add_0_r.
      tauto.
    + simpl.
      split; firstorder;
      now do 5 rewrite Nat.add_succ_r in *.
Qed.

Lemma snoc_path : forall (ss : sseq) (T : trans) (i j: nat),
  path T ss i (S j) <->
  path T ss i j /\ T ss.[i+j] ss.[S (i+j)].
Proof.
  intros.
  simpl.
  replace (i + S j) with (S (i + j)).
  tauto.
  auto.
Qed.

Lemma skip1_path : forall (T : trans) (i j : nat),
  forall ss : sseq,
  path T ss (S i) j -> path T (skipn 1 ss) i j.
Proof.
  intros.
  induction j.
  - simpl. intuition.
  - rewrite -> snoc_path in H.
    destruct H.
    rewrite -> snoc_path.
    split.
    * apply IHj.
      apply H.
    * do 2 rewrite skipn_nth.
      replace (1+(i+j)) with (S i + j).
      replace (1+S (i+j)) with (S (S i + j)).
      apply H0.
      auto. 
      auto.
Qed.

Lemma shift_path : forall (ss : sseq) (T : trans) (i j : nat), 
  path T ss 0 i /\ path T ss i (S j) <-> 
  path T ss 0 (S i) /\ path T ss (S i) j .
Proof.
  intros.
  rewrite snoc_path with (i:=0).
  rewrite and_assoc.
  rewrite cons_path.
  reflexivity.
Qed.

Lemma split_path : forall (ss : sseq) (T : trans) (i j: nat),
  path T ss 0 (i+j) <-> path T ss 0 i /\ path T ss i j.
Proof.
  induction i.
  - simpl.
    tauto.
  - split.
    + intros.
      rewrite -> Nat.add_succ_comm in H.
      apply IHi in H.
      apply shift_path.
      apply H.
    + intros.
      apply shift_path in H.
      apply IHi in H.
      rewrite <- Nat.add_succ_comm in H.
      apply H.
Qed.

Lemma split_loop_free : forall  (ss : sseq) (T : trans) (i j : nat),
  loop_free T ss 0 (i+j) -> 
  loop_free T ss 0 i /\ loop_free T ss i j.
Proof.
  unfold loop_free.
  intros.
  destruct H.
  apply split_path in H.
  apply split_no_loop in H0.
  tauto.
Qed.

Lemma split_path_lf :
  forall (T:trans) (ss:sseq) (m n:nat),
    loop_free T ss 0 m /\ path T ss m n ->
    path T ss 0 (m+n).
Proof.
  induction m.
  - intros.
    unfold loop_free in H.
    decompose [and] H; clear H.
    tauto.
  - intros.
    unfold loop_free in H.
    decompose [and] H; clear H.
    assert (path T ss 0 (S m) /\ path T ss (S m) n) by auto.
    clear H1 H2.
    apply shift_path in H.
    destruct H.
    rewrite <- Nat.add_1_r in H3.
    apply split_no_loop_former in H3.
    assert (loop_free T ss 0 m /\ path T ss m (S n)) by (unfold loop_free; tauto).
    clear H3 H H0.
    apply IHm in H1.
    rewrite <- Nat.add_succ_comm in H1.
    apply H1.
Qed.

Lemma split_lf_path :
  forall (T:trans) (ss:sseq) (n:nat),
    path T ss 0 (n+1) -> 
    ss.[n+1] <> ss.[n] ->
    path T ss 0 n /\ loop_free T ss n 1.
Proof.
  induction n.
  - intros.
    unfold path.
    unfold loop_free.
    unfold no_loop.
    unfold no_loop'.
    rewrite -> Nat.add_0_l in *.
    tauto.
  - intros.
    split.
    + rewrite -> Nat.add_1_r in H.
      rewrite -> snoc_path in H.
      destruct H.
      apply H.
    + unfold loop_free.
      split.
      * rewrite -> split_path in H.
        destruct H.
        apply H1.
      * unfold no_loop.
        unfold no_loop'.
        (*rewrite -> Nat.add_0_r.*)
        tauto.
Qed.

(**)

Lemma lf_path :
  forall (T:trans) (ss:sseq) (i:nat),
  loop_free T ss 0 i ->
  path T ss 0 i.
Proof.
  intros.
  induction i.
  - simpl. intuition.
  - simpl.
    rewrite <- Nat.add_1_r in H.
    apply split_loop_free in H.
    destruct H.
    split.
    + apply IHi in H.
      apply H.
    + unfold loop_free in H0.
      destruct H0.
      unfold path in H0.
      destruct H0.
      rewrite -> Nat.add_0_r in H2.
      rewrite -> Nat.add_1_r in H2.
      apply H2.
Qed.

Lemma no_loop'_neq' :
  forall (ss:sseq) (o i j:nat),
  i >= j -> no_loop' ss o (S i) (i-j) ->
  ss.[o + S i] <> ss.[o+(i-j)].
Proof.
  intros.
  destruct j.
  - destruct i.
    + rewrite -> Nat.sub_0_r in *.
      rewrite -> Nat.add_0_r.
      simpl in H0.
      apply H0.
    + rewrite -> Nat.sub_0_r in *.
      simpl in H0.
      destruct H0.
      apply H1.
  - remember (i - S j) as k.
    destruct k.
    + simpl in H0.
      rewrite -> Nat.add_0_r.
      apply H0.
    + simpl in H0.
      destruct H0.
      apply H1.
Qed.

Lemma no_loop'_neq :
  forall (ss:sseq) (o i j:nat),
  no_loop' ss o (S i) i ->
  i > j -> ss.[o + S i] <> ss.[o+j].
Proof.
  intros.
  remember (i-j) as k.
  replace j with (i-k).
  apply no_loop'_neq'.
  omega.
  assert (j = i - k) by omega.
  rewrite <- H1.
  assert (i = j + k) by omega.
  rewrite -> H2 in H.
  apply split_no_loop' in H.
  rewrite <- H2 in H.
  apply H.
  omega.
Qed.

Lemma neq_states_no_loop' :
  forall (ss:sseq) (o i j:nat),
  i > j -> 
  no_loop' ss o (S i) j -> ss.[o + S i] <> ss.[o+(S j)] ->
  no_loop' ss o (S i) (S j).
Proof.
  intros.
  destruct j.
  - simpl.
    split.
    + simpl in H0.
      apply H0.
    + apply H1.
  - simpl.
    split.
    + simpl in H0.
      apply H0.
    + apply H1.
Qed.

Lemma eq_states_not_no_loop' :
  forall (ss:sseq) (o i j:nat),
  i > j -> ss.[o + S i] = ss.[o+j] ->
  ~ no_loop' ss o (S i) i.
Proof.
  intros.
  assert (~(ss.[o + S i] <> ss.[o+j])) by tauto.
  contradict H1.
  apply no_loop'_neq.
  apply H1.
  apply H.
Qed.

Lemma lf_loop_path :
  forall (T:trans) (i j:nat) (ss:sseq),
  loop_free T ss 0 i -> 
  path T ss 0 j -> ~ no_loop ss 0 j -> 
  (* i <= j *) ~ i > j.
Proof.
  intros.
  contradict H1.

  unfold loop_free in H.
  destruct H.

  remember (i-j) as k.
  assert (i = j+k) by omega.

  rewrite -> H3 in H2.
  apply split_no_loop in H2.
  destruct H2.
  apply H2.
Qed.

Lemma lf_loop_path' :
  forall (T:trans) (i j:nat) (ss:sseq),
  loop_free T ss 0 i -> 
  i > j -> 
  ~no_loop ss 0 j -> ~path T ss 0 j.
Proof.
  intros.
  assert (~~(i > j)) by omega.
  contradict H2.
  revert H H2 H1.
  apply lf_loop_path.
Qed.

Lemma lf_loop_path'' :
  forall (T:trans) (i j:nat) (ss:sseq),
  loop_free T ss 0 i -> 
  path T ss 0 j -> i > j -> 
  no_loop ss 0 j.
Proof.
  intros.
  apply NNPP.
  contradict H1.
  revert H H0 H1.
  apply lf_loop_path.
Qed.

Lemma split_skipn :
  forall (m n i : nat) (ss : sseq),
  (skipn (m+n) ss).[i] = (skipn m (skipn n ss)).[i].
Proof.
  intros.
  do 3 rewrite -> skipn_nth.
  assert (m + n + i = n + (m + i)) by omega.
  rewrite -> H.
  reflexivity.
Qed.

(*
Require Import FunctionalExtensionality.

Lemma split_skipn' :
  forall (m n : nat) (ss : sseq),
  (skipn (m+n) ss) = (skipn m (skipn n ss)).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  apply split_skipn.
Qed.
*)

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

Lemma safety_lf_path :
  forall (I:init) (T:trans) (P:prop) (k:nat),
    (forall (j:nat), j < k -> prop_k_init I T P j) ->
    prop_k_init_lf I T P k ->
    prop_k_init I T P k.
Proof.
  unfold prop_k_init.
  intros.
  assert ((forall (p1 p2 p3:Prop), ((p1 /\ p3 -> ~p2) <-> ~(p1 /\ p2 /\ p3)))) as A by tauto.
  apply A.
  intros; destruct H1.

  assert (~loop_free T ss 0 k) as A0.
  { revert H1 H2.
    assert ((forall (p1 p2 p3:Prop), (~(p1 /\ p3 /\ p2) <-> (p1 -> p2 -> ~p3)))) as A1 by tauto.
    apply A1; clear A1.
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
    assert (~ j+d <= S k -> j+d > S k) as A4 by omega.
    apply A4; clear A4.
    contradict A3.
    split.
    + apply H1.
    + split.
      * apply shorter_ss_prop1 with (i:=j) (ss1:=ss).
        { apply H3. }
        { unfold shorter_ss_u in H7.
          symmetry.
          replace j with (j+0).
          rewrite -> H7.
          replace (j+0) with (j-0).
          rewrite H5.
          reflexivity.
          omega. omega. omega. }
        { easy. }
      * apply H2.
Qed.

(* eof *)