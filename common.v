Require Export ZArith.
Require Export logic.
Require Import Fourier.
(*Require Import FunctionalExtensionality.*)
(*Require Export SMTC.Tactic.
Require Import SMTC.Integers.*)

Open Scope nat_scope.

(* utility axiom for proof by SMT solvers. *)
Axiom by_smt : forall P : Prop, P.

Set Implicit Arguments.

(**)

(*Definition state : Type := nat -> Z.*)
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

(*
Fixpoint neq_states (si sj : state) (size : nat) : Prop :=
  match size with
  | O => True
  | S sz' => neq_states si sj sz' \/ ~ (si sz' = sj sz')
  end.
*)

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
    (*rewrite <-  plus_n_O.*)
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
      (*assert (neq_states ss.[(i + S k)] ss.[i] size /\
        neq_states ss.[S (i + k)] ss.[S (i + S (S j))] size /\
        neq_states ss.[S (i + k)] ss.[S (i + S j)] size /\
        no_loop' ss size (S i) k j <->
          ( neq_states ss.[(i + S k)] ss.[i] size /\
            neq_states ss.[S (i + k)] ss.[S (i + S j)] size /\
            no_loop' ss size (S i) k j ) /\
          neq_states ss.[S (i + k)] ss.[S (i + S (S j))] size)
        by tauto.*)
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

(*
Lemma snoc_path : forall (ss : sseq) (T : trans) (i : nat),
  path T ss 0 (S i) <->
  path T ss 0 i /\ T ss.[i] ss.[S i].
Proof.
  intros. 
  destruct i. 
  - unfold path.
    tauto.
  - unfold path; fold path; simpl.
    tauto.
Qed.
*)

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

(*
Lemma split_path_init_lf :
  forall (I:init) (T:trans) (size m n:nat) (ss:sseq),
    I ss.[0] /\ loop_free T ss size 0 m /\ path T ss m n ->
    I ss.[0] /\ path T ss 0 (m+n).
Proof.
  induction m.
  - intros.
    (*rewrite -> Nat.add_0_r in *.*)
    unfold loop_free in H.
    decompose [and] H; clear H.
    tauto.
  - intros.
    unfold loop_free in H.
    decompose [and] H; clear H.
    assert (path T ss 0 (S m) /\ path T ss (S m) n) by auto.
    clear H3 H1.
    apply shift_path in H.
    (*rewrite <- Nat.add_succ_r in H.
    rewrite -> Nat.add_succ_comm in H.*)
    destruct H.
    rewrite <- Nat.add_1_r in H4.
    apply split_no_loop_former in H4.
    assert (I ss.[0] /\ loop_free T ss size 0 m /\ path T ss m  (S n)) by (unfold loop_free; tauto).
    clear H0 H1 H4 H.
    apply IHm in H2.
    rewrite <- Nat.add_succ_comm in H2.
    apply H2.
Qed.
*)

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

(*
Lemma shift_path_init' :
  forall (I:init) (T:trans) (ss:sseq) (m n:nat),
  I ss.[m] /\ ss.[m] = ss.[n] ->
  I ss.[n].
Proof.
  intros.
  destruct H.
  rewrite <- H0.
  apply H.
Qed.
*)

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

(*
Lemma neq_states_no_loop' :
  forall (o i:nat) (ss:sseq),
  (forall (j:nat), i >= j -> ss.[o + S i] <> ss.[o+j]) ->
  no_loop' ss o (S i) i.
Proof.
  intros.
  unfold no_loop'.

  induction i.
  - simpl.
    assert (ss.[o+1] <> ss.[o+0]) by (apply H; intuition).
    rewrite -> Nat.add_0_r in H0.
    apply H0.
  - simpl.
    split.
    + unfold no_loop'.

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
*)

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

(*
Fixpoint loop' (ss : sseq) (o i j: nat) : Prop :=
  match j with
  | O => ss.[o+i] = ss.[o]
  | S j' => loop' ss o i j' \/ ss.[o+i] = ss.[o+j]
  end.

Lemma not_no_loop'_loop' :
  forall (j o i:nat) (ss:sseq),
  ~ no_loop' ss o i j ->
  loop' ss o i j.
Proof.
  induction j.
  - intros.
    simpl.
    simpl in H.
    tauto.
  - intros.
    simpl.
    simpl in H.
    apply not_and_or in H.
    destruct H.
    + apply IHj in H.
      left.
      apply H.
    + right.
      tauto.
Qed.
*)

(*
Fixpoint no_loop (ss : sseq) (o k : nat) : Prop :=
  match k with
  | O => True
  | S k' => no_loop' ss o k k' /\ no_loop ss o k'
  end.
*)

(*
Definition eq_states (s1 s2 : state) : bool :=
  match (s1 - s2)%Z with
  | 0%Z => true
  | _ => false
  end.

Fixpoint is_loop (ss : sseq) (o i j : nat) : bool :=
  match j with
  | O => eq_states ss.[o+i] ss.[o]
  | S j' => if eq_states ss.[o+i] ss.[o+j] then true
            else is_loop ss o i j'
  end.

Fixpoint find_state (ss : sseq) (o i j : nat) : nat :=
  match j with
  | O => i
  | S j' => if eq_states ss.[o+i] ss.[o+j'] then j
            else find_state ss o i j'
  end.

Fixpoint loop_state (ss : sseq) (o i : nat) : nat :=
  match i with
  | O => o
  | S j => if is_loop ss o i j then i
           else loop_state ss o j
  end.
*)

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

(*
Definition shorter_ss' (ss1 ss2 : sseq) (o i : nat) : Prop :=
  let i1 := loop_state ss1 o i in
  let i2 := find_state ss1 o i1 i1 in
  forall (j:nat), 
    (j <= i2 /\ ss2.[j] = ss1.[j]) \/
    (j >=  i2 /\ ss2.[j] = ss1.[i1+(j-i2)]).
*)

(*
Definition shorter_ss (ss1 ss2 : sseq) (i d: nat) : Prop :=
  forall (j : nat),
  (j <= i /\ ss2.[j] = ss1.[j]) \/
  (j >= i /\ ss2.[j] = ss1.[j+d]).

Lemma skipn_shorter_ss :
  forall (i j d : nat) (ss1 ss2 : sseq),
  shorter_ss ss1 ss2 (i+j) d ->
  shorter_ss (skipn i ss1) (skipn i ss2) j d.
Proof.
  induction i.
  - intros.
    rewrite -> Nat.add_0_l in H.
    unfold shorter_ss.
    intros.
    do 3 rewrite -> skipn_nth.
    do 2 rewrite -> Nat.add_0_l.
    apply H.
  - intros.
    rewrite -> Nat.add_succ_comm in H.
    apply IHi in H.
    unfold shorter_ss.
    intros.
    unfold shorter_ss in H.
    assert(S j0 <= S j /\ (skipn i ss2).[S j0] = (skipn i ss1).[S j0] \/
       S j0 >= S j /\ (skipn i ss2).[S j0] = (skipn i ss1).[S j0 + d]) by easy.
    destruct H0.
    + destruct H0.
      left.
      split.
      { omega. }
      { rewrite <- Nat.add_1_l.
        do 2 rewrite -> split_skipn.
        do 2 rewrite -> skipn_nth with (n := 1).
        rewrite -> Nat.add_1_l.
        apply H1. }
    + destruct H0.
      { right.
        split.
        { omega. }
        { rewrite <- Nat.add_1_l.
          do 2 rewrite -> split_skipn.
          do 2 rewrite -> skipn_nth with (n := 1).
          rewrite -> Nat.add_1_l.
          replace (1+(j0+d)) with (S j0 + d).
          apply H1.
          omega. } }
Qed.

Definition shorter_ss' (ss1 ss2 : sseq) (i d: nat) : Prop :=
  forall (j : nat),
  (0 < j <= i /\ ss2.[j] = ss1.[j]) \/
  (0 < j /\ i <= j /\ ss2.[j] = ss1.[j + d]).

Lemma skipn_shorter_ss' :
  forall (i j d : nat) (ss1 ss2 : sseq),
  shorter_ss' (skipn i ss1) (skipn i ss2) j d ->
  shorter_ss' ss1 ss2 (i+j) d.
Proof.
  induction i.
  - intros.
    rewrite -> Nat.add_0_l.
    unfold shorter_ss' in *.
    intros.
    assert (
      0 < j0 <= j /\ (skipn 0 ss2).[j0] = (skipn 0 ss1).[j0] \/
      0 < j0 /\ j <= j0 /\ (skipn 0 ss2).[j0] = (skipn 0 ss1).[j0 + d]) by easy.
    do 3 rewrite -> skipn_nth in H0.
    do 2 rewrite -> Nat.add_0_l in H0.
    apply H0.
  - intros.
    rewrite -> Nat.add_succ_comm.

    (* rewrite <- Nat.add_1_r in H.
    do 2 rewrite -> split_skipn' in H.
    apply IHi in H. 
    *)

    apply IHi.
    unfold shorter_ss'.
    intros.
    unfold shorter_ss' in H.
    assert(
      0 < pred j0 <= j /\
      (skipn (S i) ss2).[pred j0] = (skipn (S i) ss1).[pred j0] \/
      0 < pred j0 /\ j <= pred j0 /\ 
       (skipn (S i) ss2).[pred j0] = (skipn (S i) ss1).[pred j0 + d]) by easy.

    destruct H0.
    + destruct H0.
      left; split.
      * omega.
      * rewrite <- Nat.add_1_l with (n := i) in H1.
        do 2 rewrite -> split_skipn in H1.
        do 2 rewrite -> skipn_nth with (n := 1) in H1.
        replace (1 + pred j0) with j0 in H1.
        apply H1.
        omega.
    + destruct H0.
      right; split.
      * omega.
      * split.
        { omega. }
        { rewrite <- Nat.add_1_l with (n := i) in H1.
          do 2 rewrite -> split_skipn in H1.
          do 2 rewrite -> skipn_nth with (n := 1) in H1.
          replace (1 + pred j0) with (j0) in H1.
          replace (1 + (pred j0 + d)) with (j0+d) in H1.
          apply H1.
          omega. omega. }
Qed.
*)

Definition shorter_ss_l (ss1 ss2 : sseq) (o i: nat) : Prop :=
  forall (j : nat), j <= i-o -> ss1.[i-j] = ss2.[i-j].

(*
Definition shorter_ss_l (ss1 ss2 : sseq) (i: nat) : Prop :=
  forall (j : nat), j <= i -> ss1.[j] = ss2.[j].
*)

Definition shorter_ss_u (ss1 ss2 : sseq) (i d: nat) : Prop :=
  forall (j : nat), ss1.[i+j] = ss2.[i+j+d].

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

(*
Lemma skipn_shorter_ss_l :
  forall (i j : nat) (ss1 ss2 : sseq),
  shorter_ss_l ss1 ss2 (i+j) ->
  shorter_ss_l (skipn i ss1) (skipn i ss2) j.
Proof.
  destruct i.
  - intros.
    unfold shorter_ss_l in *.
    intros.
    do 2 rewrite -> skipn_nth.
    do 1 rewrite -> Nat.add_0_l.
    apply H.
    apply H0.
  - unfold shorter_ss_l.
    intros.
    assert(S i + j0 <= S i + j -> ss1.[S i + j0] = ss2.[S i + j0]) by apply H.
    do 2 rewrite -> skipn_nth with (n := S i).
    apply H1.
    omega.
Qed.
*)

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

Lemma shorter_ss'_prop :
  forall (P : prop) (i d : nat) (ss1 ss2 : sseq),
  P ss1.[i] /\ shorter_ss' ss1 ss2 i d ->
  P ss2.[i].
Proof.
  induction i.
  - intros.
    destruct H.
    unfold shorter_ss' in H0.
    assert (0 <= 0 /\ ss2.[0] = ss1.[0] \/
      0 > 0 /\ ss2.[0] = ss1.[0+d]) by easy.
    destruct H1.
    + destruct H1.
      rewrite -> H2.
      apply H.
    + destruct H1.
      contradict H1.
      omega.
  - intros.
    rewrite <- Nat.add_1_l in *.
    rewrite <- skipn_nth in *.
    destruct H.
    apply skipn_shorter_ss' in H0.
    apply IHi with (d := d) (ss1 := (skipn 1 ss1)).
    tauto.
Qed.

Lemma shorter_ss'_prop' :
  forall (P : prop) (i d : nat) (ss1 ss2 : sseq),
  P ss1.[i+d+d] /\ shorter_ss' ss1 ss2 i d ->
  P ss2.[i+d].
Proof.
  induction i.
  - intros.
    destruct H.
    unfold shorter_ss' in H0.
    assert (d <= 0 /\ ss2.[d] = ss1.[d] \/
      d > 0 /\ ss2.[d] = ss1.[d+d]) by easy.
    destruct H1.
    + destruct H1.
      assert (d = 0) by omega.
      rewrite -> H3 in *.
      do 2 rewrite -> Nat.add_0_r in *.
      rewrite -> H2.
      apply H.
    + destruct H1.
      rewrite -> Nat.add_0_l in *.
      rewrite -> H2.
      apply H.
  - intros.
    rewrite <- Nat.add_1_l in H.
    rewrite <- skipn_nth in *.
    destruct H.
    apply skipn_shorter_ss' in H0.
    rewrite <- Nat.add_1_r.
    rewrite -> split_skipn.
    apply skipn_shorter_ss'.
    apply IHi with (d := d) (ss1 := (skipn 1 ss1)).
    tauto.
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

Lemma not_no_loop_eq_states :
  forall (i o:nat) (ss:sseq),
  ~ no_loop ss o i ->
  (*
  exists (ss':sseq) (k:nat), k < i /\ ss.[o+i] = ss'.[o+k].
  *)
  ~(forall (ss':sseq) (k:nat), k >= i \/ ss.[o+i] <> ss'.[o+k]).
Proof.
  induction i.
  - intros.
    contradict H.
    simpl. intuition.
  - intros.
    simpl in H.
    apply not_and_or in H.
    destruct H.
    + apply not_no_loop'_eq_states in H.
      contradict H.
      intros.
      assert (k >= S i \/ ss.[o+S i] <> ss.[o+k]) by easy.
      destruct H0.
      * left.
        apply H0.
      * right.
        apply H0.
    + apply IHi in H.
      contradict H.
      intros.
      assert (S k >= S i \/ ss.[o+S i] <> ss.[o+S k]) by easy.
      destruct H0.
      * left.
        apply le_S_n in H0.
        apply H0.
      * Admitted.


Lemma loop_path_prev_state :
  forall (T:trans) (i:nat) (ss:sseq),
  path T ss 0 i -> ~ no_loop ss 0 i ->
  (* 
  exists (j:nat), j < i /\ ss.[i] = ss.[j].
  *)
  ~(forall (j:nat), j < i -> ss.[i] <> ss.[j]).
Proof.
  Admitted.

Lemma loop_path_prev_state' :
  forall (T:trans) (i:nat) (ss:sseq),
  path T ss 0 i ->
  (forall (j:nat), j < i -> ss.[i] <> ss.[j]) ->
  no_loop ss 0 i.
Proof.
  Admitted.

Lemma safety_lf_not_path :
  forall (I:init) (T:trans) (P:prop) (i j:nat),
    prop_k_init_lf I T P i -> i > j ->
    ~ prop_k_init I T P j.
Proof.
  Admitted.

Lemma safety_lf_path0 :
  forall (I:init) (T:trans) (P:prop),
    (forall (i:nat), prop_k_init_lf I T P i) ->
    prop_k_init I T P 0.
Proof.
  unfold prop_k_init.
  unfold prop_k_init_lf.
  intros.
  assert ((forall (p1 p2 p3:Prop), ((p1 /\ p3 -> ~p2) <-> ~(p1 /\ p2 /\ p3)))) by tauto.
  apply H0.
  intros.
  assert (~loop_free T ss 0 0).
  { revert H1.
    apply H0.
    apply H. }
  contradict H2.
  unfold loop_free.
  split.
  - apply H2.
  - simpl. intuition.
Qed.

Lemma safety_lf_path1 :
  forall (I:init) (T:trans) (P:prop),
    prop_k_init_lf I T P 0 ->
    prop_k_init_lf I T P 1 ->
    prop_k_init I T P 1.
Proof.
  unfold prop_k_init.
  unfold prop_k_init_lf.
  intros.
  assert ((forall (p1 p2 p3:Prop), ((p1 /\ p3 -> ~p2) <-> ~(p1 /\ p2 /\ p3)))) by tauto.
  apply H1.
  intros.
  assert (~loop_free T ss 0 1).
  { revert H2.
    apply H1.
    apply H0. }
  contradict H3.
  unfold loop_free.
  split.
  - apply H3.
  - simpl.
    destruct H2.
    split.
    contradict H4.
    rewrite -> H4.
    assert (loop_free T ss 0 0) by easy.
    revert H2 H5.
    apply imply_not_and3.
    apply H.
    intuition.
Qed.

Lemma safety_lf_path :
  forall (I:init) (T:trans) (P:prop) (k:nat),
    (forall (j:nat), prop_k_init_lf I T P j) ->
    (forall (j:nat), j < k -> prop_k_init I T P j) ->
    prop_k_init I T P k.
Proof.
  intros.
  unfold prop_k_init.
  intros.
  assert ((forall (p1 p2 p3:Prop), ((p1 /\ p3 -> ~p2) <-> ~(p1 /\ p2 /\ p3)))) by tauto.
  apply H1.
  intros.
  destruct H2.

  assert (~loop_free T ss 0 k).
  { revert H2 H3.
    assert ((forall (p1 p2 p3:Prop), (~(p1 /\ p3 /\ p2) <-> (p1 -> p2 -> ~p3)))) by tauto.
    apply H2.
    apply H. }

  unfold loop_free in H4.
  apply not_and_or in H4.
  destruct H4.
  apply H4.

  contradict H4.

  apply loop_path_prev_state' with (T:=T).
  apply H4.
  intros.

  assert (prop_k_init I T P j).
  apply H0. apply H5.

  unfold prop_k_init in H6.

  remember (k-j) as j'.
  replace k with (j+j') in H4.
  apply split_path in H4.
  destruct H4.

  assert (P ss.[j]).
  revert H2 H4.
  apply imply_not_and3.
  apply H6.

  contradict H3.
  rewrite -> H3.
  apply H8.

  omega.
Qed.

Lemma safety_lf_path' :
  forall (I:init) (T:trans) (P:prop) (k:nat),
    (forall (j:nat), j < k -> prop_k_init I T P j) ->
    prop_k_init_lf I T P k ->
    prop_k_init I T P k.
Proof.
  intros.
  unfold prop_k_init.
  intros.
  assert ((forall (p1 p2 p3:Prop), ((p1 /\ p3 -> ~p2) <-> ~(p1 /\ p2 /\ p3)))) by tauto.
  apply H1.
  intros.
  destruct H2.

  assert (~loop_free T ss 0 k).
  { revert H2 H3.
    assert ((forall (p1 p2 p3:Prop), (~(p1 /\ p3 /\ p2) <-> (p1 -> p2 -> ~p3)))) by tauto.
    apply H2.
    apply H0. }

  unfold loop_free in H4.
  apply not_and_or in H4.
  destruct H4.
  apply H4.

  contradict H4.

  apply loop_path_prev_state' with (T:=T).
  apply H4.
  intros.

  assert (prop_k_init I T P j).
  { apply H. apply H5. }

  unfold prop_k_init in H6.

  remember (k-j) as j'.
  replace k with (j+j') in H4.
  apply split_path in H4.
  destruct H4.

  assert (P ss.[j]).
  revert H2 H4.
  apply imply_not_and3.
  apply H6.

  contradict H3.
  rewrite -> H3.
  apply H8.

  omega.
Qed.


(*

Lemma safety_lf_path :
  forall (I:init) (T:trans) (P:prop) (size:nat) (i:nat),
    (forall (i:nat), prop_k_init_lf I T P size i) ->
    prop_k_init I T P i.
Proof.
  unfold prop_k_init.
  unfold prop_k_init_lf.
  intros.
  apply and_imply_not_and3.
  intros.
  destruct H0.
  assert (no_loop ss size 0 i \/ ~no_loop ss size 0 i) by tauto.
  destruct H2.
  - assert (loop_free T ss size 0 i) by easy.
    revert H0 H3.
    apply imply_not_and3.
    apply H.
  - 


  (*unfold prop_k_init.
  unfold prop_k_init_lf.*)
  induction i.
  - unfold prop_k_init.
    unfold prop_k_init_lf.
    intros.
    assert (loop_free T ss size 0 0) by easy.
    apply and_imply_not_and3.
    intros.
    destruct H1.
    revert H1 H0.
    apply imply_not_and3.
    apply H.
  - intros.
    unfold prop_k_init.
    intros.
    apply and_imply_not_and3.
    intros.
    destruct H0.
    assert (no_loop ss size 0 (S i) \/ ~no_loop ss size 0 (S i)) by tauto.
    destruct H2.
    + unfold prop_k_init_lf in H.
      assert (loop_free T ss size 0 (S i)) by easy.
      revert H0 H3.
      apply imply_not_and3.
      apply H.


    assert (neq_states ss.[S i] ss.[i] size \/
      ~neq_states ss.[S i] ss.[i] size) by tauto.
    destruct H2.
    + rewrite <- Nat.add_1_r in H1.
      (*rewrite split_path in H1.
      destruct H1.*)
      assert (loop_free T ss size i 1).
      { apply split_lf_path.
        apply H1.
        rewrite -> Nat.add_1_r.
        apply H2. }
      
      
      assert ().


    apply IHi.
    apply H.
    unfold prop_k_init.
    intros.


Lemma safety_lf_path' :
  forall (I:init) (T:trans) (P:prop) (size:nat),
    (forall (i:nat), prop_k_init_lf I T P size i) ->
    (forall (i j:nat), i >= j -> prop_k_init I T P j).
Proof.
  intros.
  unfold prop_k_init.
  unfold prop_k_init_lf in H.
  (*unfold loop_free in H.*)
  intros.
  induction i.
  - assert (j = 0) by intuition.
    assert (no_loop ss size 0 j) by now rewrite -> H1.
    apply and_imply_not_and3.
    intros.
    destruct H3.
    assert (loop_free T ss size 0 j) by now unfold loop_free.
    revert H3 H5.
    apply imply_not_and3.
    apply H.
  - apply IHi. Admitted.

(*  - assert (loop_free T ss size 0 j \/ ~loop_free T ss size 0 j) by tauto.
    destruct H1.
    + apply and_imply_not_and3.
      intros.
      destruct H2.
      revert H2 H1.
      apply imply_not_and3.
      apply H.
    + contradict H1.
      decompose [and] H1; clear H1.
      unfold loop_free.
      split.
      * apply H4.
      * assert (~no_loop ss size 0 j).
        revert H2 H4 H5.
        assert (forall (p1 p2 p3 p4:Prop), 
          ~(p1 /\ (p2 /\ p4) /\ p3) -> (p1 -> p2 -> p3 -> ~p4)).
        { intros. revert H2 H3 H4.
          apply not_and_or in H1.
          destruct H1. tauto.
          apply not_and_or in H1.
          destruct H1.
          apply not_and_or in H1.
          destruct H1. tauto.
          tauto. tauto. }
        apply H1.
        apply H.
        Admitted.
*)

(*
Lemma safety_lf_path :
  forall (I:init) (T:trans) (P:prop) (size:nat),
    (forall (i:nat), prop_k_init_lf I T P size i) ->
    (forall (i:nat), prop_k_init I T P i).
Proof.
  intros.
  unfold prop_k_init.
  unfold prop_k_init_lf in H.
  (*unfold loop_free in H.*)
  intros.
  induction i.
  - assert (no_loop ss size 0 0) by intuition.
    apply and_imply_not_and3.
    intros.
    decompose [and] H1; clear H1.
    assert (loop_free T ss size 0 0) by now unfold loop_free.
    revert H2 H1.
    apply imply_not_and3.
    apply H.
  - assert (loop_free T ss size 0 (S i) \/ ~loop_free T ss size 0 (S i)) by tauto.
    destruct H0.
    + apply and_imply_not_and3.
      intros.
      decompose [and] H1; clear H1.
      revert H2 H0.
      apply imply_not_and3.
      apply H.
    + contradict H0.
      decompose [and] H0; clear H0.
      unfold loop_free.
      split.
      * apply H3.
      * simpl.

loop_free T ss size 0 k -> 
~(I ss.[0] /\ path T ss 0 k /\ ~P ss.[k])

Lemma safety_lf_path :
  forall (I:init) (T:trans) (P:prop) (size:nat),
    (forall (i:nat), prop_k_init_lf I T P size i) ->
    (forall (k i:nat), i <= k -> prop_k_init I T P i).
Proof.
  intros.
  unfold prop_k_init.
  unfold prop_k_init_lf in H.
  (*unfold loop_free in H.*)
  intros.
  induction k.
  - assert (i = 0) by intuition.
    assert (no_loop ss size 0 i) by now rewrite -> H1.
    apply and_imply_not_and3.
    intros.
    decompose [and] H3; clear H3.
    assert (loop_free T ss size 0 i) by now unfold loop_free.
    revert H4 H3.
    apply imply_not_and3.
    apply H.
  - 


Lemma safety_lf_path :
  forall (I:init) (T:trans) (P:prop) (size:nat),
    (forall (i:nat), prop_k_init_lf I T P size i) ->
    (forall (i:nat), prop_k_init I T P i).
Proof.
  intros.
  unfold prop_k_init.
  unfold prop_k_init_lf in H.
  (*unfold loop_free in H.*)
  intros.
  induction i.
  - assert (no_loop ss size 0 0) by intuition.
    apply and_imply_not_and3.
    intros.
    decompose [and] H1; clear H1.
    assert (loop_free T ss size 0 0) by now unfold loop_free.
    revert H2 H1.
    apply imply_not_and3.
    apply H.

  - assert (loop_free T ss size 0 (S i) \/ ~loop_free T ss size 0 (S i)) by tauto.
    destruct H0.
    + apply and_imply_not_and3.
      intros.
      decompose [and] H1; clear H1.
      revert H2 H0.
      apply imply_not_and3.
      apply H.
    + 
*)

(* eof *)