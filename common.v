Require Export ZArith.
(*Require Export SMTC.Tactic.
Require Import SMTC.Integers.*)

Open Scope nat_scope.

(* utility axiom for proof by SMT solvers. *)
Axiom by_smt : forall P : Prop, P.

Set Implicit Arguments.

(**)

Definition state : Type := nat -> Z.
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

(*Lemma skipn_nth: forall A:Type, forall l:list A, forall n m:nat, forall d:A,
  nth m (skipn n l) d = nth (n+m) l d.
Proof.
  intros A l.
  induction l; intros; 
    destruct m; destruct n; simpl; auto.
Qed.
*)

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
  | S O => T ss.[o] ss.[o+1]
  | S len' => path T ss o len' /\ T ss.[len'+o] ss.[len+o]
  end.

Fixpoint invariance (P : prop) (ss : sseq) (len : nat) : Prop :=
  match len with
  | O => P ss.[0]
  | S len' => invariance P ss len' /\ P ss.[len]
  end.

Fixpoint neq_states (si sj : state) (n : nat) : Prop :=
  match n with
  | O => True
  | S O => ~ (si 0 = sj 0)
  | S n' => neq_states si sj n' \/ ~ (si n' = sj n')
  end.

Fixpoint no_loop' (ss : sseq) (size o n m: nat) : Prop :=
  match m with
  | O => neq_states (ss.[o+n]) (ss.[o+m]) size
  | S m' => neq_states (ss.[o+n]) (ss.[o+m]) size /\
      no_loop' ss size o n m' 
  end.

Fixpoint no_loop (ss : sseq) (size o k : nat) : Prop :=
  match k with
  | O => True
  | 1 => no_loop' ss size o 1 0
  | S k' => no_loop' ss size o k k' /\ no_loop ss size o k'
  end.

Definition loop_free (T : trans) (ss : sseq) (size o k: nat) : Prop :=
  path T ss o k /\ no_loop ss size o k.

Definition lasso (I : init) (T : trans) (P : prop) (size k : nat) : Prop :=
  forall ss : sseq,
  ~ (I ss.[0] /\ loop_free T ss size 0 k).

Definition violate_loop_free (I : init) (T : trans)
           (P : prop) (size k: nat) : Prop :=
  forall ss : sseq,
  ~ (loop_free T ss size 0 k /\ ~ P ss.[k ]).


Definition safety_k_init (I : init) (T : trans) (P : prop) (k : nat) : Prop :=
  forall ss : sseq,
  ~ (I ss.[0] /\ path T ss 0 k /\ ~ P ss.[k]).

Definition safety_k_init_lf  (I : init) (T : trans) (P : prop) (size k : nat) : Prop :=
  forall ss : sseq,
  ~ (I ss.[0] /\ loop_free T ss size 0 k /\ ~ P ss.[k]).

Fixpoint safety_k (I : init) (T : trans) (P : prop) (k : nat) : Prop :=
  match k with
  | O => safety_k_init I T P k
  | S k' => safety_k I T P k' /\ safety_k_init I T P k
  end.

Fixpoint safety_k_offset (P : prop) (ss : sseq) (o k: nat) : Prop :=
  match k with
  | O => True
  | S 0  => P ss.[o]
  | S k' => safety_k_offset P ss o k' /\ P ss.[o+k']
  end.

(**)

Lemma path_skipn : forall (T : trans) (i j : nat),
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
      rewrite <- plus_n_O.
      tauto.
    }
    apply H0.
    clear H0.

    split.
    apply IHi.
    destruct i; firstorder.
    clear IHi.
    rewrite skipn_nth.
    rewrite skipn_nth.
    replace (j + i) with (i + j).
    replace (j + S i) with (S i + j).
    simpl in *.
    destruct i.
    simpl in *.
    rewrite Nat.add_1_r in H.
    auto.
    tauto.
    omega.
    omega.
Qed.

Lemma no_loop'_skipn : forall (size i j k : nat),
  forall ss : sseq,
  no_loop' ss size j k i ->
  no_loop' (skipn j ss) size 0 k i.
Proof.
  intros.
  destruct i.
  - simpl in *.
    do 2 rewrite skipn_nth.
    auto.

  - induction i.
    + simpl in *.
      do 3 rewrite skipn_nth.
      simpl in *.
      auto.

    + simpl.
      split.
      simpl in H.
      do 2 rewrite skipn_nth.
      tauto.

      simpl in H.
      split.
      do 2 rewrite skipn_nth.
      tauto.
      firstorder.
Qed.

Lemma no_loop_skipn : forall (size i j : nat),
  forall ss : sseq,
  no_loop ss size j i -> no_loop (skipn j ss) size 0 i.
Proof.
  intros.
  induction i.
  - auto.

  - assert (H1 : no_loop ss size j i /\ no_loop' ss size j (S i) i)
      by ( destruct i; firstorder; rewrite <- plus_n_O in *).
    clear H.

    assert ( H :no_loop (skipn j ss) size 0 i /\
      no_loop' (skipn j ss) size 0 (S i) i -> 
      no_loop (skipn j ss) size 0 (S i) ).
    intros.
    destruct i; firstorder; rewrite <- plus_n_O in *.
    apply H.
    clear H.
    split.
    apply IHi.
    tauto.
    destruct H1.
    clear H.
    apply no_loop'_skipn in H0.
    tauto.
Qed.

Lemma prop_skipn : forall (P : prop) (i k : nat),
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
  i <= k -> safety_k I T P k -> safety_k_init I T P i.
Proof.
  intros.
  apply Nat.lt_eq_cases in H. 
  destruct H.
  - induction k.  
    + easy.
    + destruct (Nat.lt_ge_cases i k).
      * assert (H2 : safety_k I T P k /\ safety_k_init I T P k).
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

Lemma split_no_loop_former : forall (ss : sseq) (size j i : nat),
  no_loop ss size 0 (i+j) -> no_loop ss size 0 i.
Proof.
  induction j.
  - intros.  rewrite <- plus_n_O in H.
    easy.
  - intros.
    rewrite <- Nat.add_succ_comm in H.
    apply IHj in H.
    assert(no_loop ss size 0 (S i) <-> 
      no_loop ss size 0 i /\ no_loop' ss size 0 (S i) i)
      by (destruct i; firstorder).
    apply H0 in H.
    firstorder.
Qed.

Local Lemma split_no_loop_latter'' : forall (ss : sseq) (size i j k : nat) ,
  no_loop' ss size i (S k) (S j) <->
    neq_states ss.[(i + (S k))] ss.[i] size /\
    no_loop' ss size (S i) k j.
Proof.
  destruct j.
  - simpl. rewrite <-  plus_n_O.
    intros.
    now rewrite <- Nat.add_succ_l;
      rewrite Nat.add_succ_comm; rewrite Nat.add_1_r.
  - induction j.
    + simpl.
      intros.
      now rewrite <- Nat.add_succ_r; rewrite <- Nat.add_succ_r;
        rewrite <-  Nat.add_1_r; rewrite <- (plus_n_O i);
          rewrite <- (Nat.add_1_r i).
    + intros.
      simpl in *.
      assert (neq_states ss.[(i + S k)] ss.[i] size /\
        neq_states ss.[S (i + k)] ss.[S (i + S (S j))] size /\
        neq_states ss.[S (i + k)] ss.[S (i + S j)] size /\
        no_loop' ss size (S i) k j <->
          ( neq_states ss.[(i + S k)] ss.[i] size /\
            neq_states ss.[S (i + k)] ss.[S (i + S j)] size /\
            no_loop' ss size (S i) k j ) /\
          neq_states ss.[S (i + k)] ss.[S (i + S (S j))] size)
        by tauto.
      now rewrite H; rewrite <- IHj; rewrite <- Nat.add_succ_r;
        rewrite <- Nat.add_succ_r.
Qed. (*26*)

Local Lemma split_no_loop_latter' : forall (ss : sseq) (size j i : nat),
  no_loop ss size i (S j) -> no_loop ss size (S i) j.
Proof.
  induction j.
  intros.
  - destruct i; firstorder.
  - intros.
    assert (no_loop ss size (S i) (S j) <->
      no_loop' ss size (S i) (S j) j /\ no_loop ss size (S i) j)
      by (destruct j; firstorder).
    apply H0.
    assert (no_loop ss size i (S (S j)) <->
      no_loop' ss size i (S (S j)) (S j) /\ 
      no_loop ss size i (S j))
      by (destruct j; firstorder).
    apply -> H1 in H.
    destruct H.
    split.
    now apply split_no_loop_latter'' in H.
    now apply IHj in H2.
Qed. (*19*)

Lemma split_no_loop_latter : forall (ss : sseq) (size i j : nat),
  no_loop ss size 0 (i+j) -> no_loop ss size i j.
Proof.
  induction i.
  - easy.
  - intros.
    rewrite Nat.add_succ_comm in H.
    apply IHi in H.
    now apply split_no_loop_latter' in H.
Qed. (*7*)

Lemma split_no_loop : forall (ss : sseq) (size i j: nat),
    no_loop ss size 0 (i+j) ->
    no_loop ss size 0 i /\ no_loop ss size i j.
Proof.
  intros.
  split.
  - now apply split_no_loop_former in H.
  - now apply split_no_loop_latter in H.
Qed.

Lemma snoc_path : forall (ss : sseq) (T : trans) (i : nat),
  path T ss 0 (S i) <->
  path T ss 0 i /\ T ss.[i] ss.[S i].
Proof.
  intros. 
  destruct i. 
  - unfold path.
    tauto.
  - unfold path; fold path; simpl.
    rewrite <- plus_n_O.
    tauto.
Qed. (*8*)


Lemma cons_path : forall (ss : sseq) (T : trans) (i j : nat),
  T ss.[i] ss.[S i] /\ path T ss (S i) j <->
  path T ss i (S j).
Proof.
  destruct j.
  - unfold path. simpl.
    rewrite Nat.add_1_r.
    tauto.
  - induction j. simpl. 
    rewrite Nat.add_1_r.
    tauto.
    simpl. 
    split; firstorder; now rewrite Nat.add_succ_r in *.
Qed. (*13*)

Lemma shift_path : forall (ss : sseq) (T : trans) (i j : nat), 
  path T ss 0 i /\ path T ss i (S j) <-> 
  path T ss 0 (S i) /\ path T ss (S i) j .
Proof.
  intros.
  rewrite snoc_path.
  rewrite and_assoc.
  rewrite cons_path.
  reflexivity.
Qed. (*5*)

Lemma split_path : forall (ss : sseq) (T : trans) (i j: nat),
  path T ss 0 (i+j) -> path T ss 0 i /\ path T ss i j.
Proof.
  induction i.
  - simpl.
    tauto.

  - intros.
    rewrite -> Nat.add_succ_comm in H.
    apply IHi in H.
    apply shift_path.
    apply H.
Qed. (*8*)

Lemma split_loop_free : forall  (ss : sseq) (T : trans) (size i j : nat),
  loop_free T ss size 0 (i+j) -> 
  loop_free T ss size 0 i /\ loop_free T ss size i j.
Proof.
  unfold loop_free.
  intros.
  destruct H.
  apply split_path in H.
  apply split_no_loop in H0.
  tauto.
Qed.

(* eof *)