Require Import Coq.Strings.String.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Export Coq.fourier.Fourier.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.omega.Omega.
Require Import Compare_dec.
Require Export Coq.Lists.List.
Require Export Arith.
Require Export Arith.EqNat. 
Require Import SMTC.Tactic.
Require Import SMTC.Integers.

Open Scope string_scope.

Set SMT Solver "z3".
Set SMT Debug.

Local Open Scope nat_scope.
Local Axiom by_smt : forall P : Prop, P.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


Set Implicit Arguments.


Definition state : Type := nat -> Z.
Definition default (x : nat) := 99999%Z.

Notation "l _[ n ] " := (nth n l default)
                       (at level 60, right associativity).


Definition init : Type := state -> Prop.
Definition trans : Type := state -> state -> Prop.
Definition property : Type := state -> Prop.



(*Fixpoint ss_body (f : list state -> nat -> Prop)
         (l : list state) (iter n : nat) : Prop :=
  match iter with
  | 0 => forall s0 : state, f (l++[s0]) n
  | S iter' => forall s0 : state, ss_body f (l++[s0]) iter' n
  end.

Definition ss (f : list state -> nat -> Prop)
           (l : list state) (n : nat) : Prop :=
  ss_body f l n n.
*)

Fixpoint path (T : trans) (l : list state) (o len : nat) : Prop :=
  match len with
  | O => True
  | S O => T (l _[ o ]) (l _[(o+1)])
  | S len' => path T l o len' /\ T (l _[ (len'+o) ]) (l _[ (len+o) ])
  end.

Fixpoint invariance (P : property) (l : list state) (k : nat): Prop :=
  match k with
  | O =>  P (l _[ 0 ])
  | S k' => invariance P l k' /\  P (l _[ k ])
  end.

Definition naive_method (I : init) (T : trans) (P : property)
           (k : nat) : Prop :=
  forall l : list state,
  ~ (I (l _[ 0 ]) /\ path T l 0 k /\ ~ invariance P l k).

  
Definition ex_I (s : state) : Prop :=
  s 2 = 1%Z /\ s 1 = 0%Z /\ s 0 = 0%Z. 

Definition ex_T (si sj : state) : Prop :=
  sj 2 = 1%Z /\ sj 1 = si 2 /\ sj 0 = si 1.
 
Definition ex_P (s : state) : Prop :=
  ~ (s 0 = 0%Z /\ s 1 = 0%Z /\ s 2 = 0%Z).

Example naive_method_test1 :
  naive_method ex_I ex_T ex_P 3.
Proof.
  unfold naive_method.
  simpl.
  unfold ex_I; unfold ex_T; unfold  ex_P.
  intros.
  unfold state in *.


  intros.
  smt solve; apply by_smt.
Qed.


Fixpoint neq_state (si sj : state) (n : nat) : Prop :=
  match n with
  | O => True
  | S O => ~ (si 0 = sj 0)
  | S n' => neq_state si sj n' \/ ~ (si n' = sj n')
  end.


Fixpoint no_loop' (l : list state) (size o n m: nat) : Prop :=
  match m with
  | O => neq_state (l _[ (o+n) ]) (l _[ (o+m) ]) size
  | S m' => neq_state (l _[(o+n)]) (l _[(o+m)]) size /\ no_loop' l size o n m' 
  end.

Fixpoint no_loop (l : list state) (size o k : nat) : Prop :=
  match k with
  | O => True
  | 1 => no_loop' l size o 1 0
  | S k' => no_loop' l size o k k' /\ no_loop l size o k'
  end.

    
Definition loop_free (T : trans) (l : list state) (size o k: nat) : Prop :=
  (path T l o k /\ no_loop l size o k). 

Definition lasso (I : init) (T : trans) (P : property) (size k : nat) : Prop :=
  forall l : list state,
  ~ (I (l _[0]) /\ loop_free T l size 0 k).

Definition violate_loop_free (I : init) (T : trans)
           (P : property) (size k: nat) : Prop :=
  forall l : list state,
  ~ (loop_free T l size 0 k /\ ~ P (l _[k ])).


Definition P_state1 (I : init) (T : trans) (P : property)
           (k : nat) : Prop :=
  forall l : list state,
  ~ (I (l _[ 0]) /\ path T l 0 k /\ ~ P (l _[k])).

Fixpoint safety (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  match k with
  | O => P_state1 I T P k
  | S k' => safety I T P k' /\ P_state1 I T P k
  end.


Definition Sheeran_method1 (I : init) (T : trans) (P : property) (size k: nat) : Prop :=
  ((lasso I T P size k) \/
   (violate_loop_free I T P size k)) /\ safety I T P k.

(*
Tactic Notation "Sheeran_smt_solve1" :=
 unfold Sheeran_method1;
 unfold state, lasso, violate_loop_free, safety;
 unfold loop_free, P_state1;
 simpl;
 repeat tryif split then try split else
     tryif right; intros; smt solve then apply by_smt
     else  left; intros; smt solve; apply by_smt.
*)

Example Sheeran_method1_test1 :
  Sheeran_method1 ex_I ex_T ex_P 3 4.
Proof.
  unfold ex_I, ex_T, ex_P.
  unfold Sheeran_method1, lasso, violate_loop_free, safety;
  split;
  unfold loop_free, P_state1;
  unfold state;
  simpl;
  unfold neq_state.

  (right; intros; smt solve; apply by_smt) ||
  (left; intros; smt solve; apply by_smt).

  repeat tryif split then split
    else smt solve; apply by_smt.
                    
Qed.



Definition P_state2  (I : init) (T : trans) (P : property) (size k : nat) : Prop :=
  forall l : list state,
  ~ (I (l _[0]) /\ loop_free T l size 0 k /\ ~ P (l _[k])).



Lemma le_safety_relation : forall (i k : nat) (I : init) (T : trans) (P : property),
    (i <= k) ->  safety I T P k -> P_state1 I T P i.
Proof.
  intros.
  apply Nat.lt_eq_cases in H. 
  destruct H.
  - induction k.  
    + easy.
    + destruct (Nat.lt_ge_cases i k).
      * assert (H2 : safety I T P k /\ P_state1 I T P k).
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

Theorem Sheeran_method_soundness_case1 :
  forall (I : init) (T : trans) (P : property) (size k : nat),
    Sheeran_method1 I T P size k
    -> (forall (i : nat), (i <= k) -> P_state2 I T P size i).
Proof.
  intros.
  unfold Sheeran_method1 in H.
  destruct H.
   apply (le_safety_relation I T P) in H0.
   firstorder.
  auto.
Qed.


Lemma divide_no_loop1 : forall (l : list state) (size j i : nat), 
  no_loop l size 0 (i+j) -> no_loop l size 0 i.
Proof.
  induction j.
  - intros.  rewrite <- plus_n_O in H.
    easy.
  - intros.
    rewrite <- Nat.add_succ_comm in H.
    apply IHj in H.
    assert(no_loop l size 0 (S i) <-> no_loop l size 0 i /\
                                    no_loop' l size 0 (S i) i)
      by (destruct i; firstorder).
    apply H0 in H.
    firstorder.
Qed.

Lemma divide_no_loop2'' : forall (l : list state) (size i j k : nat) ,
        no_loop' l size i (S k) (S j) <->
        neq_state (l _[(i + (S k))]) (l _[i]) size /\
        no_loop' l size (S i) k j.
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
      assert(neq_state (l _[(i + S k)]) (l _[i]) size /\
             neq_state (l _[(S (i + k))]) (l _[(S (i + S (S j)))]) size /\
             neq_state (l _[(S (i + k))]) (l _[(S (i + S j))]) size /\
             no_loop' l size (S i) k j <->
             (neq_state (l _[(i + S k)]) (l _[i]) size /\
              neq_state (l _[(S (i + k))]) (l _[(S (i + S j))]) size /\
              no_loop' l size (S i) k j ) /\
             neq_state (l _[(S (i + k))]) (l _[(S (i + S (S j)))]) size)
        by tauto.
      now rewrite H; rewrite <- IHj; rewrite <- Nat.add_succ_r;
        rewrite <- Nat.add_succ_r.
Qed. (*26*)


Lemma divide_no_loop2' : forall (l : list state) (size j i : nat),
    no_loop l size i (S j) -> no_loop l size (S i) j.
Proof.
  induction j.
  intros.
  - destruct i; firstorder.
  - intros.
    assert(no_loop l size (S i) (S j) <->
           no_loop' l size (S i) (S j) j /\ no_loop l size (S i) j)
      by (destruct j; firstorder).
    apply H0.
    assert(no_loop l size i (S (S j)) <->
           no_loop' l size i (S (S j)) (S j) /\ no_loop l size i (S j))
      by (destruct j; firstorder).
    apply -> H1 in H.
    destruct H.    
    split. 
    now apply divide_no_loop2'' in H.
    now apply IHj in H2.
Qed. (*19*)


Lemma divide_no_loop2 : forall (l : list state) (size i j : nat),
    no_loop l size 0 (i+j) -> no_loop l size i j.
Proof.
  induction i.
  - easy.
  - intros.
    rewrite Nat.add_succ_comm in H.
    apply IHi in H.
    now apply divide_no_loop2' in H.
Qed. (*7*)


Lemma divide_no_loop : forall (l : list state) (size i j: nat),
    no_loop l size 0 (i+j) ->
    no_loop l size 0 i /\ no_loop l size i j.
Proof.
  intros.
  split.
  - now apply divide_no_loop1 in H.
  - now apply divide_no_loop2 in H.
Qed.


Lemma divide_tl_path : forall (l : list state) (T : trans) (i : nat),
    path T l 0 (S i) <->
    path T l 0 i /\ T (l _[i]) (l _[(S i)]).
Proof.
  intros. 
  destruct i. 
  - unfold path.
    tauto.
  - unfold path; fold path; simpl.
    rewrite <- plus_n_O.
    tauto.
Qed. (*8*)


Lemma divide_hd_path : forall (l : list state) (T : trans) (i j : nat),
    T (l _[i]) (l _[(S i)]) /\ path T l (S i) j <->
    path T l i (S j).
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


Lemma shift_path : forall (l : list state) (T : trans) (i j : nat), 
  path T l 0 i /\ path T l i (S j) <-> 
  path T l 0 (S i) /\ path T l (S i) j .
Proof.
  intros.
  rewrite divide_tl_path.
  rewrite and_assoc.
  rewrite divide_hd_path.
  reflexivity.
Qed. (*5*)

Lemma divide_path : forall (l : list state) (T : trans) (i j: nat),
    path T l 0 (i+j) -> path T l 0 i /\ path T l i j.
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

Lemma divide_loop_free : forall  (l : list state) (T : trans) (size i j : nat),
    loop_free T l size 0 (i+j) -> loop_free T l size 0 i /\ loop_free T l size i j.
Proof.
  unfold loop_free.
  intros.

  destruct H.
  apply divide_path in H.
  apply divide_no_loop in H0.
  tauto.
Qed.

Lemma case2_1 :
  forall (I : init) (T : trans) (P : property) (size i k : nat),
    i > k -> lasso I T P size k -> P_state2 I T P size i.
Proof.
  unfold lasso, P_state2 in *.
  intros.
  apply neg_false.
  split.
  intros.
  destruct H1.
  destruct H2.
  assert (H4 : i = k + (i - k)) by omega.
  rewrite H4 in H2.
  apply divide_loop_free in H2.
  firstorder.
  firstorder.
Qed.


Lemma skipn_nth: forall A:Type, forall l:list A, forall n m:nat, forall d:A,
  nth m (skipn n l) d = nth (n+m) l d.
Proof.
  intros A l.
  induction l; intros; 
    destruct m; destruct n; simpl; auto.
Qed.

(*
Lemma skipn_relation : forall(l : list state) (i j : nat) ,
    l _[(i + j)] = (skipn i l) _[j].
Proof.
  intros l.
  induction l; intros;
  destruct j; destruct i; simpl; auto.
Qed.
*)

Lemma path_skipn_relation : forall (T : trans) (i j : nat),
    forall l : list state,
    path T l j i  -> path T (skipn j l) 0 i.
Proof.
  intros.
  induction i.
  - auto.

  - assert (path T (skipn j l) 0 (S i) <->
            path T (skipn j l) 0 i /\
            T ((skipn j l) _[i]) ((skipn j l) _[(S i)])).
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


Lemma no_loop'_skipn_relation : forall (size i j k : nat),
    forall l : list state,
    no_loop' l size j k i
    -> no_loop' (skipn j l) size 0 k i.
Proof.
  intros.
  destruct i.
  - simpl in *.
    do 2 rewrite skipn_nth.
    simpl in *.
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


Lemma no_loop_skipn_relation : forall (size i j : nat),
    forall l : list state,  no_loop l size j i
    -> no_loop (skipn j l) size 0 i.
Proof.
  intros.
  induction i.
  - auto.

  - assert (H1 : no_loop l size j i /\ no_loop' l size j (S i) i)
     by ( destruct i; firstorder; rewrite <- plus_n_O in *).
    clear H.

    assert (H :no_loop (skipn j l) size 0 i /\ no_loop' (skipn j l) size 0 (S i) i
            -> no_loop (skipn j l) size 0 (S i)).
    intros.
    destruct i; firstorder; rewrite <- plus_n_O in *.
    apply H.
    clear H.
    split.    
    apply IHi.
    tauto.
    destruct H1.
    clear H.
    apply no_loop'_skipn_relation in H0.
    tauto.
Qed.
          

Lemma P_skipn_relation : forall (P : property) (i k : nat),
    forall l : list state,
    i >= k -> ~ P (l _[i])
    -> ~ P ((skipn (i - k) l) _[k]).
Proof.
  intros.
  rewrite skipn_nth.
  replace (i - k + k) with i.
  auto.
  omega.
Qed.


(*
Lemma case2_2'' : forall (T : trans) (P : property) (size i k : nat),
    i > k ->
    (forall l : list state,
        ~ (loop_free T (skipn l (i - k)) size 0 k /\ ~ P ((skipn l (i-k)) _[k])))
    ->  (forall l : list state, 
          ~ (loop_free T l size (i-k) k /\ ~ P (l _[i]))).

Proof.
  intros.
  assert ( ~ (loop_free T (skipn l (i - k)) size 0 k /\
              ~ P ((skipn l (i - k)) _[k]))) by auto.
  assert (H2 : forall A B, (~ A -> ~ B) <-> (B -> A)) by (intros; tauto).
  revert H1.
  apply H2.
  clear H2.
  intros.
  unfold loop_free in *. 
  destruct H1.
  destruct H1.
  apply path_skipn_relation in H1.
  apply no_loop_skipn_relation in H3.
  apply P_skipn_relation with (k := k) in H2.
  auto. omega. 
Qed.
*)

Theorem case2_2' : forall (T : trans) (P : property) (size i k : nat),
    i > k -> 
    (forall l : list state, ~ (loop_free T l size 0 k /\ ~ P (l _[k])))
    -> forall l : list state, ~ (loop_free T l size (i-k) k /\ ~ P (l _[i])).
Proof.
  intros.
  apply neg_false.
  split.
  unfold loop_free in *.
  intros.
  destruct H1.
  destruct H1.
  apply no_loop_skipn_relation in H3.
  apply P_skipn_relation with (k:= k) in H2.
  apply path_skipn_relation in H1.
  firstorder.
  omega.
  tauto.
Qed.


Theorem case2_2 : forall (I : init) (T : trans) (P : property) (size i k : nat),
    i > k -> violate_loop_free I T P size k -> P_state2 I T P size i.
Proof.
  unfold violate_loop_free, P_state2.
  intros.
  apply neg_false.
  split.
  intros.
  destruct H1.
  destruct H2.
  assert (i = (i - k) + k) by omega.
  rewrite H4 in H2.
  apply divide_loop_free in H2.  
  apply case2_2' with (i := i) (k := k) (l := l) in H0.
  firstorder.
  apply H.
  tauto.
Qed.
  


Theorem Sheeran_method_soundness_case2 :
  forall (I : init) (T : trans) (P : property) (size k : nat),
    Sheeran_method1 I T P size k
    -> (forall (i : nat), (i > k) -> P_state2 I T P size i).
Proof.
  intros.
  unfold Sheeran_method1 in H.
  destruct H.

  destruct H.
  - now apply case2_1 with (k := k).

  - now apply case2_2 with (k := k).
Qed.

  
Theorem Sheeran_method_soundness :
  forall (I : init) (T : trans) (P : property) (size k : nat),
    Sheeran_method1 I T P size k
    -> (forall (i : nat), P_state2 I T P size i).
Proof.
  intros.
  destruct (Nat.le_gt_cases i k).
  - revert H0.
    now apply Sheeran_method_soundness_case1.
  - revert H0.
    now apply Sheeran_method_soundness_case2.
Qed.