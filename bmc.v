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

(*
Definition state : Type := nat -> Z.
Definition default := fun x : nat => 99999%Z.
 *)

Definition state : Type := Z.
Definition default := 99999%Z.

Definition init : Type := state -> Prop.
Definition trans : Type := state -> state -> Prop.
Definition property : Type := state -> Prop.



Fixpoint ss_body (f : list state -> nat -> Prop)
         (l : list state) (iter n : nat) : Prop :=
  match iter with
  | 0 => forall s0 : state, f (l++[s0]) n
  | S iter' => forall s0 : state, ss_body f (l++[s0]) iter' n
  end.

Definition ss (f : list state -> nat -> Prop)
           (l : list state) (n : nat) : Prop :=
  ss_body f l n n.

(*
Fixpoint ss_body (f : list state -> nat -> Prop) (l : list state) (iter n : nat) : Prop :=
  match iter with
  | 0 => forall s0 : state, f (l++[s0]) n
  | S iter' => forall s0 : state, ss_body f (l++[s0]) iter' n
  end.

Definition ss (f : list state -> nat -> Prop) (l : list state) (n : nat) : Prop :=
  ss_body f l n n.
*)

Fixpoint path (T : trans) (l : list state) (o len : nat) : Prop :=
  match len with
  | O => True
  | S O => T (nth o l default) (nth (o+1) l default)
  | S len' => path T l o len' /\ T (nth (len'+o) l default) (nth (len+o) l default)
  end.

Fixpoint violate_P (P : property) (l : list state) (k : nat): Prop :=
  match k with
  | O =>  P (nth 0 l default)
  | S k' => violate_P P l k' /\  P (nth k l default)
  end.

Definition Naive_method_body  (I : init) (T : trans) (P : property)
          (l : list state) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ path T l 0 k /\ ~ violate_P P l k).

Definition Naive_method (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  ss (Naive_method_body I T P) [] k.

  
Definition ex_I (s : state) : Prop :=
  s = 0%Z.

Definition ex_T (si sj : state) : Prop :=
  sj = (si + 1)%Z.
 
Definition ex_P (s : state) : Prop :=
  ~ (s = -1)%Z.

Example naive_method_test1 :
  Naive_method ex_I ex_T ex_P 5.
Proof.
  unfold Naive_method; unfold Naive_method_body.
  unfold ss.
  simpl.
  unfold ex_I; unfold ex_T; unfold  ex_P.
  intros.
  unfold state.
  smt solve; apply by_smt.
Qed.


Definition neq_nth_mth (si sj : state) : Prop :=
 ~ (si = sj).

Fixpoint loop_check' (l : list state) (o n m : nat) : Prop :=
  match m with
  | O => neq_nth_mth (nth (o+n) l default) (nth (o+m) l default)
  | S m' => neq_nth_mth (nth (o+n) l default) (nth (o+m) l default) /\
            loop_check' l o n m'
  end.

Fixpoint loop_check (l : list state) (o k : nat) : Prop :=
  match k with
  | O => True
  | 1 => loop_check' l o 1 0
  | S k' => loop_check' l o k k' /\ loop_check l o k'
  end.

    
Definition loop_free (T : trans) (l : list state) (o k : nat) : Prop :=
  (path T l o k /\  loop_check l o k). 

Definition lasso (I : init) (T : trans) (P : property)
           (l : list state) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ loop_free T l 0 k).

Definition violate_loop_free (I : init) (T : trans) (P : property)
           (l : list state) (k : nat) : Prop :=
  ~ (loop_free T l 0 k /\ ~ P (nth k l default)).


Definition P_state1 (I : init) (T : trans) (P : property)

           (l : list state) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ path T l 0 k /\ ~ P (nth k l default)).

Fixpoint safety_by_k (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  match k with
  | O => ss (P_state1 I T P) [] 0
  | S k' => safety_by_k I T P k' /\ ss (P_state1 I T P) [] k
  end.


Definition Sheeran_method1 (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  ((ss (lasso I T P) [] k) \/
   (ss (violate_loop_free I T P) [] k)) /\ safety_by_k I T P k.


Definition P_state2  (I : init) (T : trans) (P : property)
           (l : list state) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ loop_free T l 0 k /\ ~ P (nth k l default)).


Lemma ss_property : forall (f g : list state -> nat -> Prop) (i j : nat),
    ((forall l, length l > i -> f l i) -> forall l, length l > j -> g l j)
    -> (ss f [] i -> ss g [] j).
Proof.
 intros.
Admitted.


Lemma case1_t1' : forall (i k : nat) (I : init) (T : trans) (P : property),
    (i < k) /\ safety_by_k I T P k -> ss (P_state1 I T P) [] i.
Proof.
  intros.
  induction k.
  - easy.
    
  - destruct H.
    destruct (Nat.lt_ge_cases i k).
    + assert (safety_by_k I T P k /\ ss (P_state1 I T P) [] k)
        by (destruct k; firstorder; now rewrite <- plus_n_O in *).
      now apply IHk.
    + apply gt_S_le in H.
      assert (i = k) by omega.      
      destruct k; rewrite H2; firstorder.
Qed.


Lemma case1_t1 : forall (i k : nat) (I : init) (T : trans) (P : property),
    (i <= k) /\ safety_by_k I T P k -> ss (P_state1 I T P) [] i.
Proof.
  intros.
  destruct H.
  assert (i <= k <-> i < k \/ i = k) by omega.
  apply H1 in H.
  destruct H.
  apply case1_t1' with (k := k).
  tauto.
  subst.

  destruct k.
  tauto.
  assert (safety_by_k I T P k /\ ss (P_state1 I T P) [] (S k)).
  destruct k; firstorder.

  firstorder.
Qed.


Theorem Proof_Sheeran_method_case1 :
  forall (I : init) (T : trans) (P : property) (k : nat),
    Sheeran_method1 I T P k
    -> (forall (i : nat), (i <= k) -> ss (P_state2 I T P) [] i).
Proof.
  intros.
  unfold Sheeran_method1 in H.
  destruct H.
  assert (i <= k /\ safety_by_k I T P k) by easy.
  apply case1_t1 in H2.

  
  revert H2.
  apply ss_property.
  firstorder.
Qed.


Lemma divide_lc1 : forall (l : list state) (j i : nat), 
  loop_check l 0 (i+j) -> loop_check l 0 i.
Proof.
  induction j.
  - intros.  rewrite <- plus_n_O in H.
    easy.
  - intros.
    rewrite <- Nat.add_succ_comm in H.
    apply IHj in H.
    assert(loop_check l 0 (S i) <-> loop_check l 0 i /\
                                    loop_check' l 0 (S i) i)
      by (destruct i; firstorder).
    apply H0 in H.
    firstorder.
Qed.

Lemma divide_lc2'' : forall (l : list state) (i j k : nat) ,
        loop_check' l i (S k) (S j) <->
        neq_nth_mth (nth (i + (S k)) l default) (nth i l default) /\
        loop_check' l (S i) k j.
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
      assert(neq_nth_mth (nth (i + S k) l default) (nth i l default) /\
             neq_nth_mth (nth (S (i + k)) l default) (nth (S (i + S (S j))) l default) /\
             neq_nth_mth (nth (S (i + k)) l default) (nth (S (i + S j)) l default) /\
             loop_check' l (S i) k j <->
             (neq_nth_mth (nth (i + S k) l default) (nth i l default) /\
              neq_nth_mth (nth (S (i + k)) l default) (nth (S (i + S j)) l default) /\
              loop_check' l (S i) k j ) /\
             neq_nth_mth (nth (S (i + k)) l default) (nth (S (i + S (S j))) l default))
        by tauto.
      now rewrite H; rewrite <- IHj; rewrite <- Nat.add_succ_r;
        rewrite <- Nat.add_succ_r.
Qed. (*26*)


Lemma divide_lc2' : forall (l : list state) (j i : nat),
    loop_check l i (S j) -> loop_check l (S i) j.
Proof.
  induction j.
  intros.
  - destruct i; firstorder.
  - intros.
    assert(loop_check l (S i) (S j) <->
           loop_check' l (S i) (S j) j /\ loop_check l (S i) j)
      by (destruct j; firstorder).
    apply H0.
    assert(loop_check l i (S (S j)) <->
           loop_check' l i (S (S j)) (S j) /\ loop_check l i (S j))
      by (destruct j; firstorder).
    apply -> H1 in H.
    destruct H.    
    split. 
    now apply divide_lc2'' in H.
    now apply IHj in H2.
Qed. (*19*)


Lemma divide_lc2 : forall (l : list state) (i j : nat),
    loop_check l 0 (i+j) -> loop_check l i j.
Proof.
  induction i.
  - easy.
  - intros.
    rewrite Nat.add_succ_comm in H.
    apply IHi in H.
    now apply divide_lc2' in H.
Qed. (*7*)


Lemma divide_loop_check : forall (l : list state) (i j: nat),
    loop_check l 0 (i+j) ->
    loop_check l 0 i /\ loop_check l i j.
Proof.
  intros.
  split.
  - now apply divide_lc1 in H.
  - now apply divide_lc2 in H.
Qed.


Lemma divide_tl_path : forall (l : list state) (T : trans) (i : nat),
    path T l 0 (S i) <->
    path T l 0 i /\ T (nth i l default) (nth (S i) l default).
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
    T (nth i l default) (nth (S i) l default) /\ path T l (S i) j <->
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

Lemma divide_loop_free : forall  (l : list state) (T : trans) (i j : nat),
 loop_free T l 0 (i+j) -> loop_free T l 0 i /\ loop_free T l i j.
Proof.
  unfold loop_free.
  intros.

  destruct H.
  apply divide_path in H.
  apply divide_loop_check in H0.
  tauto.
Qed.

Lemma case2_t1 : forall (I : init) (T : trans) (P : property) (i k : nat),
    i > k ->  ss (lasso I T P) [] k -> ss (P_state2 I T P) [] i.
Proof.
  intros.
  revert H0.
  apply ss_property.
  intros.
  unfold lasso, P_state2 in *.
  apply neg_false.
  split. 
  intros.
  destruct H2.
  destruct H3.
  assert (i = k + (i - k)) by omega.
  rewrite H5 in H3.
  apply divide_loop_free in H3.
  assert (length l > k) by omega.  
  apply H0 in H6.
  tauto.
  tauto.
Qed.



Fixpoint itl (l : list state) (i : nat) : list state :=
  match i with
  | O => l
  | S i' => itl (tl l) i'
  end.



Lemma aaa : forall (T : trans) (i k : nat),
    i > S k ->
    forall l : list state, length l > i
    -> ~ path T (itl l (i - S k)) 0 (S k)
    -> ~ path T (itl l (i - k)) 0 k.
Proof. Admitted.

Lemma aa : forall (T : trans) (i k : nat),
    i > S k ->
    forall l : list state, length l > i
    ->  ~ (T (nth (i - S k) l default) (nth (i - k) l default) /\
                    path T l (i - k) k) 
    ->  ~ path T l (i - S k) (S k).
Proof. Admitted.


Lemma a : forall (T : trans) (i k : nat),
    i > k ->
    forall l : list state, length l > i ->
      ~ path T (itl l (i - k)) 0 k
      -> ~ path T l (i - k) k.
Proof.
  intros.
  induction k.
  - auto.
    
  - apply aa.
    auto. auto.
    
    assert (H2 : ~ (T (nth (i - S k) l default) (nth (i - k) l default) /\
               path T l (i - k) k) <->
            ~ T (nth (i - S k) l default) (nth (i - k) l default) \/
            ~ path T l (i - k) k) by tauto.
    apply H2.
    clear H2.
    right.
    apply IHk.
    omega.

    apply aaa.
    auto. auto. auto.
Qed.    


Lemma b : forall (i k : nat),
    i > k ->
    forall l : list state,  length l > i ->
    ~ loop_check (itl l (i - k)) 0 k
    -> ~ loop_check l (i - k) k .
Proof. Admitted.


Lemma c : forall (P : property) (i k : nat),
    i > k ->
    forall l : list state, length l > i ->
    P (nth k (itl l (i - k)) default)
    -> P (nth i l default).
Proof. Admitted.


Lemma case2_t2'' : forall (T : trans) (P : property) (i k : nat),
    i > k ->
    (forall l : list state, length l > i ->
       ~ (loop_free T (itl l (i - k)) 0 k /\ ~ P (nth k (itl l (i-k)) default)))
    ->  (forall l : list state, length l > i ->
          ~ (loop_free T l (i-k) k /\ ~ P (nth i l default))).

Proof.
  intros.
  assert (H2 : length l > i).
  omega.
  apply H0 in H2.
  clear H0.

  unfold loop_free in *. 


  assert (H3 : ~ path T (itl l (i - k)) 0 k \/ ~ loop_check (itl l (i - k)) 0 k \/
          P (nth k (itl l (i - k)) default)).
  tauto.


  clear H2.

  assert (H2 : ~ path T l (i - k) k \/ ~ loop_check l (i - k) k \/  P (nth i l default)
           ->  ~ ((path T l (i - k) k /\ loop_check l (i - k) k) /\ ~ P (nth i l default))).
  tauto.

  apply H2.
  clear H2.

  destruct H3.
  left.
  apply a.
  auto. auto. auto.

  destruct H0.
  right.
  left.
  apply b.
  auto. auto. auto.

  right.
  right.
  apply c with (k := k).
  auto. auto. auto.
Qed.


Lemma d : forall (i k : nat),
    i > k ->
    forall l : list state,
    length l > i -> length (itl l (i-k)) > k.
Proof. Admitted.

Lemma case2_t2' : forall (T : trans) (P : property) (i k : nat),
    i > k -> 
    (forall l : list state, length l > k ->
                        ~ (loop_free T l 0 k /\ ~ P (nth k l default)))
    -> (forall l : list state, length l > i ->
        ~ (loop_free T l (i-k) k /\ ~ P (nth i l default))).
Proof.
  intros.
  revert l H1.
  apply case2_t2''.
  auto.
  intros.
  apply H0.

  apply d.
  auto. auto.
Qed.


(*
  (*kについての帰納法*)
  induction k.
  + unfold loop_free in *.
    simpl in *.

    assert (~ ((True /\ True) /\ ~ P (nth i l default)) <->
            ~~ P (nth i l default)) by tauto.
    assert ((forall l : list state, length l > 0
                              -> ~ ((True /\ True) /\ ~ P (nth 0 l default)))
            <->
            (forall l : list state,length l > 0
                               -> ~~ P (nth 0 l default))) by firstorder.


    apply H2.
    rewrite H3 in H1.
    clear H2 H3.

    apply lll1.
    tauto.
    tauto.
  + 


    assert (forall l : list state,
               length l > S k ->
               ~ (loop_free T l 0 k /\ ~ P (nth k l default))).
    apply by_smt.
    

*)




Lemma case2_t2 : forall (I : init) (T : trans) (P : property) (i k : nat),
    i > k ->  ss (violate_loop_free I T P) [] k -> ss (P_state2 I T P) [] i.
Proof.
  intros.
  revert H0.
  apply ss_property.
  intros.
  unfold P_state2.
  apply neg_false.
  split.
  intros.
  destruct H2.
  destruct H3.
  assert (i = (i - k) + k) by omega.
  rewrite H5 in H3.
  apply divide_loop_free in H3.
  destruct H3.
  assert (loop_free T l (i - k) k /\  ~ P (nth i l default)) by tauto.
  unfold violate_loop_free in H0.
  apply case2_t2' with (i := i) (l := l) in H0.
  auto.
  auto.
  auto.
  tauto.
Qed.
  

Theorem Proof_Sheeran_method_case2 :
  forall (I : init) (T : trans) (P : property) (k : nat),
    Sheeran_method1 I T P k
    -> (forall (i : nat), (i > k) -> ss (P_state2 I T P) [] i).
Proof.
  intros.
  unfold Sheeran_method1 in H.
  destruct H.

  destruct H.
  - now apply case2_t1 with (k := k).

  - now apply case2_t2 with (k := k).
Qed.

  
Theorem Proof_Sheeran_method :
  forall (I : init) (T : trans) (P : property) (k : nat),
    Sheeran_method1 I T P k
    -> (forall (i : nat), ss (P_state2 I T P) [] i).
Proof.
  intros.
  destruct (Nat.le_gt_cases i k).
  - revert H0.
    now apply Proof_Sheeran_method_case1.
  - revert H0.
    now apply Proof_Sheeran_method_case2.
Qed.