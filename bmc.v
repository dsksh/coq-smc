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

(*
Definition state : Type := nat -> Z.
Definition ss : Type := nat -> nat -> state.
Definition sub_trans : Type := state -> state -> state -> state -> Prop.
Definition sub_init : Type := state -> state -> Prop.
Definition trans : Type :=  (nat -> state) -> (nat -> state) -> Prop.
Definition init : Type := (nat -> state) -> Prop.
Definition property : Type := (nat -> state) -> Prop.*)

Set Implicit Arguments.

Definition state : Type := nat -> Z.

Definition default := fun x : nat => 99999%Z.

Definition init : Type := state -> Prop.
Definition trans : Type := state -> state -> Prop.
Definition property : Type := state -> Prop.

Fixpoint ss A (f : list A -> init -> trans -> property -> nat -> Prop)
         (l : list A) (I : init) (T : trans) (P : property)
         (n : nat) : Prop :=
  match n with
  | 0 => forall s0 : A, f (l++[s0]) I T P (length l)
  | S n' => forall s0 : A, ss f (l++[s0]) I T P n'
  end.



Fixpoint path (l : list state) (T : trans) (o len : nat) : Prop :=
  match len with
  | O => True
  | S O => T (nth o l default) (nth (o+1) l default)
  | S len' => path l T o len' /\ T (nth (len'+o) l default) (nth (len+o) l default)
  end.


Fixpoint violate_P (l : list state) (P : property) (k : nat) : Prop :=
  match k with
  | O =>  P (nth 0 l default)
  | S k' => violate_P l P k' /\  P (nth k l default)
  end.

Definition Naive_method_body (l : list state) (I : init)
           (T : trans) (P : property) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ path l T 0 k /\ ~ violate_P l P k).

Definition Naive_method (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  ss Naive_method_body [] I T P k.

Module test1.
  
  Definition ex_I (s : state) : Prop :=
    s 0 = 0%Z.

  Definition ex_T (si sj : state) : Prop :=
    sj 0 = (si 0%nat + 1)%Z.
 
  Definition ex_P (s : state) : Prop :=
    ~ (s 0%nat = -1)%Z.

  Example naive_method_test1 :
    Naive_method ex_I ex_T ex_P 5.
  Proof.
    unfold Naive_method; unfold Naive_method_body.
    simpl.
    unfold ex_I; unfold ex_T; unfold  ex_P.
    intros.
    smt solve; apply by_smt.
  Qed.
End test1.


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

    
Definition loop_free (l : list state) (T : trans) (o k : nat) : Prop :=
  (path l T o k /\  loop_check l o k). 

Definition lasso (l : list state)
           (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ loop_free l T 0 k).

Definition violate_loop_free (l : list state)
           (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  ~ (loop_free l T 0 k /\ ~ P (nth k l default)).


Definition P_state1 (l : list state) (I : init) (T : trans)
           (P : property) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ path l T 0 k /\ ~ P (nth k l default)).

Fixpoint safety_by_k (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  match k with
  | O => ss P_state1 [] I T P 0
  | S k' => safety_by_k I T P k' /\ ss P_state1 [] I T P k
  end.


Definition Sheeran_method1 (I : init) (T : trans) (P : property) (k : nat) : Prop :=
  ((ss lasso [] I T P k) \/
   (ss violate_loop_free [] I T P k)) /\ safety_by_k I T P k.


Definition P_state2 (l : list state) (I : init) (T : trans)
           (P : property) (k : nat) : Prop :=
  ~ (I (nth 0 l default) /\ loop_free l T 0 k /\ ~ P (nth k l default)).


Lemma case1_t1 : forall (i k : nat) (I : init) (T : trans) (P : property),
    (i < k) /\ safety_by_k I T P k -> ss P_state1 [] I T P i.
Proof.
  intros.
  induction k.
  - easy.
    
  - destruct H.
    destruct (Nat.lt_ge_cases i k).
    + assert (safety_by_k I T P k /\ ss P_state1 [] I T P k)
        by (destruct k; firstorder; now rewrite <- plus_n_O in *).
      now apply IHk.
    + apply gt_S_le in H.
      assert (i = k) by omega.      
      destruct k; rewrite H2; firstorder.
Qed.


Lemma ss_property : forall (f g : list state -> init -> trans -> property -> nat -> Prop)
                       (I : init)  (T : trans)
                       (P : property) (i : nat),
    (forall l, f l I T P i -> g l I T P i)
    -> (ss f [] I T P i -> ss g [] I T P i).
Proof.
  intros.
  unfold ss.
  
Admitted.



Theorem Proof_Sheeran_method_case1 :
  forall (I : init) (T : trans) (P : property) (k : nat),
    Sheeran_method1 I T P k
    -> (forall (i : nat), (i < k) -> ss P_state2 [] I T P i).
Proof.
  intros.
  unfold Sheeran_method1 in H.
  destruct H.
  assert (i < k /\ safety_by_k I T P k) by easy.
  apply case1_t1 in H2.

  revert H2.
  apply ss_property.
  intros.
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
    path l T 0 (S i) <->
    path l T 0 i /\ T (nth i l default) (nth (S i) l default).
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
    T (nth i l default) (nth (S i) l default) /\ path l T (S i) j <->
    path l T i (S j).
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
  path l T 0 i /\ path l T i (S j) <-> 
  path l T 0 (S i) /\ path l T (S i) j .
Proof.
  intros.
  rewrite divide_tl_path.
  rewrite and_assoc.
  rewrite divide_hd_path.
  reflexivity.
Qed. (*5*)

Lemma divide_path : forall (l : list state) (T : trans) (i j: nat),
    path l T 0 (i+j) -> path l T 0 i /\ path l T i j.
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
 loop_free l T 0 (i+j) -> loop_free l T 0 i /\ loop_free l T i j.
Proof.
  unfold loop_free.
  intros.

  destruct H.
  apply divide_path in H.
  apply divide_loop_check in H0.
  tauto.
Qed.






Lemma case2_t1 : forall (I : init) (T : trans) (P : property) (i k : nat),
    i >= k ->  ss lasso [ ] I T P k -> ss P_state2 [ ] I T P i.
Proof.
  intros.
  assert (forall l : list state, lasso l I T P k ->  P_state2 l I T P i) by apply by_smt.
Admitted.


Lemma case2_t2 : forall (I : init) (T : trans) (P : property) (i k : nat),
    i >= k ->  ss violate_loop_free [ ] I T P k -> ss P_state2 [ ] I T P i.
Proof. Admitted.

Theorem Proof_Sheeran_method_case2 :
  forall (I : init) (T : trans) (P : property) (k : nat),
    Sheeran_method1 I T P k
    -> (forall (i : nat), (i >= k) -> ss P_state2 [] I T P i).
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
    -> (forall (i : nat), ss P_state2 [] I T P i).
Proof.
  intros.
  destruct (Nat.lt_ge_cases i k).
  - revert H0.
    now  apply Proof_Sheeran_method_case1.
  - revert H0.
    now apply Proof_Sheeran_method_case2.
Qed.