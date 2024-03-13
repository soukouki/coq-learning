(* 
# Coq勉強会の解答
問題でどのようなことを説いているのかも解説する
 *)
From mathcomp Require Import ssreflect.

Section Section1.
Variables A B C : Prop.

(* Q1-1 直前のA_to_Aを写経する問題 *)
Definition admitted_sample : A -> A := fun a  => a.

(* Q1-2 ラムダ式を使う問題 *)
Definition A_to_B_to_A :  A -> B -> A := fun a  => fun b  => a.
Definition A_to_B_to_A2 : A -> B -> A := fun a b  => a. (* 2引数を同時に受け取ることもできる *)

(* Q1-3 関数を含意として使う問題 *)
Definition modus_ponens : (A -> B) -> A -> B := fun H a  => H a.

(* Q1-4 *)
Definition imply_trans : (A -> B) -> (B -> C) -> (A -> C) := fun h1 h2 a  => h2 (h1 a).

(* Q2-1 直前のパターンマッチの記述を理解しているか問う問題 *)
Definition and_right : A /\ B -> B :=
  fun h1 => match h1 with
    | conj a b  => b
  end.

(* Q2-2 andを式から組みたてる問題 *)
Definition A_to_B_to_A_and_B :  A -> B -> A /\ B :=
  fun a b => conj a b.

(* Q2-3 andの総合問題 *)
Definition and_comm' : A /\ B -> B /\ A :=
  fun h1 => match h1 with
    | conj a b  => conj b a
  end.

(* Q2-4 or_introlとor_introrを理解してるか問う問題 *)
Definition B_to_A_or_B : B -> A \/ B := fun b  => or_intror b.

(* Q2-5 orの総合問題 *)
Definition or_comm' : A \/ B -> B \/ A :=
  fun H => match H with
    | or_introl b  => or_intror b
    | or_intror a  => or_introl a
  end.

(* Q2-6 使わない項がある問題 *)
Definition and_to_or : A /\ B -> A \/ B :=
  fun H => match H with
    | conj a _ => or_introl a
  end.

(* Q3-1 move =>とexactを使う問題 *)
Theorem A_to_B_to_A' : A -> B -> A.
Proof.
move => a.
move => b.
exact a.
Restart.
move => a b. (* 2引数を同時に受け取れる *)
by []. (* byタクティックを使って自動で証明を進められる *)
Qed.

(* Q3-2 applyを使う問題 *)
Theorem imply_trans' : (A -> B) -> (B -> C) -> (A -> C).
move => h1 h2 a.
apply h2.
apply h1.
exact a.
Restart.
move => h1 h2 a.
by apply /h2 /h1. (* applyは複数の仮定を同時に渡すこともできる *)
Qed.

(* Q4-1 andに対してcaseを使う問題 *)
Theorem and_right' : A /\ B -> B.
Proof.
case => a b.
exact b.
Restart.
by case.
Qed.

(* Q4-2 andに対してsplitを使う問題 *)
Theorem and_comm'' : A /\ B -> B /\ A.
Proof.
case => a b.
split.
- exact b.
- exact a.
Restart.
case.
by split.
Qed.

(* Q4-3 leftとrightを使う問題 *)
Theorem or_comm'' : A \/ B -> B \/ A.
Proof.
case.
- move => a.
  right.
  exact a.
- move => b.
  left.
  exact b.
Restart.
case => [ a | b ]. (* このように書くと、複数の枝に分かれるcaseでもmoveを省略できます *)
- by right.
- by left.
Restart.
case => [ a | b ]; by [ right | left ].
Qed.

(* Q4-4 andとorの総合問題 *)
Theorem Q4_4 : (A /\ B) \/ (B /\ C) -> B.
Proof.
case.
- case => a b.
  exact b.
- case => b c.
  exact b.
Restart.
case.
- by case.
- by case.
Restart.
by case => [[] | []]. (* 可読性はかなり悪いが、このような書き方もできる *)
Qed.

(* Q5-1 rewriteとreflexivityを使う問題 *)
Theorem rewrite_sample2 n : n = 3 -> n + 1 = 4.
Proof.
move => H.
rewrite H.
rewrite /=.
reflexivity.
Restart.
move => H.
by rewrite H.
Qed.

(* Q5-2 関数を使った命題の証明を問う問題 *)
Theorem rewrite_sample3 n m: n = S m -> pred n = m.
Proof.
rewrite /=.
move => H.
by rewrite H.
Restart.
move => H.
by rewrite H.
Qed.

(* Q5-3 existsを使う問題 *)
Theorem mul_functional : forall n m, exists x, x = n * m.
Proof.
move => n m.
by exists (n * m).
Qed.

(* Q5-4 *)
Theorem sqrt_5 : exists x, x * x = 25.
Proof.
by exists 5.
Qed.

(* Q6-1 inductionを使う問題 *)
Theorem n_plus_zero_eq_n n : n + 0 = n.
Proof.
induction n.
- by [].
- rewrite /=.
  by rewrite IHn.
Restart.
by induction n.
Qed.

(* Q6-2 *)
Theorem succ_plus n m : n + (S m) = S (n + m).
Proof.
induction n.
- by rewrite /=.
- rewrite /=.
  by rewrite IHn.
Restart.
by induction n.
Qed.

(* Q6-3 これまでに証明した命題を使う問題 *)
Theorem plus_comm n m : n + m = m + n.
Proof.
induction n.
- rewrite /=.
  by rewrite n_plus_zero_eq_n.
- rewrite /=.
  rewrite IHn.
  by rewrite succ_plus.
Restart.
induction n.
- by rewrite n_plus_zero_eq_n.
- by rewrite /= IHn succ_plus.
Qed.

Fixpoint length (l : list nat) := 
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Fixpoint append (l : list nat) (n : nat) :=
  match l with
  | nil => cons n nil
  | cons head l' => cons head (append l' n)
  end.

(* Q7-1 リストに関する関数を定義する問題 *)
Fixpoint list_sum (l : list nat) :=
  match l with
  | nil => 0
  | cons n l' => n + list_sum l'
  end.

(* Q7-2 少し複雑な関数を定義する問題 *)
Fixpoint list_at (l : list nat) (n : nat) := 
  match l with
  | nil => 0
  | cons h l' =>
    match n with
    | 0 => h
    | S n' => list_at l' n'
    end
  end.

Fixpoint last (l : list nat) :=
  match l with
  | nil => 0
  | cons n1 nil => n1
  | cons n1 (cons n2 l' as tail) => last tail
  end.

(* Q7-3 リストに関する関数の性質を証明する問題 *)
Theorem cons_length l n : length (cons n l) = S (length l).
Proof.
by rewrite /=.
Qed.

Theorem append_neq_nil l n : append l n <> nil.
Proof.
move => H1.
case_eq l.
- move => H2.
  rewrite H2 in H1.
  by rewrite /= in H1.
- move => n' l' H2.
  rewrite H2 in H1.
  by rewrite /= in H1.
Restart.
by case_eq l.
Qed.

(* Q7-4 リストに関する関数について帰納法を使って証明する *)
Theorem last_append l n : last (append l n) = n.
Proof.
induction l.
- by rewrite /=.
- rewrite /=.
  case_eq (append l n).
  + move => H1.
    by apply append_neq_nil in H1.
  + move=> n' l' H1.
    by rewrite H1 in IHl.
Restart.
induction l => //.
rewrite /=.
case_eq (append l n) => [ H1 | n' l' H1 ].
- by apply append_neq_nil in H1.
- by rewrite H1 in IHl.
Qed.

(* Q7-5 *)
Theorem list_at_pred_length_eq_last l : list_at l (pred (length l)) = last l.
Proof.
induction l.
- by rewrite /=.
- rewrite /=.
  rewrite -IHl.
  case l.
  + by rewrite /=.
  + by rewrite /=.
Restart.
induction l => //.
rewrite /=.
rewrite -IHl.
by case l.
Qed.

Require Import Coq.Arith.PeanoNat.

(* Q8-1 *)
Theorem eqb2_eq2 n : (n =? 2) = true -> n = 2.
Proof.
case n.
- by [].
- move => n0.
  case n0.
  + by [].
  + move => n1.
    case n1.
    * by [].
    * by [].
Restart.
case n => // n0.
case n0 => // n1.
by case n1.
Qed.

(* Q8-2 *)
Lemma eq_eqb n m : n = m -> (n =? m) = true.
Proof.
move => H1.
rewrite H1.
clear n H1.
induction m.
- by [].
- by [].
Restart.
move => ->.
by induction m.
Qed.

(* Q8-3 *)
Theorem eqb_eq n m : (n =? m) = true -> n = m.
Proof.
move : m.
induction n.
- move => m H1.
  case_eq m.
  + by [].
  + move => n H2.
    by rewrite H2 in H1.
- move => m H1.
  rewrite /= in H1.
  case_eq m.
  + move=> H2.
    by rewrite H2 in H1.
  + move=> m1 H2.
    rewrite H2 in H1.
    apply f_equal.
    by apply IHn.
Restart.
move : m.
induction n => m H1.
- case_eq m => // m1 H2.
  by subst.
- case_eq m => [ H2 | m1 H3 ].
  + by subst.
  + apply /f_equal /IHn.
    by subst.
Qed.

Axiom classic : forall P : Prop, P \/ ~ P.

(* Q9-1 *)
Theorem Peirce P : (~ P -> P) -> P.
Proof.
case (classic P) => //.
move => np H1.
by apply H1.
Qed.

(* Q9-2 *)
Theorem not_and_or P Q : ~ (P /\ Q) <-> ~ P \/ ~ Q.
Proof.
split => [ H1 | H1 H2 ].
- case (classic P) => [ p | np ].
  + right => q.
    apply H1.
    by split.
  + by left.
- case H2 => [ p q ].
  by case H1 => [ np | nq ].
Qed.

(* Q9-3 *)
Theorem not_or_and P Q : ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
split => [ H1 | H1 H2 ].
- split => [ p | q ];
    apply H1;
    by [ left | right ].
- case H1 => np nq.
  by case H2.
Qed.















