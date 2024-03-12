(* 
# Coq勉強会の解答
問題でどのようなことを説いているのかも解説する
 *)
From mathcomp Require Import ssreflect.

Section Section1.
Variables A B C : Prop.

(* Q1-1 直前のA_to_Aを写経する *)
Definition admitted_sample : A -> A := fun a  => a.

(* Q1-2 ラムダ式を使えるか問う問題 *)
Definition A_to_B_to_A :  A -> B -> A := fun a  => fun b  => a.
Definition A_to_B_to_A2 : A -> B -> A := fun a b  => a. (* 2引数を同時に受け取ることもできる *)

(* Q1-3 関数を含意として使う問題 *)
Definition modus_ponens : (A -> B) -> A -> B := fun H a  => H a.

(* Q1-4 同上 *)
Definition imply_trans : (A -> B) -> (B -> C) -> (A -> C) := fun h1 h2 a  => h2 (h1 a).

(* Q2-1 直前のパターンマッチの例を理解しているか問う問題 *)
Definition and_right : A /\ B -> B :=
  fun h1  => match h1 with
    | conj a b  => b
  end.

(* Q2-2 andを式から組みたてる方法を問う問題 *)
Definition A_to_B_to_A_and_B :  A -> B -> A /\ B :=
  fun a b  => conj a b.

(* Q2-3 andの総合的問題 *)
Definition and_comm' : A /\ B -> B /\ A :=
  fun h1  => match h1 with
    | conj a b  => conj b a
  end.

(* Q2-4 or_introlとor_introrを理解してるか問う問題 *)
Definition B_to_A_or_B : B -> A \/ B := fun b  => or_intror b.

(* Q2-5 orの総合的問題 *)
Definition or_comm' : A \/ B -> B \/ A :=
  fun H  => match H with
    | or_introl b  => or_intror b
    | or_intror a  => or_introl a
  end.

(* ボツ問題 追加問題が必要なら使ってください *)
Definition and_to_or : A /\ B -> A \/ B :=
  fun H  => match H with
    | conj a b  => or_introl a
  end.

(* Q3-1 move=>とexactが使えることを問う問題 *)
Theorem A_to_B_to_A' : A -> B -> A.
Proof.
move => a.
move => b.
exact a.
Restart.
move => a b. (* 2引数を同時に受け取れる *)
by []. (* byタクティックを使って自動で証明を進められる *)
Qed.

(* Q3-2 applyを使えることを問う問題 *)
Theorem imply_trans' : (A -> B) -> (B -> C) -> (A -> C).
move => h1 h2 a.
apply h2.
apply h1.
exact a.
Restart.
move => h1 h2 a.
by apply /h2 /h1. (* applyは複数の仮定を同時に渡すこともできる *)
Qed.

(* Q4-1 andに対してcaseを使えることを問う問題 *)
Theorem and_right' : A /\ B -> B.
Proof.
case => a b.
exact b.
Restart.
by case.
Qed.

(* Q4-2 andに対してsplitを使えることを問う問題 *)
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

(* Q4-3 leftとrightを使えることを問う問題 *)
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
Qed.

(* Q4-4 andとorの総合的問題 *)
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

(* Q5-1 rewriteとreflexivityの使い方を問う問題 *)
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

(* Q5-2 *)
Theorem rewrite_sample3 n : n = 2 + 2 -> n * n = 16.
Proof.
rewrite /=.
move => H.
by rewrite H.
Restart.
move => H.
by rewrite H.
Qed.

(* Q6-1 *)
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

(* Q6-3 *)
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

