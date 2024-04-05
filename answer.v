(* 
# Coq勉強会の解答
 *)
From mathcomp Require Import ssreflect.

Section Section1.
Variables A B C : Prop.

(* Q1-1 直前のA_to_Aを写経する問題 *)
Definition admitted_sample : A -> A := fun a => a.

(* Q1-2 ラムダ式を使う問題 *)
Definition A_to_B_to_A  : A -> B -> A := fun a => fun b => a.
Definition A_to_B_to_A2 : A -> B -> A := fun a b => a. (* 2引数を同時に受け取ることもできます *)
Definition A_to_B_to_A3 : A -> B -> A := fun a _ => a. (* 使わない引数はアンダーバーにもできます *)

(* Q1-3 関数を含意として使う問題 *)
Definition modus_ponens : (A -> B) -> A -> B := fun H a => H a.

(* Q1-4 *)
Definition imply_trans : (A -> B) -> (B -> C) -> (A -> C) := fun h1 h2 a => h2 (h1 a).

(* Q2-1 直前のパターンマッチの記述を理解しているか問う問題 *)
Definition and_right : A /\ B -> B :=
  fun h1 =>
    match h1 with
    | conj a b => b
    end.

(* Q2-2 andを式から組みたてる問題 *)
Definition A_to_B_to_A_and_B :  A -> B -> A /\ B :=
  fun a b => conj a b.

(* Q2-3 andの総合問題 *)
Definition and_comm' : A /\ B -> B /\ A :=
  fun h1 =>
    match h1 with
    | conj a b => conj b a
    end.

(* Q2-4 or_introlとor_introrを理解してるか問う問題 *)
Definition B_to_A_or_B : B -> A \/ B := fun b => or_intror b.

(* Q2-5 orの総合問題 *)
Definition or_comm' : A \/ B -> B \/ A :=
  fun H =>
    match H with
    | or_introl b => or_intror b
    | or_intror a => or_introl a
    end.

(* Q2-6 使わない項がある問題 *)
Definition and_to_or : A /\ B -> A \/ B :=
  fun H =>
    match H with
    | conj a _ => or_introl a
    end.
Definition and_to_or2 : A /\ B -> A \/ B :=
  fun H =>
    match H with
    | conj _ b => or_intror b (* この定理はこうも書けます *)
    end.

(* Q3-1 move =>とexactを使う問題 *)
Theorem A_to_B_to_A' : A -> B -> A.
Proof.
move => a.
move => b.
exact a.
Restart.
move => a b. (* 2引数を同時に受け取れます *)
by []. (* byタクティックを使って自動で証明を進められます *)
Qed.

(* Q3-2 applyを使う問題 *)
Theorem imply_trans' : (A -> B) -> (B -> C) -> (A -> C).
move => h1 h2 a.
apply h2.
apply h1.
exact a.
Restart.
move => h1 h2 a.
by apply /h2 /h1. (* applyは/を使うことで複数の仮定を同時に渡すこともできます *)
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
case; by [ right | left ].
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
by case => [ [ ] | [ ] ]. (* 可読性はかなり悪いですが、このような書き方もできます *)
Qed.

End Section1.

(* Q5-1 rewriteとreflexivityを使う問題 *)
Theorem rewrite_sample2 n : n = 3 -> n + 1 = 4.
Proof.
move => H.
rewrite H.
rewrite /=.
reflexivity.
Restart.
by move => ->. (* ゴールに対するrewriteはこのようにも書けます *)
Qed.

(* Q5-2 関数を使った命題の証明を問う問題 *)
Theorem rewrite_sample3 n m: n = S m -> pred n = m.
Proof.
move => H.
rewrite H.
rewrite /=.
reflexivity.
Restart.
by move => ->.
Qed.

(* Q5-3 existsを使う問題 *)
Theorem mul_functional : forall n m, exists x, x = n * m.
Proof.
move => n m.
by exists (n * m).
Qed.

(* Q5-4 *)
Theorem sqrt_25 : exists x, x * x = 25.
Proof.
by exists 5.
Qed.

(* Q5-5 仮定にexistsが来るので、それを分解する問題 *)
Theorem exists_sample1 n : (exists m, n = m + 2 /\ m = 2) -> n = 4.
Proof.
case => x.
case => H1 H2.
rewrite H1.
rewrite H2.
reflexivity.
Restart.
by case => x [ -> -> ].
Qed.

(* Q5-6 仮定のexistsを分解し、更にexistsタクティックを使う問題 *)
Theorem exists_sample2 n : (exists m, n = S (S m)) -> (exists l, n = S l).
Proof.
case => m H1.
by exists (S m).
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
induction n => /=.
- by rewrite n_plus_zero_eq_n.
- by rewrite IHn succ_plus.
Qed.

Require Import Coq.Arith.PeanoNat.

(* Q7-1 *)
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

(* Q7-2 *)
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

(* Q7-3 *)
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

(* Q7-4 *)
Theorem neq_S n m : S n <> S m -> n <> m.
Proof.
move => H1 H2.
apply H1.
apply f_equal.
by [].
Restart.
move => H1 H2.
by apply /H1 /f_equal.
Qed.

(* ボツ問題 *)
Theorem S_neq n m : n <> m -> S n <> S m.
Proof.
move => H1 H2.
apply (f_equal pred) in H2.
by rewrite /= in H2.
Restart.
move => H1 H2.
apply H1.
by case: H2.
Qed.


Axiom classic : forall P : Prop, P \/ ~ P.

(* Q8-1 *)
Theorem Peirce P : (~ P -> P) -> P.
Proof.
case (classic P) => //.
move => np H1.
by apply H1.
Qed.

(* Q8-2 *)
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

(* Q8-3 *)
Theorem not_or_and P Q : ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
split => [ H1 | H1 H2 ].
- split => [ p | q ];
    apply H1;
    by [ left | right ].
- case H1 => np nq.
  by case H2.
Qed.

Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.

Module Section2.

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

(* Q9-1 *)
Fixpoint reverse (l : list nat) :=
  match l with
  | nil => nil
  | cons n l' => append (reverse l') n
  end.

(* Q9-2 少し複雑な関数を定義する問題 *)
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

(* Q9-3 リストに関する関数の性質を証明する問題 *)
Theorem cons_length l n : length (cons n l) = S (length l).
Proof.
by rewrite /=.
Qed.

Theorem length_append_succ l n : length (append l n) = S (length l).
Proof.
induction l.
- by [].
- rewrite /=.
  by rewrite IHl.
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

(* Q9-4 リストに関する関数について帰納法を使って証明します *)
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
induction l => //=.
case_eq (append l n) => [ H1 | n' l' H1 ].
- by apply append_neq_nil in H1.
- by rewrite H1 in IHl.
Qed.

(* Q9-5 *)
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
induction l => //=.
rewrite -IHl.
by case l.
Qed.

(* Q9-6 *)
Theorem reverse_length l : length (reverse l) = length l.
Proof.
induction l.
- by rewrite /=.
- rewrite /=.
  rewrite length_append_succ.
  by rewrite IHl.
Restart.
induction l => //=.
by rewrite length_append_succ IHl.
Qed.

(* Q9-7 *)
Theorem reverse_reverse l : reverse (reverse l) = l.
Proof.
induction l.
- by [].
- rewrite -{2}IHl.
  rewrite /=.
  clear IHl.
  induction (reverse l).
  + by rewrite /=.
  + rewrite /=.
    rewrite IHl0.
    by rewrite /=.
Restart.
induction l => //=.
rewrite -{2}IHl.
clear IHl.
move : (reverse l) => rev.
induction rev => //=.
by rewrite IHrev.
Qed.

End Section2.

Require Import Recdef FunInd Coq.Lists.List Coq.Arith.Wf_nat Coq.Arith.PeanoNat Coq.Arith.Lt.
Import Coq.Lists.List.ListNotations Coq.Arith.PeanoNat.Nat.
(* Listの記法については https://coq.inria.fr/doc/V8.19.0/stdlib/Coq.Lists.List.html を見てください *)

(* Q10-1 *)
Fixpoint sorted (l : list nat) : Prop :=
  match l with
  | [] => True
  | x1 :: xs1 => (forall x, In x xs1 -> x1 <= x) /\ sorted xs1
    (* この方が累積帰納法と相性が良いためこの定義にしています。余裕があれば素朴な定義との同値性を示してみると良いでしょう *)
  end.

(* Q10-2 *)
Lemma length_filter {A: Type} : forall (xs: list A) f,
  length (filter f xs) <= length xs.
Proof.
move => xs f.
induction xs => //=.
case (f a) => /=.
- by rewrite -Nat.succ_le_mono.
- by apply Nat.le_le_succ_r.
Qed.

(* Q10-3 *)
Function quick_sort (xs: list nat) {measure length}: list nat :=
  match xs with
  | [] => []
  | pivot :: xs1 =>
    let right := filter (fun x => x <? pivot) xs1 in
    let left := filter (fun x => pivot <=? x) xs1 in
      quick_sort right ++ pivot :: (quick_sort left)
  end.
Proof.
- move => xs pivot xs1 Hxs /=.
  by apply /le_lt_n_Sm /length_filter.
- move => xs pivot xs1 Hxs /=.
  by apply /le_lt_n_Sm /length_filter.
Qed.

(* Q10-4 *)
Lemma quick_sort_nil : quick_sort nil = nil.
Proof.
by rewrite quick_sort_equation.
Qed.

(* Q10-5 *)
Lemma filter_negb_In xs (x : nat) f g :
  In x xs ->
  (forall x', g x' = negb (f x')) ->
  In x (filter f xs) \/ In x (filter g xs).
Proof.
move => Hxin.
case_eq (f x) => /= Hfx.
- left.
  rewrite filter_In.
  by split.
- right.
  rewrite filter_In.
  split => //.
  by rewrite H Bool.negb_true_iff.
Qed.

(* Q10-6 *)
Lemma sorted_app l r :
  sorted l -> sorted r -> (forall lx rx, In lx l -> In rx r -> lx <= rx) ->
  sorted (l ++ r).
Proof.
move => Hsorted_l Hsorted_r Hlx_le_rx.
induction l as [ | n ] => //=.
split.
- move => x Hin_x.
  rewrite in_app_iff in Hin_x.
  case Hin_x.
  + move => Hx_in.
    rewrite /= in Hsorted_l.
    case Hsorted_l => H _.
    by apply H.
  + apply Hlx_le_rx.
    by apply in_eq.
- apply IHl.
  + by apply Hsorted_l.
  + move => lx rx Hlx_in Hrx_in.
    apply Hlx_le_rx => //=.
    by right.
Qed.

(* Q10-7 *)
Lemma quick_sort_In_ind xs x :
  (forall xs', length xs' < length xs -> (In x xs' <-> In x (quick_sort xs'))) ->
  (In x xs <-> In x (quick_sort xs)).
Proof.
move => Hquick_sort_In_length.
split => [ Hinx | ].
- case_eq xs => [ H | x1 xs1 Hxs ].
    by rewrite H in Hinx.
  rewrite quick_sort_equation.
  remember (quick_sort (filter (fun x0 => x0 <? x1) xs1)) as left.
  remember (quick_sort (filter (fun x0 => x1 <=? x0) xs1)) as right.
  rewrite in_app_iff /=.
  rewrite or_comm or_assoc.
  rewrite Hxs /= in Hinx.
  case Hinx => H1.
    by left.
  right.
  have : forall f, length (filter f xs1) < length xs => [ f | Hlength_filter ].
    rewrite Hxs /=.
    by apply /le_lt_n_Sm /length_filter.
  rewrite Heqright Heqleft.
  repeat rewrite -Hquick_sort_In_length; (* repeatはタクティックを何度も実行します *)
    try by apply Hlength_filter. (* 元のゴール+2つの追加されたゴールに対してby applyします。tryなのでエラーが出る方は無視されます *)
  apply filter_negb_In => // x'.
  by apply leb_antisym.
- rewrite quick_sort_equation.
  case_eq xs => //= x1 xs1 Hxs.
  remember (quick_sort (filter (fun x0 => x0 <? x1) xs1)) as left.
  remember (quick_sort (filter (fun x0 => x1 <=? x0) xs1)) as right.
  rewrite in_app_iff.
  case => /= Hinx.
  + rewrite Heqleft in Hinx.
    rewrite -Hquick_sort_In_length in Hinx.
    * rewrite filter_In in Hinx.
      case Hinx => H _.
      by right.
    * rewrite Hxs /=.
      by apply /le_lt_n_Sm /length_filter.
  + case Hinx => H1.
      by left.
    rewrite Heqright in H1.
    rewrite -Hquick_sort_In_length in H1.
    * rewrite filter_In in H1.
      case H1 => H2 _.
      by right.
    * rewrite Hxs /=.
      by apply /le_lt_n_Sm /length_filter.
Qed.

Definition length_quick_sort_In(l: nat) :=
  forall xs x, l = length xs -> In x xs <-> In x (quick_sort xs).

(* Q10-8 *)
Lemma quick_sort_In xs x :
  In x xs <-> In x (quick_sort xs).
Proof.
apply (lt_wf_ind (length xs) length_quick_sort_In) => //.
move => l Hlength_lt_In xs1 x1 Hxs1_length.
subst.
apply quick_sort_In_ind.
move => xs2 Hxs2.
by apply (Hlength_lt_In (length xs2)).
Qed.

(* Q10-9 *)
Lemma quick_sort_sorted_length_ind xs :
  (forall xs', length xs' < length xs -> sorted (quick_sort xs')) ->
  sorted (quick_sort xs).
Proof.
move => Hsorted_quick_sort.
case_eq xs.
  by rewrite quick_sort_nil.
move => pivot xs1 Hxs.
rewrite quick_sort_equation.
remember (quick_sort (filter (fun x0 => x0 <? pivot) xs1)) as left.
remember (quick_sort (filter (fun x0 => pivot <=? x0) xs1)) as right.
case_eq left.
- rewrite /=.
  split => [ x | ].
  + rewrite Heqright -quick_sort_In filter_In.
    case.
    by rewrite Nat.leb_le.
  + rewrite Heqright.
    apply Hsorted_quick_sort.
    subst => /=.
    by apply /le_lt_n_Sm /length_filter.
(* (head :: left) ++ x1 :: right *)
- rewrite Heqleft.
  clear Heqleft left.
  move=> head left Heqleft /=.
  split => [ x | ].
  (* headはそれ以外の要素のどれよりも小さいことを示します *)
  + rewrite in_app_iff.
    case => [ Hin_left | Hin_right ].
    * suff : sorted (head :: left).
        rewrite /=.
        case => H _.
        by apply H.
      rewrite -Heqleft.
      apply Hsorted_quick_sort.
      rewrite Hxs /=.
      by apply /le_lt_n_Sm /length_filter.
    * have : head <= pivot => [ | Hhead_le_x1 ].
        move : (in_eq head left).
        rewrite -Heqleft.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case => _.
        rewrite ltb_lt.
        by apply lt_le_incl.
      have : pivot = x \/ In x right.
        by move : Hin_right.
      clear Hin_right.
      case => [ <- | ].
      - by apply Hhead_le_x1.
      - rewrite Heqright.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case => _.
        rewrite leb_le.
        apply le_trans.
        by apply Hhead_le_x1.
  (* head以外の要素がソートされていることを示します *)
  + apply sorted_app.
    * suff : sorted (head :: left).
        rewrite /=.
        by case.
      rewrite -Heqleft.
      apply Hsorted_quick_sort.
      rewrite Hxs /=.
      by apply /le_lt_n_Sm /length_filter.
    * rewrite Heqright /=.
      split => [ x | ].
      -- rewrite -quick_sort_In.
         rewrite filter_In.
         case => _.
         by rewrite leb_le.
      -- apply Hsorted_quick_sort.
         rewrite Hxs /=.
         by apply /le_lt_n_Sm /length_filter.
    * move => lx rx Hlx Hrx.
      rewrite /le.
      apply (le_trans lx pivot rx).
      -- subst.
         have : In lx (head :: left).
           rewrite /=.
           by right.
         rewrite -Heqleft.
         rewrite -quick_sort_In.
         rewrite filter_In.
         case => _.
         rewrite ltb_lt.
         by apply lt_le_incl.
      -- rewrite /= in Hrx.
         case Hrx => [ -> // | ].
         rewrite Heqright.
         rewrite -quick_sort_In.
         rewrite filter_In.
         rewrite leb_le.
         by case.
Qed.

Definition length_quick_sort_sorted (l: nat) :=
  forall xs, l = length xs -> sorted (quick_sort xs).

(* Q10-10 *)
Theorem quick_sort_sorted xs :
  sorted (quick_sort xs).
Proof.
apply (lt_wf_ind (length xs) length_quick_sort_sorted) => // len.
rewrite /length_quick_sort_sorted.
move => Hlength_lt_sorted xs1 Hxs1_length.
subst.
apply quick_sort_sorted_length_ind.
move => xs2 Hxs2_length.
by apply (Hlength_lt_sorted (length xs2)).
Qed.

