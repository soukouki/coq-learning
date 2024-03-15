(*
# Coq勉強会の資料

## 想定読者

強い静的型付けが行われる関数型プログラミングに慣れた方
(例えば、Haskell、OCamlといった言語を触ったことがある方)

## 目指すレベル

基本的なSSReflectのタクティックの機能を使って証明できる
簡単なInductiveの定義を見て理解できる
マージソートの形式化の証明ができる

## 扱わない内容

uniqueやsigma-typeといった一段複雑なもの
モジュールシステム

*)

(* 
CoqIDEではCtrl+↓とCtrl+↑キーを使い、一部分ずつ型検査できます
Ctrl+↓を押して進んでいきましょう
 *)

From mathcomp Require Import ssreflect.

Section Section1.
Variables A B C : Prop.

(* 
*** ステップ1 ***

Definitionで定数を定義します
A_to_Aという変数はA -> Aという型を持ちます
fun <名前>  => <式> でラムダ式を定義できます
 *)
Definition A_to_A : A -> A := fun a  => a.

(* Q1-1 問題はこの形式で書かれているので、末尾のカンマとAdmittedを消して穴埋め部分を埋めてください *)
Definition admitted_sample : A -> A.
Admitted.

(* Q1-2 *)
Definition A_to_B_to_A : A -> B -> A.
Admitted.

(*
f : A -> B
a : A
という型のとき、f aとすることで関数呼び出しを行い、b型の値を得ることができます
 *)

(* Q1-3 *)
Definition modus_ponens : (A -> B) -> A -> B.
Admitted.

(* Q1-4 3引数を受け取ることに注意しましょう *)
Definition imply_trans : (A -> B) -> (B -> C) -> (A -> C).
Admitted.


(* 
*** ステップ2 ***

Inductive and (A B  : Prop)  : Prop :=  conj  : A -> B -> A /\ B.
andの定義は上記の通りです。Inductiveは帰納型で、いわゆる代数的データ構造です
Printコマンド、あるいはCoqIDEではandにカーソルを合わせてCtrl+Shift+Pで定義を確認できます
Coqでは記法を自由に拡張することができ、A /\ Bと書くことでand A Bと同等のことができます

 *)

Print and.
(*
Inductiveで定義された帰納型は、パターンマッチを用いて分解することができます。andは1つの枝conjを持ちます
conjは2引数を受け取るので、分解するときには2つの値が出てきます。求める型の値はその2つ目の値なので、それを返すことで証明できます
 *)
Definition and_left : A /\ B -> A :=
  fun a_and_b  => match a_and_b with
    | conj a b  => a
  end.

(* Q2-1 *)
Definition and_right : A /\ B -> B.
Admitted.

About conj.
(* 
Aboutコマンド、あるいはCoqIDEではconjにカーソルを合わせてCtrl+Shift+Aでどのような型を持っているか確認できます
conjは、2つの値A, Bを受け取り、A /\ Bを返す関数であることがわかります
 *)

(* Q2-2 *)
Definition A_to_B_to_A_and_B : A -> B -> A /\ B.
Admitted.

(* Q2-3 *)
Definition and_comm' : A /\ B -> B /\ A.
Admitted.

Print or.
(* 
Inductive or (A B  : Prop)  : Prop :=
  | or_introl  : A -> A \/ B
  | or_intror  : B -> A \/ B.
orは2つの枝をもつ帰納型です。パターンマッチするさいには2つの枝(or_introl, or_intror)に別れます。
 *)

Definition A_or_A_to_A : A \/ A -> A :=
  fun a_or_a  => match a_or_a with
    | or_introl ha  => ha
    | or_intror ha  => ha
  end.

Definition A_to_A_or_B : A -> A \/ B := fun a  => or_introl a.

(* Q2-4 *)
Definition B_to_A_or_B : B -> A \/ B.
Admitted.

(* Q2-5 *)
Definition or_comm' : A \/ B -> B \/ A.
Admitted.

(* Q2-6 使わない項がある問題 *)
Definition and_to_or : A /\ B -> A \/ B.
Admitted.


(* 
*** ステップ3 ***

ここまで直接式を書いて証明してきましたが、式を直接書くやり方では複雑な証明に耐えられません
そこで、Coqではタクティックと呼ばれるものを使って証明します

また、ここからはDefinitionの変わりにTheoremというコマンドを使います
TheoremはDefinitionと違い式を直接書けませんが、定理を証明する際はTheoremを使います
 *)

Theorem A_to_A' : A -> A.
Proof. (* Proofコマンドは特に効果はありませんが、慣習的に書くことになっています。 *)
move => a. (* move =>タクティックは、ゴールエリアの仮定をコンテキストエリアに移動します *)
exact a. (* exactタクティックは、ゴールエリアの型をもつ式を書くことで、証明を終了できます。 *)
Qed.

(* Q3-1 *)
Theorem A_to_B_to_A' : A -> B -> A.
Proof.
Admitted.

Theorem modus_ponens' : (A -> B) -> A -> B.
Proof.
move => a_to_b a.
apply a_to_b.
(* 
applyタクティックは、ゴールエリアの値に関数を適用します。BにA -> Bを適用することで、Aに変換します
普段プログラムを書くときとは逆方向に証明が進むことに注意してください
 *)
exact a.
Qed.

(* Q3-2 *)
Theorem imply_trans' : (A -> B) -> (B -> C) -> (A -> C).
Admitted.


(* 
*** ステップ4 ***
 *)
Theorem and_left' : A /\ B -> A.
case.
(* caseタクティックは、仮定に帰納型がきたときに、自動でパターンマッチを行い分解します *)
move => ha hb.
exact ha.
Restart. (* Restartコマンドは、証明を最初からやり直せます *)
case => ha hb.
(* 
caseタクティックには=>を付けることで、caseとmove =>を合わせたような動作をします
他のタクティックにも=>を付けると同じように動作するものがあります。いろいろ試してみましょう
 *)
exact ha.
Qed.

(* Q4-1 *)
Theorem and_right' : A /\ B -> B.
Proof.
Admitted.

Theorem A_to_B_to_A_and_B' : A -> B -> A /\ B.
Proof.
move => a b.
split.
(* 
splitタクティックは、ゴールに帰納型がきたときに分解します
ゴールが2つに分かれるので、それぞれに対してタクティックを適用していきます
 *)
- exact a.
- exact b.
Restart.
apply conj. (* これはconjそのものなので、このように書いても証明できます *)
Qed.

(* Q4-2 *)
Theorem and_comm'' : A /\ B -> B /\ A.
Proof.
Admitted.

Theorem A_to_A_or_B' : A -> A \/ B.
Proof.
move => a.
left.
(* ゴールがA \/ Bの形になっているときには、leftタクティックとrightタクティックを使うことで、選択することができます *)
exact a.
Restart.
move => a.
apply or_introl. (* applyタクティックでor_introlを直接使うことでも証明できます *)
exact a.
Restart.
exact (fun a  => or_introl a). (* 可読性は悪いですが、このような書き方もできます *)
Qed.

(* Q4-3 *)
Theorem or_comm'' : A \/ B -> B \/ A.
Proof.
Admitted.

(* Q4-4 *)
Theorem Q4_4 : (A /\ B) \/ (B /\ C) -> B.
Proof.
Admitted.

End Section1.


(* 
*** ステップ5 ***

ここまで「ならば」「かつ」「または」といった基本的な命題を扱ってきましたが、ここからはより数学的な命題を証明していきます
 *)

Print nat.
(* 
Inductive nat  : Set :=
  | O  : nat
  | S  : nat -> nat.
Coqでは、nat(naturl number - 自然数)型を扱って証明していきます
0 = O
1 = S(O)
2 = S(S(O))
...
というふうに続きます
 *)

Theorem rewrite_sample1 n : n = 2 -> n + 1 = 3.
Proof.
move => H1.
rewrite H1. (* rewriteタクティックは、仮定の等式を使用してゴールを置き換えます *)
rewrite /=. (* rewrite /=とすると、式中の単純な等式変形を行います *)
reflexivity. (* 両辺が等しいときにはreflexivityタクティックを使うと証明できます *)
Restart.
move => H1.
by rewrite H1.
(* byを前に付けると証明をある程度自動で進めてくれます。また、SSReflectではゴールを解決したタイミングでbyを付けるようにすることが多いです *)
Qed.

(* Q5-1 *)
Theorem rewrite_sample2 n : n = 3 -> n + 1 = 4.
Proof.
Admitted.

(* 
Coqでは関数の中身を見ることができます
また、rewrite /Nat.predというふうにすると中身を展開することができます
 *)
Print Nat.add.
Print Nat.mul.
Print Nat.sub.
Print Nat.pred.

(* Q5-2 *)
Theorem rewrite_sample3 n m: n = S m -> pred n = m.
Proof.
Admitted.

(* 
論理学では、すべての<変数>に対して<命題>が成り立つ(全称量化)、ある<変数>が存在し<命題>を満たす(存在量化)、という命題を書けます
Coqでは、前者をforall <変数>, <命題>、後者をexists <変数>, <命題>と書きます

例えば、次の定理add_functinalは「すべての自然数n, mに対して、ある自然数xが存在し、x = n + mを満たす」という意味です
 *)
Theorem add_functional : forall n m, exists x, x = n + m.
Proof.
move => n m.
by exists (n + m).
Qed.

(* Q5-3 *)
Theorem mul_functional : forall n m, exists x, x = n * m.
Proof.
Admitted.

(* Q5-4 *)
Theorem sqrt_5 : exists x, x * x = 25.
Proof.
Admitted.


(* 
*** ステップ6 ***

ここからは帰納法を使い、一般的な値の定理を証明していきます
 *)
Theorem mul_one_eq_n n : n * 1 = n.
Proof.
move : n. (* move :タクティックを使うことで、コンテキストからゴールへ移動できます *)
induction n. (* inductionタクティックを使うことで、帰納法を利用できます *)
- by [].
- rewrite /=.
  by rewrite IHn.
Qed.

(* Q6-1 *)
Theorem n_plus_zero_eq_n n : n + 0 = n.
Proof.
Admitted.

(* Q6-2 *)
Theorem succ_plus n m : n + (S m) = S (n + m).
Proof.
Admitted.

(* Q6-3 rewrite n_plus_zero_eq_nとすると既に証明した定理を使えます *)
Theorem plus_comm n m : n + m = m + n.
Proof.
Admitted.


Require Import Coq.Arith.PeanoNat.

(* 
*** ステップ7 ***

Coqでは、真と偽を表すのにbool型の真偽値だけではなく、命題型を使うことができます
trueとfalseはbool型の値で、TrueとFalseは命題型の型になります
True型はコンストラクタIを持つ値で、常に作成できます。任意の命題Pに対してP -> Trueは成り立ちます
False型はコンストラクタを持たない値で、この型を持つ値は存在しません。ところで、この型の値をパターンマッチするとどうなるでしょうか？
 *)
Print bool.
Print True.
Print False.

Definition False_nat : False -> nat :=
  fun fals => match fals with
  end.
Definition False_bool : False -> bool :=
  fun fals => match fals with
  end.
About False_ind.
(* 
なんと任意の型に変換することができるのです。これは論理学の「矛盾からなんでも導ける」という性質に対応しています
証明している際、仮定が矛盾していることを見つければ、仮定をいじってFalseを導くことで、そこからゴールの型を生成して証明を終わらせられます
 *)

Print not.

(* Q7-1 CoqIDEではCtrl+Shift+nでNotationの切り替えができます *)
Theorem eqb2_eq2 n : (n =? 2) = true -> n = 2.
Proof.
Admitted.

(* clearタクティックを使うことで、コンテキストにある仮定や変数を削除できます *)

(* Q7-2 *)
Lemma eq_eqb n m : n = m -> (n =? m) = true.
Proof.
Admitted.

Search (_ _ = _ _ -> _ = _). (* 次の問題を解く際にはある定理を使う必要があります *)

(* Q7-3 *)
Theorem eqb_eq n m : (n =? m) = true -> n = m.
Proof.
Admitted.

(* 命題A, Bに対して、A <-> Bという命題はA -> BかつB -> Aを表します *)
Theorem eq_iff_eqb n m : (n =? m) = true <-> n = m.
Proof.
split.
- by apply eqb_eq.
- by apply eq_eqb.
Qed.

Theorem eqb2_eq2' n : (n =? 2) = true -> n = 2.
Proof.
by rewrite eq_iff_eqb. (* <->にするとrewriteタクティックを使って式中の値を書き換えることができます *)
Restart.
rewrite -eq_iff_eqb. (* また、rewrite -<命題名>とすると逆方向への書き換えができます *)
by [].
Qed.


(* 
*** ステップ8 ***

bool型はパターンマッチすることでtrueかfalseに場合分けできます
しかし、Prop型はそのままでは場合分けできません
カリー・ハワード同系対応と対応する論理である直感主義論理では、命題が真か偽かで場合分けできません
ですがこれではまともに数学ができないので、公理としてある命題が真か偽かで場合分けできるようにします
標準ライブラリではCoq.Logic.Classicに存在しますが、ここでは車輪の再実装をします
 *)

Axiom classic : forall P : Prop, P \/ ~ P.

Theorem NNPP P : ~ ~ P -> P.
Proof.
by case (classic P).
Qed.

(* Q8-1 *)
Theorem Peirce P : (~ P -> P) -> P.
Proof.
Admitted.

(* Q8-2 *)
Theorem not_and_or P Q : ~ (P /\ Q) <-> ~ P \/ ~ Q.
Proof.
Admitted.

(* Q8-3 *)
Theorem not_or_and P Q : ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
Admitted.


Module Section2.

(* 
*** ステップ9 ***

ここからはリストを使い、アルゴリズムの証明を行います
 *)
Print list.
(* 
リストの定義は次のようになっています
Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.
 *)
Compute nil.
Compute (cons 1 nil).
Compute (cons 1 (cons 2 nil)).

(* 
リストの長さを計算する関数です
再帰関数を定義するときはFixpointコマンドを使います
 *)
Fixpoint length (l : list nat) := 
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
Compute length nil.
Compute length (1 :: nil). (* consはこのような書き方もできます *)
Compute length (1 :: 2 :: nil).

(* リストの末尾に値を追加する関数です *)
Fixpoint append (l : list nat) (n : nat) :=
  match l with
  | nil => cons n nil
  | cons head l' => cons head (append l' n)
  end.
Compute append (1 :: nil) 2.

(* Q9-1 リストを逆順に並べる関数reverseを定義してみましょう *)
Fixpoint reverse (l : list nat) := l.

(* Q9-2 リストのn番目の要素を取得する関数を定義してみましょう 2重にパターンマッチングする必要があります *)
Fixpoint list_at (l : list nat) (n : nat) := 0.
Compute list_at (1 :: 2 :: nil) 0.
Compute list_at (1 :: 2 :: nil) 1.

(* 
リストの最後の要素を取得する関数です
パターンマッチの一部を取るときにはasを使います
Coqでは無限ループができないことになっているので、それを保証するために必ずパターンマッチの一部を使って呼び出す必要があります
(もっと一般に無限ループしないこと(=停止性)を保証するやり方は後ほど述べます)
 *)
Fixpoint last (l : list nat) :=
  match l with
  | nil => 0
  | cons n1 nil => n1
  | cons n1 (cons n2 l' as tail) => last tail (* asを使うとパターンマッチの内容の一部を変数に取り出せます *)
  end.
Compute last (1 :: nil).
Compute last (1 :: 2 :: nil).

(* 定義した関数に対して性質を証明することもできます *)
Theorem one_length n : length (cons n nil) = 1.
Proof.
rewrite /=.
reflexivity.
Restart.
by []. (* byタクティックは証明を大幅に短くできます。活用していきましょう *)
Qed.

(* Q9-3 *)
Theorem cons_length l n : length (cons n l) = S (length l).
Proof.
Admitted.

(* listも帰納型の一種なので、帰納法を使えます *)
Theorem length_append_succ l n : length (append l n) = S (length l).
Proof.
induction l.
- by [].
- rewrite /=.
  by rewrite IHl.
Qed.

(* 
last_appendに使用する補題です
Lemma, Fact, Remark, Corollary, Proposition, PropertyはTheoremと同等です
 *)
Lemma append_neq_nil l n : append l n <> nil.
Proof.
move => H1. (* A <> Bはnot (A == B)になります。not AはA -> False(偽)なので、moveで移動できます *)
case_eq l. (* caseだけでは条件が足りないとき、case_eqというタクティックを使うとうまく行く場合もあります *)
- move => H2.
  rewrite H2 in H1.
(* 
rewrite inを使うことで、コンテキストにある項を書き換えられます
同様のタクティックとして、apply inもあります
 *)
  rewrite /= in H1.
  by []. (* 仮定にn :: nil = nilのように明らかに偽である式があるとき、byタクティックを使うとゴールを問わず証明できます *)
- move => n' l' H2.
  rewrite H2 in H1.
  by rewrite /= in H1.
Qed.

(* Q9-4 *)
Theorem last_append l n : last (append l n) = n.
Proof.
have : append l n <> nil.
(* haveとsuffはゴールを追加し、それを使って証明を進めます。長い証明ではhaveとsuffを使い見通しを良くします *)
  move => H1. (* A <> Bはnot (A == B)になります。not AはA -> False(偽)なので、moveで移動できます *)
  case_eq l. (* caseだけでは条件が足りないとき、case_eqというタクティックを使うとうまく行く場合もあります *)
  - move => H2.
    rewrite H2 in H1.
(* 
rewrite inを使うことで、コンテキストにある項を書き換えられます
同様のタクティックとして、apply inもあります
 *)
    rewrite /= in H1.
    by []. (* 仮定にn :: nil = nilのように明らかに偽である式があるとき、byタクティックを使うとゴールを問わず証明できます *)
  - move => n' l' H2.
    rewrite H2 in H1.
    by rewrite /= in H1.
move => append_neq_nil.
Admitted.

(* Q9-5 *)
Theorem list_at_pred_length_eq_last l : list_at l (pred (length l)) = last l.
Proof.
Admitted.

Search nat list.
Search length append.
Search (length (append _ _)).
(* 
次の問題では、これまでに証明した定理を再利用します
今使える定理はSearchコマンドで検索できます
複数並べるとandに、括弧で括って_を使うとパターンマッチによる検索ができます
 *)

(* Q9-7 *)
Theorem reverse_length l : length (reverse l) = length l.
Proof.
Admitted.

(* Q9-8 *)
Theorem reverse_reverse l : reverse (reverse l) = l.
Proof.
Admitted.

End Section2.

(* 
説明してないが重要なタクティック
have :
suff :
rewriteの{}を使った置換の指定
rewriteの[]を使った置換の指定
 *)


(* 
*** ステップ10 ***

ここまでお疲れ様でした。ここからはラストスパート、ソートの形式化に突き進んでいきましょう
 *)
Require Import Recdef FunInd Coq.Lists.List Coq.Arith.Wf_nat Coq.Arith.PeanoNat Coq.Arith.Lt.
Import Coq.Lists.List.ListNotations Coq.Arith.PeanoNat.Nat.
(* Listの記法については https://coq.inria.fr/doc/V8.19.0/stdlib/Coq.Lists.List.html を見てください *)

Print In.
Print length.
Print filter.
Print app.

(* Q10-1 リストがソートされていればTrueになる関数is_sortedを定義してみましょう *)
Fixpoint sorted (l : list nat) : Prop := True.

(* Q10-2 *)
Lemma length_filter : forall (xs: list nat) f,
  length (filter f xs) <= length xs.
Proof.
Admitted.

(* Q10-3 複雑な再帰の場合にはFunctionコマンドを使用する必要があります。停止性を証明してみましょう *)
Function quick_sort (xs: list nat) {measure length}: list nat :=
  match xs with
  | [] => []
  | pivot :: xs1 =>
    let right := filter (fun x => x <? pivot) xs1 in
    let left := filter (fun x => pivot <=? x) xs1 in
      quick_sort right ++ pivot :: (quick_sort left)
  end.
Proof.
Admitted.

(* Q10-4 Functionコマンドでquick_sort_equationが定義されるので、それを使いましょう *)
Lemma quick_sort_nil : quick_sort nil = nil.
Proof.
Admitted.

(* Q10-5 *)
Lemma quick_sort_single x1 : quick_sort [x1] = [x1].
Proof.
Admitted.

(* Q10-6 *)
Lemma filter_negb_In {A: Type}: forall xs (x: A) f g,
  In x xs ->
  (forall x', g x' = negb (f x')) ->
  In x (filter f xs) \/ In x (filter g xs).
Proof.
Admitted.

(* 
便利タクティック
- remember <式> as <名前> はゴールやコンテキスト中の式をくくりだして、証明を見やすくできます
- subst はコンテキストにある等式を自動で使用し、最小限の変数で表せるように展開します
 *)

(* Q10- *)
Lemma quick_sort_In_ind xs x :
  (forall xs', length xs' < length xs -> (In x xs' <-> In x (quick_sort xs'))) ->
  (In x xs <-> In x (quick_sort xs)).
Proof.
Admitted.

(* Q10- *)
Theorem quick_sort_sorted: forall xs,
  sorted (quick_sort xs).
Proof.
Admitted.















