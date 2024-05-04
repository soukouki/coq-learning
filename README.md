
# Coq勉強会の資料

- ならばの関係からクイックソートの証明までを10ステップ49問にまとめました
- 各ステップの依存関係はgraph.pngにて図解しています
- 各問題には解答があります。answer.vを確認してください

## Coqとは

Coqとは、カリー・ハワード同系対応を用いて、数学の証明をプログラムに落とし込んで型検査を行うことで証明の検証をする定理証明支援系です。カリー・ハワード同系対応とは、数学の証明とプログラムの直接的な対応関係のことです。例えば、「AならばB」は「A型の値を受け取りB型の値を返す関数」と対応しています。

証明が正しいことを確認するのはとても難しいです。例えば4色定理と呼ばれる問題では、とても人には読めないほど長い証明になります。そこで、人が読む以上の検証方法として、証明をプログラムに落とし込み、プログラムに対するツールを使うことが考えられました。Coqはそのようなツールの一つで、型検査を行うことで証明の正しさを検証しています。

## 始め方

次のツールをインストールしてください
1. Coq(本体)
2. MathComp-SSReflect
3. CoqIDE

インストールできましたら、CoqIDEでdocument.vを開いてください

## 想定読者

- 代数的データ構造とパターンマッチがある言語を触ったことがある方
  - 例えば、HaskellやOCamlなど
- 高階関数を扱える方

## 目指すレベル

- 基本的なSSReflectのタクティックの機能を使って証明できる
- 帰納型の定義を見て理解できる
- クイックソート程度のアルゴリズムの証明ができる
- 四則演算の簡単な定理の証明ができる

## 扱わないもの

- uniqueやsigma-type
- 整数・実数・複素数
- 集合
- モジュールシステム
- リフレクション

## 各ステップの概要

- ステップ1
  - ラムダ式と関数呼び出しを用いて簡単な証明をする
  - タクティックは使いません
- ステップ2
  - andとorを用いて証明する
  - タクティックは使いません
- ステップ3
  - exactとapply
- ステップ4
  - caseとsplit
- ステップ5
  - rewriteとexists
- ステップ6
  - induction(帰納法)
  - Coqを少し触る方はQ6-3(加算の交換律)まで解くのがおすすめです
- ステップ7
  - bool型とProp型
- ステップ8
  - 排中律
- ステップ9
  - リストの関数の証明
  - Coqに入門する方はQ9-7(2重にreverseすると元に戻ることの証明)まで解くのがおすすめです
- ステップ10
  - クイックソートがソートできることの証明
  - Q10-10まで解けたらなかなかのものです。是非挑戦してみてください

## 各ステップの依存関係

![](graph.png)
