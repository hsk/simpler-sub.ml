# simpler-sub.ml
## 1. はじめに

simpler-sub.ml は simple-sub を単純化した simpler-sub を OCamlに移植してより手を加えたものです。
simple-sub は合併型、交差型、レコード型、再帰型、多相型推論を高速に実行するScalaのプログラムです。
若干量が多いので simpler-sub ではいくつかの機能を削除しより理解しやすいものとなっていました。
Scalaで書かれたプログラムは自由に書くことができるのでOCamlに移植することで依存関係を明確にし、最小限の機能で実装することができました。
さらに、型のみが関係しているファイルと構文が関係するファイルをtypeとtyperディレクトリに分けました。
分離したことで型の計算を理解するには構文を意識する必要がなくなりました。
## 2. コード一覧

1. type/ty.ml
2. type/simpleType.ml
3. type/coalesce.ml
4. type/simpleTyper.ml
5. typer/syntax.ml
6. typer/parser.mly
7. typer/lexer.mll
8. typer/typer.ml
9. test/parserTests.ml
10. test/typerTests.ml

ソースコードは型に関する ty.ml simpler.ml coalesce.ml simpleTyper.ml と構文に関係する syntax.ml parser.mly lexer.mll typer.ml それからテスト parserTests.ml typerTests.ml があります。
## 3. 型
## 3.1. 型の表示
型についての表示の処理はTy.show,SimpleType.simplifyType,Coalesce.coalesce によって行われます。
Ty.show は型を表示します。
SimpleType.simplifyTypeは型推論時に用いられるsimpleTypeを簡単化します。
Coalesce.coalesceは型推論時に用いられたsimpleTypeをtyに変換する処理です。

```
type tv = string * int
type ty =
 | Union of ty * ty
 | Inter of ty * ty
 | FunctionType of ty * ty
 | RecordType of (string * ty) list
 | RecursiveType of tv * ty
 | PrimitiveType of string
 | TypeVariable of tv
```
tv は型変数を表すもので、TypeVariable に含まれたりRecursiveTypeに含まれたりします。
ty には合併型や交差型、関数型、レコード型、再帰型、プリミティブ型、型変数型があります。

ty.ml は他にshow関数がありty型を表示する目的で用います。
show関数内では型変数に名前を付け直す機能があります。まず全ての型変数の集合を作り、型変数から名前へのマップを作ります。
後はshowIn関数で型をトラバースし文字列化します。カッコをつけるために優先順位を持たせ、parensIn関数で必要な場合にかっこをつけます。

simpleType.ml では simpleな型表現を定義しています。

```
type simpleType =
  | STTop
  | STBot
  | STFunction of simpleType * simpleType
  | STRecord of (string * simpleType) list
  | Primitive of string
  | STVariable of stv
and stv = {
  mutable _lowerBound: simpleType;
  _uid: int;
  mutable _upperBound: simpleType;
  mutable _representative: stv option;
}
```

TOPとBOTと関数とレコード、プリミティブ型と型変数があり、型変数は破壊的に変更できるようにして型変数との制約のあるサブタイプ関係(_lowerBound,_upperBound)と単一化された変数へのリンク(_representative)があります。UnionやIntersectionはなくてサブタイプ関係の制約が保存されているだけです。

simplifyType は以下の２つの処理をしてsimpleType内の型変数の上限と下限に置き換えて単純化したsimpleTypeを返します。

1. 解析
    - 型をトラバースして型変数が pos か neg か判定しsetに追加
    - pos と neg に分けたほうがサイズが1/2になるので1つのmapより検索効率が2倍速い

2. 変換
    - transformConcrete は型変数なし transformが型変数ありのシンプル化変換
    - transformConcrete はトラバースして transformを呼ぶ
    - mappingにあればそれを返し
    - 上限下限とpolを考慮して lowerBoundかupperBoundを選んで新しい型に書き換えmappingに保存する

coalesce.ml は coalesce : simpleType -> ty な関数です。simpleTypeを合体させて表示しやすいtyにします。
内部関数のgoはpolarity を考慮した変換処理で型変数以外の処理は素直に変換でき、Top,Botもprimitive型に変換してしまいます。
goの型変数の処理は型変数の上限と下限を考慮した変換を行うメインの処理です。

recursiveには再帰型の型と対応する型変数が、inProcessには比較中の型変数が含まれています。
変換する型変数がinProcessに含まれていれば再帰があるので新しい型変数を作りrecursiveに追加し結果とします。
変換する型変数がinProcessに含まれていなければpolarityによって上限か下限を選択し変換後、結果により∨や∧するなどして結果とし、recursiveに含まれているなら再起型にします。
## 3.2. 型推論

simpleTyper.ml は型推論で用いる関数のうち構文と関係なく型のみに注目して処理できるoccursCheck,subtype,instantiateがあります。
subtyping は 2つの型をトラバースして両方とも変数なら単一化し片方だけなら新しく上限あるいは下限をglb,lub関数で計算した値を追加します。
単一化の処理は片方の変数からもう片方への変数へリンクを張って、上限下限を引き継ぎます。
サブタイプ関係は関数の引数で反転することに注意してください。
## 4. 構文

syntax.ml には以下の定義のみがあります:

```
type term =
 | Lit of int
 | Var of string
 | Lam of string * term
 | App of term * term
 | Rcd of (string * term) list
 | Sel of term * string
 | Let of bool * string * term * term
type pgrm = (bool * string * term) list
```
## 4.1. 構文解析
parser.mly lexer.mll はそれぞれ構文解析器と字句解析器で突筆すべき点はありません。
## 4.2. 型推論
typer.ml は構文と関係する型推論をするプログラムです。組込型定義 builtins と型推論のメイン処理 typeTerm letの左側を推論する typeLetRhs があり
inferType inferTypes は1つあるいは複数の型推論のインターフェイスとなる関数です。
typer.ml のコードも特に難しいことはやっていません。
## 5. まとめ

## 6. 参考文献

