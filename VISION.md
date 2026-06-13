# VISION

## Making software evolution computable.

このプロジェクトは、ソフトウェアアーキテクチャとソフトウェア進化について責任をもって語るための、数学、形式化、道具、公開面を作る。

アーキテクチャについて語るとき、私たちは多くの言葉を使う。

```text
この変更は境界を越えている。
この設計は保たれている。
この依存は危険である。
この抽象は壊れている。
この修正は未来の変更を難しくする。
```

このプロジェクトは、それらの言葉を変革する。

何が primitive fact なのか。
どの law が作用し、どの obstruction が現れているのか。
どの局所事実が大域的に貼り合うのか。
どの変化がどの future architecture を開くのか。
どの claim が証明で、どれが観測で、どれが予測で、どれがまだ語られていないのか。

AAT / SFT は、この問いに答えるための研究である。

**Goal:** ソフトウェア進化を、経験と直感だけで扱う対象から、定義・観測・計算・証明・統治の対象へ移す。

**What changes:** アーキテクチャレビュー、設計判断、CI、AI proposal、運用 feedback が、同じ語彙の上で接続される。変更は、未来の可能性を変える構造として扱われる。

---

## The grammar of architecture

このプロジェクトの中心には、ウィトゲンシュタイン的な思想がある。

意味は、使われ方の中にある。

ソフトウェアアーキテクチャの語彙も同じである。

`component`、`dependency`、`contract`、`effect`、`state`、`authority`、`semantic meaning`、`runtime interaction`。
これらは、どの文脈で使われ、どの規則に従い、どの law に接続され、どの obstruction を生み、どの operation によって変化するのかによって意味を持つ。

このプロジェクトにおける理論とは、語りの文法を作ることである。
アーキテクチャ、変更、破れ、修復、未来について、語彙、使用条件、推論規則、観測境界、証明境界を明らかにする。

**Goal:** ソフトウェアアーキテクチャの言葉に、使用条件と責任境界を与える。

**What changes:** 「なんとなく良い設計」「危ない気がする変更」という会話が、どの語彙、どの law、どの evidence、どの claim boundary に基づく判断なのかを共有できる会話へ変わる。

---

## AAT: architecture as algebraic geometry

AAT, Algebraic Architecture Theory は、ソフトウェアアーキテクチャを代数幾何の対象として扱うための理論である。

AAT の出発点は Atom である。
Atom は、ソフトウェアアーキテクチャにおいて primitive architectural fact として扱う型付き事実である。

AAT は、Atom から architecture object を生成し、その上に law、obstruction、signature、cover、cohomology、lawful locus、derived / stacky geometry を構成する。

代数幾何は、このプロジェクトが扱いたいものにもっとも適した言語である。
局所的な事実、大域的な貼り合わせ、law が切り出す locus、obstruction が示す破れ、repair による変形を、同じ文法の中で扱えるからである。

重要なのは、AAT がアーキテクチャを「図」から「幾何」へ移すことである。

contract、effect、state、authority、semantic meaning、runtime interaction を含む構造を見る。
局所的に正しいものが、大域的にどう貼り合い、どこで貼り合わないのかを読む。
law が切り出す locus、obstruction が witness する失敗、repair が変形する geometry を扱う。

AAT は、アーキテクチャを代数幾何的対象として扱うための文法である。

**Goal:** ソフトウェアアーキテクチャを、代数幾何の言葉で語れるようにする。

**What changes:** 設計原則は law、locus、obstruction、cover、cohomology、repair geometry として扱われる。アーキテクチャレビューは、taste の衝突から、どの幾何を見ているかを共有する診断へ変わる。

---

## SFT: evolution as computable field

SFT, Software Field Theory は、ソフトウェア進化を計算可能な field として扱う理論である。

ソフトウェアは、状態から状態へ変わる。
その変化は、要求、仕様、Issue、PR、review、CI、運用、incident、ownership、組織判断、feedback によって形づくられる。

変更は、局所的な operation である。
同時に、未来の可能性を変える field action でもある。

SFT は、選ばれた model、horizon、policy、observation boundary、governance の中で、どの future architecture が reachable になり、どの trajectory が開かれ、どの shortcut が減衰され、どの feedback が次の field を変えるのかを扱う。

AAT が architecture の文法を作る。
SFT は、その文法を時間の中へ置く。

**Goal:** ソフトウェア進化を計算可能にする。

**What changes:** PRD、Issue、PR、review、CI、運用 feedback が、future architecture を形づくる field action になる。開発プロセスは、trajectory を設計し、狭め、開き、統治する営みへ変わる。

---

## Proof: grammar made checkable

Lean 形式化は、このプロジェクトの数学面を支える柱である。

AAT / SFT が作る語彙を、検査可能な定義、構成、定理へ落とす。
証明は、語り方の文法を checkable grammar にする。

どの定義から、どの仮定のもとで、どの命題が従うのか。
どの claim が theorem なのか。
どれが construction、analytic reading、empirical hypothesis なのか。

Lean は、この境界を明らかにする。

AAT / SFT において、証明とは、選ばれた universe、選ばれた law、選ばれた witness、選ばれた coverage、選ばれた exactness の中で、何が本当に従うのかを示すことである。

**Goal:** AAT / SFT を比喩ではなく、定義、構成、定理に支えられた本物の数学として立たせる。

**What changes:** もっともらしい説明と証明された主張が分離される。研究上の claim、tooling claim、empirical hypothesis、non-conclusion が混線せずに扱われる。

---

## Tooling: theory in practice

tooling は、理論を実践に適用するための層である。
tool は、選ばれた evidence language の中で、語れることを扱える artifact にする。

ArchSig は、architecture evidence を signature、obstruction、assumption、boundary を持つ diagnostic artifact に変換する。
FieldSig は、その artifact を software evolution の field、trajectory、forecast、governance の側へ渡す。

tooling の役割は、理論を現実に接続することである。
コード、PR、policy、review、CI、運用記録、AI proposal を、AAT / SFT の語彙で扱える evidence へ変換する。

```text
artifact
  -> evidence
  -> signature
  -> diagnosis
  -> forecast
  -> governance
```

**Goal:** AAT / SFT を、実際の開発 artifact に適用できる道具にする。

**What changes:** review や CI は、変更がどの invariant、obstruction、signature、future trajectory に作用しているかを読む場へ変わる。tool は、責任ある判断のための language surface になる。

---

## Publication: opening the language

このプロジェクトの公開面は、語彙を開くためにある。

AAT / SFT は、内部文書から外へ開かれる理論である。
アーキテクチャを考える人、形式手法に関心を持つ人、開発プロセスを設計する人、review や CI を作る人、ソフトウェア進化を考える人へ届く必要がある。

website、記事、preprint、manual、example は、そのための surface である。

公開文書は、研究の語彙を、読める思想として提示する。
数学本文は精密さを担う。
website は導線を担う。
manual は実践を担う。
outreach は外部との接続を担う。

```text
Architecture as algebraic geometry.
Evolution as computable field.
Proof as checkable grammar.
Tooling as responsible speech.
Publication as opening the language.
```

**Goal:** AAT / SFT / tooling の語彙を、外部の読者が使える思想と道具として開く。

**What changes:** アーキテクチャ研究、形式手法、開発者 tooling、AI-assisted development の間に共通の言語が生まれる。研究は内部台帳から外へ出て、読まれ、批判され、応用される対象になる。

---

## Why this matters in the age of AI

この研究は、AI 時代のソフトウェア開発に深く関係する。

AI は、コードを書く速度を上げる。
変更案を増やす。
局所的な pattern を素早く再利用し、PR、修正案、移行案、回避策、設計案を高速に生成する。

その時代に必要になるのは、生成された変更をどの文法で受け止めるかである。

AI が proposal を出す。
AAT は、それがどの architecture geometry に作用するのかを読む。
SFT は、どの future trajectory が開かれるのかを扱う。
Lean は、語れる theorem boundary を固定する。
tooling は、proposal を evidence language の中で診断する。
governance は、それを受け入れ、拒み、修正し、減衰し、field に戻す。

AI 時代において、このプロジェクトは、AI によって増幅されるソフトウェア進化を、計算可能で、診断可能で、責任ある対象として扱う。

**Goal:** AI が高速に変更を生成する時代に、その変更を architecture、evolution、proof、tooling、governance の語彙の中へ置く。

**What changes:** AI-generated code は、速さだけで評価されるものから、law、obstruction、trajectory、boundary の中で読まれる proposal へ変わる。AI-assisted development は、生成の技術から、進化を統治する技術へ広がる。

---

## The final aim

このリポジトリは、ソフトウェアアーキテクチャについての言葉を作る。

その言葉を数学にする。
数学を形式化する。
形式化を artifact へ接続する。
artifact を進化と governance へ接続する。
その全体を、読める思想として外へ開く。

最終的に目指すのは、変更が速く作られる時代に、変更について深く、正確に、責任をもって語ることである。

```text
Architecture becomes speakable
when its atoms, laws, obstructions, and covers are explicit.

Evolution becomes computable
when its fields, trajectories, horizons, and feedback are explicit.

Responsibility becomes possible
when the grammar of our claims is explicit.
```

**Making software evolution computable.**
