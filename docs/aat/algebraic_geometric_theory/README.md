# 代数幾何的アーキテクチャ論

Algebraic Architecture Theory（AAT）は、AtomとLawによって意味の対象と射を定め、
その実現・変更・修復の全体を調べる数学である。共通の語彙で何を区別するかを指定し、
実際の状態・操作・関係・量を持つモデルを構成する。その後に、モデルの族の幾何、
局所からの組立て、障害、観測に必要な情報を扱う。

中心となる問いは次である。

> Law・操作・観測を指定すると、どのような実現と変更が可能になるか。
> その全体の幾何から、修復の存在と自由度、判断と構成に必要な情報をどう導けるか。

- [序論](introduction.md)：三つの到達点と、そこへ至る論証の順序。
- [共通記号](notation.md)：対象、写像、係数、文脈の記号。
- [第I部 Lawと意味の基礎](#第i部-lawと意味の基礎)：第1–3章。
- [第II部 実現の族とLawの幾何](part_2/README.md)：第4–6章。
- [付録A 正の論理の導出と健全性](appendix_a_positive_logic.md)：理論解釈に用いる導出規則。
- [付録B 係数・affine構成・descent](appendix_b_coefficients_and_descent.md)：第II部で使う係数変更と局所からの組立て。

## 全体の構成

以下の章名は全体の構成を示す。後続の結果の予告は、
[序論](introduction.md)で各結果の問いと入力を述べるために用いる。
第I部の証明は第1–3章と付録Aの中で閉じる。
第II部はこの結果を使い、第4–6章と付録Bで実現の表示と係数descentを構成する。

### 第I部 Lawと意味の基礎

1. [Atom・Law・理論の指定](part_1/chapter_1_atoms_laws_theories.md)
2. [意味の対象と射](part_1/chapter_2_models_and_morphisms.md)
3. [文脈と局所モデル](part_1/chapter_3_contexts_and_local_models.md)

### 第II部 実現の族とLawの幾何

4. [係数的実現と意味の回復](part_2/chapter_4_coefficient_realizations.md)
5. [量とLawから生じる相対幾何](part_2/chapter_5_quantities_and_law_geometry.md)
6. [構造の族と実現のモジュライ](part_2/chapter_6_families_and_moduli.md)

### 第III部 意味を保つ変更の全体

7. 意味保存変更と合成の幾何
8. 条件を満たす変更と図式補完
9. 商・対称性・持ち上げの分類

### 第IV部 局所変更・修復・障害

10. 実現と変更のdescent
11. 固定部分と変更範囲に相対的な全修復――アリアドネ
12. 変形・特異性・修復の障害
13. 有限部分から大域へ

### 第V部 輸送・比較・診断

14. readingと係数に沿う輸送
15. 生成比較と正規化
16. 診断の族と障害の比較

### 第VI部 観測・必要情報・再構成

17. 観測の十分性と選択
18. 修復と観測
19. 局所再構成と有限決定

## 数学本文の自立性（hard rule）

このディレクトリの数学本文は Tier 1 の正典であり、定義、命題、定理、証明を
数学本文自身の公理、構成、仮定だけで閉じる。次を数学本文へ持ち込むことを禁止する。

1. Lean status、宣言名、source path、import、build、CI、axiom audit、形式化の進捗。
2. この正典シリーズ外にある repository 内文書への参照。research、GOAL、台帳、PRD、
   tooling、website、outreach、archive その他の文書を、定義・仮定・証明・完了根拠に用いない。
3. GitHub Issue、Pull Request、review comment、番号、URL、acceptance、merge state への参照。
4. web page、外部 repository、release artifact、外部 status、その他の外部資料への参照。

各部・各章・付録の間の参照は、同じ数学正典の内部参照として扱う。
歴史的説明、実装状況、形式化状況、研究運用、公開計画、外部資料との比較が必要な場合は、
数学本文の外で記述する。それらは数学 claim の仮定、証拠、完成判定にならない。
