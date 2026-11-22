# 代数幾何的アーキテクチャ論

Algebraic Architecture Theory（AAT）は、Atom と Law によって意味の対象と射を定め、その実現・変更・修復の全体を調べる純粋数学の理論である。まず共通の語彙によって何を区別するかを指定し、実際の状態・操作・関係・量をもつモデルを構成する。そのうえで、モデルの族が定める幾何、局所データからの組み立て、修復や変形の障害、そして判断と再構成に必要な情報を体系的に扱う。

本書の中心となる問いは次の二つである。

> Law・操作・観測を指定すると、どのような実現と変更が可能になるか。
> その全体の幾何から、修復の存在と自由度、および判断と構成に必要な情報をどのように導けるか。

## 目次と入口

- [序論](introduction.md)：本書が目指す三つの到達点と、そこへ至る論証の順序。
- [共通記号](notation.md)：対象、写像、係数、文脈に用いる記号の一覧と使い分け。
- [第I部 Lawと意味の基礎](#第i部-lawと意味の基礎)：第1–3章。
- [第II部 実現の族とLawの幾何](#第ii部-実現の族とlawの幾何)：第4–6章。
- [第III部 意味を保つ変更の全体](#第iii部-意味を保つ変更の全体)：第7–9章。
- [第IV部 局所変更・修復・障害](#第iv部-局所変更修復障害)：第10–13章。
- [第V部 輸送・比較・診断](#第v部-輸送比較診断)：第14–16章。
- [第VI部 観測・必要情報・再構成](#第vi部-観測必要情報再構成)：第17–19章。
- [付録A 正の論理の導出と健全性](appendix_a_positive_logic.md)：理論解釈に用いる正の論理の導出規則と健全性。
- [付録B 係数・アフィン構成・descent](appendix_b_coefficients_and_descent.md)：第II部で用いる係数変更、アフィン構成、および局所からの組み立て。
- [付録C 関係・解消・逆極限・整数障害](appendix_c_homological_constructions.md)：余接複体、Tor と交差、整数修復の有限算術判定、調和レギュレータ。
- [付録D 有限根スキーム・診断次元・降下](appendix_d_finite_roots_and_stalks.md)：診断次元の原始実現、幾何点の茎、スペクトル根診断の降下と選択。
- [付録E 変更経路と費用の問題](appendix_e_change_paths_and_costs.md)：許容経路の費用と最適経路の再構成。

## 全体の構成

全6部19章の論証は、原始的な宣言から意味を保つ変更の全体を構成し、さらにその修復・観測・再構成へと進む。全体の見通しとなる三つの主結果と四つの接続は、[序論](introduction.md)からたどることができる。

- **第I部（第1–3章、付録A）**：証明はこの部と付録Aの中で閉じる。Atom 語彙、署名、Law、モデルと射、および宣言の文脈による制限と局所モデルを定める。
- **第II部（第4–6章、付録B）**：第I部の結果を用い、係数環上の実現の表示、量と Law が定める相対幾何、モデルの族のモジュライ、および係数の descent を構成する。
- **第III部（第7–9章）**：意味を保つ変更の全体と条件付きの変更族を構成し、さらに商、対称性、代表の選択、持ち上げの分類を行う。
- **第IV部（第10–13章、付録C）**：文脈と係数の 2 方向の descent、固定部分と許可範囲に相対的な修復の全体（アリアドネ）、変形と交差の障害、および有限断片からの大域的な復元を構成する。
- **第V部（第14–16章、付録D）**：reading と係数に沿う輸送、生成される比較と正規化、および診断の族と指定された障害の比較を構成する。
- **第VI部（第17–19章、付録E）**：状態からの観測、判定と数値補正に必要な情報、局所読み取りからの条件付き変更の全体および修復の全体の回復、ならびに有限決定と実行可能な復元算法を構成する。

### 第I部 Lawと意味の基礎

1. [Atom・Law・理論の指定](part_1/chapter_1_atoms_laws_theories.md)
2. [意味の対象と射](part_1/chapter_2_models_and_morphisms.md)
3. [文脈と局所モデル](part_1/chapter_3_contexts_and_local_models.md)

### 第II部 実現の族とLawの幾何

4. [係数的実現と意味の回復](part_2/chapter_4_coefficient_realizations.md)
5. [量とLawから生じる相対幾何](part_2/chapter_5_quantities_and_law_geometry.md)
6. [構造の族と実現のモジュライ](part_2/chapter_6_families_and_moduli.md)

### 第III部 意味を保つ変更の全体

7. [意味保存変更と合成の幾何](part_3/chapter_7_semantic_changes_and_composition.md)
8. [条件を満たす変更と図式補完](part_3/chapter_8_constrained_changes_and_completions.md)
9. [商・対称性・持ち上げの分類](part_3/chapter_9_quotients_symmetry_and_lifts.md)

### 第IV部 局所変更・修復・障害

10. [実現と変更のdescent](part_4/chapter_10_descent_of_realizations_and_changes.md)
11. [固定部分と変更範囲に相対的な修復の全体――アリアドネ](part_4/chapter_11_ariadne_relative_repairs.md)
12. [変形・特異性・修復の障害](part_4/chapter_12_deformations_and_obstructions.md)
13. [有限部分から大域へ](part_4/chapter_13_fragments_and_globalization.md)

### 第V部 輸送・比較・診断

14. [reading と係数に沿う輸送](part_5/chapter_14_transport_along_readings_and_coefficients.md)
15. [生成比較と正規化](part_5/chapter_15_generated_comparisons_and_normalization.md)
16. [診断の族と障害の比較](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md)

### 第VI部 観測・必要情報・再構成

17. [観測の十分性と選択](part_6/chapter_17_observation_sufficiency_and_selection.md)
18. [修復と観測](part_6/chapter_18_repair_and_observation.md)
19. [局所再構成と有限決定](part_6/chapter_19_local_reconstruction_and_finite_determination.md)

## 問いから定理へ

| 問い | 主な構成と証明 |
| --- | --- |
| 指定した補正や修復全体を比較先から戻せるか | [指定補正・全解・残差](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#167-指定した補正をそのまま持ち上げる)、[原始比較と修復のファイバー](part_4/chapter_11_ariadne_relative_repairs.md#1110-原始操作の比較と指定修復のファイバー) |
| 診断は表示変更や局所貼り合わせでどう変わるか | [支持付き細分と実セル交差](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#168-支持と整合する表示変更)、[安全性と有限観測幅](part_6/chapter_17_observation_sufficiency_and_selection.md#176-全-law-族に対する安全性と有限幅観測) |
| 修復に必要な情報は構造と範囲によってどう変わるか | [構成可能な層別化](part_6/chapter_18_repair_and_observation.md#186-構造パラメータと必要情報の層別化)、[凍結範囲の保存則](part_6/chapter_18_repair_and_observation.md#189-凍結範囲と必要情報の三項保存則) |
| 未定義状態・係数変更・Law の変更は何を変えるか | [単項部分操作の商](part_3/chapter_9_quotients_symmetry_and_lifts.md)、[線形定義域と Tor](part_5/chapter_14_transport_along_readings_and_coefficients.md)、[Law 生成余法係数](part_4/chapter_12_deformations_and_obstructions.md#127-lawが生成する余法係数と指定切断の一次持ち上げ) |
| 有限の公開語から実現とモジュライを構成できるか | [有限ハンケル表](part_6/chapter_19_local_reconstruction_and_finite_determination.md#196-有限ハンケル表からの最小実現)、[内在的生成元と Grassmann 表示](part_2/chapter_6_families_and_moduli.md#66-入力語による内在的生成元と最小実現) |
| 整数障害や実現族上の診断をどう読むか | [整数障害と指定比較](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#1612-整数障害有限素数冪指定比較)、[診断次元の実現](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#1611-診断次元を実現する幾何)、[根診断の降下と選択](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#1613-固有値の根診断と商上の選択) |

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
