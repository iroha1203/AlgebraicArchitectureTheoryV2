# 主張と証拠の対応

このファイルは執筆・レビュー時の照合記録である。原稿本文の数学は、原稿内の定義と証明で記述する。
共通基準は[論文作成ガイドライン](../../../docs/paper/guideline.md)に従う。

## 第1章の下書き

- 対象: [第1章 相対的アーキテクチャの構成](ja/04-relative-architecture.md)。
- 原稿 SHA-256: `0b257946663bbac32e118396f946873fba00e3f0083571eb60a5b523e2e868c2`。
- リポジトリ内の一次資料の固定版: `babd4d0ba63384991b488d3779f19d0b239365e2`。
- 確認者・日付: Codex（GPT-6）、2026-09-20。
- 方法: 定義・仮定・構成・証明の読解と照合。本文の証明を読み直し、射の構成に必要な全成分、量化、保存条件を確認した。
- Lean source は既存の形式化との対応に用いた。この作業で Lean の再検証は行っていない。

| ID | 原稿の節・主張 | 種類 | 対象・仮定 | 一次資料の箇所 | 確認結果 |
| --- | --- | --- | --- | --- | --- |
| C1-01 | §1.1、命題1.4 | 数学 | 非空の Atom 語彙、五座標の外延性、抽出 doctrine と source | [数学本文 I §§1–3][math-i]、[Axioms][axioms] の `AtomAxiomSystem`、`ExtractionDoctrine`、抽出族の構成と一意性 | 正規化を含む抽出述語を明記し、存在一意性を外延性から証明 |
| C1-02 | §1.2、定理1.18 | 数学 | 有限抽出族、族を保つ composition、configuration を保つ object reading、operation reading | [数学本文 I §§4–6・10][math-i]、[ObjectAlgebra][object-algebra]、[AATCore][core] の `generate`、`algebra_object_nonempty_iff_reachable` と生成成分の定理 | operation を作用写像と同一視せず、最小閉包と有限到達可能性を両向きに証明 |
| C1-03 | §§1.3–1.4、命題1.16 | 数学 | 対象依存の残差、必須添字、有限符号付き query、健全性と必須添字上の完全性 | [数学本文 I §§7–9][math-i]、[AATCore][core]、[ReadingFunctoriality/Core][reading-core]、[LawfulnessZero][lawfulness] | circuit の不在と方程式の成立に必要な条件を明記。量の零性との同値は零を反映する集約を条件として記載 |
| C1-04 | §§1.5–1.6、命題1.21・1.23、例1.24 | 数学 | 小さい前順序文脈圏、選択した pullback、被覆要件 | [数学本文 II §§2–13][math-ii]、[Coverage][coverage]、[Topology][topology]、[Stacks Tag 00YW](https://stacks.math.columbia.edu/tag/00YW)、[Tag 00ZG](https://stacks.math.columbia.edu/tag/00ZG) | 生成位相と情報の可視性を区別。層化の構成・普遍性と、貼り合わせを追加する二点の例を記述 |
| C1-05 | 定義1.25、補題1.26、章末 | 数学 | 係数環、座標・構造関係、多項式制限によるイデアル保存。方程式と幾何の対応には実現の条件が必要 | [StructureSheaf][structure-sheaf]、[GeometryTransport/Basic][geometry-basic] の raw system の再添字づけ・係数変更、[WitnessIdeal][witness-ideal]、[Correspondence][law-correspondence] | 商前層と係数変更を記述。第2章への接続では、記号的座標から作るイデアルと対象ごとの残差を区別し、両者を結ぶ実現の条件を明記 |
| C1-06 | §1.7、命題1.29、定理1.31 | 数学 | Atom の全単射、一般の source 写像、exact core 射、被覆・overlap・係数・raw system・文脈データの比較 | [AtomFoundation/Doctrine][doctrine]、[Core の exact 射][reading-core]、[AtomFoundation/Categories][atom-categories]、[GeometryTransport/Categories][geometry-categories]、[ThreeStageProjection][three-stage] | 構成成分を定義してから射影の関手性を証明。文脈の前順序性と raw 表示データの等式を明記 |
| C1-07 | §1.8、命題1.33・1.34、例1.35 | 数学 | 全域 lens の三法則、基準 view と有限基準 fiber | [LensSemantics][lens-semantics] の `canonicalNormalFormEquiv`、`homEquivFiberMap`、[相対的な操作保存][lens-relative]、[FGMPS04 §3.1](https://www.cis.upenn.edu/~bcpierce/papers/newlenses-full.pdf) | 積表示と射の制限・延長を証明。可視変更と補完の対応、get のみなら4個・put も保てば2個となる例を検算 |
| C1-08 | §1.9、命題1.37・1.38 | 数学 | 有限グラフ・有限宣言関係・有限状態、観測関手、一般の意味保存射 | [ProtocolSchema][protocol-schema]、[ProtocolSemantics][protocol-semantics]、[ProtocolFinitePresentation][protocol-presentation]、[ProtocolReconstruction][protocol-reconstruction]、[Spivak12 §§3.2・3.4–3.5](https://arxiv.org/pdf/1009.1166v3) | 有限表から全経路への延長を合同関係と帰納法で証明。adapter の保存を頂点成分の平方で説明 |
| C1-09 | 構成1.39・1.40、命題1.41 | 数学 | 型の役割と操作名の有限語彙、状態値を持つ source、法則をまだ課していない操作データ | [CSAATArchitectureObjects][cs-objects]、[CSAATLawSystems][cs-laws] の role 対象・名前付き操作・抽出・Lawfulness 同値 | source と Atom の役割を区別し、非単射の状態写像を保持。Law は固定 carrier の操作データを評価。定数環前層を一文脈へ制限した場合を本文に構成し、三法則・経路等式との同値を証明 |
| C1-10 | 定義1.42、命題1.43 | 数学 | 明示した型付き役割写像と、get/put または edge/observe の可換性 | [CSAATTypedOperationTranslation][cs-typed]、[CSAATForwardMorphisms][cs-forward]、[ProtocolReconstruction][protocol-reconstruction] | 型付き射と意味保存射の Hom 全単射を両逆・恒等・合成まで証明。§1.7 の exact core 射とは射の定義を区別 |

標準的な先行研究の引用内容と書誌の確認は [references.csv](references.csv) に記録する。
主張・証明を修正した場合は、影響する行と原稿 hash を更新する。

## 読みやすさの調整

2026-09-20、人間の依頼に基づき、具体例から始まる導入、構成の見通し、用語の初出説明、
定義間の接続を改稿した。被覆・reading の射の条件を項目に分け、意味論との対応表を整理した。
lens の三法則、基準 fiber、射の延長、プロトコルの観測の意味を文章で補った。

初稿との差分を照合し、独立行57式の内容・順序、43件の定義等の番号、28件の式番号、
外部文献の引用4か所を保持した。本文内数式の分割は、役割・集合・操作を分けた表の10式であり、
対応する集合と写像を維持した。定義の条件、定理の仮定・結論、証明の論理は変更していない。
この確認は執筆者による通読・差分確認であり、独立レビューの結果は次節に記録する。

同日、追加の依頼に基づき、冒頭を概要として整理し、lens・プロトコルへ接続する理由と
章末のまとめを加えた。接続の目的は、独立に定めた意味論の操作・法則・意味保存射を
回復し、共通の定理の帰結を元の問題へ戻すための基礎を与えることとして説明した。
命題1.16の健全性・完全性、定理1.18の基点を含む最小閉包、命題1.41のLaw成立の同値、
命題1.43の型付き射との対応に、概要・まとめの主張を照合した。
本文の定義・命題・証明、全634式、番号と外部引用は、追加前の原稿から保持した。

## 独立レビューと表示確認

概要・接続理由・まとめの追加後、ローカルで全634式（うち独立行57式）を KaTeX 0.18.7 で構文検査し、
エラー・警告がないことを確認した。43件の定義・構成・結果・例、28件の式番号、
章内参照、相対リンク、文献3件の記録と hash、空白・不可視文字・公開情報の検査も通過した。

GitHub のファイルプレビューでは、定義1.30の番号付きリスト内の独立行3式が
コードとして表示されることを確認した。項目番号を保持した段落形式へ変更し、
数式ブロックを字下げのない位置へ移した。全634式の内容・順序と周辺の条件を保持した。
さらに、式番号を持つ数式で縦方向への配置崩れを確認したため、式番号28件の記法を
`\tag` から数式末尾の `\qquad\text{(...)}` へ変更した。式の数学的内容と番号を保持した。

2026-09-20、第1章は人間による原稿確認を経て、PR 作成の承認を受けた。
commit `3d867ccea586840681812e4e8beae1cf5542d1f9` に対し、
[Claude のレビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4831#issuecomment-5749092682)は
approve とし、記法と説明の任意提案3件を挙げた。
[ChatGPT のレビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4831#pullrequestreview-5260310485)も
主要証明を肯定し、記号的座標と残差の区別1件、読みやすさの改善3件を提案した。
両者の確認範囲は各レビューに記載されている。GitHub 上の数式表示は、
同 commit に対する Codex と Claude の確認結果を PR に記録している。

同日、人間の採用指示に基づき、記号的座標から生成するイデアルと対象ごとの残差を、
実現の条件の下で結ぶ説明へ修正した。`WitnessIdeal` の生成座標、`Correspondence` の実現条件、
第2章の数学棚卸し2-A〜2-Dに照合した。reading の射と意味保存射の区別、
core の射の条件と名前付き操作の構成の目的を先に示し、重複する説明を整理した。
二点の例は貼り合わない部分を層化の前へ移し、層化の結果と普遍性を例1.24に残した。
プロトコルの経路対集合を `Π` に統一し、molecule・adequacy・基準fiberの用途と、
overlap の普遍性の説明を整えた。定義・結果43件と式番号28件を保持した。
記号の変更を除き独立行57式の内容・順序は不変であり、本文内の追加数式は前層を指す `F` の2件である。
修正版の全636式（本文内579・独立行57）を KaTeX 0.18.7 で検査し、エラー・警告がないことを確認した。
引用内容・書誌は変更せず、原稿 hash を更新した。GitHub のプレビュー・描画済み差分の表示確認と
CI の対象 commit・結果は PR に記録する。

[math-i]: ../../../docs/aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md
[math-ii]: ../../../docs/aat/algebraic_geometric_theory/part_2_architecture_geometry_sites_sheaves.md
[axioms]: ../../../Formal/AG/Atom/Axioms.lean
[core]: ../../../Formal/AG/Atom/AATCore.lean
[object-algebra]: ../../../Formal/AG/Atom/ObjectAlgebra.lean
[lawfulness]: ../../../Formal/AG/Atom/LawfulnessZero.lean
[coverage]: ../../../Formal/AG/Site/Coverage.lean
[topology]: ../../../Formal/AG/Site/Topology.lean
[reading-core]: ../../../Formal/AG/ReadingFunctoriality/Core.lean
[structure-sheaf]: ../../../Formal/AG/LawAlgebra/StructureSheaf.lean
[witness-ideal]: ../../../Formal/AG/LawAlgebra/WitnessIdeal.lean
[law-correspondence]: ../../../Formal/AG/LawAlgebra/Correspondence.lean
[doctrine]: ../../../research/lean/ResearchLean/AG/AtomFoundation/Doctrine.lean
[atom-categories]: ../../../research/lean/ResearchLean/AG/AtomFoundation/Categories.lean
[geometry-basic]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Basic.lean
[geometry-categories]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Categories.lean
[three-stage]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/ThreeStageProjection.lean
[lens-semantics]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/LensSemantics.lean
[lens-relative]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATLensRelativeOperationSquares.lean
[protocol-schema]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSchema.lean
[protocol-semantics]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSemantics.lean
[protocol-presentation]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolFinitePresentation.lean
[protocol-reconstruction]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolReconstruction.lean
[cs-objects]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATArchitectureObjects.lean
[cs-laws]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATLawSystems.lean
[cs-typed]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATTypedOperationTranslation.lean
[cs-forward]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATForwardMorphisms.lean
