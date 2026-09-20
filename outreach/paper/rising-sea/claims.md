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

## 第2章の下書き

- 対象: [第2章 Lawの幾何と局所整合性](ja/05-law-geometry.md)。
- 原稿 SHA-256: `edeb3688627085c357282c034c6f23968dd77aad39d15b1ea282cba528f0910e`。
- リポジトリ内の一次資料の固定版: `313086df1e2071236b64ffd454615e927e428e26`（第1章の PR #4831 のマージ版）。
- 確認者・日付: Codex（GPT-6）、2026-09-20。
- 方法: 数学棚卸し2-A〜2-Iに従い、一次資料の定義・仮定・構成・証明と照合。原稿の全証明を読み直し、有限例は別途計算した。
- Lean source は既存の形式化との対応に用いた。この作業で Lean の変更・再検証は行っていない。

| ID | 原稿の節・主張 | 種類 | 対象・仮定 | 一次資料の箇所 | 確認結果 |
| --- | --- | --- | --- | --- | --- |
| C2-01 | §2.1、定義2.1・命題2.2 | 数学 | 構造関係の商、observable ring との表示同型、制限との整合 | [数学本文 III §4][c2-math-iii]、第1章の定義1.25 | 配置の関手を定義し、多項式環と商の普遍性から自然な全単射を証明 |
| C2-02 | 定義2.3・命題2.4 | 数学 | 記号的生成元の制限則、必須添字、層化したイデアルの像 | [数学本文 III §§5–6][c2-math-iii]、[WitnessIdeal][witness-ideal] | 生成元の有限和から制限の包含と層化後のイデアル性を確認。必須添字の和を明示 |
| C2-03 | §§2.1–2.2、構成2.6・定理2.9・系2.11 | 数学 | 評価関手のアフィン表現、残差の正則性、開部分の比較・合成条件、被覆と重なりを保つchart対応 | [数学本文 III §§5.2–5.2C・11.1][c2-math-iii]、[Correspondence][law-correspondence]、[Stacks 01HR](https://stacks.math.columbia.edu/tag/01HR)・[01JA](https://stacks.math.columbia.edu/tag/01JA)・[01HP](https://stacks.math.columbia.edu/tag/01HP) | 方程式と残差の評価を等しくする商を作り、生成元の評価と局所化を証明。siteのイデアルとschemeのイデアルの比較を指定。加群の引き戻しの零性ではなく、構造層内で生成するイデアルの零性を用いる。対象の残差へ戻る同型は系2.11の追加条件 |
| C2-04 | §2.3、構成2.12・命題2.15 | 数学 | 商係数、対象依存の残差、circuitの健全性・完全性、自然な係数実現と非零性 | [数学本文 IV §2.1A][c2-math-iv]、[数学本文 X §5.1][c2-math-x] | 記号的生成元と残差類を区別。残差のイデアル所属を商の零性として記述。集約の相殺条件を分離し、単独circuitの検出命題を証明 |
| C2-05 | §2.4、補題2.17・例2.19 | 数学 | 固定した有限単射射被覆、アーベル群値の係数、空交差の零係数 | [数学本文 IV §§3–4][c2-math-iv]、[数学本文 X §2][c2-math-x] | 微分の合成、固定被覆の商群、三chartのperiodによる同型を本文で計算 |
| C2-06 | §2.5、命題2.21・定理2.22・系2.23 | 数学 | 交差図式上の自由かつ推移的な作用、局所atlas、空交差の高々一元性、実際の状態の層条件 | [数学本文 IV §§5・11][c2-math-iv]、[数学本文 X §8][c2-math-x]、[Stacks 03AG](https://stacks.math.columbia.edu/tag/03AG) | 差のcocycle、atlas変更によるcoboundary、補正後の貼り合わせを証明。自己交差・逆向き・空交差の一致を確認。Lawful状態が層になる理由と、有限検査からLawfulnessへ進むための条件を明記 |
| C2-07 | §2.6、命題2.24–2.28 | 数学 | 有限次元・有限長、連結な交差、定数係数、forestの制限全射、単体のchainとcochain | [数学本文 IV §§12–13][c2-math-iv] | 容量下界、Euler交代和、nerve比較、forest消滅、Stokesを証明。群の次元と指定類の非零性を区別 |
| C2-08 | 命題2.29 | 数学 | 有限単体複体の二部分複体による分解、共通の定数係数 | [数学本文 IV §§8–9・13][c2-math-iv] | 原稿では有限cochainの場合を構成。制限の差の全射、持ち上げ独立性、零性の同値、境界とのペアリングを直接証明 |
| C2-09 | §2.7、命題2.32・例2.33–2.34 | 数学 | 宣言した意味変形族に対する抽出の不変性、構造座標、条件E、構造側の一次コホモロジー消滅 | [DependencyProfile][c2-two-phase-dependency]、[CoefficientComplex][c2-two-phase-complex]、[CohomologyComparison][c2-two-phase-h1]、[ForestSupport][c2-two-phase-forest]、[FiniteWitnesses][c2-two-phase-finite] | AtomKindだけの分類を用いず、商の微分と単射性を証明。Eの不成立例と、Eだけでは単射にならない例を計算 |
| C2-10 | §2.8、定義2.35・補題2.36 | 数学 | 有限source・Law族、Law値を保つ原始関係、整数係数 | [PresentationGroup][c2-presentation] の `presentationGroupEquivBlocks` | 生成子関係の商と成分ごとの自由アーベル群の両逆を証明。四生成子・二関係の例を計算 |
| C2-11 | 構成2.37–2.39 | 数学 | 選定した点・生成子のAtom族、開集合に対応する文脈、三chart・四chart、局所定数係数 | [PointGeneratorAtomInput][c2-atoms]、[FiniteCoverGeometry][c2-cover-geometry]、[CombinedAtomContextSupport][c2-support]、[CombinedAtomContextContinuity][c2-continuity]、[CombinedAtomActualNerve][c2-nerve] | 原稿では全生成子を読む開集合文脈の部分圏を明示して構成。より大きな文脈siteとの同値は主張しない。八点の位相から被覆・連結性・三重交差の空性を示し、実際の切断と制限でČech座標を得る |
| C2-12 | 命題2.40–2.41・例2.42 | 数学 | 同じ整数係数と実被覆、任意のchart状態と辺遷移 | [SpecifiedAffineObstruction][c2-affine]、[ExistingObstructionBridge][c2-existing]、[CombinedAtomSpecifiedObstruction][c2-specified] | 原始関係の方程式が評価・制限・平行移動で成立することを証明。実際の比較から指定cocycleを作り、torsorの貼り合わせ障害との一致と局所状態変更による類の不変性を記述 |
| C2-13 | §2.9、定義2.43–構成2.46 | 数学 | semantic atom、supported generator、制限で保たれる修復関係、修復語の作用、別に選ぶ方程式側のlift | [数学本文 X §§3–6][c2-math-x]、[SAGA §§3.4–4](https://arxiv.org/html/2608.21458v1) | 二つの係数と二つの残差をそれぞれ構成。作用からtorsorを導く条件と、修復生成元を対象依存の残差類へ送る写像を明記 |
| C2-14 | §2.10、補題2.48・定理2.49 | 数学 | 生成元に関して同変な局所状態写像、関係と生成元の完全性、空交差の正規化 | [数学本文 X §§6–7][c2-math-x]、[KappaComparison][c2-saga-kappa]、[SAGA 定理5.1(i)–(ii)](https://arxiv.org/html/2608.21458v1#S5) | 関係の健全性を状態写像と自由作用から導出。係数同型、次数0〜2の複体同型、一次コホモロジー同型を証明。独立に選んだatlasの差を明示的なcoboundaryとして比較 |
| C2-15 | 系2.50・例2.51 | 数学 | 実際の修復状態の層条件、固定被覆、独立な偶奇表示と剰余表示 | [数学本文 X §§8・10.2][c2-math-x]、[SAGA 定理5.1(iii)・5.2、例5.3](https://arxiv.org/html/2608.21458v1#S5) | 零類から補正と層の貼り合わせを経て実際の修復へ進むことを証明。四chartの非零periodと遷移変更後の零類を検算 |

### 有限例と読みやすさの確認

第1章と同じく、概要、接続の目的、各節の問い、定義・証明・例、章末のまとめを置いた。
冒頭のサービス間の基準の例を三chartのperiodへつなぎ、八点の空間から二つの実被覆を構成した。
第3章に渡す係数・被覆・局所データ・指定障害類を章内で揃えた。
原稿本文にはAAT内部の章番号、GOAL、Lean識別子、リポジトリ内パスへの案内を置いていない。

Pythonによる有限計算では、八点の被覆、全chartと非空交差の連結性、三重交差の空性、
有理数上の微分の階数（四chartで3、三chartで2）、四生成子二関係の商の階数2を確認した。
二相の例では全体の一次コホモロジーの次元2、構造側の次元1を確認した。
49個の整数chart状態について原始関係の評価が零であることを検算した。
SAGAの偶奇例では、全16通りの局所補正でperiodが1に保たれて貼り合わないことと、
遷移を零に変更すると零状態が貼り合うことを確認した。
これらは有限例の計算であり、一般の定理は原稿内の証明により述べている。

### 数式・引用と残る確認

全504式（本文内461・独立行43）をKaTeX 0.18.7で構文検査し、エラー・警告なし。
同じ数式から作ったローカルのMathMLプレビューで、数式の認識、本文幅676pxでの独立行数式のはみ出し、
主要な定理の表示を確認した。数式の区切り、定義等51件・式番号39件、章内参照も確認した。
ローカルの確認はGitHub上の描画結果を保証するものではない。

SAGAの公開第1版とStacksの原典で引用内容を照合し、[文献](ja/14-references.md)と
[references.csv](references.csv)に書誌・確認箇所・原稿一式のhashを記録した。
2026-09-20、人間による原稿確認を経て、PR作成の承認を受けた。
GitHubファイルプレビュー・描画済み差分の表示確認とCIの対象commit・結果はPRに記録する。
Claudeによる独立レビューはPR上で受ける。

同日、PR #4832の固定commit `64036ad552c5235c360f012610ff325fc0ea348d` のGitHubプレビューで、
`\operatorname` が拒否され、16式が描画エラーになることを確認した。
作用素名を `\mathrm` と明示的な空白で表し、全504式の数学的内容・順序と周辺の本文を保持した。
原稿hashを更新し、修正後のcommitでプレビュー・描画済み差分とCIを確認する。

[c2-math-iii]: ../../../docs/aat/algebraic_geometric_theory/part_3_law_algebra_obstruction_ideal_lawful_locus.md
[c2-math-iv]: ../../../docs/aat/algebraic_geometric_theory/part_4_obstruction_cohomology.md
[c2-math-x]: ../../../docs/aat/algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md
[c2-two-phase-dependency]: ../../../research/lean/ResearchLean/AG/TwoPhase/DependencyProfile.lean
[c2-two-phase-complex]: ../../../research/lean/ResearchLean/AG/TwoPhase/CoefficientComplex.lean
[c2-two-phase-h1]: ../../../research/lean/ResearchLean/AG/TwoPhase/CohomologyComparison.lean
[c2-two-phase-forest]: ../../../research/lean/ResearchLean/AG/TwoPhase/ForestSupport.lean
[c2-two-phase-finite]: ../../../research/lean/ResearchLean/AG/TwoPhase/FiniteWitnesses.lean
[c2-presentation]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/PresentationGroup.lean
[c2-atoms]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/PointGeneratorAtomInput.lean
[c2-cover-geometry]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/FiniteCoverGeometry.lean
[c2-support]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomContextSupport.lean
[c2-continuity]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomContextContinuity.lean
[c2-nerve]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomActualNerve.lean
[c2-affine]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedAffineObstruction.lean
[c2-existing]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/ExistingObstructionBridge.lean
[c2-specified]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomSpecifiedObstruction.lean
[c2-saga-kappa]: ../../../Formal/AG/SemanticRepair/Saga/KappaComparison.lean
