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
- 原稿 SHA-256: `d1cfbc4112e76cc51c8d1968d0b9b5813d0265b0fd4b9acb566055859b14ca96`。
- リポジトリ内の一次資料の固定版: `313086df1e2071236b64ffd454615e927e428e26`（第1章の PR #4831 のマージ版）。
- 確認者・日付: Codex（GPT-6）、2026-09-20。
- 方法: 数学棚卸し2-A〜2-Iに従い、一次資料の定義・仮定・構成・証明と照合。原稿の全証明を読み直し、有限例は別途計算した。
- Lean source は既存の形式化との対応に用いた。この作業で Lean の変更・再検証は行っていない。

| ID | 原稿の節・主張 | 種類 | 対象・仮定 | 一次資料の箇所 | 確認結果 |
| --- | --- | --- | --- | --- | --- |
| C2-01 | §2.1、定義2.1・命題2.2 | 数学 | 構造関係の商、observable ring との表示同型、制限との整合 | [数学本文 III §§4・8、定理8.3][c2-math-iii]、第1章の定義1.25 | 配置の関手を定義し、多項式環と商の普遍性から自然な全単射を証明。原稿では有限性を仮定せず、任意の元が有限個の変数だけを使う普遍性を用いる |
| C2-02 | 定義2.3・命題2.4 | 数学 | 記号的生成元の制限則、必須添字、層化したイデアルの像 | [数学本文 III §§5–6][c2-math-iii]、[WitnessIdeal][witness-ideal] | 生成元の有限和から制限の包含と層化後のイデアル性を確認。必須添字の和を明示 |
| C2-03 | §§2.1–2.2、構成2.6・定理2.9・系2.11 | 数学 | 評価関手のアフィン表現、残差の正則性、開部分の比較・合成条件、被覆と重なりを保つchart対応 | [数学本文 III §§5.2–5.2C・11.1][c2-math-iii]、[Correspondence][law-correspondence]、[Stacks 01HR](https://stacks.math.columbia.edu/tag/01HR)・[01JA](https://stacks.math.columbia.edu/tag/01JA)・[01HP](https://stacks.math.columbia.edu/tag/01HP) | 方程式と残差の評価を等しくする商を作り、生成元の評価と局所化を証明。siteのイデアルとschemeのイデアルの比較を指定。加群の引き戻しの零性ではなく、構造層内で生成するイデアルの零性を用いる。対象の残差へ戻る同型は系2.11の追加条件 |
| C2-04 | §2.3、構成2.12・命題2.15 | 数学 | 商係数、対象依存の残差、circuitの健全性・完全性、自然な係数実現と非零性 | [数学本文 III §5.1A][c2-math-iii]、[数学本文 IV §2.1A][c2-math-iv]、[数学本文 X §5.1][c2-math-x] | 文脈ごとの残差の失敗、局所configuration上の有限query、制限に安定な選択circuit族、局所健全性・局所完全性を明記。記号的生成元と残差類を区別し、集約の相殺条件を分離して単独circuitの検出命題を証明 |
| C2-05 | §2.4、補題2.17・例2.19 | 数学 | 固定した有限単射射被覆、アーベル群値の係数、空交差の零係数 | [数学本文 IV §§3–4][c2-math-iv]、[数学本文 X §2][c2-math-x] | 微分の合成、固定被覆の商群、三chartのperiodによる同型を本文で計算 |
| C2-06 | §2.5、命題2.21・定理2.22・系2.23 | 数学 | 交差図式上の自由かつ推移的な作用、局所atlas、空交差の高々一元性、実際の状態の層条件 | [数学本文 IV §§5・11][c2-math-iv]、[数学本文 X §8][c2-math-x]、[Stacks 03AG](https://stacks.math.columbia.edu/tag/03AG) | 差のcocycle、atlas変更によるcoboundary、補正後の貼り合わせを証明。自己交差・逆向き・空交差の一致を確認。Lawful状態が層になる理由と、有限検査からLawfulnessへ進むための条件を明記 |
| C2-07 | §2.6、命題2.24–2.28 | 数学 | 有限次元・有限長、連結な交差、定数係数、forestの制限全射、単体のchainとcochain | [数学本文 IV §§12–13][c2-math-iv] | 容量下界、Euler交代和、nerve比較、forest消滅、Stokesを証明。群の次元と指定類の非零性を区別 |
| C2-08 | 命題2.29 | 数学 | 有限単体複体の二部分複体による分解、共通の定数係数 | [数学本文 IV §§8–9・13][c2-math-iv] | 原稿では有限cochainの場合を構成。制限の差の全射、持ち上げ独立性、零性の同値、境界とのペアリングを直接証明 |
| C2-09 | §2.7、命題2.32・例2.33–2.34 | 数学 | 宣言した意味変形族に対する抽出の不変性、構造座標、条件S、構造側の一次コホモロジー消滅 | [DependencyProfile][c2-two-phase-dependency]、[CoefficientComplex][c2-two-phase-complex]、[CohomologyComparison][c2-two-phase-h1]、[ForestSupport][c2-two-phase-forest]、[FiniteWitnesses][c2-two-phase-finite] | AtomKindだけの分類を用いず、商の微分と単射性を証明。条件S（原資料のConditionE）の不成立例と、それだけでは単射にならない例を計算。例2.34とLeanの複体はともに二組の二頂点・二平行辺からなる。原稿の一般の体に対し、Leanの係数はZMod 2 |
| C2-10 | §2.8、定義2.35・補題2.36 | 数学 | 有限source・Law族、Law値を保つ原始関係、整数係数 | [PresentationGroup][c2-presentation] の `presentationGroupEquivBlocks` | 生成子関係の商と成分ごとの自由アーベル群の両逆を証明。四生成子・二関係の例を計算 |
| C2-11 | 構成2.37–2.39 | 数学 | 選定した点・生成子のAtom族、開集合に対応する文脈、三chart・四chart、局所定数係数 | [PointGeneratorAtomInput][c2-atoms]、[FiniteCoverGeometry][c2-cover-geometry]、[CombinedAtomContextSupport][c2-support]、[CombinedAtomContextContinuity][c2-continuity]、[CombinedAtomActualNerve][c2-nerve] | 原稿では全生成子を読む開集合文脈の部分圏を明示して構成。より大きな文脈siteとの同値は主張しない。八点の位相から被覆・連結性・三重交差の空性を示し、実際の切断と制限でČech座標を得る |
| C2-12 | 命題2.40–2.41・例2.42 | 数学 | 同じ整数係数と実被覆、任意のchart状態と辺遷移 | [SpecifiedAffineObstruction][c2-affine]、[ExistingObstructionBridge][c2-existing]、[CombinedAtomSpecifiedObstruction][c2-specified]、[SelectedFiniteObstructionExamples][c2-selected-examples] の `coarse_nonzero_actual` | 原始関係の方程式が評価・制限・平行移動で成立することを証明。実際の比較から指定cocycleを作り、torsorの貼り合わせ障害との一致と局所状態変更による類の不変性を記述 |
| C2-13 | §2.9、定義2.43–構成2.46 | 数学 | semantic atom、supported generator、制限で保たれる修復関係、修復語の作用、別に選ぶ方程式側のlift | [数学本文 X §§3–6][c2-math-x]、[SAGA §§3.4–4](https://arxiv.org/html/2608.21458v1) | 二つの係数と二つの残差をそれぞれ構成。作用からtorsorを導く条件と、修復生成元を対象依存の残差類へ送る写像を明記 |
| C2-14 | §2.10、補題2.48・定理2.49 | 数学 | 生成元に関して同変な局所状態写像、関係と生成元の完全性、空交差の正規化 | [数学本文 X §§6–7][c2-math-x]、[EquationRealization][c2-saga-realization] の `equationRelationSound`、[KappaComparison][c2-saga-kappa]、[SAGA 定理5.1(i)–(ii)](https://arxiv.org/html/2608.21458v1#S5) | 関係の健全性を状態写像と自由作用から導出。係数同型、次数0〜2の複体同型、一次コホモロジー同型を証明。独立に選んだatlasの差を明示的なcoboundaryとして比較 |
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

### 第2章のPRレビューと修正

2026-09-20、commit `53422eb867858e306daace5974ebc3eb684cb568` に対する
[Claudeの独立レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4832#issuecomment-5749801775)は、
数学・有限例・引用・GitHub描画の検証結果を記録し、局所circuitの定義不足と第1章の要約の修正を要求した。
[別の内容レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4832#pullrequestreview-5260546350)は、
数学的内容を支持し、torsor、二回の商、八点空間の図について説明の補強を提案した。
各レビューの検証範囲はリンク先に記載されている。

人間の採用指示に従い、定義2.14に局所検出の入力と成立条件を記述し、命題2.15の対象・文脈を明示した。
局所circuitの制限は、選択した族のデータとして恒等・合成と一致・受理の保存を要求する。
第1章の要約は、意味論の格納、対象・型付き射からの回復、法則の成立の同値を区別して書き直した。
torsorの局所状態と係数の0-cochainの違い、評価の一致とLaw成立を課す二回の商、
構成2.6の比較・chart対応、period、有限検査の条件を補足した。
記号・訳語を整理し、準備節P.5の番号を付ける項目に「構成」を追加した。

[図2.1](figures/ch02-finite-covers.svg)は、八点空間の八本の順序関係と、
四chart・三chartそれぞれのnerveを分けて示す。図の三角形に面はない。
辺点の記号 `e_{01}` は、一次資料の `k` と同じ点を指す。
図のSVG自体を編集元とし、字形・矢印・交差ラベルは本文幅676pxのブラウザ表示で確認した。

任意提案C3の「例2.34とLeanでは複体の形が異なる」という説明は採用しなかった。
固定版の `FiniteWitnesses.lean` の `twoPhaseCycleNerve` は、原稿と同じ二組の平行辺である。
原稿の一般の体とLeanの `ZMod 2` という係数の違いをC2-09に記録した。
C2-01・C2-12・C2-14には、確認した直接の参照先を補った。

修正版の第2章全534式（本文内487・独立行47）をKaTeX 0.18.7で検査し、エラー・警告なし。
既存の番号付き39式は辺点の記号変更を除いて一致し、定義等51件・章内参照を保持した。
準備節の全112式は変更していない。文書内の相対リンク318件、空白・不可視文字も検査した。
八点空間の全47開集合を列挙し、両被覆の被覆性・連結性・交差と、SVG内の8本の順序矢印を検算した。
本文と図を通読し、局所検出の定義から命題2.15、torsorから貼り合わせ、二回の商から定理2.9への接続を確認した。
図のSHA-256は `0827c5487af26d4fde58149668d3900089ac27dbe6b680999bf171a6bc8f9e4e`。
文献確認記録の原稿一式のhashも更新した。GitHubの表示確認とCIは、修正後commitを対象にPRへ記録する。
2026-09-20、修正後commit `877bc313b2160e59d359f8b94e43506a5c5076c3` に対する
[Claudeの再レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4832#issuecomment-5749951478)でapproveを得た。
同commitのGitHub数式表示・CIの確認を経て、人間がPR #4832をマージした。
merge commitは `8d949b2c116551f680f9792842e79e58d529e30a` である。

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
[c2-selected-examples]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedFiniteObstructionExamples.lean
[c2-saga-realization]: ../../../Formal/AG/SemanticRepair/Saga/EquationRealization.lean


## 第3章「標準解像度と診断不変性」

2026-09-20、第2章をマージした固定版
[8d949b2c116551f680f9792842e79e58d529e30a](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/tree/8d949b2c116551f680f9792842e79e58d529e30a)
の一次資料を読み、[日本語原稿](ja/06-resolution-invariance.md)を作成した。
以下の相対リンクはこの固定版のファイルを指す。
原稿のSHA-256は `bc865566dcb6a96aeaa6a8c7b9fae0171ca06d0739ed26048fa438485d75fca7`。

主張は原稿内の定義と証明による数学として記述する。既存のLean sourceとは、
入力・成立条件・写像・結論を照合した。Leanの変更とローカル再検証は行っていない。
原稿の有限例として構成し直したものは、下表で既存の形式化と区別する。

| ID | 原稿の箇所 | 入力・成立条件 | 確認した一次資料 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- |
| C3-01 | 定義3.1–定理3.4・例3.5 | 同じsource上の全射、有限Law族、評価の降下 | [Reading][c3-reading]、[JointKernel][c3-joint] | kernel上の恒常性と降下、canonical factorの全射性、joint kernel商の普遍性・一意性を証明 |
| C3-02 | 構成3.6–例3.8 | 有限source、評価値と抽出結果の等号判定、指定されたdoctrine族 | [Effective][c3-effective]、[Admissible][c3-admissible]、[正例][c3-positive]・[反例][c3-negative] | partitionを計算し、抽出結果のkernelとの一致を判定。六sourceの二つの真の細分から、adequacyだけでは表示可能性が従わないことを示す |
| C3-03 | 定義3.9–命題3.12 | 有限nerve、chartの台、辺・面の交差台、adequacy、有理係数 | [LawGeneratedComplex][c3-complex] | 座標はLawと相異なる値の組とし、witnessを座標に加えない。二つの微分とLaw値ごとの直和分解を記述 |
| C3-04 | 定義3.13・命題3.14 | chart写像、辺・面の部分写像、台の包含、縮約面の三辺の縮約 | [SupportedNerveMorphism][c3-morphism]、[GeneratedComparisonMap][c3-map] | 実際の座標式からcochain比較を生成し、二つの微分平方とH¹写像を証明 |
| C3-05 | 定義3.15–定理3.17・例3.18 | C0・C5・C6は全体、C1–C4は各Law-value block。C3は有理chainで定義 | [条件C][c3-conditions]、[block比較の全単射][c3-bijective]、[SelectedReadingConditionC][c3-selected-c] | fiber内部の道積分による補正、単射性、辺・面の持ち上げによる全射性を証明。三chart・四chartの具体例を与える |
| C3-06 | 例3.19 | 全体のchart台、三source、二つのLaw、異なるnerveの比較 | [AdequateConditionCFailure][c3-adequate-failure]、[CanonicalInadequateFalsePositive][c3-false-positive]、[CanonicalInadequateHiddenClass][c3-hidden] | loopと道、道と平行二辺を本文用の小例として計算。共通Lawのadequacyと被覆条件を分け、追加Lawが降下しない場合も説明 |
| C3-07 | 定義3.20–命題3.23 | 同じ比較幾何、全adequate有限Law族、明示的有限表示 | [UniformityReduction][c3-uniform]、[DefectSemantics][c3-defect]、[UniformPresentationDecider][c3-decider] | Law値のfiberによる部分nerveの同定とindicator Lawの逆方向を証明。実比較の核・余核の次元による判定を有理行列計算として示す |
| C3-08 | 系3.24・例3.25 | 全非空target部分集合、C0–C6、全体のchart台 | [AtlasPositioning][c3-atlas] | 各条項を部分集合とLaw-value blockの間で移す。条項の非必要性は本文用に七つの小例を構成し、各実比較の階数を別途検算。既存の七つのLean witnessと同じ有限表であるとは主張しない |
| C3-09 | 定義3.26–命題3.28 | 接続役割別の隣接色とclip2個数を読む、本文で定義した局所観測 | [T3/T6の有限入力][c3-t3t6]、[一様性の相違][c3-t3t6-uniform] | 同じ有限入力について局所型の一致と周期3・6のcocycleを直接計算。観測の範囲は下記に明記 |
| C3-10 | 定義3.29–命題3.32 | 語彙・解像度・source意味論・正規化を固定し、意味readingと許可述語を変える族。source別の有理係数 | [NerveGeneration][c3-struct-nerve]、[StructuralLocalization][c3-struct-local]、[GeneratedH1Vanishing][c3-struct-zero] | 構造台を族全体で残る抽出対として定め、nerveの一致を証明。各sourceの基準Atomを用いてすべてのcocycleのprimitiveを構成 |
| C3-11 | 構成3.33–例3.35 | ラベルを保つ原始関係、整数presentation係数 | [CoefficientComparison][c3-coefficient] | 同じラベルに属する関係成分の係数和としてεを定義。同ラベルの連結性による単射性と、二生成子・空関係の非単射例を示す |
| C3-12 | 構成3.36・定理3.37 | 連結なchart・非空二重交差、異なる三chartの交差が空、局所定数な整数係数、任意の局所データ | [FaceEmptyCechNormalization][c3-normalization]、[ActualCechH1Comparison][c3-h1]、[CombinedAtomSpecifiedObstruction][c3-specified] | 実際の切断・制限からφを定め、同じ入力で独立に書いた診断生成式とのcochain等式を示す。Φは整数係数から有理係数への加法的準同型として扱う |
| C3-13 | 定義3.38–例3.41 | 同ラベル生成子の原始関係による連結性、各ラベルの全chart共通代表 | [IntegralReflection][c3-integral]、[SpecifiedClassReflection][c3-reflection]、[CombinedAtomSpecifiedReflection][c3-selected-reflection] | 有理primitiveの床関数から整数primitiveを作り、実切断へ戻して零性を反映。共通代表を欠く反例は本文の被覆上で別途構成 |
| C3-14 | 構成3.42・定理3.43 | 同じ点・生成子Atom入力、第一成分Law、粗いreadingと恒等reading、実際の三chart・四chartの細分 | [SelectedReadingRefinement][c3-refinement]、[CombinedAtomReadingNaturality][c3-naturality] | 内部辺を零へ送る実restrictionを計算し、cochainの比較平方、局所データと指定類の輸送を証明 |
| C3-15 | 定理3.44・例3.45 | 同じ入力で両端の反映条件とC0–C6が成立し、canonical factorは非単射 | [SelectedReadingConditionC][c3-selected-c]、[SelectedFiniteObstructionExamples][c3-examples] | 四つの零性の同値を合成。非零mismatchを持つ零障害例と非零障害例について、整数・有理periodを粗細両側で計算 |
| C3-16 | §3.11末尾 | 対応する交差図式、制限と可換な係数同型、対応するLaw・witness・軸 | [数学本文VIII §7][c3-math-viii]、[Stacks Tag 09UY](https://stacks.math.columbia.edu/tag/09UY) | 固定被覆の各次数のcochain同型から、対応する障害類の零性同値を説明 |

### 局所観測と有限例の範囲

定義3.26の `Obs_loc` は、本章で定義した接続役割別の色・個数の観測である。
既存の [GLocalV1Nonfactorization][c3-full-local] が扱う `G_local-v1` は、
終端簡約、半径1の接続情報、targetの同時再ラベル等を含む別の観測仕様である。
本章ではT3/T6の同じ生の入力を使い、定義3.26の観測について命題3.28を直接証明した。
二つの観測関数を同一視せず、既存仕様全体の非因子化を証明済みとして転記しない。
既存仕様の全定義・形式化との対応は、付録B・Cの作成時に扱う。

例3.25では、非零の共通loop成分を加えた上で、それぞれの条項が必要ではないことを示す。
共通loopにより全行でC3も破れる。本文の主張は七条項それぞれの非必要性であり、
「他の六条項をすべて満たす」という独立性の主張ではない。

### 有限計算と読者向け確認

本文の有限表から、Pythonの有理数演算で微分・比較行列を生成して検算した。
cocycleの基底とfine側のcoboundaryを使い、実H¹写像の階数を計算した。
両側のH¹の次元の一致だけを同型性の判定に使っていない。

- 六sourceのpartitionが指定のkernelを持ち、二つの抽出方法が標準解像度の真の細分となる。
- 例3.19の核・余核の次元は一座標あたり `(1,0)` と `(0,1)` となる。
- 例3.25の七例は指定条項を破り、いずれも実比較の核・余核が零となる。共通のH¹はC3の行で次元2、他の行で次元1。
- 命題3.28の全三つの非空部分集合について、局所観測表の一致と式(3.23)のdefectを確認した。
- 命題3.32の順序付きnerveをAtom数1〜4で生成し、H¹が零であることを確認した。一般の場合は本文のprimitive構成による。
- 三chart・四chartの比較の二つの微分平方、条件C、実比較の階数を確認した。粗い側の125個の辺値と細かい側の625個の整数chart値でperiodの保存・coboundaryのperiod零を検算した。
- 床関数による整数化は、四chart上の625個の整数値に四つの有理定数を加えた2,500例で辺差の保存を確認した。一般の証明は補題3.39に記載した。

概要、診断を比較する目的、各節の導入、定義・証明・正負例、章末のまとめを配置した。
第2章の三chart・四chart被覆を再利用し、条件Cの説明から指定障害類の零性同値までつないだ。
本文にAAT内部の章番号、GOAL、Lean識別子、repoのパスへの案内を置いていない。
Lean状態、tool schema、websiteの公開内容への変更はない。

人間との議論に基づき、章末にコードレビューへの応用可能性を追加した。
注文処理のレビューを説明例とし、標準解像度、条件C、指定障害類の零性反映に対応づけた。
この段落は応用の見通しであり、実コード上のモデル構成・仮定の検証・有効性の実験を実施したという主張ではない。
補正可能性とコードへの実現、同じ入力の読み方の比較と変更前後の入力の比較を区別した。
既存の全数式、定義・結果・式番号、引用の保持を修正前後で確認した。

### 初稿の数式・引用の確認

初稿の全451式（本文内409・独立行42）をKaTeX 0.18.7で構文検査し、エラー・警告なし。
ローカルのMathMLプレビューでは、全数式の描画、本文幅676pxでの独立行のはみ出し、
主要な定義・零性反映・比較平方の表示を確認した。
定義等45件・式番号42件と、第1・2章を含む結果の参照を検査した。

第3章で追加した引用はStacks §20.15の被覆の細分によるČech cochain写像であり、
原典の冒頭の構成を確認した。既存の引用内容は変更していない。
[文献](ja/14-references.md)と[references.csv](references.csv)に参照箇所と更新したhashを記録した。

2026-09-20、人間が原稿とコードレビューへの応用可能性の追記を確認し、PR作成を承認した。
GitHubのファイルプレビュー・描画済み差分の表示確認とCIの対象commit・結果はPRに記録する。
ローカル表示確認をGitHubの確認済みとは扱わない。

### PR #4833のレビューと修正

2026-09-20、commit `29916abc04e06b3aab352934e9b1f6e2d2865484` に対する
[Claudeの独立レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4833#issuecomment-5750455622)はapproveとした。
[別の内容レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4833#pullrequestreview-5260814132)も
主要定理の結論を肯定した。確認範囲と独立計算はそれぞれのレビューに記録されている。

人間の採用指示に基づき、例3.18でfine側の一般のperiodと比較像上の値を区別した。
一般のperiodには内部辺の項を含め、比較像ではこの項が零になることを明記した。
併せて、次の任意提案7件を反映した。

- §3.7のchart名を `w_0,w_1` に揃え、例3.19のLawの評価記号との衝突を解消。
- 例3.25で、非零類も運ぶために共通loopを加える目的と、全行でC3も破れることを説明。
- 構成3.6で、Law添字集合が空であることとsource集合が空でないことを明確化。
- 定理3.22の指示Lawの定義を和文に統一。
- §3.3でLaw-valueラベルと有理係数を区別し、局所データから診断類を作る§3.9へ接続。
- 定義3.9で被覆の開集合と解像度の台を区別し、例3.18から図2.1を参照。
- §3.8で同じsourceに属するAtomの全ての組とsource別係数を使う目的を説明。

変更後の全457式（本文内415・独立行42）はKaTeX 0.18.7の構文エラー・警告なし。
定義等45件・式番号42件を保ち、独立行の数式の変更は式(3.20)のchart名だけである。
§3.7全体がchartの改名だけであること、結果・式の参照と図2.1の参照先を確認した。
periodは625通りの整数chart値でcoboundary上の零を、125通りのcoarse辺値で比較による保存を再検算した。
内部辺を省くとcoboundaryでも値が零にならない例も確認した。
書誌・引用範囲・コードレビューへの応用段落を保ち、原稿hashを更新した。
修正後のGitHub表示・CIの対象commitと結果はPRに記録した。
2026-09-20、人間が[PR #4833](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4833)をマージした。
最終headは `a972997abbc7142c3a65d0454977af5b568e8709`、
merge commitは `bb9c533efbd68adc0e8004a90e5a782c8497a1c2`。
上記のClaudeレビューは修正前のcommitに対するものであり、修正後の独立再レビューは記録していない。

[c3-reading]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/Reading.lean
[c3-joint]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/JointKernel.lean
[c3-effective]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/Effective.lean
[c3-admissible]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/Admissible.lean
[c3-positive]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/PositiveWitness.lean
[c3-negative]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/NegativeWitness.lean
[c3-complex]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean
[c3-morphism]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/SupportedNerveMorphism.lean
[c3-map]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/GeneratedComparisonMap.lean
[c3-conditions]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditions.lean
[c3-bijective]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonBijectivity.lean
[c3-adequate-failure]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/AdequateConditionCFailure.lean
[c3-false-positive]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/CanonicalInadequateFalsePositive.lean
[c3-hidden]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/CanonicalInadequateHiddenClass.lean
[c3-uniform]: ../../../research/lean/ResearchLean/AG/UniformInvariance/UniformityReduction.lean
[c3-defect]: ../../../research/lean/ResearchLean/AG/UniformInvariance/DefectSemantics.lean
[c3-decider]: ../../../research/lean/ResearchLean/AG/UniformInvariance/UniformPresentationDecider.lean
[c3-atlas]: ../../../research/lean/ResearchLean/AG/UniformInvariance/AtlasPositioning.lean
[c3-t3t6]: ../../../research/lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Witnesses.lean
[c3-t3t6-uniform]: ../../../research/lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Uniformity.lean
[c3-full-local]: ../../../research/lean/ResearchLean/AG/UniformInvariance/GLocalV1Nonfactorization.lean
[c3-struct-nerve]: ../../../research/lean/ResearchLean/AG/StructuralCover/NerveGeneration.lean
[c3-struct-local]: ../../../research/lean/ResearchLean/AG/StructuralCover/StructuralLocalization.lean
[c3-struct-zero]: ../../../research/lean/ResearchLean/AG/StructuralCover/GeneratedH1Vanishing.lean
[c3-coefficient]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CoefficientComparison.lean
[c3-normalization]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/FaceEmptyCechNormalization.lean
[c3-h1]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/ActualCechH1Comparison.lean
[c3-specified]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomSpecifiedObstruction.lean
[c3-integral]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/IntegralReflection.lean
[c3-reflection]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedClassReflection.lean
[c3-selected-reflection]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomSpecifiedReflection.lean
[c3-refinement]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedReadingRefinement.lean
[c3-naturality]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomReadingNaturality.lean
[c3-selected-c]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedReadingConditionC.lean
[c3-examples]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedFiniteObstructionExamples.lean
[c3-math-viii]: ../../../docs/aat/algebraic_geometric_theory/part_8_measurement_theory.md

## 第4章「輸送と合成の整合性」

2026-09-21、第3章をマージした固定版
[bb9c533efbd68adc0e8004a90e5a782c8497a1c2](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/tree/bb9c533efbd68adc0e8004a90e5a782c8497a1c2)
の一次資料と、第1〜3章の原稿を照合して[日本語初稿](ja/07-transport-coherence.md)を作成した。
以下の一次資料の相対リンクは、この固定版で照合したファイルを示す。
原稿のSHA-256は `daecfc94783b5e8e11728c54444a6e979c40aca92e97167974ad8ac2058457b3`。
確認者はCodex（GPT-6）である。

本文に必要な定義・条件・構成・証明を記述し、内部資料への案内はこの記録へ分けた。
Lean sourceは既存の形式化の条件と結論の照合に使い、変更・ローカル再検証は行っていない。
本文の群による有限例は、下記のとおり既存のAAT packageの有限witnessと区別する。

| ID | 原稿の箇所 | 入力・成立条件 | 確認した一次資料 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- |
| C4-01 | 定義4.1・補題4.2 | 関手、任意の底の後続射を量化する強いopcartesian射 | [Coreの普遍性][c4-core-opcart]、[liftの一意性][c4-core-unique]、[Stacks Tag 02XJ](https://stacks.math.columbia.edu/tag/02XJ) | 任意の後続射について存在一意性を定義し、vertical同型の一意性、恒等・合成の閉性を証明。Stacksの強いcartesian射の双対であることを明記 |
| C4-02 | 構成4.3–定理4.5 | Exactな抽出射、Atom全単射、一般のsource写像、元のcore | [AtomFoundation/Transport][c4-core-transport]、[Opcartesian][c4-core-opcart] | configuration・対象形成・名前付きoperation・方程式・detector・invariant・signatureを再添字づけし、任意のexactな後続射に対する因子を逆再添字づけで構成。各成分の一意性を確認 |
| C4-03 | 例4.6・構成4.7 | 前向き抽出保存、Atom全単射、追加抽出族の有限性、実際のbase operation、方程式とdetector健全性 | [RefinementObstruction][c4-refinement-obstruction]、[RefinementSupply][c4-refinement-supply] | 三Atomの交換と追加によるexact性の失敗を記述。追加operationの向きは拡大基点から旧基点の像とし、到達可能性と像の上でのquery・受理保存を導出 |
| C4-04 | 構成4.8–定理4.11 | Coreの文脈同値、被覆要件の存在量化像、選択overlap、同じ係数でのraw system再添字づけ、三つの実現比較 | [GeometryTransport/Transport][c4-geom-transport]、[Supply][c4-geom-supply]、[Factorization][c4-geom-factor]、[Opcartesian][c4-geom-opcart] | 一般のcore射にはH_geomを必要十分な存在条件として示す。標準core輸送では三つの可逆な実現比較を構成し、任意のcoreの後続射について幾何の因子を構成・一意化 |
| C4-05 | 補題4.12–定理4.16 | 選択した強いlift、fiberの対象とvertical射、coreへの射影 | [CorePseudofunctor][c4-core-pseudo]、[Pseudofunctor][c4-geom-pseudo]、[TowerCompatibility][c4-tower] | 輸送関手、compositor、unitorを因子分解から作り、自然性、三重合成・単位と段間の二経路の一致を同じ普遍性から証明 |
| C4-06 | 定義4.17–構成4.18 | 有限グラフ、底で等しい二道、強い辺lift、独立に指定した終点自己同型 | [FinitePresentation][c4-presentation] | 指定比較とcanonical comparatorを区別し、raw defectを合成順序込みで定義。指定比較の整合性を入力へ含めない |
| C4-07 | 定義4.19–定理4.22 | 終点fiber群のedge gauge、現在の辺の選択を含む作用空間 | [FinitePresentation][c4-presentation]、[VanishingCoherence][c4-vanishing] | vertical同型の因子分解を明示し、道の終点変化とdefectの共変式から作用則を証明。二辺の計算で現在の選択への依存を示す。軌道による消滅と独立な道の可換式を、強いliftの一意性で同値化 |
| C4-08 | 補題4.23–命題4.26 | 後続道へのwhiskering、向き付き面の貼り合わせ、同じ始終道を持つsyzygy | [PastingObstruction][c4-pasting] | 逆向きでは指定比較と標準比較をそれぞれ反転。貼り合わせのdefectには共役を含め、cocycle条件には指定比較のsyzygy整合を要求。閉じた不一致の共役式は固定したedge gaugeで証明 |
| C4-09 | 例4.27–例4.29 | 一対象群圏、恒等の初期lift、独立な平行二辺と一面、辺を共有する複数面 | [VanishingCoherence][c4-vanishing]、[FiniteWitnesses][c4-finite]、[UnifiedObstruction][c4-unified] | 独立な二辺での比較の吸収、同じ二辺への異なる要求、S3の非可換な三比較を本文用の群圏で直接計算。既存のAAT package全成分をこの小例に含めたとは扱わない |
| C4-10 | 定義4.30–定理4.33 | 抽出を固定する上下の自己同型群、core射影と核、辺ごとのlift、coreの道の整列 | [SectionDecomposition][c4-section] | 無条件のdefect射影を先に示す。整列と一意性からp(m)=p(u)を導き、核への所属とuφ⁻¹=(um⁻¹)(mφ⁻¹)をこの順序で証明 |
| C4-11 | 定理4.34 | 同じcoreの辺の選択の上のlift、核のedge gauge、全ての面 | [GlobalVanishing][c4-global] | 固定sectionの上の全体整合性と、同じsectionに相対的な核の補正を両向きに構成。さらにsectionの存在を量化して同時消滅を特徴づける |
| C4-12 | 例4.35 | S4、選択した二軸の安定化群とC2の直積、一頂点・二loop・二面 | [CrossStageCoherence/FiniteWitnesses][c4-stage-finite]の四軸と平方根の機構 | 本文用に群準同型K→S4を構成。Coreの二つの平方根がどちらも持ち上がらず、独立な核の条件は解けることを証明・全数検算。元の係数環ℤ×ℤの幾何packageの代わりに、核を明示的なC2とした有限群の塔を用いた |
| C4-13 | 定義4.36–例4.39 | 三法則を持つlens、一般の状態・view写像、同じ状態写像の再利用 | [CSAATLensRelativeOperationSquares][c4-lens]、第1章の定義1.32・命題1.34・例1.35・定義1.42 | getとputを直和写像に束ね、共有されたhとh×uによる一つの平方との同値を証明。第一・第二法則から更新保存が読取り保存を含意することを原稿内で導出し、可逆な組の共通部分がput保存群に等しいことを示す。非単射の意味保存射も保持 |
| C4-14 | 命題4.40 | 固定プロトコル、名前付き生成辺、頂点写像、観測とadapter | [CSAATProtocolAdapterSquares][c4-protocol]、第1章の命題1.38 | 生成辺から全実行への自然性を帰納法で導き、adapter平方を頂点成分で特徴づける |
| C4-15 | 定理4.41・章末 | 充満忠実関手、任意の比較射、両端の自己同型。Sectionの対応には比較射の可逆性 | [CSAATFullyFaithfulComparisonTransport][c4-fully-faithful]、第1章の命題1.43 | 比較を保つ群の全単射をfullnessとfaithfulnessから証明。適用先は実際に構成した型付き圏とし、幾何の輸送には別途core射と局所実現の比較を指定 |

### 有限例と計算の確認

本文の証明と別に、有限置換を全列挙するPythonスクリプトで次を検算した。

- S3で長さ3の道を用い、defectの共変式を7,776通り、作用の合成則を46,656通りの辺の選択で確認。
- 独立な平行二辺の比較は6個の各指定比較について6通りの解を持つ。同じ二辺への異なる二要求と、非可換な三比較には同時解がない。
- 貼り合わせの共役を含む式を1,296通り、閉じた比較の式を216通りで確認。Defectの単純な積への置換は648通りで失敗した。
- 順序を保つ二因子の分解を216通りで確認。因子順序の交換は108通りで失敗した。
- S4で(12)(34)の平方根は二つで、どちらも選択対{1,2}を保たない。本文の群の塔ではcoreの全条件に2解、幾何だけの第二の面に8解、両面の同時条件に0解。
- 四状態のlensの全置換でgetだけを保つものは4個、putも保つものは2個。非単射の補完写像も読取り・更新を保つことを確認。

四軸の例は、sectionの存在条件を小さな群で説明するための本文内の構成である。
この例の検算を、既存のLeanによる幾何package全体の再検証として扱わない。
一般の定理は本文の証明と一次資料の読解で確認した。

### 初稿の表示・引用と確認状態

全410式（本文内358・独立行52）をKaTeX 0.18.7で構文検査し、エラー・警告がないことを確認した。
本文内数式の改行を解消し、定義等41件・式番号52件と前章からの参照を確認した。
ローカルのMathMLプレビューで、本文幅676pxでの描画漏れ・はみ出しと主要な式の表示を確認した。

新しい引用はStacks §4.33の強いcartesian射と選択した輸送の構成であり、
原典の定義4.33.1、補題4.33.2・4.33.7を確認した。
本章ではその双対を使い、必要な普遍性と整合性の証明を本文に記述した。
Lensとプロトコルは第1章で定めた意味論から出発し、既存文献の引用範囲を広げていない。
文献確認記録の原稿hashには、第4章までの日本語原稿を掲載順に含めた。

2026-09-21、下記の具体例の改善を含む原稿について人間の確認を終え、
[PR #4834](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4834)を作成した。
commit `edd77183adc4e1f6a8d7a622b753fc69ff8658ed` の全410式をGitHubのファイルプレビュー・
描画済み差分で確認し、CI7件の成功とともにPRに記録した。その後のレビュー対応は下記に記す。

### 導入とまとめの具体例の改善

2026-09-21、人間の依頼に基づき、概要の動機を注文APIのリファクタリングで説明した。
データ・操作・条件の引継ぎと、段階的な変換と直接の変換の一致を分け、
配送先と請求先の入替えを、可逆でも経路が整合しない説明例として加えた。
実開発での実証結果を追加したものではない。全410式、番号、§4.1以降の定義・証明・引用の保持を
差分で確認し、原稿hashを更新した。

同日、人間の依頼に基づき、章末のまとめでも同じ注文APIの例に戻った。
経路間の住所の入替え、共有する変換を修正したときの他経路への影響、
読取りと更新の両方を保つ必要性を、構成4.18・定理4.22・命題4.37・4.38・4.40に照合して記述した。
全410式、定義・結果・式の番号、まとめより前の本文と引用を保持し、原稿hashを更新した。

### PRレビューと採用した7件の修正

2026-09-21、commit `edd77183adc4e1f6a8d7a622b753fc69ff8658ed` に対する
[Claudeレビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4834#issuecomment-5751572737)は
approveとし、任意提案4件を示した。
[別の内容レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4834#pullrequestreview-5261278310)は
主要定理の結論を肯定し、例の適用範囲の正確化1件と説明の補強2件を提案した。
人間は計7件の採用を指示した。

| 対象 | 修正と確認 |
| --- | --- |
| 例4.27 | 吸収できる理由を、二本の平行な辺を独立に選び直せることとして明示。一般の一面への拡張を避け、例4.35の第一面だけでも解がないことと整合させた |
| 命題4.21・構成4.24の説明 | 二辺の道の終点変化を直接計算し、現在の選択への依存を示した。道の記述順と射の合成順も一式で明示 |
| 定義4.36・命題4.38とまとめ | 第1章の式(1.16)の第一・第二法則から、更新保存が読取り保存を含意することを一般の写像について導出。可逆な場合の群の包含と例1.35の反例を結びつけた。この補足は本文内の証明であり、新たなLean theoremの追加としては扱わない |
| 定義4.19 | vertical同型の因子が逆射で一意に作れることを補い、補題4.2の合成の性質に接続。既存Leanの `reselectedEdgeLift_isStronglyCocartesian` と同じ構成であることを確認 |
| §§4.5–4.9の記法 | 面の右道を `ρ_f` として関手 `r` と区別。旧記号の全12箇所を同じ意味で置換した |
| 定理4.33 | 再選択前の比較を `φ_f^0` として、再選択を引数に取る比較族と区別。分解・射影の式の積順序を保持 |
| 例4.35 | 四つの添字を軸と見なす群の例であることを冒頭で説明。群と指定比較の条件は保持 |

二辺の終点変化をS3の全1,296通りで検算し、固定した再選択でも現在の選択によって
三つの異なる終点変化が得られる例を確認した。独立な二辺での各指定比較の解6件と、
S4の選択対の安定化群に平方根がないことも再確認した。
四状態の積lensでは、一般の状態・view写像の組1,024通りのうち更新保存は16通りで、
すべて読取りも保存した。読取り保存64通りのうち48通りは更新を保存しなかった。
一般の含意の根拠は、有限検算ではなく本文に記した法則による証明である。

修正後の全425式（本文内370・独立行55）をKaTeX 0.18.7で検査し、エラー・警告なし。
定義等41件と式番号52件を保持し、追加の三つの計算は番号なしの式とした。
参照・文献・不可視文字・公開情報と原稿hashを確認した。
修正後のcommit `51995e33b3b416d0e07399c78787ad3c97163034` で全425式のGitHub表示とCI7件の成功を確認し、PRに記録した。
2026-09-21、人間がPR #4834をマージした。Merge commitは `9364f25d1b54dff9ad059ae95c71d0404626d0d6`。
Claudeのapproveは修正前のcommitに対するものであり、修正版の独立再レビューとは区別する。

[c4-core-transport]: ../../../research/lean/ResearchLean/AG/AtomFoundation/Transport.lean
[c4-core-opcart]: ../../../research/lean/ResearchLean/AG/AtomFoundation/Opcartesian.lean
[c4-core-unique]: ../../../research/lean/ResearchLean/AG/AtomFoundation/LiftUniqueness.lean
[c4-refinement-obstruction]: ../../../research/lean/ResearchLean/AG/AtomFoundation/RefinementObstruction.lean
[c4-refinement-supply]: ../../../research/lean/ResearchLean/AG/AtomFoundation/RefinementSupply.lean
[c4-geom-transport]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Transport.lean
[c4-geom-supply]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Supply.lean
[c4-geom-factor]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Factorization.lean
[c4-geom-opcart]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Opcartesian.lean
[c4-core-pseudo]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/CorePseudofunctor.lean
[c4-geom-pseudo]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/Pseudofunctor.lean
[c4-tower]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/TowerCompatibility.lean
[c4-presentation]: ../../../research/lean/ResearchLean/AG/TransportCoherence/FinitePresentation.lean
[c4-vanishing]: ../../../research/lean/ResearchLean/AG/TransportCoherence/VanishingCoherence.lean
[c4-pasting]: ../../../research/lean/ResearchLean/AG/TransportCoherence/PastingObstruction.lean
[c4-finite]: ../../../research/lean/ResearchLean/AG/TransportCoherence/FiniteWitnesses.lean
[c4-unified]: ../../../research/lean/ResearchLean/AG/TransportCoherence/UnifiedObstruction.lean
[c4-section]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/SectionDecomposition.lean
[c4-global]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/GlobalVanishing.lean
[c4-stage-finite]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/FiniteWitnesses.lean
[c4-lens]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATLensRelativeOperationSquares.lean
[c4-protocol]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATProtocolAdapterSquares.lean
[c4-fully-faithful]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATFullyFaithfulComparisonTransport.lean

## 第5章の原稿と一次資料の対応

確認対象は [第5章 基底変換と生成比較](ja/08-base-change.md) の日本語原稿である。
一次資料の固定版は、第4章マージ後の `9364f25d1b54dff9ad059ae95c71d0404626d0d6`。
原稿のSHA-256は `f878b074b73e210f4944b3eefc9058cf11dd2f9ccaccb1d344e02affbdb7c439`。
確認者はCodex（GPT-6）、確認日は2026-09-21である。

必要な定義・仮定・構成・証明を原稿内に記述し、内部の数学・Leanとの対応をこの記録に置いた。
Lean sourceは宣言の量化、構成要素、証明の依存を確認するために読んだ。
Leanの変更・ローカル再検証は行っていない。
以下の対応は既存sourceとの照合であり、本文の全命題を新たに形式化したという記録ではない。

| ID | 原稿の箇所 | 入力・成立条件 | 確認した一次資料 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- |
| C5-01 | 構成5.1・命題5.2・例5.3 | 同じAtom carrier、exactなcospan、一般のcone。Pointed版ではcompatibleな選択source | [DoctrinePullback][c5-pullback]、[PointedDoctrinePullback][c5-pointed] | Sourceのcompatible pair、成分ごとの正規化、第一成分の抽出を定義。第二射影のAtom成分をe₂⁻¹e₁とし、Atom成分が恒等とは限らない全coneに普遍射を構成・一意化 |
| C5-02 | 定義5.4・構成5.5・定理5.6 | 任意のsemantic exact底射、任意のtarget core。有限codeによる表示は仮定しない | [CartesianTarget][c5-cartesian]、[ExactBottomGlobalLift][c5-global]、[Stacks §4.33](https://stacks.math.columbia.edu/tag/02XJ) | 有限な選択族を逆Atom写像で戻し、対象形成・operation・方程式・detector・invariant・signatureを再添字づけ。任意の先行底射を量化する強いcartesian性を上段の逆から証明 |
| C5-03 | 補題5.7・命題5.8・例5.9 | 選択したlift、fiber内の対象と射、第4章のcanonicalな前向き輸送 | [GlobalLiftCoherence][c5-global-coherence]、[PackageProjectionBeckChevalleyExactness][c5-bc-exactness]、[TransportEquivalence][c5-transport-equiv] | 引き戻し関手・単位・合成比較を普遍性から作る。底がσである射の集合を介して随伴を構成し、両方向のliftの上段逆から単位・余単位の可逆性を証明。Sourceを二点から一点へ潰す例は本文内の例 |
| C5-04 | 構成5.10–命題5.12・例5.13 | Exactなpointed pullback、実際の二輸送経路と単位・余単位。指定比較との一致は三角形で判定 | [CoreBeckChevalleyMate][c5-bc-mate]、[PackageProjectionBeckChevalleyExactness][c5-bc-exactness] | 三段のmateを記述し、三角形で特徴づけ、cleavageを替えた場合も端点同型の下で一致することを証明。既存mate宣言の有限presentation・Atom等号判定という入力と、本文のsemanticな構成範囲を区別する。本文では定理5.6・命題5.8から一般のexact squareに同じ構成を行う証明を与えた |
| C5-05 | 定義5.14・定理5.15・例5.16 | Source有限表、Atom述語の既定値と有限例外、有限台の置換。端点同型も許す表示可能性 | [Schema][c5-code]、[CoverageSchema][c5-coverage-schema]、[CoverageClassification][c5-coverage] | 両端sourceの有限性と全target sourceの有限・余有限抽出を必要十分条件として証明。正規化の像だけで元の述語を符号化し、正規化の冪等性を要求しない。任意のAtom全単射はtarget端点同型へ移す。固定code間のHomの充満性とは量化を分ける |
| C5-06 | 定義5.17・構成5.18 | 有限の底の図式、辺平方、sourceの強い辺lift、頂点でのcanonical輸送 | [IndexedBaseDiagram][c5-diagram]、[IndexedDiagnosticAssembly][c5-assembly] | 生成辺から道の自然性を帰納的に導出し、同じ平方で上段の辺を因子分解。合成・単位・貼り合わせを一意性から比較 |
| C5-07 | 命題5.19・例5.20 | 変更前の関係、変更先の生の辺と可換平方の族。Epiは指定面の始点での消去に使用 | [IndexedRawFamilyClassification][c5-raw-family] | 面の両経路は頂点射との前合成後に等しいことを示す。本文の十分条件は指定面の始点だけにepiを要求し、既存Leanの生成辺の始点も含むSupportEpiより弱い条件で、本文内の消去証明を用いる。全対象・全平行射への一様な消去条件とepiの同値は、固定した図式の整合性の必要条件とは区別する。二点のsourceで非epiの失敗例と整合する対照例を構成 |
| C5-08 | 構成5.21・定理5.22・例5.23 | 両端で関係を満たす固定図式、同じ入力から生成した辺と指定比較、全てのedge gauge | [EndpointExactness][c5-endpoint]、[CoherenceExactness][c5-coherence]、[ObstructionExactness][c5-obstruction]、[OrbitExactness][c5-orbit] | Fiber同値から終点群の同型を作り、cochain・再選択を両方向へ対応づける。標準比較とraw defectの自然性を示し、整合性、消滅する再選択の存在、任意cochainの軌道所属を保存・反映。S3の例は本文内の群による検算 |
| C5-09 | 定義5.24・定理5.25 | 前向きの抽出保存、上段のexact条件、target coreが存在する選択点での抽出の反映 | [RealizedSupport][c5-realized]、[Refinement Projection][c5-ref-projection]、[Qualification][c5-qualification] | 実現台をcore fiberの非空性で定義。反映条件から逆再添字づけを作り、逆に任意のliftの選択族等式から反映を導く。空fiberの空虚な場合を明示 |
| C5-10 | 構成5.26・命題5.27 | Exact cospanと一方のlegへのrefinement、compatibleなsource対。逆方向にはその点の実現台条件 | [Configuration][c5-ref-configuration]、[Regime][c5-regime]、[Mate][c5-ref-mate]、[Qualification][c5-qualification] | 前向きの平方を反映条件なしで作る。Exactな第一射影によるcore輸送で実現台を移し、二つの逆経路とmateを構成。全compatible点での分類と、恒等・合成の閉性を証明 |
| C5-11 | 例5.28・例5.29 | 三Atom、二source、非自明なAtom交換、各点の実core。別に無限抽出による空fiber | [Refinement Witnesses][c5-ref-witnesses] | 前向きだけの点と、compatibleな入力をallへ絞ると逆輸送できる点を対照化。本文用の小例ではcomposition・対象形成・恒等operation・空Law等を指定し、coreの存在を説明。既存witness packageをそのまま引用したとは扱わない |
| C5-12 | 定義5.30・構成5.31・定理5.32前半 | 生成したcore liftの上段逆、完全な被覆・overlap・raw systemと同じ係数環 | [RefinementGeometry][c5-ref-geometry]、[UpperGeometryCleavage][c5-upper-cleavage]、[UpperGeometryCleavageRealization][c5-upper-realization]、[UpperGeometryMate][c5-upper-mate] | 幾何の全成分を引き戻し、coreと幾何の二段のcartesian性からmate・逆・下段射影・三角形・係数恒等を構成。任意の一方向の幾何射を可逆とは扱わない |
| C5-13 | 定理5.32後半・補題5.33 | 有限根付き図式、同じ底のfiberのsource core図式、二段の強い辺lift、固定係数、同じsourceから引き戻す指定比較 | [CompatibleInput][c5-compatible-input]、[UpperRefinementBCProblem][c5-upper-problem]、[CompatibleMateNaturality][c5-compatible-natural]、[CompatibleGlobalMate][c5-compatible-global]、[SolutionContracts][c5-solution-contracts]、[SolutionEquivalence][c5-solution-equiv] | 辺と指定比較のintertwiningを二段のcartesian一意性から証明。端点同型によるc⁻¹sbと逆を明示し、三角形・道・貼り合わせを含む解と再選択軌道を両方向へ移す |
| C5-14 | 命題5.34–命題5.36 | 第1章の全域lens三法則とlens同型、残す操作と関係のプロトコル、自然なadapter | 第1章の定義1.32・1.36と第4章の定義4.36・命題4.40 | Lensのviewの制限と更新の閉性、移行と制限の可換性を三法則から直接証明。プロトコルの前合成とadapter自然性を生成辺から証明。この章で追加した意味論内の命題であり、新たなLean theoremとは扱わない。AATへ適用する際の入力構成・exactness・幾何の指定は別途必要 |
| C5-15 | 構成5.37・命題5.38 | 同じexact square・比較図式・面・cochain・source core・完全幾何・係数、実際の二経路と端点同型 | [ExactDerivedMateComposite][c5-derived-mate]、[ExactDerivedBarAlphaTriangle][c5-alpha-triangle]、[ExactDerivedBarAlphaProjection][c5-alpha-projection] | 完全幾何の二経路を実際のpush-pullで構成し、単位・始点同型・逆経路mate・終点同型・余単位による比較を説明。三角形の一意性からcanonical mateとの一致とcoreへの射影式を証明 |
| C5-16 | 定義5.39・構成5.40・まとめ | Sourceのconfigurationを保つ対象正規化、残差・operation・invariant・座標のadmissibility、同じcochainによる分岐 | [ObjectNormalization][c5-normalization]、[CanonicalNormalization][c5-geom-normalization]、[ExactBarBetaFactorization][c5-beta-factor]、[ExactBarBetaProjection][c5-beta-projection] | 関数型invariantの輸送条件と値の不変性の同値を、対象写像の冪等性と値域の全単射の単射性から本文内で導出。条件を明記してcoreと幾何の自己射を構成し、二番目の実経路で運んだ因子とcanonical mateの積としてβ・barβを定める。射影式までを本章で示し、射としての冪等性・可逆性分類・像の実現は第6章へ接続。分岐を有限アルゴリズムとは扱わない |

### 本文用の例と有限検算

Pythonの有限列挙で、本文の例と主要な式を次の範囲で検算した。

- Fiber productでは三点から二点へのsource写像と非自明なAtom置換を用い、二点のcone sourceからの全54coneについて、2,916候補の中の普遍射の一意性を確認。例5.3の二つのcompatible pairも確認した。
- 例5.20では、二つの平方が可換でも変更先の関係が破れることと、同じ非epiで関係が成立する対照を計算した。
- S3では、共役による標準比較・raw defectの対応と逆対応を1,296通りで確認。例5.23の(12)から(23)への対応も確認した。
- 例5.28では、二sourceとも前向き保存を満たし、反映条件がpartialで偽、allで真となることと、第二legによるcompatible pairの制限を確認した。
- 四状態の積lensで三法則16通り、移行と更新の可換性8通り、全4種類のview部分集合に対する12通りの制限後更新を確認した。
- 三source・三Atomで、正規化写像と述語表の13,824組を列挙し、正規化後に読むcodeが元の抽出と一致することを確認。そのうち8,704組は正規化が冪等ではない。

無限集合を使う例5.16・5.29は本文の集合論的な証明による。
有限検算は既存Lean package全体の再検証でも、一般定理の証明の代替でもない。
モノリスの分割とコードレビューの説明は応用可能性を示す例であり、実コードの評価結果は追加していない。

### 初稿の表示・引用と確認状態

全416式（本文内368・独立行48）をKaTeX 0.18.7で構文検査し、エラー・警告なし。
数式区切り、定義等40件・式番号48件、前章からの参照、内部資料への案内が本文にないことを確認した。
ローカルのMathMLプレビューで数式の認識と本文幅676pxでの表示を確認した。

Stacks §4.33の定義4.33.1・4.33.5–4.33.6、補題4.33.2・4.33.7を原典と照合した。
参照するのは強いcartesian射と引き戻しの標準構成であり、本章のBeck–Chevalley mateの
可逆性は、実際の再添字づけによる随伴同値から原稿内で証明している。
Lensとプロトコルは第1章の定義を使い、外部文献の引用範囲を追加していない。
文献確認記録の原稿hashには、第5章までの日本語原稿を掲載順に含めた。

2026-09-21、人間がモノリスの分割の例を含む原稿を確認し、PR作成を承認した。
GitHub上の表示確認とCIの対象commit・結果はPRに記録し、Claudeの独立レビューをPR上で受ける。

### 注文APIの説明の具体化

2026-09-21、人間の依頼に基づき、概要の注文APIの例を具体化した。
区分の `web` から `online` への変更と、101・103番の注文を残す二つの手順を表で示した。
絞り込みを前へ移して処理件数を減らす場面から、対応する選択条件を求める理由を説明した。
章末も同じ例に揃え、返る注文の一致から取消・金額チェックの対応へつなげた。
例5.35では、区分を読む・更新する積lensと、区分の更新で保つ内部フラグを説明し、
名前の対応とフラグの符号化を明示した。意味論の条件と全416式は保持した。
これは説明の改善であり、実際のAPIへの適用や性能測定を追加したものではない。
数式の内容・順序、定義等と式番号、引用の保持、参照・Unicodeと更新後のhashを確認した。

### モノリスの分割への例の変更

2026-09-21、人間が採用した方針に従い、導入とまとめを、注文処理と在庫管理を持つ
モノリスのサービス分割へ書き換えた。全体を分割してから注文取消の範囲を選ぶ経路と、
元の設計から同じ範囲を選んで同じ分割方針を適用する経路を比較する。
取消要求・在庫予約の解除・取消完了と、「取消完了なら対応する予約も解除済み」という
条件を例の中心に置き、在庫側の依存を比較範囲へ含める理由を記述した。

例5.3は設計資料・コードをsourceとする場合のreading指定へ接続し、例5.13は在庫予約の
対応の取り違えに変更した。例5.13の入替えを自己同型とする仮定は保持した。
命題5.36の説明では、adapterの自然性による実行の対応と、状態のLawの確認を分けた。
サービス分割の適用には、業務操作だけを読む場合と通信・失敗・再試行まで読む場合の
入力・保存条件をそれぞれ指定する。分割一般の正しさを主張する例とはしない。

例5.35は命題5.34を確認する独立した四状態の計算例とし、viewの名前を0・1とA・Bへ変更した。
全416式のうち、この名前に関する3式以外は内容・順序を保持した。
定義・命題・定理・補題・構成の本文と証明、番号、引用を差分で照合し、
四状態のlensの対応と制限後の更新、数式構文、参照・Unicode・公開情報・hashを確認した。
既存の形式化と証明範囲は変更していない。この修正を含む原稿について人間の確認とPR作成の承認を得た。

### PR #4836のレビューと採用した7件の改善

2026-09-21、[Claudeレビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4836#issuecomment-5754757670)は
`04754169df819fdd4f8f2212726610da7741a385` をapproveとし、任意提案3件を示した。
[別の内容レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4836#pullrequestreview-5262708668)も
同じcommitで修正必須の数学的な誤りを認めず、任意提案5件を示した。
両者は一次資料の照合と有限例の独立検算を行い、Claudeは全416式の構文とGitHub表示も確認した。
導入に関する重複をまとめ、人間が採用した次の7件を反映した。

1. §5.3に導入文と四頂点の対応表を加え、モノリスの分割と範囲の選択をD・Vへ対応づけた。頂点をdoctrineと選択sourceの組とし、sourceの範囲の選択とcore内のAtomの削除を区別した。
2. §5.4で、存在結果と有限表示の分類の関係、および§5.5から比較と診断へ戻る流れを説明した。
3. 命題5.19のepi条件を、実際に消去を使う指定面の始点へ限定した。本文の証明と、より広いsupportを使う既存Leanの条件の違いをC5-07へ記した。
4. 例5.35で、状態の対応hと選ぶ表示値W′の説明を二文に分けた。
5. 構成5.37に、逆経路の比較と、単位・比較・余単位を合成する端点付きの式を加えた。別のliftを選ぶ場合の二つの端点同型は、中央の比較の前後へ入れることを明記した。
6. 定義5.39の関数型invariantを値の不変性で記述し、全単射による輸送条件との同値性を本文内で証明した。使用する冪等性は対象写像のもので、次章の射としての冪等性を仮定していない。
7. §5.10の冒頭に、標準比較へ正規化を組み込み、表現の区別がどこまで残るかを調べる目的を置いた。

定義等40件の番号・見出しと、式番号5.1〜5.48の全数式を保持した。
新しい独立行の式3件は番号なしとし、全436式（本文内385・独立行51）の構文を
KaTeX 0.18.7で検査してエラー・警告なし。引用URLと引用内容は保持した。
Invariantの同値性は、対象数0〜4・値域の要素数0〜3の全4,430組の冪等写像・値関数と、
23,291通りの値域置換で検算した。輸送条件を満たす1,235通りすべてで値が不変であり、
逆向きも恒等の置換で成立する。単射性または冪等性を外した二つの反例も確認した。
この有限検算は本文の一般的な証明を補うものであり、新たなLean theoremは追加していない。

修正版に対する独立再レビューは未記録である。
数式のGitHub表示とCIは修正後のcommitで確認し、その結果をPRに記録する。

[c5-pullback]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/DoctrinePullback.lean
[c5-pointed]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/PointedDoctrinePullback.lean
[c5-cartesian]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean
[c5-global]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLift.lean
[c5-global-coherence]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLiftCoherence.lean
[c5-bc-mate]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMate.lean
[c5-bc-exactness]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactness.lean
[c5-transport-equiv]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/TransportEquivalence.lean
[c5-code]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/Schema.lean
[c5-coverage-schema]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageSchema.lean
[c5-coverage]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClassification.lean
[c5-diagram]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IndexedBaseDiagram.lean
[c5-assembly]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticAssembly.lean
[c5-raw-family]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IndexedRawFamilyClassification.lean
[c5-endpoint]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/EndpointExactness.lean
[c5-coherence]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/CoherenceExactness.lean
[c5-obstruction]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/ObstructionExactness.lean
[c5-orbit]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/OrbitExactness.lean
[c5-realized]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/RealizedSupport.lean
[c5-ref-projection]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Projection.lean
[c5-qualification]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Qualification.lean
[c5-ref-configuration]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Configuration.lean
[c5-regime]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Regime.lean
[c5-ref-mate]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Mate.lean
[c5-ref-witnesses]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Witnesses.lean
[c5-ref-geometry]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementGeometry.lean
[c5-upper-cleavage]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean
[c5-upper-realization]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageRealization.lean
[c5-upper-mate]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMate.lean
[c5-compatible-input]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleInput.lean
[c5-upper-problem]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperRefinementBCProblem.lean
[c5-compatible-natural]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleMateNaturality.lean
[c5-compatible-global]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleGlobalMate.lean
[c5-solution-contracts]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSolutionContracts.lean
[c5-solution-equiv]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSolutionEquivalence.lean
[c5-derived-mate]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedMateComposite.lean
[c5-alpha-triangle]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedBarAlphaTriangle.lean
[c5-alpha-projection]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedBarAlphaProjection.lean
[c5-normalization]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalization.lean
[c5-geom-normalization]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalization.lean
[c5-beta-factor]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaFactorization.lean
[c5-beta-projection]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaProjection.lean

### PR #4836のマージ確認

2026-09-21、人間による第5章のマージを確認した。修正版のheadは
`32e12f8c8685f2fc04c0085ff6b610696b6f87a2`、merge commitは
`ccdfd313e12d64d17ecfe2f16fd460bf8b121310` である。
同PRの7件のCIはすべて成功している。GitHubの表示確認はPRの記録を参照する。
修正版の独立再レビューとは区別し、原稿と採用済み修正の人間による確認・マージを記録する。

## 第6章「冪等正規化と実現」

2026-09-21、第5章を含む固定版
[12884419d705624be39e8a87393ed50385395469](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/tree/12884419d705624be39e8a87393ed50385395469)
の一次資料と、第1〜5章の原稿を照合して[日本語初稿](ja/09-idempotent-normalization.md)を作成した。
以下の一次資料の相対リンクは、この固定版で照合したファイルを示す。
初稿のSHA-256は `3a8f382b2cde88bd011eefe3698daa1bd1e7946bc30464a343891e5afbee891d`。
確認者はCodex（GPT-6）である。

構成6.1〜命題6.31と式6.1〜6.48を置き、必要な定義・仮定・証明を原稿内に記述した。
内部資料への案内とLean宣言との対応は本記録に置く。
既存Lean sourceは条件・結論・証明の照合に使い、変更・ローカル再検証は行っていない。

| ID | 原稿の箇所 | 入力・成立条件 | 確認した一次資料 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- |
| C6-01 | 構成6.1–例6.4 | 対象形成のconfiguration保存、全architecture object、任意の値集合 | [ConfigurationDescent][c6-descent] | 射影とsection、固定点とconfigurationの対応、商、正規化で不変な写像の一意因子化を証明。四対象のモデルはこの集合上の構成を説明する本文用の例 |
| C6-02 | 定理6.5 | 定義5.39のAd。型の等号に沿うoperation写像 | [Core normalization][c6-core-normalization]、[IdempotentExchangeNormalization][c6-idempotence] | 対象だけでなく、operation・底・文脈・方程式・invariant・signatureを含む射全体の冪等性を証明。任意の選択同型を型の同一視と扱わない |
| C6-03 | 補題6.6 | 任意のcore射の対象形成・configuration保存。Adは不要 | [CanonicalObjectNormalizationNaturality][c6-object-naturality] | 対象写像の自然性を導き、operationまで含む自然性の条件と分ける |
| C6-04 | 命題6.7・定理6.8 | 任意のconfiguration上の全architecture object。Core内の分裂は両射がcore射であることを要求 | [DistinctArchitectureObjects][c6-distinct]、[InternalNormalizationSplitNoGo][c6-no-split] | 一元型・二元型の対象から非単射性を示す。仮想的なsectionの単射性と対象自然性から、全対象が固定点になる矛盾を導く |
| C6-05 | 定義6.9–例6.13 | 任意の圏、同型α、冪等射d | [RawFailureLocus][c6-raw-failure]、[Karoubi image][c6-image] | 冪等完備化・分裂を定義から説明。β=dα、e=α⁻¹dα、γ=α⁻¹dについて両側逆を計算し、元の圏の可逆性と像の同型を区別。四点の例は本文で追加した有限集合の計算 |
| C6-06 | 定理6.14・命題6.22 | Adを満たすcoreを持つ完全幾何と、その充満部分圏の全射 | [CanonicalNormalization][c6-geom-normalization] | Coreと被覆・overlap・係数・support・軸・observable・raw systemを含めて冪等性と片側吸収を確認。正規化関手の充満性、coreへの射影、底・係数の保存を証明 |
| C6-07 | 補題6.15 | 同じ再添字づけから生成したexactな輸送・引き戻しと実際のlift | [ExactNormalizationNaturality][c6-exact-naturality] | Adの保存とoperationの同一視の整合からliftとの交換を証明し、普遍性から正規化射の輸送を同定。任意のcore射の両側自然性へは拡張しない |
| C6-08 | 定理6.16 | 構成5.37・5.40の共通square・面・cochain・source core・係数・完全幾何 | [ExactDerivedBarAlphaTriangle][c6-alpha-triangle]、[ExactBarAlphaNormalizationNaturality][c6-alpha-naturality]、[ExactBarBetaFactorization][c6-beta-factor]、[ExactBarBetaClassification][c6-beta-classification] | 同じ生成比較の冪等分解・可逆性分類・像の同型を証明。χのとき両端の冪等射をcanonical正規化へ同定。恒等でない診断だけから正規化の許容性や診断の消滅を主張しない |
| C6-09 | 命題6.17 | 第5章の端点同型と、同じsourceの正規化 | [ExactBarBetaProjection][c6-beta-projection]、[G116KaroubiPlacement][c6-placement] | 標準比較・二冪等射・生成比較のcore射影を照合。Karoubi内の端点同型は冪等射を合成したe j_D・E j_Vとして与える |
| C6-10 | 例6.18 | 一Atom・一source、二つの選択軸、configurationのHomをoperationとするcore、空の方程式・invariant添字 | 第1章の定義1.6・1.7・1.10・1.12・1.17・1.25・1.28と定理6.16。[ExactBarBetaFiniteWitness][c6-beta-witness]の補助幾何の構成も照合 | 本文用に恒等な底の平方と非自明な軸交換を用いる別の入力を構成。文脈・環・detector・raw座標・関係・制限を指定。既存Leanの固定axis-fold witnessそのものを引用したとは扱わず、新しい入力から本文内で非可逆性を導く |
| C6-11 | 補題6.19–定理6.21 | Ad coreの充満部分圏、全てのcore射 | [CanonicalNormalizationAbsorption][c6-absorption]、[NormalizationCategory][c6-category]、[NormalizationProjection][c6-projection] | N_Q f N_P=f N_Pを全成分で示す。Sandwich条件を満たす射の圏、恒等射N_P、充満関手f↦f N_Pを構成 |
| C6-12 | 命題6.23・命題6.24 | 同じ充満部分圏。正規化のoperation写像を固定 | [NormalizationNaturalityFailure][c6-naturality-failure]、[ModificationBlocker][c6-operation-coherence] | Karoubi内の包含の自然性を片側吸収から証明。逆方向の族の自然性をf N_P=N_Q f、さらにoperation成分の等式と同値とする |
| C6-13 | 例6.25 | 例6.18をHom×Boolのoperationへ拡張。元の対象に依存するBool反転 | [ModificationCounterexample][c6-counterexample]、[NormalizationNaturalityFailure][c6-naturality-failure] | 型の違いを使う既存反例の仕組みを、本文のcore上に構成。f²=1、fN=N、Nf≠fNを示す。f≠1とfN=Nから正規化関手の非忠実性も本文内で導く |
| C6-14 | 定義6.26–命題6.28 | 任意の圏と関手、三段の射影 | [KaroubiArrowEquivalence][c6-arrow-equivalence]、[FunctorNaturality][c6-functor-naturality]、[ThreeStageProjection][c6-three-stage] | 冪等平方(c,e,d)をdceへ送る関手と逆を構成。往復の同型・自然性、関手への適合と射影の合成を成分で証明 |
| C6-15 | 構成6.29 | 比較の圏の全対象、同型の端点変更 | [MaximalSubgroupoid][c6-groupoid]、[G116KaroubiPlacement][c6-placement] | 非可逆な比較も対象に残す最大亜群を説明。J(β)と像の間のβの端点と恒等射を区別 |
| C6-16 | 例6.30と直後の一般形・命題6.31 | 固定viewのlens三法則と有限な基準fiber、有限状態のプロトコル実現、実行・観測を保つ冪等adapter | 第1章の定義1.32・命題1.33・命題1.34・定義1.36・命題1.38 | Lensの四状態から二状態への射を検算。さらに積表示で自己射を(v,k)↦(v,t(k))と書き、tの固定点から同じLensの圏内で任意の冪等射を分裂させる。プロトコルは固定点集合を実行・観測へ制限し、二つの意味保存adapterの分裂を直接証明。状態ごとの冪等性だけでは実行が閉じない反例を付す。本文で証明した帰結であり、同じCS命題のLean形式化完了とは記録しない |

### 初稿の検証と確認範囲

- 原稿を通読し、対象の正規化、射全体の冪等性、元の圏内の非分裂、Karoubi内の像、正規化関手を区別した。Overview・節の導入・章末のまとめを置き、モノリス分割後の設計比較と、実装方式による操作ラベルの違いへ戻る説明を加えた。
- Configuration descentは、対象数0〜4・configuration数0〜3の全151組の全射・sectionについて、値域の要素数0〜3の12,974通りの読み取りを列挙し、一意因子化との同値を確認した。
- 要素数0〜4の全1,052組の全単射・冪等写像について、βの可逆性分類、共役の冪等性、像の間の二つの合成を確認した。例6.13の表も同じ計算で確認した。
- 端点集合の要素数0〜3の冪等平方835件と、端点の要素数0〜2のsandwich条件を満たす可換平方1,273件で、Karoubiと射の圏の往復・端点の同型を確認した。
- 例6.25の二対象・二種類の印の有限部分で全8操作を検算し、二つの順序で印が0と1に分かれること、片側吸収と正規化後の射の一致を確認した。これを全architecture objectのLean検証とは扱わない。
- Lensの全4状態と2更新値で三法則・射の条件・固定点の閉性を確認した。一頂点・一操作、状態数0〜3、定値の観測先への二値観測で、自然性と観測保存を満たす249組の遷移・冪等写像・観測を列挙し、像の実行・観測と分裂を確認した。非自然な交換操作・定値正規化の反例も検算した。
- 全425式（本文内375・独立行50）をKaTeX 0.18.7で検査し、構文エラー・警告はない。ローカルのMathMLプレビューで式の個数・表示幅と、主要式・表・本文の表示を確認した。GitHubファイルプレビューとPRの描画済み差分での確認は、PR作成後に行う。
- 番号、章間の参照、リンク、空白・不可視文字・公開資料向けの検査、原稿と文献確認表のhashを確認した。参考文献4件の引用文・書誌は変更せず、原稿一式のhashに第6章を含めた。

上記の有限検算は、本文の一般的な証明を補助する。一回限りの検査を恒久CIへ追加していない。
人間が原稿を確認し、PR作成を承認した。確認済みの原稿を保持してPRを作成し、
GitHub表示確認とCIの対象commit・結果をPRに記録する。Claudeの独立レビューはPR上で行う。

### PR #4839の独立レビューと採用済み修正

2026-09-21、commit `fea1ddad9a23bab0e8cb0681550ccdafa2dc7a7c` に対する
[Claudeレビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4839#issuecomment-5755976525)はapproveとした。
全31項目の証明、一次資料との対応、全425式の構文とGitHub表示、六系統の有限検算と件数を独立に確認している。
[別の内容レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4839#pullrequestreview-5263374743)も、
確認した範囲で修正必須の数学的誤りはないとした。一次資料の確認範囲は四ファイルであり、
全27ファイルの監査・Lean再ビルド・GitHub表示の再確認は含まない。
両レビューの任意提案は計8件で、例6.18への2案を一緒に扱う7項目を人間が採用した。

| 採用項目 | 反映内容 |
| --- | --- |
| 式6.3の向き | 固定点からconfigurationへの射影と、その逆の選択を、定義域・値域を持つ二つの矢印で表示 |
| 定理6.3への呼称 | 「この命題」を「この定理」へ統一 |
| 命題6.7の型と値 | 量の型を一元集合、値をその唯一の元として明記 |
| 定理6.16の意味 | 共役で得た始点の冪等射が、終点で独立に定まる正規化と一致することを説明 |
| 例6.18の読み順 | 非恒等な入力を作る軸交換と、対象表現をまとめる正規化の役割を先に説明。Coreと幾何の全データを箇条書きで整理 |
| 定理6.27の図 | [図6.1](figures/ch06-karoubi-arrow.svg)で、冪等な可換平方から両端の像の間の射dceへの対応を表示。左側の可換性dc=ceと、像の射の条件を区別 |
| Lensの一般形 | 第1章の命題1.33・1.34から、固定view・有限な基準fiberのLensの圏で任意の冪等射が分裂することを証明。四状態の具体例も保持 |

修正版の原稿SHA-256は `8a9ac9608fcca6ea6879f303be23d9117c75bf85b70c851ddaa4c8796efda906`。
図6.1の編集元SVGのSHA-256は `6e37897fd7912478b5b3391100dead8fa1eb3c8318759bfd97e2519a197dae4a`。
定義等31件と番号付き48式を保持し、追加したLensの一般形は本文の証明として記録する。
Lean実装や、その形式化済み範囲は変更していない。

- Lensの追加検算では、viewの要素数1〜3、基準fiberの要素数0〜4について全168組の冪等写像から分裂を構成し、読取り・更新の保存、両合成、基準fiberの有限性を確認した。元の状態を整数ラベルへ置き換え、積表示を通して射を戻す場合も検算した。
- 別に、viewの要素数1〜2、基準fiberの要素数0〜3で、読取りを保つ全780状態写像を列挙した。更新も保つ66写像が積表示(v,k)↦(v,t(k))を持つこと、そのうち冪等な30写像がtの冪等性と対応することを確認した。これらは一般証明を補助する有限検算である。
- 全451式（本文内399・独立行52）をKaTeX 0.18.7で検査し、構文エラー・警告なし。番号・章間参照・リンク、原稿と文献表のhash、空白・不可視文字・公開資料向けの検査を確認した。図6.1はSVGの構文、矢印の向きとラベルを式(6.42)の構成と照合した。既存4文献の書誌・引用内容は保持し、一般形は第1章の結果から本文内で導く。

修正後のGitHubファイルプレビュー・描画済み差分・図6.1とCIの対象commit・結果はPRに記録する。
初稿へのapproveと、修正版への独立再レビュー・人間による最終差分確認・マージを区別する。

[c6-descent]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ConfigurationDescent.lean
[c6-core-normalization]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalization.lean
[c6-idempotence]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeNormalization.lean
[c6-object-naturality]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/CanonicalObjectNormalizationNaturality.lean
[c6-distinct]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/DistinctArchitectureObjects.lean
[c6-no-split]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/InternalNormalizationSplitNoGo.lean
[c6-raw-failure]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeRawFailureLocus.lean
[c6-image]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeKaroubiImage.lean
[c6-geom-normalization]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalization.lean
[c6-exact-naturality]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactNormalizationNaturality.lean
[c6-alpha-triangle]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedBarAlphaTriangle.lean
[c6-alpha-naturality]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarAlphaNormalizationNaturality.lean
[c6-beta-factor]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaFactorization.lean
[c6-beta-classification]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaClassification.lean
[c6-beta-projection]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaProjection.lean
[c6-beta-witness]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaFiniteWitness.lean
[c6-absorption]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/CanonicalNormalizationAbsorption.lean
[c6-category]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationCategory.lean
[c6-projection]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationProjection.lean
[c6-naturality-failure]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationNaturalityFailure.lean
[c6-operation-coherence]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorModificationBlocker.lean
[c6-counterexample]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorModificationCounterexample.lean
[c6-arrow-equivalence]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/KaroubiArrowEquivalence.lean
[c6-functor-naturality]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/FunctorNaturality.lean
[c6-three-stage]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/ThreeStageProjection.lean
[c6-groupoid]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/MaximalSubgroupoid.lean
[c6-placement]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/G116KaroubiPlacement.lean
