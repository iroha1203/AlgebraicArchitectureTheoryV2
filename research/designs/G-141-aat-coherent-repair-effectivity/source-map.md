# G-141の条項・原始構成・source対応

## 固定targetとの対応

[固定target](../../goals/G-141-aat-coherent-repair-effectivity.md)のA–Hを次の構成で証明する。全変更・補完・移送はG-140の独立なfiberを使用し、複体の零性だけを別の「変更」の定義にしない。

| target | 本文 | 構成と証明 |
| --- | --- | --- |
| A 原始fragmentと実制限 | [A1](fragments-and-adapters.md) | 全field・totality block・全syzygyの有限support、実際の射の制限 |
| A 大域複体と `Rlim` | [A2–A3](fragments-and-adapters.md) | labelごとのcoinduced diagram、積、Roos複体、Milnor列、MLの放電条件 |
| A 任意の小さい加法作用diagram | [A4–A5](fragments-and-adapters.md) | 全translation・推移的public作用から全Hom分類、adapter合成則、全chain |
| A 任意moduleと係数変更 | [A5](fragments-and-adapters.md) | 自由表示とcokernel、有限projectiveの場合の双対、native `Z` |
| B 無限整数adapterと全変更scheme | [B1–B2](telescope-and-extension.md) | 全 `u_t` とflip、全係数列、有限段 `A¹` と実制限、斉次群 |
| B Telescope・cotangent・平方零 | [B3–B4](telescope-and-extension.md) | 直和の自由分解、全積の実Law複体、filtered colimit、同じ補正式 |
| B 実拡大とExt類 | [B5](telescope-and-extension.md) | 原始 `a_n` から `E_a`、flat quotient、retraction、Sym、Yoneda類 |
| C 全有限段と大域不存在 | [C1](local-obstruction.md) | 後向き整数解、全 `4^m` の割切りによる矛盾 |
| C Zariski・2進・有理の同じ類 | [C2–C4](local-obstruction.md) | `D(2),D(3)` の全解、差 `−1/3`、局所化の完全列、2進和 |
| C 実際の微小liftと係数比較 | [C5–C6](local-obstruction.md) | 普遍 `d` の平方零fiber、同じ `[a]`、有限smooth性、無限積とtensor |
| C 有限図式・固定長経路・移送のdescent | [C7–C8](descent-and-selection.md) | 全頂点・実map・翻訳・同型・cocycleの貼合せ、全修復と自己同型 |
| C 有限étale選択 | [C9](descent-and-selection.md) | `z²=t` の有限free・étale・torsor、局所比、coboundary、section不存在 |
| D MLと有効有限還元の区別 | [D1–D3](effective-solving.md) | 有限構文compiler、有限seedと代入のideal安定化、周期certificate |
| D 有限体・整数・有理affineの全解 | [D4](effective-solving.md) | 全列挙、Gaussian/Smith、可逆変形と不存在certificate、原始mapの復元 |
| D 多項式・所属locus・実像 | [D5–D6](effective-solving.md) | 逆元変数、Gröbner所属証拠、特殊化の層別、開条件分岐、全fiber |
| D 四分類と実witness | [D7](effective-solving.md) | 原始成立集合または全補完familyの像、Chevalley、空実現の区別 |
| D 有限候補でも停止不能 | [D8](effective-solving.md) | `F₂` の `a_nc=0`、未検査位置、停止問題、有限生成性の限界 |
| E Smooth ambient・全syzygy | [E1–E2](obstruction-complexes.md) | 原始GrassmannianとHom bundle、冪等元lift、conormalの全関係 |
| E 零性・全lift・cotangent | [E3–E4](obstruction-complexes.md) | Taylor差、実Lawful lift、全補正torsor、単一chartによらない比較 |
| E 指定観測liftの相対障害 | [E5](obstruction-complexes.md) | compatible graph ambient、cone、Law残差と像の差、同じliftの回復 |
| E Affine・還元自己同型 | [E6](obstruction-complexes.md)、[A1](fragments-and-adapters.md) | affine二項複体、平方零の `1+A`、適用域の区別 |
| E 合法な制限・Čech・syzygy | [E7–E8](descent-and-selection.md) | 全参照support、full simplex収縮、kernelへの実残差、細分化 |
| E 普遍conormalと忘却の差 | [E6](obstruction-complexes.md) | 評価前の `J/J²`、局所化と層化、`κ`、`xy−1` の忘却不能 |
| F 定義的消去・全Artin判定 | [F1–F3](artin-detection.md) | 同じ型・生成元、閉埋込み、普遍Artin商、Krull交叉、局所同型 |
| F 初回障害と共有演算 | [F4–F5](artin-detection.md) | `κ_u`、`ν=1` と `ν≥2` の区別、二contextの同じ差 |
| F 表示・合成・pointed Real | [F6](artin-detection.md) | 同じideal、合成の最小次数、生成元atlas、全相対groupoid |
| F 上界・係数変更・jet比較 | [F7–F9](artin-detection.md) | 自由chartの構文次数、tensor後の像、全Artinとjet functorの量化 |
| F 部分変更・全環座標面ideal | [F10–F11](interaction-families.md) | 原始 `h,τ`、零化図式、単項式basis、普遍tuple |
| F 極小不成立・補正・Boolean | [F12–F13](interaction-families.md) | 相殺後support、実制限と不存在、直交冪等元、一意lift |
| G 実adapter・層・全context | [G1–G3](graph-repair.md) | 固定 `p` の全係数、実交差、transition、State、生成topology |
| G SAGA・Part IV・全修復 | [G4–G5](graph-repair.md) | LiftFiberDataの各条件、全添字の空交差、向き `T`、実section、許容域 |
| H1–H3 | [H1–H3](witnesses.md) | 全許容修復、冗長Lawの全syzygy、同じ支持と異なる障害 |
| H4–H7 | [H4–H7](witnesses.md) | 二context、任意の高次数、非flat特殊化、無限Artin反例 |
| H8–H9 | [H8–H9](witnesses.md) | 三角形の全修復とholonomy、四分類の全fiber |
| H Snapshot・評価・変更追加 | [H10–H11](witnesses.md) | `μδ`、指定lift、同じread差、`ρ` の全解と `G_m²` |
| H 拡張した操作言語 | [H12](witnesses.md) | 実 `g_1`、phase閉性の失敗、runtime引数compactの非可換 |

## 先行する紙上証明・原始仕様

| source | 使用箇所 |
| --- | --- |
| [G-139 原始意味](../G-139-aat-law-generated-relative-geometry/primitive-semantics.md) | A・C：独立な対象・全構造保存map・原始参照 |
| [G-139 多項式実現](../G-139-aat-law-generated-relative-geometry/polynomial-realizations.md) | E・F：marked実現schemeと全R点、G：全contextの点supportとrestriction |
| [G-139 descent](../G-139-aat-law-generated-relative-geometry/descent-and-algebraicity.md) | C・E・F：生成付きmodule、全Homの有効descent、frameとatlas |
| [G-140 意味保存射](../G-140-aat-semantic-change-category/semantic-morphisms.md) | A・D・G：全実map、原始操作から全語への帰納法、商環のideal所属 |
| [G-140 条件付き変更](../G-140-aat-semantic-change-category/conditional-changes.md) | D・F・H：原始許容規則、探索fiber、共有候補、固定Rと全係数の量化 |
| [G-140 図式・経路・移送](../G-140-aat-semantic-change-category/diagrams-paths-transfer.md) | C：実際の全補完、指定部分の同型、固定長経路、状態移送 |
| [G-140 native比較](../G-140-aat-semantic-change-category/native-comparisons.md) | A・B：全translation分類と整数adapterの原始操作 |
| [G-140 台帳](../G-140-aat-semantic-change-category/ledger-specialization.md) | G・H：固定 `p` のmarked同型、同じsnapshot・phase・原始式・翻訳 |
| [n1019 §6–8](../../../docs/note/n1019_shigure_representability_design.md) | 原始adapter、条件付きfiber、無限fragmentと有限判定の問題 |
| [n1020 §13・15・16](../../../docs/note/n1020_shigure_polynomial_specializations.md) | lift・全Artin・局所修復、指定台帳・graph・評価例 |

## 既存Leanへの具体的な接続

以下は参照する既存APIと、本稿で新たに証明する比較の対応である。新しい紙上証明のLean形式化を示す一覧ではない。

| source | 既存の宣言・field | 本稿の構成 |
| --- | --- | --- |
| [Site/Geometry](../../../Formal/AG/Site/Geometry.lean) | `AATSite.category`、`topology` | G3：全contextの点supportの内部から係数を生成 |
| [Site/ContextCategory](../../../Formal/AG/Site/ContextCategory.lean) | `contextMorphismPreorderCategory` | G3：実support mapの包含、thin性によるmonomorphism |
| [Site/Coverage](../../../Formal/AG/Site/Coverage.lean)、[Site/Topology](../../../Formal/AG/Site/Topology.lean) | `CoverageRequirements`、`AdmissibleCover`、`generate_mem` | G3：全点supportで被覆性を放電、実productのopen交差 |
| [Saga/Cover](../../../Formal/AG/SemanticRepair/Saga/Cover.lean) | `MonomorphicOrderedCover`、`TopologicalMonomorphicCover` | G3：全pair・triple、射影・lift、省略指定、topologyへの所属 |
| [Saga/EquationLift](../../../Formal/AG/SemanticRepair/Saga/EquationLift.lean) | `LiftFiberData`、`liftSystem`、`AffineCoefficientLiftSystem`、`CoefficientLiftAtlas`、`residualClass_isZero_iff_matching_correction` | G4–G5：同じ層の完全列、実局所操作、右−左の差、引く補正と貼合せ |
| [Saga/PartIVBridge](../../../Formal/AG/SemanticRepair/Saga/PartIVBridge.lean) | `SitePresheafData.ofObstructionSheaf`、`incToCoverRelativeH1`、相互逆比較 | G4：同じObと制限、全添字の省略交差が零、指定類の輸送 |
| [Conormal/LawGeneratedIdealPowerShortExact](../../../Formal/AG/SemanticRepair/Conormal/LawGeneratedIdealPowerShortExact.lean) | `Raw.shortComplex` | E6：評価前の普遍Law ideal、`(J²)_s=(J_s)²`、同じ `κ` |
| [ResolutionInvariance/LawGeneratedComplex](../../lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean) | `TargetSupportedNerve`、`edgeSupport`、`faceSupport` | E8・G4：実supportの交差とincidence、係数・微分の追加比較 |

## 仮定が使われる箇所

| 条件 | 使用と原始dataからの確認 |
| --- | --- |
| 任意可換環・零環 | Bの全R表示、F1・F8・F11・F13、Gの全式。非零性を使う点の区別はHで明示 |
| 全translation・非空推移的public作用 | A4・B1の全Homがtranslationであること。単一の `u_1` のみには弱めない |
| 全積cochain・有限参照・回復可能なblock | A2の導来逆極限と、得た解を実際のmapへ戻す比較 |
| 可算cofinal tower・ML | A3のMilnor列・vanishing。有限段の決定はDで別に構成 |
| Lawful基準・平方零kernel | E2–E5の全syzygy、Taylor、相対障害。一般affine修復は二項複体を用いる |
| Affine式・原始加法作用 | E6・C8・A4・G5の有限変位。一般の有限自己同型群を加法群に置換しない |
| 有限projective ambient data | E1の独立なambient lift、E4の次数0・1のcotangent計算 |
| Noetherian係数・有限表示 | E4のHom局所化、F2の普遍Artin商とF3のKrull交叉 |
| 自由な観測chart | F7の構文次数上界。既存Lawを持つ観測環はH5で区別 |
| Labelと零化図式 | F11の座標面判定。一般座標変更ではこの図式も運ぶ |
| 有限候補の有効生成・全Lawとの同値 | D1–D2の全解算法。D8は候補数だけでは足りない反例 |
| 有効な係数域 | D4の有限体・Z・Q、D5–D6のQ上の多項式計算。一般Noetherian基底の構成可能性と分離 |
| 幾何点と有限型 | D7の構成可能像の全fiber、field拡大と四分類。指定R点の量化はG-140 E |
| 全参照を含む宣言cover | E7–E8・C7–C8の合法制限と実貼合せ。観測を分解して別の式へ変えない |
| 同じ実層と全交差 | G3–G5のSAGA・Part IV比較、零類から実操作への回復 |
| 固定 `p`・全domain・語翻訳・許容規則 | G・Hの台帳比較。旧Busy Lawを保持する規則と編集できる規則を区別 |

## 標準数学への依存

本文は、自由代数・module表示・商の普遍性、有限構文の帰納法、有限変数多項式のNoetherian性、加群・層・複体の基本完全列を用いる。次の標準結果へ接続する際も、原始残差・指定類・全解のmapは本文で構成したものを使う。

- [導来逆極限, Stacks 07KV](https://stacks.math.columbia.edu/tag/07KV)：A3・B3。積の `1−shift` とその長完全列。
- [Cotangentの自由分解とfiltered colimit, Stacks 08PL](https://stacks.math.columbia.edu/tag/08PL)：B4・E4。有限段の実微分 `×2` と原始Lawの関係を運ぶ。
- [平方零変形, Stacks 08S3](https://stacks.math.columbia.edu/tag/08S3)：E3–E4。conormal評価 `κ` と標準障害の同定。
- [Krull交叉, Stacks 00IP](https://stacks.math.columbia.edu/tag/00IP)：F3。Noetherian局所環での `∩m^n=0`。
- [冪等元のlift, Stacks 00J9](https://stacks.math.columbia.edu/tag/00J9)：F13。Boolean分解の一意lift。E1のmatrix liftは同じ多項式をmatrixへ直接適用。
- [Chevalley, Stacks 054K](https://stacks.math.columbia.edu/tag/054K)：D7。有限型射による構成可能集合の像。
- [Nullstellensatz, Stacks 00FS](https://stacks.math.columbia.edu/tag/00FS)：D5–D7。幾何的空性とunit ideal、非空fiberの残留体witness。
- [de Fernex–Ein–Ishii, Jet closures and the local isomorphism problem](https://arxiv.org/abs/1704.07494)：F9。jet試験と全局所Artin試験の比較対象を区別する。

G-139・G-140に依存する箇所は、それぞれの紙上証明に記した標準descent・表現結果への依存も引き継ぐ。本稿の有限算法は数学的な構成と停止性の証明であり、算法を実装したソフトウェアの実行記録ではない。
