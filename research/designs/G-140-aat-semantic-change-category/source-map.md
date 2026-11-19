# 固定target・原始source・仮定の対応

## 固定targetへの対応

| [G-140](../../goals/G-140-aat-semantic-change-category.md) の条項 | 紙上証明 | 結論を与える構成 |
| --- | --- | --- |
| A 実際の全sort map、非可逆射、観測 | [A1–A2](semantic-morphisms.md) | 全原始保存式と有限語・termの帰納法 |
| A traceとの区別、観測強化 | [A2.1–A2.2](semantic-morphisms.md) | 定値観測と交換操作の反例、同じmapによる包含 |
| A 型・phase・stuttering・翻訳合成 | [A3](semantic-morphisms.md) | 型付き有限syntaxの代入、domainの反復pullback |
| B 全係数の全Homとnative比較 | [B3–B3.1](geometry-and-descent.md) | copying全profile、全matrix・module表示、指定regular解釈 |
| B quantity引戻し・対応、端点だけの不足 | [B3.1](geometry-and-descent.md) | 同じmapへのquantity合成、G-139の対応 `Z_h`、二元集合の四map |
| B 非可逆射のnerve、Segal、coherence | [B1](semantic-morphisms.md) | 全矢印列とつなぎ同型、strictification、tupleの結合 |
| B 表示同型・定義的演算の追加消去 | [B2](semantic-morphisms.md) | 値とpartial domainをtermで一意に定義し、全Homを保存 |
| B Lawful状態への因子分解、合成 | [B4](geometry-and-descent.md) | 商環の普遍性、原始代入、ideal包含の合成 |
| B 開条件とwitness商 | [B4.1–B4.2](geometry-and-descent.md) | `y∈(ay)⇔a` unit、導出witnessとambient代表の両方の商 |
| C 原始supportからの文脈cover | [C1–C2](geometry-and-descent.md) | 参照閉包、Law・witness・全行block、fieldごとのassembly |
| C 係数descentと制限の交換 | [C3–C3.1](geometry-and-descent.md) | QCの全map、冪等分割による構文選択、忠実平坦な等式検査 |
| C 平方零lift・組立て・fragment延長 | [C4](geometry-and-descent.md) | 三つの制限mapのfiber、全false行と無限supportの反例 |
| D 全lens・protocol Hom、G-124 query | [D1–D2](native-comparisons.md) | hidden mapの分類、全自然変換、同じgraphと二query合成 |
| D 非可逆lens射 | [D1](native-comparisons.md) | `K×Bool→Bool`、全Hom分類、copyingへの輸送 |
| D G-126と指定adapterの比較 | [D3–D4](native-comparisons.md) | 共通behavior上端の区間、漸化式fiber、整数上の反証 |
| E 原始規則と全候補、評価fiber | [E1–E2](conditional-changes.md) | 全actual map・固定部分・補助選択、実評価と部分関手への引戻し |
| E 自然性、source変更、併用と合成、順位 | [E2.1–E2.2](conditional-changes.md) | 同じtuple、規則の輸送、別々のfiber、順序保存・反映 |
| E 共通readingと `E_ok,E_exists` | [E3](conditional-changes.md) | 原始reading、共有規則・補助選択、全解fiberの保持 |
| E 三量化と非空性 | [E4](conditional-changes.md) | 共通witnessによる含意、二元対角反例、空fiberの計算 |
| E 全係数自然なrobust条件 | [E5–E5.1](conditional-changes.md) | 環射の合成、恒等射への制限、`F_p[t]` 反例、reading比較 |
| F 全図式補完と2-fiber | [F1](diagrams-paths-transfer.md) | 各頂点・全射・恒等合成式・固定部分の自然同型 |
| F 四角形、鎖、自然性、有限表示 | [F1.1–F1.2](diagrams-paths-transfer.md) | 指定forkの保持、原始式compiler、有効有限還元とwitness商 |
| F 許容経路・連結・細分化 | [F2–F3](diagrams-paths-transfer.md) | 一段候補の2-fiber列、つなぎ同型、実際の合成へのfiber |
| F 係数曲線との違い | [F3.1](diagrams-paths-transfer.md) | `A¹` と恒等だけの一段規則 |
| G 合法状態liftと全共通語 | [G1–G2](diagrams-paths-transfer.md) | `hm=ι` の全fiber、全prefixのdomain、語保存への代入 |
| G 旧語のliftと移送合成 | [G2–G3](diagrams-paths-transfer.md) | 翻訳preimageの全候補、開始域のpullback、三つ組の結合 |
| P 原始Atom・rank変更・affine term | [P0–P0.1](ledger-specialization.md) | 同じ五座標、直和上の加法、構文帰納法、比較matrix |
| P1 全原子語、`SL₂×A¹`、marked fiber | [P1–P1.2](ledger-specialization.md) | `pi=id,pj=0`、明示逆matrix、kernel座標、三コピー |
| P2 途中read | [P2](ledger-specialization.md) | `Q,λ=1/2,u=2` の中間値 |
| P3 snapshotの必要十分性 | [P3–P3.1](ledger-specialization.md) | Busy不変量のpullback、指定domainの閉性、ambientとの比較 |
| P4 compactと修正版 | [P2.1、P4](ledger-specialization.md) | `t=C` の代入、translationとの違い、旧合法状態の包含 |
| P5 原式・四flag経路・Busy反例 | [P5–P5.3](ledger-specialization.md) | `g_ρ` の導出、八係数点、Idleでの切替domain、Busy残差 `−1` |
| E・P 指定評価と型reading | [P6–P7](ledger-specialization.md) | unit局所化、固定Lawの相違、同じraw構文の評価差 |

## 先行構成と既存Lean

新しい同値・fiber・descent・台帳特殊化は本稿の紙上証明である。次の既存宣言を参照したことは、G-140の新しい結論がLeanで証明済みであることを意味しない。

| source | 使用する既存の内容 | 本稿での接続 |
| --- | --- | --- |
| [G-139 紙上証明](../G-139-aat-law-generated-relative-geometry/README.md) | Nの原始意味・全copying Hom、A–Dのquantity・係数descent、Pの多項式実現 | B3の全変更表示、Cの対象・全map、P0の同じ入力 |
| [G-139 source対応](../G-139-aat-law-generated-relative-geometry/source-map.md) | Atom・Configuration・ArchitectureObject・context・Equationの宣言対応 | 原始field・参照・値・Lawを維持した比較 |
| [GeneralRelativeLens](../../lean/ResearchLean/AG/RealizationReconstruction/GeneralRelativeLens.lean) | `productEquiv`、`normalForm`、`productMap` | D1の全hidden mapと合成、非可逆射、係数化 |
| [IndependentProtocolPrimitiveReconstruction](../../lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentProtocolPrimitiveReconstruction.lean) | 頂点・path・自然変換の原始readingとassembly | D2の全Homと観測slice |
| [IndependentCarrierGraphReadings](../../lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentCarrierGraphReadings.lean) | `IsTyped`、`IsTotal`、`compose_finite_support` | 同じ `edge(S,T,x,y)` とprofileの比較 |
| [IndependentGeometryCategoryReconstruction](../../lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryCategoryReconstruction.lean)、[IndependentGeometryHomNativeFullRecovery](../../lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryHomNativeFullRecovery.lean) | representative / explicitの全Hom read・assembleと恒等・合成 | D2のnative回復、raw mapと全context actionの保持 |
| [OperationRepair/Basic](../../lean/ResearchLean/AG/OperationRepair/Basic.lean) | `OperationSystem`、`eval`、`eval_append`、`OperationCongruence` | A2・D3・P1の同じ全域操作評価 |
| [OperationRepair/Endpoints](../../lean/ResearchLean/AG/OperationRepair/Endpoints.lean) | `generated`、`behavior`、`generated_le_iff`、`le_behavior_iff`、`generated_le_behavior_iff` | D3の下端・共通上端と語保存 |
| [OperationRepair/Classification](../../lean/ResearchLean/AG/OperationRepair/Classification.lean) | `RepairQuotient`、`RepairHom`、`nonempty_iff_kernel_le`、`quotientRepair`、`repair_exists_iff_request_behavior` | 同じ全射・降下操作・観測を持つ修復区間 |
| [OperationRepair/Composition](../../lean/ResearchLean/AG/OperationRepair/Composition.lean) | `generated_requestUnion`、`repairable_requestUnion_iff` | 同じ `S,T,o` を固定した任意要求族の組立て |
| [n1019 §5–8](../../../docs/note/n1019_shigure_representability_design.md) | 意味変更・条件付きfiber・図式・移送、整数adapterの原始入力 | A–Gの構成とD4の独立な全map分類 |
| [n1020 §12・16](../../../docs/note/n1020_shigure_polynomial_specializations.md) | 台帳のsort・演算・比較・phase・指定係数 | P0–P7の全係数計算と反例 |

## 仮定とその使用箇所

| 条件・入力 | 使用と放電 |
| --- | --- |
| 小さいsignature・規則族・図式、有限term | 全候補を集合・groupoidとして構成。濃度の有限性は課さず、各構文のみ有限 |
| 実際のoperation・relation/domain・指定witness | Aの保存式に全て保持。存在命題を選択関数に変えない |
| G-139の指定した係数的実現 | Bのcopying・linear・regularを別々に構成。任意関数のregular性は追加しない |
| native基点・構文選択 | connected非零環で全native copying mapと構文を回復。任意環の固定構文fiberでは元のlinear Homを回復 |
| coefficient descent | 全意味圏の構文選択はC3.1の局所定数block、対象・全mapはG-139とQC descent。任意の規則付き `C_H` や評価部分関手のsheaf性は別の条件 |
| context cover | Law・witness・totality・全行supportを持つ原始blockのcoverとして生成。任意の有限query族とは区別 |
| quotientの導出witness | 表示用に生成し、同じmapの証拠とambient liftを商にする。意味上の補助選択は保持 |
| 観測と語翻訳 | 原始入力から有限term・pathとして評価。合成は構文代入。強い観測から弱い観測への包含を証明 |
| 固定source、固定部分、許容規則 | Eの独立な編集仕様。sourceへの前合成では規則を輸送し、任意 `H` の閉性は追加しない |
| 集合値評価と部分関手 `P↪T` | 全係数で型付き原始評価を行い自然性を帰納法で証明。評価liftが条件を満たすとき一点になる |
| 候補の順位比較 | 単調性は不等式を保つ。完全な順位回復には反映を持つ比較を使う |
| 共通候補・補完存在 | 必要なmap・翻訳・補助選択を候補または全解fiberに保持。存在の真偽から自然な選択は作らない |
| 一段規則の同型輸送 | 任意 `H` ではつなぎ同型を保持する。規則内のstrictificationは輸送構成があるときに限る |
| 有効な有限Law還元 | F1.2の有限方程式生成に使用。witness付き解は商後に全補完へ対応 |
| 移送開始域とphase | Gの実際の包含・pullbackで生成し、語の全prefix domainを保持 |
| Snapshotのapply domain | 全合法Busy状態・全引数に定義する宣言を固定。閉性から `μδ=0`、一般化では `μδ(1−ρ)=0` を導出 |
| 非零環 | 四flag順序・非単射例・異なる係数点の区別に使用。schemeと環の恒等式は零環も含む |
| 共通 `S,T,o` | G-126の合併要求の組立てに必須。指定adapter比較は別の自然性式の全解 |

## 標準数学への依存

自由代数・商・module表示・集合商・fiber productの普遍性と、有限syntaxの帰納法を用いる。2-fiberの対象・射・同値とそのcoherenceは本文でtupleを展開して証明する。

- [閉部分空間への一意因子分解, Stacks 01HP](https://stacks.math.columbia.edu/tag/01HP)：B4。本文ではaffine商環の両方向を直接証明する。
- [QC moduleと全mapの有効descent, Stacks 023T](https://stacks.math.columbia.edu/tag/023T)：C3。対象はG-139の係数family、mapは実際の全Homで、保存式を忠実平坦に検査する。

G-139への依存は同稿に証明された構成と、そのsource対応に記した標準数学への依存を含む。新規形式化では、ここで構成した同じ候補・全Hom・商・domain・残差を保持して宣言を作る。
