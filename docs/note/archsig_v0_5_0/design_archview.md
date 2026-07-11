> [!NOTE]
> 本文書は ArchSig v0.5.0 再設計の次元別詳細設計(2026-07-04、並列設計+3レンズ敵対査読の改訂版)。
> 6文書間で食い違う箇所は [統合ノート](../archsig_v0_5_0_redesign_note.md) §8 の統合裁定を正とする。

# ArchSig v0.5.0 設計次元5: ArchView 再設計 — 幾何らしい可視化

設計日: 2026-07-04(査読反映改訂版)。担当: ArchView 再設計(調査と設計のみ、実装なし)。
根拠レポート: `reader_archview.md`(全文)、`reader_ag-theory.md`(全文)、`reader_saga.md`(全文)、`reader_archsig-code.md`(全文)、`reader_philosophy.md` / `reader_measurement-notes.md`(要点)。
一次確認: `.tmp/archsig-practical-rust-service/` の実 artifact(viewer data / measurement packet)のフィールド名を実測済み。査読対応で `ag_measurement.rs` / `main.rs` / `schema_catalog.rs` / `tests/cli.rs` / `archview.html` / 理論本文 part_4 / part_5 / part_8 / part_10 / appendix の該当行を再実測済み(文書末尾の「査読対応」参照)。

---

## 1. 目的

AAT 代数幾何版の一次対象 — **finite poset site、selected cover の nerve、overlap 上の 1-cochain、cover-relative Čech H^1 の class、descent の成立/不成立、obstruction の局在、SAGA 定理の結論** — を、ArchSig の計測 artifact に既に存在する(または v0.5.0 で計測側が emit する)フィールドの忠実な投影として 3D で描く。

到達目標を 3 行で言うと:

1. **site は点の集まりではなく順序構造として、cover は選択として、nerve は形として見える**(現状: 無向 strut の力学配置のみ)。
2. **H^1 は「どの辺で」だけでなく「どの閉路にどんな値で」住むかまで見える**。descent の成立は「局所 section が貼り合って 1 枚の大域 sheet になる」運動として、不成立は「閉じない縫い目」として見える。
3. **SAGA 定理の結論(global section の存在/一意、H^1 zero ⇔ effective gluing、law 依存/非依存の分割)が 1 画面で読める**。

規律は現行 ArchView が確立したものを全部引き継ぐ: 計測=主/可視化=従、viewer は新しい verdict を作らない、沈黙は霧/frosted/非描画、肯定的結論が最も強い視覚資源を得る。

## 2. 現状の問題

`reader_archview.md` §4 の欠落分析を設計課題として再掲する(各項目は file:line 付きで同レポートに典拠がある)。

| # | 問題 | 現状 |
| --- | --- | --- |
| P1 | site の poset 順序が描かれない | `restrictsTo` は detail panel の文字列のみ。strut は無向 |
| P2 | cover が第一級でない | `covers[0]` の id をブランド行に出すだけ。複数 cover・refinement の可視化なし |
| P3 | nerve が 2-骨格止まりで b₁ が形にならない | 系12.3 `H^1(U,k) ≅ b₁(N(U))` の幾何的本体(光る閉路)が無い |
| P4 | cocycle が「どの辺で」まで | `edge.value` は parity marker。値・向き・一周の蓄積が無い(packet 側の投影限界でもある) |
| P5 | descent の運動が無い | assembly snap(V13)は旧 viewer ごと消滅。sequence mode は「別計測の並置」であり gluing 過程ではない |
| P6 | H² の描画だけが沈黙 | 計測・投影は既に在る: `project_h2_coherence_to_cover_nerve`(`ag_measurement.rs:10245`)が face 単位の `coherenceClaim`(measured_zero/measured_nonzero)+ `structuralVerdictRef` を投影し、coherence verdict が出た packet では `h2CoherenceVisualized: true` に反転(`ag_measurement.rs:4337` で analyze 接続済み、`tests/cli.rs:2423` で true が test-lock 済み)。viewer も `coherenceClaim` を parse 済み(`archview.html:501`)で、**沈黙しているのは描画のみ**。実測 artifact の false は当該 profile で coherence verdict が出ていないだけで、投影機構の欠落ではない |
| P7 | locusField の完全脱落 | `fieldRows` / `measuredZeroRegions` / `blockedRegions` は packet 実在・parse 済み・未描画。肯定的結論(measured_zero 盆地)を「地」にする最短の材料が捨てられている |
| P8 | SAGA 接続 surface ゼロ | 第X部の定理連鎖(2026-07-03 target-theorem-proved)に対応する幾何 lexicon が viewer に無い |
| P9 | packet 実在・未描画のフィールド群 | `periodStokes.meters` / `transferCostOverlays` / `singularityConcentrationOverlays` / M2/M3/M5/M6 verdict 群 — 捏造リスクゼロで足せるのに沈黙 |
| P10 | 可視化系 PRD 3 本の target surface が消滅 | insight viewer PRD / gluing geometry PRD #2082 / M+V 統合 PRD #2217 の V 側は旧 viewer に実装後、旧 viewer ごと削除。PRD の生死判定が未整理 |
| P11 | 技術負債 | O(n²) layout(>400 contexts で縮退)、InstancedMesh 未使用、largeGraphStrategy 未実装、CDN importmap で offline 不可 |

背景にある非対称: **「計測は前進し、可視化は後退した」**(M ワークストリームは Rust に現存、V5–V18 の大半は消滅)。v0.5.0 の ArchView 再設計はこの非対称の解消であり、大部分は「既に測れているものを描く」作業である。P6 はその典型で、artifact 変更なしの描画解禁だけで閉じる。

## 3. 設計案

### 3.0 設計原則(5 つ)

1. **幾何対象が主語、シーンは問い**。ArchView の「1 シーン = 1 つの問い」構造は維持し、シーンの語彙を AG の幾何対象(site / cover / nerve / cochain / descent / locus / conflict / SAGA)に揃える。
2. **投影対応表なしの視覚要素は追加しない**。すべての新規描画は §3.2 の台帳で「計測 artifact のどのフィールドを投影するか」を宣言する。フィールドが無ければ描かない(沈黙)。
3. **verdict は参照、計算しない**。viewer が行ってよい計算は「作図」(レイアウト、rank、経路探索、アニメの振付)のみ。境界所属・class 零性・poset 深さ等の値はすべて ArchSig 側が emit し、viewer は ref で結び直すだけ。**structure レーンのフィールド(boolean・数値)を条件式に使って verdict レーンの表示を点けることも「計算」に含まれ、禁止する**。verdict レーンの表示条件は常に verdict 行への ref の解決可能性である。
4. **肯定的結論が最大の視覚資源を得る**。measured_zero 盆地が「地」、global section sheet が「冠」、REPAIR_GLUES が SAGA ビューの中央。非結論・沈黙は霧と frosted に留め、一覧化しない。
5. **capacity と class の分離**(第IV部 原則4.4)。「cover の形が持つ H^1 の容量(b₁ 閉路)」と「実測された非零 class の support」は別レーンで描く。容量は debt ではない。

### 3.1 色レーン(1 レーン追加)

現行 4 レーンに **structure レーン**を追加する。

| レーン | 色 | 意味 | 例 |
| --- | --- | --- | --- |
| measured_zero | teal `#38e0c8` | 構造的零 verdict | 盆地、global section sheet、呼吸リング |
| measured_nonzero | amber `#ffb24c` | 構造的非零 verdict + class support(bloom はここだけ) | seam、非零 class 閉路、H² 破孔 |
| analytic | lavender `#b69cff` | analytic reading(lawfulness を駆動しない) | 曲率地形、Stokes メーター、Hilbert 干渉 |
| silence | grey `#6a7790` + 霧/frosted | 未計測・語彙外 | 未計測面、blockedRegions |
| **structure(新)** | slate-white `#c9d4e3`(低輝度、非 bloom) | verdict を持たない computed invariant(cover の形、poset の順序、b₁ 容量、χ) | Hasse 矢印、capacity 閉路、topology HUD |

structure レーンは「事実としての形」であり判定ではない。legend に「structure lane carries no verdict」を明記し、Rust 側投影の `visualEncodingLegend[]` に追加する。**structure レーンのフィールドは teal/amber(verdict レーン)の表示条件に使わない**(原則3 の系。verdict レーンの点灯は必ず verdict 行 ref の解決による)。

### 3.2 描くべき幾何対象の台帳(対象 × 視覚表現 × 投影フィールド × 沈黙条件)

以下が本設計の中核。**投影元**列のフィールドは、(既存)= 現行 packet に実在、(新設)= viewer data で ArchSig 側が emit する新フィールド(計測次元・artifact 次元との contract)。

verdictRef の表記はすべて v0.4.0 が実際に emit する安定 ref 形式 `structuralVerdict/{evaluator}/{law}/{method_status}`(`ag_measurement.rs:5611` `structural_verdict_ref`、各 segment は英数字以外を `-` に正規化)に従う。行 index 形式(`#0` 等)は採らない(並び順に脆く、既存 artifact 内 ref と不整合になるため)。

#### G1. finite site の poset(P1 解消)

- **視覚表現**: Hasse 配置。鉛直軸 y = `posetDepth`(restriction 半順序の rank)。`restrictsTo` を **有向 tapered strut + 矢尻**(structure レーン)で描き、restriction 射の向き(細かい context → 粗い context)を形にする。同一 depth 内は現行の nerve force-directed を水平面内で維持。context セルは現行のガラス icosahedron を継続(半径 ∝ √|atoms|)。
- **投影元**: `finitePosetSite.contexts[].restrictsTo`(既存)、`contexts[].posetStatus`(既存)、`contexts[].posetDepth`(新設: ArchSig が acyclic 検証時に決定論的に計算して emit。viewer は描くだけ)。
- **操作**: context hover で上方閉包/下方閉包をハイライト(順序イデアルの可視化)。2 セル選択で meet(overlap の代表)を点滅表示 — meet の同定は `nerve.edges[].{source,targetContextRef}` の実測データから引く。
- **沈黙条件**: `posetDepth` が無い旧 artifact では現行の平面配置に自動フォールバック(縦軸を使わない)。
- **忠実性注記**: y 座標は「poset の作図」であり計測値ではない。README 忠実性契約に「posetDepth は restrictsTo から決定論的に導出される描画順位。高さに verdict はない」を追記。

#### G2. selected cover と nerve 複体(P2 解消)

- **視覚表現**: 画面上部に **cover チップ列**(`covers[]` 全列挙、`coverageStatus` バッジ付き)。アクティブ cover の nerve のみ実体描画。多重 overlap 成分(第IV部 定義12.1 の多重複体)は**平行 strut** で成分数を形にする。
- **投影元**: `finitePosetSite.covers[]`(既存)、`nerve.coverRef`(既存)、`nerve.edges[]`(既存。多重成分の区別は新設 `edges[].overlapComponentIndex`)。
- **cover 間関係**: `finitePosetSite.coverRelations[]`(新設)がある場合のみ、チップ間に refinement 矢印を描く。関係の provenance は supplied data(定理8.5: refinement 自然性はデータ)。矢印には「zero transfers coarse→fine (one-way)」の一方向注記(命題4.10)。データが無ければチップは孤立表示 — cover 間の verdict 比較は描かない。
- **沈黙条件**: coverRelations 不在 → 矢印なし(エラーではない)。

#### G3. nerve topology と b₁ 閉路(P3 解消)

- **視覚表現**: **capacity 閉路** = `cycleBasis` の各閉路を structure レーンの閉じたチューブとして nerve 上に立たせる(低輝度、非 bloom)。HUD に topology チップ行: `b₀=1 · b₁=2 · χ=−1 · capacity≥1 · forest: no`。**topology チップ行はすべて structure レーン(slate-white)の事実表示であり、`forest` を含めどのフィールドも verdict レーンの表示を点けない**。
- **H¹=0 保証バッジ(verdict レーン)**: teal の肯定的バッジ「H¹ = 0 (measured; Thm 12.4 regime)」は、`nerve.topology.guarantee.verdictRef`(新設・optional)が measurement packet の `structuralVerdict[]` の measured_zero 行に解決できるときにのみ表示する。この行は **計測側が定理12.4 の 3 前提 — (1) N(U) is a forest、(2) no triple overlap faces、(3) 選ばれた係数 sheaf での restriction 全射性 — をすべて検査した上で emit する** verdict であり(検査は計測次元の管轄)、forest フラグ単独では点かない。verdict 行が無い packet では forest は HUD の事実表示に留まる。定理12.4 の前提と結論の対応は detail panel に表示する(バッジ本体は measured verdict の表示であり、viewer による定理適用ではない)。
- **投影元**(新設): `nerve.topology: { b0, b1, oneSkeletonB1, eulerCharacteristic, capacityLowerBound, forest, cycleBasis: [{cycleId, edgeRefs[]}], guarantee?: { verdictRef }, sourceEvaluator }`。計算源は `ag.cech-obstruction@1` の nerve 計算(b₁/F₂ rank は実装済み: `ag_measurement.rs:6351` 付近)を投影に昇格させる。
- **b₁ の意味の固定(contract invariant)**: 現行計測は `oneSkeletonB1`(選ばれた triple-overlap 面で商を取る前のグラフ閉路数)と `nerveComplexB1`(面込み複体の Betti 数)を明示的に区別している(`ag_measurement.rs:6321-6333` の distinction 文言)。系12.3 も「face が選ばれて loop を埋める場合、その face を含む複体の Betti 数として読む」と規定する(part_4:1418-1435)。よって contract に次を明記する: **`topology.b1` = nerveComplexB1(面込み複体の Betti 数)であり、`cycleBasis` は選ばれた面で埋まらない閉路の基底である**。oneSkeletonB1 は別名フィールドとして併載し、HUD では区別表示(面で埋まる閉路を capacity チューブとして立てない — 容量の過大表示を防ぐ)。
- **class との分離**: 実測非零 class の support(G4)が乗った閉路だけが amber+bloom に「点灯」する。容量 2 のうち 1 つが点灯していれば、「debt の余地 2、実測 debt 1」が一目で分かる — 原則4.4 の視覚化。
- **沈黙条件**: `nerve.topology` 不在 → HUD チップ非表示、閉路非描画。`guarantee` 不在 → バッジ非表示(沈黙。forest 事実表示のみ残る)。

#### G4. overlap 上の 1-cochain と非零 H¹ 類(P4 解消)

- **視覚表現**:
  - 辺ごとの **値グリフ**: `edgeValues[].value` を billboard で表示(F₂ なら「1」、0 値は表示抑制)。辺に**向き矢印**(orientation)を付す。
  - **seam**(現行のアーチ状 glowing stitches)は class support 表示として継続。bloom は従来どおりここだけ。
  - **holonomy 蓄積リング**: 選択した閉路(G3 の cycleBasis から選ぶ)を section probe が一周し、辺値を離散ステップとして積む。一周後の「閉じないズレ」を**割れたリング**(端点が値ぶんだけ段差)で描き、正確な蓄積値をラベル表示(`cycleAccumulation[].holonomyValue`)。ズレの大きさを連続量として誇張しない(値そのものを文字で示す)。擬円周 golden example では「1 周して 1 残る」が文字通り見える。
- **投影元**(新設): `geometry.cochainLayer: { coefficientDisplay: { ring: "F2", sourceProfileRef }, edgeValues: [{edgeRef, value, orientation: [fromCtx, toCtx]}], cocycleClasses: [{classId, verdictRef, supportEdgeRefs[], cycleAccumulation: [{cycleRef, holonomyValue}]}] }`。verdictRef は既存安定形式(例: `structuralVerdict/ag-cech-obstruction-1/law-example-1/measured-nonzero`)。既存 `cocycleRibbon` は supportEdges の後方互換として温存し、値表示は cochainLayer から。
- **沈黙条件**: cochainLayer 不在 → 現行 parity 表示に自動フォールバック(detail panel の「parity, not H¹ magnitude」注記を維持)。

#### G5. descent 成立/不成立の gluing 図(P5 解消 — V13 assembly snap の復活)

- **視覚表現**:
  - 各 chart 上に**局所 section パネル**(teal 半透明の板)。再生ボタンで各パネルが overlap 中点へ滑走し、辺ごとに接合を試みる。
  - `failingEdgeRefs` に載る辺では接合が**目に見える段差**を残して止まる(段差の脇に cochain 値ラベル)。
  - **class 零までの表示**: `classZeroVerdictRef` が measured_zero 行に解決できるときは、seam を消灯し「obstruction class zero」チップを表示する。**ここでパネルは融合しない** — 原則4.4 の逆向き(part_4:456-490)により、class 零だけでは大域 section の存在を語れない(torsor/module structure と effectivity assumption が要る)。
  - **融合 sheet(終状態)**: パネルが融合して **1 枚の連続した teal sheet(global section sheet)** になるのは、`effectiveGluingVerdictRef` が effectivity を運ぶ verdict 行(SAGA の descent / effective gluing 系 verdict、または torsor effectivity を検査した verdict 行)に解決できるときのみ。`globalSection.verdictRef` が SAGA packet の `uniqueGlobalSection`(定理7.3 package)行に解決できるときのみ sheet 上に「global section: exists, unique (∃!)」の冠ラベル + 呼吸リング。
  - 振付は決定論(既存の hash32+mulberry32 規律)。アニメは「実測値の提示順序」であり、中間状態は verdict を持たない。
- **投影元**(新設): `geometry.descent: { sectionAssignments: [{contextRef, verdictRef}], gluingStatus: { classZeroVerdictRef, effectiveGluingVerdictRef, failingEdgeRefs[], globalSection: { verdictRef } } }`。`sectionAssignments[].verdictRef` は各 chart の local lawful section 判定行への ref(判定語 literal は置かない)。**contract invariant: `effectiveGluingVerdictRef` は effective-gluing 系 verdict 行を指すこと。class 零 verdict(`ag.cech-obstruction@1` 系)をここに入れてはならない**(入れても viewer は融合を描かない)。
- **沈黙条件**: descent block 不在 → 現行の section probe(lunge & recoil)のみ。probe は温存する(復路探索の身振りとして有効)。`effectiveGluingVerdictRef` 不在(class 零のみ)→ seam 消灯止まり。

#### G6. obstruction の局在: lawful locus 盆地・forbidden cage・repair hitting set(P7 解消 + V6 復活)

- **視覚表現**:
  - **locusField 膜**: context 配置の上に heightmap 膜を張る。`measuredZeroRegions` = **平坦な teal 盆地**(SAFE 系肯定的結論の「地」。画面の最も静かで広い面)。`fieldRows[].signedCurvature` = lavender の起伏(analytic)。`blockedRegions` = frosted の破孔 + 霧(沈黙)。
  - **forbidden cage**(既存継続): 破線 box + supportVariables の ∧ 表示。
  - **minimal repair hitting sets**: 各 hitting set を「全 cage を貫く teal の弦束」として描く。最小 cardinality の set を keystone 星座として強調(非 bloom)。appendix B.4(Square-Free Obstruction Ideal)の worked example なら `{q}` と `{p,r}` の 2 束が見える。
  - repair ladder(現行の landing-ladder、着地しない probe)は継続。
- **投影元**: `geometry.locusField.{fieldRows, measuredZeroRegions, blockedRegions}`(**既存・実測確認済み・現在未描画**)、`geometry.forbiddenCages[]`(既存)、`geometry.repairDual: { minimalForbiddenSupports[], minimalHittingSets: [{setId, witnessVariables[], cardinality}], sourceEvaluator: "ag.square-free-repair@1" }`(新設 — ただし**既存 packet フィールドの投影のみで足り、evaluator 変更は不要**。`minimal_hitting_sets` は `ag_measurement.rs:1183` で計算済み、`:1263` / `:1298` で computed invariants に `minimalHittingSets` として emit 済み。理論根拠: 第VIII部 定理5.2 Alexander dual。Lean 側で hitting sets {q}/{p,r} example が proved 済み)。
- **沈黙条件**: repairDual 不在 → ladder のみ。hitting set は「組合せ的 repair ターゲット」であり operation 意味論を主張しない(原則5.3)注記を detail panel に固定。

#### G7. LawConflict(Tor)の幾何(V15 復活・新形)

- **視覚表現**: 対象 law 対のバッジを 2 つ置き、各 law の witness support 上に半透明の領域ハロを張る。`sharedWitnessFactors` を 2 領域を結ぶ**発光テザー**(amber、Tor verdict が measured_nonzero のとき)で描き、ラベル「**shared witness: x — joint repair must account for derived compatibility residue (Part V)**」。`hilbertWindow`(干渉級数の有限窓)があれば脇に次数別バーを lavender で表示(audit reading)。
  - **boundary note(detail panel 固定)**: 「Tor 非零は derived non-transversality の計測であり、repair 操作の可否・不可能性は operation semantics の管轄外(第V部は joint repair が residue を考慮すべきことまでを主張する。part_5:531-550)」。「独立に修理できない」という操作的不可能性の文言は claim boundary を越えるため用いない(test-lock される copy string からも排除)。
- **投影元**: `geometry.lawConflict: { pairs: [{pairId, lawRefs[2], torDegree, sharedWitnessFactors[], classSupportAtomRefs[], commonAmbientRef, verdictRef}], hilbertWindow?: [{degree, value}] }`(新設。計算源 `ag.law-conflict-tor@1` は実装済み: Taylor complex H1 類 `ag_measurement.rs:8156`)。
- **沈黙条件**: `commonAmbientRef` の無い対は描かない(原則9.3: common ambient なしに Tor 比較なし)。

#### G8. H² coherence 膜の描画解禁(P6 解消 — 既存フィールドの描画のみ)

- **視覚表現**: nerve の三角面を coherenceClaim で 3 態に描き分ける:
  - measured_zero → **封止面**(teal 縁の落ち着いたガラス面。「triple overlap は整合」)
  - measured_nonzero → **amber 縁の破孔**(面が打ち抜かれた形。class support の面のみ)
  - unmeasured → 現行の frosted(沈黙)
- **投影元(すべて既存)**: `nerve.triangles[].coherenceClaim` + `structuralVerdictRef`(`project_h2_coherence_to_cover_nerve` が既に投影、`ag_measurement.rs:10245`)、`nerve.h2CoherenceVisualized`(coherence verdict が出た packet で既に true、`tests/cli.rs:2423` で test-lock 済み)。viewer は `archview.html:501` で coherenceClaim を parse 済みで、**必要な作業は描画コード(現行 `archview.html:779, 1462` 相当の沈黙箇所)の解禁のみ**。artifact 変更・計測次元への contract 要求は無い(Phase V-A)。
  - v3 で `coherenceClaim` を `triangles[].coherence.{status, verdictRef}` の形へ寄せたい場合は「新設」ではなく**既存フィールドの rename** として §3.5 規律4 の改名リストで扱う(独立 PR、後述)。
- **沈黙条件**: coherenceClaim 不在の三角形は frosted のまま + 「H² not measured under this profile (silence)」の現行文言維持。

#### G9. Period / Stokes の実測メーター(V16 復活、schematic ring の置換)

- **視覚表現**: 現行の「SCHEMATIC placeholders」torus を廃し、`periodStokes.meters[]` の各メーターを**ダイヤル弧**として、監査対象 cycle(nerve support が引けるとき)の近傍に anchor する。Stokes 監査(`⟨δb,γ⟩ = ⟨b,∂γ⟩`)の残差ゼロを**釣り合った天秤**、非ゼロを傾いた天秤で描く(lavender / analytic レーン)。anchor 不能なメーターは HUD 側のメーター棚に置く(位置を捏造しない — 現行 hotspot の「carrier に anchor できなければ描かない」規律の踏襲)。
- **投影元**: `geometry.periodStokes.{meters[], activeMeterCount, sourceEvaluator}`(**既存・実測確認済み・現在未読**)、`analyticOverlayBundle.periodPairingOverlays[]`(既存)。
- **沈黙条件**: meters 空 → 現行の沈黙文言。

#### G10. analytic 残り物(P9 の掃き出し)

- `transferCostOverlays[]`(既存・parse 済み・未描画)→ support 間の移送コストを lavender の弧+コスト値ラベルで。`singularityConcentrationOverlays[]`(既存・未読)→ 集中度の高い context セルに lavender の収束等高線。いずれも「analytic reading — lawfulness を駆動しない」の脚注固定。

### 3.3 シーン構成(6 → 9)

各シーンは 1 つの問い。可視性トグル + カメラ再フレーミングという現行方式を維持(レイアウトは load 時 1 回)。

| # | sceneId | 問い | 主対象 | 新旧 |
| --- | --- | --- | --- | --- |
| 1 | `site-order` | どんな順序構造の site を計測したか | G1 | **新** |
| 2 | `cover-nerve` | どの cover を選び、その形はどれだけの debt 容量を持つか | G2, G3, G8(膜) | 旧 Nerve & Cover の拡張 |
| 3 | `gluing-h1` | 局所の一致は大域 section に貼り合うか(headline) | G4, G5 | 旧 headline の拡張 |
| 4 | `saga-descent` | 局所修理は大域修理に貼り合うか(SAGA) | §3.4 | **新・旗艦** |
| 5 | `locus-repair` | lawful locus はどこで、何を消せば直るか | G6 | 旧 Forbidden の拡張 |
| 6 | `law-conflict` | 2 つの規約は独立に直せるか(注: シーンの問いであって結論ラベルではない。結論は G7 の boundary note の範囲) | G7 | **新** |
| 7 | `curvature-hodge` | 曲率・調和 debt はどこに集中するか(analytic) | 既存地形 + harmonic debt 下限 `‖h(g)‖` メーター(packet の analytic reading 行を参照) | 旧 Curvature の拡張 |
| 8 | `period-stokes` | クラスは cycle にどう巻きつき、会計は合っているか(analytic) | G9 | 旧 Periods の置換 |
| 9 | `boundary-silence` | この profile は何を観測し、何に沈黙したか | 既存 fog-of-war + boundaryStatements 6 種の kind 別表示 | 旧 Projection boundary の継続 |

ArchSig 側 `viewerVisualScenes[]` の 12 シーン語彙は、この 9 シーンへの写像表(現行 `SCENE_MAP` 方式)で受ける。scene registry を artifact 次元で v3 化する際は 9 語彙に更新するのが望ましい(未決事項へ)。

### 3.4 SAGA ビュー(scene 4)の画面設計

**問い**: 「local repairs may each succeed. Do they glue to a global repair?」(第X部冒頭)を 1 画面で答える。

画面は 5 要素。すべて SAGA 計測 packet(新 evaluator 群、計測次元の管轄)の投影であり、viewer は一切判定しない。

```
┌────────────────────────────────────────────────────────────┐
│ [E] conclusion crown: MEASURED_REPAIR_GLUES_UNDER_PROFILE  │  ← decisionBar
├──────────────────────────────────┬─────────────────────────┤
│                                  │ [D] conclusions ladder  │
│   [B] repair cover nerve         │  law-independent 4–10   │
│      + residual charges          │   ▣ descent             │
│      + primitive absorption      │   ▣ ∃! global section   │
│      (H¹ mid-band)               │   ▣ coherent ⇔ H¹=0     │
│   ───────────────────────        │   ▣ additive ⇔ Čech     │
│   [A] chart floor (H⁰)           │   ▣ higher obs vanish   │
│      interpretation lamps        │  law-dependent 1–3      │
│      Λ/K satellites (alias)      │   ▣ interpretation = 0  │
│                                  │   ▣ restriction eval    │
│                                  │   ▣ detector soundness  │
├──────────────────────────────────┼─────────────────────────┤
│ [C] comparison bridge            │ supplied-layers gauge   │
│  semantic H¹  ⇄  Čech H¹        │  B ▣ C ▣ D ▢ E ▢       │
│  (両ランプ同期: teal/amber)       │  faithfulness: complete │
└──────────────────────────────────┴─────────────────────────┘
```

- **[A] chart floor(H⁰ 層)**: 各 chart を床面に並べ、law 依存結論 1(interpretation 零)を chart ごとの **teal ランプ**で表示。非零 interpretation の chart は amber ランプ + 「displayed required law failure(detector soundness, 結論3)」の detail。**law 充足は正確に degree-0 で作用する**(定理8.1)を床面=H⁰ という空間配置そのもので語る。chart 上には component(K)アンカーの周囲を semantic atom(Λ)の衛星が回る **Λ/K 二層表示**。alias(同一 component に複数衛星)が形として見える。
- **[B] repair cover nerve(H¹ 中間帯)**: 床の上方に repair cover の nerve(charts / pairwise / triple)。residual r の非零値を overlap 辺の **amber チャージ**として表示。境界所属が measured 済みなら:
  - `r ∈ B¹`(貼り合う): **faithfulness 基盤(`suppliedLayers.faithfulness` が `complete-support` 宣言 or supplied faithfulness data)を持つ packet のみ**、witness primitive g の δ⁰g がチャージを**吸収する掃引アニメ**(再生ボタン)を配線する。終状態は G5 と同じ global section sheet + 呼吸リング。faithfulness 不在の packet では境界所属単独で吸収アニメを点けない(§4 の沈黙規律のインライン化)。
  - `r ∉ B¹`(貼り合わない): チャージの残る閉路が amber に点灯(最小例は circle nerve: 2 頂点・逆向き 2 辺・値 [1])。「H¹ content は cover の幾何から来る」(意味8.3)が、床(法)ではなく輪(形)が光ることとして見える。
  - alias 反例(例2.6/3.6 型)が packet に emit されていれば: component アンカーは teal(coverage 成立)なのに、その衛星の 1 つが amber のまま残る(faithfulness 破れ)という**「component 水準は合格、semantic 水準で閉じない」の直接図**。
- **[C] comparison bridge**: semantic 側 H¹ と Čech 側 H¹ のサムネイルを双方向矢印で結び、**zero-predicate equivalence を同期ランプ対**(両 teal または両 amber)で表示。矢印には comparison data の provenance ラベル。**comparison data が supplied されていない packet では橋そのものを描かない**(定理8.4/8.5: 比較可能性はデータ)。非零転送(定理7.4)が発火した packet では両 amber + 「nonzero class transfers both ways」注記。
- **[D] conclusions ladder(10 結論パネル)**: Lean 構造体の正確な分割(law-dependent 1–3 / law-independent 4–10)をそのまま 2 段のチェックリストにする。各行の値は **SAGA packet の該当結論行への ref(または null)**であり、teal ▣ = ref が packet の emit 行に解決できる / grey ▢ = ref が null(沈黙、失敗ではない)。boolean のコピーは viewer data に持たない。**law 非依存 7 結論が law 充足なしで点く**(定理8.2)ことがパネル構造から読める。
- **[E] conclusion crown + supplied-layers gauge**: 上辺に decisionBar の結論コード。右下に**入力階段ゲージ**: B(複体)/ C(additive)/ D(比較)/ E(law-equation)の 4 層と faithfulness の供給状態(`complete-support | supplied | absent`)。ゲージは measurement packet の `assumptions` / `profile` の投影であり、「なぜ結論がここまでか」を利用者が入力側の責務として読める(境界の一括払い: 足りないのは viewer でも ArchSig でもなく supplied data)。supplied-layers は入力供給状態の表示であって verdict ではない(structure 系の扱い)。

**SAGA ビューの解放条件**: SAGA 系 evaluator(仮称 `ag.saga-descent@1` / `ag.saga-comparison@1`、id は計測次元の管轄)が packet に行を持つときのみ `sceneStatus: active`。無い packet ではシーン一覧に grey で「not measured under this profile」(現行 `not_active_for_packet` 方式の継続)。M→V gating(統合 PRD の V0)の踏襲である。

### 3.5 viewer data contract v3(JSON フィールドレベル)

注: 現行 schemaVersion は既に `archsig-atom-viewer-data-v2` なので、本設計の contract は **v3** となる(課題文の「v2 形状」は「次期形状」と読む)。表記は artifact 次元の命名統一に合わせ slash 形式 `archsig-atom-viewer-data/v3` を提案する。

**移行は 2 段に割る**(v0.5.0 内):

- **段1(optional block 追加)**: schema は `archsig-atom-viewer-data-v2` のまま、以下の新設 block を optional で追加する。規律2(不在=沈黙)がそのまま効くため、既存 golden fixture と cli.rs 契約テストの破壊が block 追加ぶんに限定される。
- **段2(v3 改名 PR、独立)**: `schemaVersion` → `schema` キー統一・slash 命名・`moleculeGroups`/`atomEdges`/`axisMapping` 系の emit 停止・`coherenceClaim` → `triangles[].coherence.{status,verdictRef}` の rename を、**viewer data の全 emitter と catalog を一括更新する独立 PR** で行う。v3 移行対象は次の 3 箇所(すべて実測済み): `ag_measurement.rs` の measurement viewer data builder、`main.rs:1223` `build_validation_failure_viewer_data`(第二の emitter — こちらも `archsig-atom-viewer-data-v2` を emit)、`schema_catalog.rs` の登録(`:307`, `:453`)。cli.rs の文字列契約テストの更新もこの PR に閉じ込める。

以下は段2 完了後の v3 最終形。

```jsonc
{
  "schema": "archsig-atom-viewer-data/v3",          // 段2で schemaVersion キーから schema へ(artifact 次元と同調)
  "sourceArtifactRefs": {
    "normalizedArchMap": "normalized-archmap.json",
    "measurementPacket": "archsig-measurement-packet.json",
    "summary": "archsig-analysis-summary.json",
    "insightReport": "archsig-insight-report.json"
  },
  "decisionBar": { "conclusion": "...", "validation": "...", "boundaryDigest": "...", "artifactLinks": [] },

  "finitePosetSite": {
    "atoms":    [ { "normalizedAtomId": "...", "atomKind": "...", "axis": "...", "predicate": "...",
                    "subject": "...", "contextMemberships": [], "sourceRefs": [] } ],
    "contexts": [ { "normalizedContextId": "...", "atomIds": [], "restrictsTo": [],
                    "posetDepth": 0,                              // 新設(G1): ArchSig が emit する描画順位
                    "posetStatus": "acyclic", "sourceRefs": [] } ],
    "covers":   [ { "normalizedCoverId": "...", "contextIds": [], "coverageStatus": "...", "sourceRefs": [] } ],
    "selectedCoverRef": "cover:main@1",                           // 新設(G2): アクティブ cover の明示
    "coverRelations": [                                           // 新設(G2): supplied refinement data の投影のみ
      { "kind": "refinement", "fromCoverRef": "...", "toCoverRef": "...",
        "provenance": "supplied-refinement-data", "sourceRef": "..." } ]
  },

  "geometry": {                                                   // 旧 aatGeometryOverlays を改名・整理(段2)
    "schema": "archsig-geometry-overlays/v2",
    "projectionBoundary": "bounded viewer projection ...; visual richness is not a new verdict",
    "visualEncodingLegend": [ /* 5 レーン(structure 追加)の宣言 */ ],

    "nerve": {
      "coverRef": "...",
      "vertices":  [ { "contextRef": "...", "atomRefs": [] } ],
      "edges":     [ { "edgeId": "...", "sourceContextRef": "...", "targetContextRef": "...",
                       "supportAtomRefs": [], "overlapComponentIndex": 0 } ],   // 新設: 多重成分
      "triangles": [ { "faceId": "...", "contextRefs": [], "edgeRefs": [], "sharedAtomRefs": [],
                       "coherence": { "status": "measured_zero|measured_nonzero|unmeasured",   // 段2 rename(G8)。段1では既存 coherenceClaim + structuralVerdictRef のまま描画解禁
                                      "verdictRef": "structuralVerdict/ag-coherence-obstruction-1/law-example-1/measured-nonzero" } } ],
      "h2CoherenceVisualized": true,                              // 既存。coherence evaluator が verdict を出した packet で true(実装済み)
      "topology": {                                               // 新設(G3)
        "b0": 1,
        "b1": 2,                                                  // invariant: b1 = nerveComplexB1(面込み複体の Betti 数)
        "oneSkeletonB1": 2,                                       // 面で商を取る前のグラフ閉路数(別名で区別)
        "eulerCharacteristic": -1, "capacityLowerBound": 1, "forest": false,
        "cycleBasis": [ { "cycleId": "gamma-1", "edgeRefs": [] } ],  // invariant: 選ばれた面で埋まらない閉路の基底
        "guarantee": null,                                        // optional。Thm 12.4 の 3 前提を計測側が検査した measured_zero 行への ref のみ
        // 例: "guarantee": { "verdictRef": "structuralVerdict/ag-cech-obstruction-1/law-example-1/measured-zero" }
        "sourceEvaluator": "ag.cech-obstruction@1" }
    },

    "cochainLayer": {                                             // 新設(G4)
      "coefficientDisplay": { "ring": "F2", "sourceProfileRef": "measurement-profile:...@1" },
      "edgeValues": [ { "edgeRef": "...", "value": "1", "orientation": ["ctx:a", "ctx:b"] } ],
      "cocycleClasses": [ { "classId": "...",
                            "verdictRef": "structuralVerdict/ag-cech-obstruction-1/law-example-1/measured-nonzero",
                            "supportEdgeRefs": [],
                            "cycleAccumulation": [ { "cycleRef": "gamma-1", "holonomyValue": "1" } ] } ]
    },
    "cocycleRibbon": { /* 既存形状を後方互換で温存(supportEdges / closureGapEncoding) */ },

    "descent": {                                                  // 新設(G5)
      "sectionAssignments": [ { "contextRef": "...",
                                "verdictRef": "structuralVerdict/..." } ],   // 判定語 literal を置かない(規律1)
      "gluingStatus": {
        "classZeroVerdictRef": "structuralVerdict/ag-cech-obstruction-1/law-example-1/measured-zero",
        "effectiveGluingVerdictRef": null,                        // 融合 sheet はこの ref が解決できるときのみ(G5)
        "failingEdgeRefs": [],
        "globalSection": { "verdictRef": null } }                 // SAGA uniqueGlobalSection 行への ref。∃! 冠はこの ref のみ
    },

    "locusField":     { "fieldRows": [], "measuredZeroRegions": [], "blockedRegions": [] },  // 既存(未描画→描画へ)
    "forbiddenCages": [ /* 既存 */ ],
    "repairMorphs":   [ /* 既存 */ ],
    "repairDual": {                                               // 新設(G6)— 既存 packet フィールドの投影のみ、evaluator 変更なし
      "minimalForbiddenSupports": [ { "supportId": "...", "witnessVariables": [] } ],
      "minimalHittingSets": [ { "setId": "...", "witnessVariables": ["q"], "cardinality": 1 } ],
      "sourceEvaluator": "ag.square-free-repair@1" },

    "lawConflict": {                                              // 新設(G7)
      "pairs": [ { "pairId": "...", "lawRefs": ["law:u", "law:v"], "torDegree": 1,
                   "sharedWitnessFactors": ["x"], "classSupportAtomRefs": [],
                   "commonAmbientRef": "...",
                   "verdictRef": "structuralVerdict/ag-law-conflict-tor-1/law-u-law-v/measured-nonzero" } ],
      "hilbertWindow": [ { "degree": 3, "value": 1 } ] },

    "sagaDescent": {                                              // 新設(§3.4)。SAGA evaluator 稼働時のみ
      "status": "active",                                         // 区画の存在表示(シーン gating 用)。verdict ではない
      "suppliedLayers": { "complex": true, "additive": true, "comparison": false, "lawEquation": false,
                          "faithfulness": "complete-support" },   // 入力供給状態の表示。verdict ではない
      "repairCover": { "chartRefs": [], "overlapRefs": [], "tripleRefs": [] },
      "residual": { "cochainValues": [ { "overlapRef": "...", "value": "1" } ],
                    "boundaryMembership": { "verdictRef": "sagaVerdict/...", "witnessPrimitiveRef": null } },
      "primitive": { "assignments": [ { "chartRef": "...", "valueDigest": "..." } ],
                     "supportDeclaration": "complete" },
      "comparisonBridge": null,                                   // この例では comparison 層が supplied されていない → 橋を描かない
      "conclusions": {
        // 各値は SAGA packet の結論行への ref(文字列)または null(沈黙)。boolean のコピーを持たない(規律1)
        "lawDependent":   { "interpretationZero": null, "restrictionEvaluator": null, "detectorSoundness": null },
        "lawIndependent": { "package": "sagaVerdict/conclusions/package",
                            "sheafCondition": "sagaVerdict/conclusions/sheaf-condition",
                            "descent": "sagaVerdict/conclusions/descent",
                            "uniqueGlobalSection": "sagaVerdict/conclusions/unique-global-section",
                            "coherentIffH1Zero": "sagaVerdict/conclusions/coherent-iff-h1-zero",
                            "additiveIffCoverRelative": "sagaVerdict/conclusions/additive-iff-cover-relative",
                            "higherObstructionsVanish": "sagaVerdict/conclusions/higher-obstructions-vanish" } },
      "aliasWitness": { "componentRef": "...", "coveredAtomRefs": [], "uncoveredAliasAtomRefs": [] },
      "nonClaims": [ "comparison data not supplied: comparison bridge is not drawn",
                     "repair synthesis / minimality is not claimed" ] },
      // 注: この例は faithfulness: "complete-support" なので十分性方向(r∈B¹ ⇒ 貼り合う)は描いてよい
      //     (part_10 定理3.5 Complete-Support Faithfulness)。faithfulness: "absent" の packet では
      //     nonClaims に "faithfulness not supplied: sufficiency direction is not drawn" が入り、
      //     吸収アニメは配線されない(§3.4 [B] の gate)。golden fixture は両状態を別 fixture として固定する。

    "spectrumLandscape": {}, "atomGlyphs": [],
    "analyticOverlayBundle": { /* 既存 5 種 + 描画解禁: transferCost / singularityConcentration */ },
    "periodStokes": { /* 既存(meters を描画へ) */ },
    "omittedGeometryCounts": {}, "nonClaims": []
  },

  "atomNodes": [], "insightQueue": [], "actionQueue": [], "guidedTours": [], "copyBlocks": {},
  "viewerVisualScenes": [ { "sceneId": "saga-descent", "sceneStatus": "active|not_active_for_packet" } ],
  "largeGraphStrategy": {}, "reportPane": {}, "omittedDetailCounts": {}, "nonConclusions": []
}
```

**contract 規律(schema に埋める不変条件)**:

1. verdict 相当の値はすべて measurement packet の `structuralVerdict[]` / SAGA packet 区画への **ref** であり、viewer data 内で独立に真偽を持たない(anti-weakening: 結論を viewer 入力に格納しない — `research/goals/G-aat-quality-surface-06.md` と同じ規律の viewer 版)。具体的に: (a) 判定語 literal(`lawful_local_section` 等)を viewer data のフィールド値に置かない、(b) verdict の boolean コピー(`exists: true` 等)を置かない — 表示は参照先 verdict 行の内容のみを反映する、(c) 「emit されたか」の判定は **ref の解決可能性**(非 null かつ参照先が実在)で行い、presence flag を別途持たない。verdict 性を持たないフィールド(supplied-layers の供給状態、`status: "active"` の区画存在表示、structure レーンの computed invariant)はこの規律の対象外だが、schema コメントで「not a verdict」を明示する。
2. 新設 block はすべて optional。不在は沈黙であり、viewer は該当要素を描かずフォールバックする。旧 v2 artifact を v3 viewer が読めること(graceful degradation)をテスト契約にする。
3. `projectionBoundary` / `nonClaims` は Rust 側 hard-code + test-lock の現行方式を継続(artifact 自身が「viewer は verdict を作らない」を宣言する構図)。
4. 改名・廃止(段2 の独立 PR に集約): `schemaVersion` → `schema` キー、slash 命名、`coherenceClaim` → `triangles[].coherence.{status,verdictRef}`(rename)、廃止 = `moleculeGroups`(v2 に molecule は存在しない・未使用)、`atomEdges`(未使用)、`viewerVisualScenes[].axisMapping / axisMetricBindings / layers`(axis 駆動レイアウトの放棄を schema にも反映)。対象 emitter は 3 箇所(measurement viewer data builder / `main.rs:1223` validation-failure viewer data / `schema_catalog.rs:307,453`)。
5. verdictRef の形式は既存の安定形式 `structuralVerdict/{evaluator}/{law}/{method_status}`(`ag_measurement.rs:5611`)に統一する。行 index 形式は導入しない。SAGA packet 区画への ref 形式(仮 `sagaVerdict/...`)は SAGA evaluator の行スキーマ確定時に同じ「安定 segment、非 index」原則で定める(未決事項1)。

### 3.6 CLI とデータフロー

新コマンドは増やさない。`analyze` 単一入口を維持し、viewer data v3 は analyze の出力の 1 つのまま。

```bash
# 計測(viewer data を含む全 artifact を出力)
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap map.json --law-policy policy.json --out-dir .tmp/run1

# 閲覧(sibling fetch 契約は現行どおり。vendoring 後は vendor/ を必ず随伴させる)
cp -r tools/archview/archview.html tools/archview/vendor .tmp/run1/
python3 -m http.server 0 --directory .tmp/run1
```

vendoring(§3.7-2)後は html 単体コピーでは `./vendor/` の import が 404 になり viewer が空表示になるため、**閲覧手順は `archview.html` + `vendor/` の同時コピーを正とする**。`examples/seam-ignition/build-sequence.sh`(現行 `:24` で html 単体コピー)も同型に更新する。release bundle・README の手順記載・cli.rs の packaging 契約テストの更新は Phase V-A の作業項目として §5.1 に列挙する。

sequence mode は `archview-sequence/v2` に更新:

```jsonc
{
  "schema": "archview-sequence/v2",
  "frames": [ { "label": "f0", "dir": "frame-00/" }, { "label": "f1", "dir": "frame-01/" } ],
  "frameComparisons": [                       // 新設・optional: supplied comparison measurement の参照のみ
    { "fromFrame": "f0", "toFrame": "f1",
      "comparisonArtifactRef": "comparisons/f0-f1/archsig-comparison-report.json",
      "transportVerdictRef": "comparisonVerdict/..." } ]   // 参照先 artifact 内の verdict 行への ref
}
```

- **sequence manifest にも §3.5 規律1 を適用する**(viewer data と sequence manifest の非対称を残さない): manifest は CI または人手で組む supplied 入力であるため、`zeroTransport: "preserved"` のような **verdict 相当の literal を manifest に置くことを禁止**する。manifest author による「計算結果の先書き」(観測純化 PRD が塞いだ形と同型)を構造的に不可能にする。
- transport 帯の表示条件: `transportVerdictRef` が `comparisonArtifactRef` の指す comparison measurement artifact 内の verdict 行に**解決でき、かつ参照先 verdict が transport を emit している場合のみ**。「not-supplied」という値は存在しない — entry の不在(または ref 不解決)が沈黙であり、帯を描かない。
- **equivalence 前提の所在**: 第VIII部 定理7.3 の zero transport 同値は refactor morphism 一般ではなく **equivalence + 係数同型等の前提の下でのみ**成立する(part_8:522-546)。双方向の「zero verdict transports both ways」帯は、参照先 comparison verdict がこの前提を検査して emit した行である場合のみ。equivalence data の無い比較(定義7.2 の一方向 pullback のみ)では、参照先 verdict が語る片方向以上を描かない。前提の検査と行スキーマは comparison artifact(archsig compare 系、artifact/CI 次元)の管轄で、viewer は参照先 verdict の内容のみを反映する。
- `frameComparisons` が無い場合の挙動は現行どおり: **隣接 frame の emitted conclusion の変化をラベルするだけ**(補間なし・新 verdict なし・fetch 失敗 frame は灰 tick)。CI の版間比較で「同じ障害の追跡」を語るにはこのデータが必須 — comparison data なしの cross-run claim を viewer が作らないことの明文化。frame 間 comparison artifact の生成と形状は CI/artifact 次元の管轄で、viewer 側は上記の**束縛要件(literal 禁止・ref 解決条件)を投影 contract 側の不変条件として先に固定**する(未決事項2)。

### 3.7 技術方式

1. **no-build 単一 HTML を維持**。フレームワークなし、CSS/JS インライン、決定論レンダリング(`Math.random` 不使用)を継続。規模見積り: 現行 1,875 行 → 3,200〜3,800 行程度(9 シーン + SAGA ビュー + G1–G10)。単一ファイルの可読性維持のため、ファイル内をセクションコメントで `// === [G4] cochain layer ===` の形に区画する(ビルドは導入しない)。
2. **Three.js の vendoring**(offline 問題の解消): unpkg importmap をやめ、`tools/archview/vendor/three.module.js` + `vendor/addons/`(OrbitControls / RoomEnvironment / EffectComposer / UnrealBloomPass 等、計 ~1.3MB)を同梱し、importmap を相対パス `./vendor/…` に向ける。バージョンは r0.164.1 に pin(現行と同一)し、更新は明示 PR でのみ。**随伴作業(同一 PR に含める)**: (a) `archsig-release.yml` の package 手順に `package/archview/vendor/` を追加、(b) cli.rs の release workflow 契約テスト(`tests/cli.rs:13931` 付近 — `package/archview/archview.html` の存在 assert と `package/archview/examples` の不在 assert)に vendor 同梱の assert を追加、(c) §3.6 の閲覧手順・`examples/seam-ignition/build-sequence.sh`・README の「html + vendor 同時コピー」化。no-build は保たれ、ローカルサーバさえあれば offline で動く。
3. **大規模化**: `largeGraphStrategy.thresholds` の実装に着手する。(a) atoms > `instancedAtoms`(10,000)で family 別 InstancedMesh へ切替(グリフ形状は family ごとに 1 geometry)、(b) contexts > 400 で現行の緩和 0 回縮退の代わりに **cover 単位の cluster_aggregation**(cover ごとに重心 1 セル + `topInsightEvidencePinning.preservedRefs` の要素のみ実体化)、(c) sceneLayerObjects 超過時は omitted カウントを HUD に表示(既存 `omittedGeometryCounts` の可視化)。
4. **レイアウト**: 基本は現行の「実測 nerve トポロジー駆動 force-directed + hash は declump のみ」を維持。追加は 2 つだけ: (a) `site-order` シーンでは y = `posetDepth × 定数`(x,z は force の水平成分)、(b) `saga-descent` シーンは repair cover 専用レイアウト(chart floor は円環配置、nerve 中間帯はその上方に対応射影)。どちらも決定論。
5. **アニメーション**(G5 の snap、SAGA の absorption): 再生ボタンによる明示トリガー + 一時停止/スクラブ。振付は実測フィールドの純関数(乱数なし)。中間フレームに verdict 的意味を与えないことを README 忠実性契約に追記。カメラは軽い ease トゥイーンのみ導入(V12 の簡易版)。
6. **テスト**: 現行方式を継続 — `tools/archsig/tests/cli.rs` の HTML 文字列契約(シーン名・legend 文言・nonClaim 文言・SCENE_MAP)+ `window.__arch.diag()`。追加: (a) `__arch.diag()` に `laneCounts`(レーン別オブジェクト数)と `sceneStatuses` を追加し、golden fixture ごとに期待値を固定、(b) v2 artifact を v3 viewer に食わせる後方互換テスト、(c) SAGA fixture(circle nerve 例9.2 / lawful firing 例9.1 の 2 witness を別 fixture として — 混同禁止の boundary note に対応)+ faithfulness `complete-support` / `absent` の両状態 fixture(§3.5 のサンプル注記に対応。誤った層状態×nonClaim 組合せの test-lock を防ぐ)。
7. **versioning**: `archview.html` 冒頭に `const ARCHVIEW_VERSION = "0.5.0"; const ACCEPTED_SCHEMAS = ["archsig-atom-viewer-data/v3", "archsig-atom-viewer-data-v2"];` を宣言。未知 schema は「this viewer cannot read schema X(silence, not an error)」のバナー表示で停止(黙って部分描画しない)。

### 3.8 既存 viewer PRD 群の吸収/破棄判断

| PRD / ノート | 判断 | 内訳 |
| --- | --- | --- |
| insight viewer PRD(v0.4.0、2032 行) | **artifact 側は維持、viewer 側は本設計が supersede** | 吸収: insight card / guided tour / action queue / copy blocks / boundary 台帳(R20-R21)/ large graph 縮退(R23)/ golden UX fixture(R25)/ 非3D可読性(R22)。破棄: 12 シーン語彙の viewer 実装(9 シーンへ再編)、axisMapping 幾何駆動(R7 系) |
| gluing geometry PRD #2082(MERGED) | **データ投影は維持、描画要求は本設計へ吸収** | 吸収: R1 nerve / R2 cocycle ribbon / R3 locusField(**未描画状態の解消が本設計 G6**)/ R4 cage / R5 repair morph / R6 atom glyph / R8 encoding 固定 / R9 projection boundary。破棄: R7 axisMapping 幾何実装 |
| M+V 統合 PRD #2217 | **M 側は現存・無関係に維持。V 側は選別復活** | 復活: V6 locusField 膜(→G6)、V7 b₁ 閉路(→G3)、V13 assembly snap(→G5)、V16 Stokes メーター(→G9)、V11 は H⁰/H¹/H² の表示トグルとして簡素化、V5 鉛直三層は SAGA ビュー内の H⁰ 床/H¹ 中間帯として限定復活、V12 は軽量カメラトゥイーンのみ。破棄: V9 demote-hash(ArchView の別解で不要化済み)、V14 breathing fiber bundle(前提 fixture 消滅・演出過多)、V4 の完全なラベル atlas(実害小、未決事項へ) |
| 3D enrichment note(2026-06-15) | **歴史文書として保持(archive 相当)** | 診断(hash 支配・沈黙の赤エラー化)は ArchView で解消済み。T3/T4 の大胆案は破棄 |

処理方法: v0.5.0 の PRD 作成時に、上記 3 PRD の冒頭へ「superseded by v0.5.0 ArchView redesign(docs/note の本設計ノート参照)」の 1 行を追記する提案を含める(既存 PRD 本文の書き換えはしない)。

## 4. 境界規律との整合

- **viewer は verdict を作らない**: 全新規視覚要素は §3.2 の台帳で投影元フィールドに束縛。verdict 相当値はすべて packet への ref(§3.5 規律1)。**structure レーンのフィールドから verdict レーンの表示を導出しない**(G3 の H¹=0 バッジは forest フラグではなく guarantee verdictRef で点く)。アニメーションは実測値の提示順序であり、中間状態に判定的意味を与えない。この規律は viewer data だけでなく sequence manifest にも適用する(§3.6 — supplied manifest に verdict literal を置かない)。
- **肯定的結論の主役化**: measured_zero 盆地が画面の「地」(G6)、global section sheet と ∃! 冠が descent の到達点(G5、SAGA [D])、H¹=0 保証バッジ(G3、verdict 行参照)。非結論一覧は reportPane の隅と boundary-silence シーンに留める。
- **ウィトゲンシュタイン的沈黙**: comparison / refinement data 不在 → 橋・矢印を描かない(エラー扱いしない)。faithfulness 不在 → SAGA の十分性方向(貼り合う、の言い切り)を描かず、無条件に成立する必要性方向(r ∉ B¹ ⇒ 貼り合わない)だけを描く(§3.4 [B] にインライン gate として明記済み)。H² 未計測 → frosted 維持。すべて「silence, not a verdict」文言つき。
- **capacity ≠ class**(原則4.4)、**analytic ≠ structural**(定義3.3): レーン分離(§3.1)と「lavender は lawfulness を駆動しない」脚注の test-lock で担保。**class 零 ≠ 大域 section**(原則4.4 逆向き): G5 の融合 sheet は effectivity verdict 参照時のみ。
- **理論の claim boundary 内のラベル**: G7 の Tor テザーは「joint repair must account for derived compatibility residue」まで(part_5 の主張範囲)。操作的不可能性(「独立に修理できない」)は operation semantics の管轄外であり copy string に載せない。
- **無制限 claim の不在**: cross-run(sequence)・cross-cover(refinement)の同一性主張は supplied data の投影がある場合のみ(定理8.4/8.5 の viewer 実装形)。cross-run の zero transport は comparison measurement の verdict 行参照のみで表示し、equivalence 前提なしに双方向を描かない(定理7.3 の前提、§3.6)。extraction completeness・コード全体品質は viewer のどの surface にも現れない(`research/goals/G-aat-quality-surface-06.md` boundary の踏襲)。
- **境界の一括払い**: supplied-layers gauge(SAGA [E])は「結論がここまでである理由」を ArchMap / LawPolicy 側の supplied data の状態として表示する。viewer 内に観測の言い訳や補完を分散させない — 足りない層は入力 contract の責務として 1 箇所(ゲージ)で示す。
- **Rust と Lean の対応は要求しない**: 10 結論パネルの構造は Lean 構造体の分割を**語彙として借りる**だけで、viewer が Lean 証明を参照・検証する仕掛けは持たない。

## 5. 移行とリスク

### 5.1 段階(計測=主・可視化=従の順序で)

- **Phase V-A(artifact 変更なし・即着手可)**: packet / viewer data 既在フィールドの描画解禁 — locusField 膜(G6 前半)、**H² coherence 膜(G8。coherenceClaim / structuralVerdictRef / h2CoherenceVisualized は投影済み、描画のみ)**、periodStokes.meters(G9)、transferCost / singularityConcentration(G10)、M2/M3/M5/M6 verdict の insight レーン表示。捏造リスクゼロ。Three.js vendoring とその随伴作業(archsig-release.yml package 手順 + cli.rs packaging 契約テスト + 閲覧手順/build-sequence.sh/README の vendor 同時コピー化 — §3.7-2)、`__arch.diag()` 拡張もここ。
- **Phase V-B1(v2 のまま optional block 追加 = artifact 次元との共同)**: posetDepth / coverRelations / nerve.topology(guarantee 含む)/ cochainLayer / descent / lawConflict の投影追加と、site-order / cover-nerve / gluing-h1 / locus-repair / law-conflict シーンの実装。repairDual もここ(**投影のみ。計測次元への依存なし** — hitting sets は packet に emit 済み)。schema は `archsig-atom-viewer-data-v2` のまま optional 追加とし、§3.5 規律2 で既存テストへの破壊を局所化。G3 guarantee の verdict 行(定理12.4 の 3 前提検査)は計測次元への contract 要求。
- **Phase V-B2(v3 改名 PR、独立)**: `schemaVersion` → `schema`・slash 命名・coherenceClaim rename・moleculeGroups / atomEdges / axisMapping 系 emit 停止を、3 emitter(measurement builder / `main.rs:1223` validation-failure / `schema_catalog.rs`)+ cli.rs 契約テストごと一括更新。新機能を含めない純粋な改名 PR とし、破壊範囲の切り分けを可能にする。
- **Phase V-C(SAGA evaluator land 後)**: sagaDescent 区画の投影 + SAGA ビュー。M→V gating の踏襲: 計測が先、可視化が従。circle nerve / lawful firing の 2 golden fixture + faithfulness 両状態 fixture を同時に固定。

### 5.2 リスクと緩和

| リスク | 緩和 |
| --- | --- |
| 単一 HTML の肥大(~3,800 行)で保守性低下 | セクションコメント区画 + `__arch.diag()` の機械検査面を広げる。それでも 5,000 行を超える見込みになったら「no-build のまま複数 `<script type="module">` ファイル + 相対 import」への分割を別 PRD で検討(ビルドは導入しない) |
| cli.rs(17,346 行)の HTML 文字列契約テストが v3 化で大量に割れる | **改名(V-B2)と block 追加(V-B1)を別 PR に分離**(§5.1)。Phase ごとに契約テストを段階更新。文字列契約は「シーン名・legend・nonClaim 文言」の意味論的な行に限定し、実装詳細行への固定を減らす |
| 投影追加(Rust 側)が ag_measurement.rs 単一ファイル肥大を悪化させる | artifact 次元のモジュール分割(viewer projection を独立モジュールへ)と同時に行う。本設計は投影 contract のみ規定し、Rust 内部配置は artifact 次元に委ねる |
| Three.js vendoring でリポジトリ +1.3MB | release bundle 同梱は必須、リポジトリ内 vendor はサイズ許容と判断(git-lfs は不要な規模)。許容できない場合は「repo は importmap CDN、release bundle のみ vendor」の折衷(未決事項へ)。いずれの場合も閲覧手順は「html + vendor 同時コピー」を正とする(§3.6) |
| 旧 v2 artifact との互換 | v3 viewer は v2 schema を受理し新規要素を沈黙させる(§3.5 規律2 + 後方互換テスト)。逆(v2 viewer に v3 data)は schema バナーで明示停止 |
| SAGA ビューが計測より先行する誘惑 | sceneStatus gating(§3.4 解放条件)を schema と test で固定。sagaDescent 区画が無い packet で SAGA シーンの 3D 要素を 1 個も生成しないことを `__arch.diag().laneCounts` で検査 |
| viewer / manifest への verdict literal 混入 | §3.5 規律1(literal・boolean コピー禁止、ref 解決可能性で presence 判定)+ §3.6 の sequence manifest 束縛。golden fixture に「verdict literal を含まないこと」の schema 検査を追加 |
| O(n²) layout の限界 | Phase V-B1 で cluster_aggregation(§3.7-3)。>400 contexts の実利用が出るまでは既存縮退で可 |

### 5.3 削除・破棄(v0.5.0 レガシー破棄との整合)

- v1 viewer data(`archsig-atom-viewer-data-v1`、typed_evaluator 内)は v1 path 削除と運命共同体 — ArchView は v2 のみ読む実装のため viewer 側の作業はゼロ(reader_archsig-code §9.2-10)。
- `schema/viewer.rs`(v0 型、dead)と孤児 `cli/atom_viewer.rs` / `cli/detail_index.rs` は artifact 次元の削除リストに含まれる前提(viewer 側依存なし)。
- `moleculeGroups` / `atomEdges` / `axisMapping` 系フィールドの emit 停止は **Phase V-B2 の独立改名 PR** で行う(§3.5 規律4)。

## 6. 未決事項

1. **SAGA evaluator の id と packet 区画名**(仮称 `ag.saga-descent@1` / `ag.saga-comparison@1`)— 計測次元の管轄。本設計の `sagaDescent` 区画は投影側の受け皿としてフィールド名を提案するが、計測側の verdict 行スキーマ(boundaryMembership を structuralVerdict のどの行形式で出すか、`sagaVerdict/...` ref の安定 segment 形式)が確定してから最終化する。ref 形式は §3.5 規律5 の「安定 segment、非 index」原則に従う。
2. **cover refinement / frame comparison data の artifact 形状**(ArchMap 内か、別 artifact か)— artifact/CI 次元との調整。viewer は `coverRelations[]` / `frameComparisons[]` の投影 contract のみ先に固定する。**確定済みの不変条件**(artifact 形状に先行して固定、§3.6): frameComparisons は verdict literal を持たず、`comparisonArtifactRef` + `transportVerdictRef` の参照のみ。transport 帯は ref が解決でき参照先 verdict が transport を emit している場合のみ。双方向表示は定理7.3 の equivalence 前提を検査した verdict 行に限る。
3. **schema 命名統一の最終形**(`archsig-atom-viewer-data/v3` の slash 形式、`schemaVersion` → `schema` キー統一)— artifact 次元の命名規約に従属。実施は Phase V-B2 の独立 PR(§3.5、対象 3 emitter を同 PR で一括)。
4. **`viewerVisualScenes` 12 語彙の扱い** — 9 シーンへ registry を更新するか、写像表(SCENE_MAP)で吸収し続けるか。registry 更新は insight card の `viewerNavigation.sceneId` 互換に波及するため artifact 次元と要調整。
5. **Three.js vendor をリポジトリに置くか release bundle のみか**(+1.3MB の許容判断)。
6. **解決済み**(査読指摘14): `repairDual.minimalHittingSets` は `ag.square-free-repair@1` の既存計算から投影できる — `minimal_hitting_sets` は `ag_measurement.rs:1183` で計算され、`:1263` / `:1298` で computed invariants に `minimalHittingSets` として emit 済み。evaluator 拡張は不要、packet → viewer data の投影追加のみ(Rust 側作業のため Phase V-B1、計測次元への依存なし)。
7. **ラベル atlas / 衝突回避(旧 V4)** — 現状実害が小さいため見送り候補。cluster_aggregation 実装時に再評価。
8. **ヘッドレス screenshot の CI 出口**(Playwright + `__arch.diag()` は既にあるが、PR コメントへの画像添付は CI 次元の判断)— viewer 側は診断フックの拡張(§3.7-6)までを担当範囲とする。
9. **H⁰/H¹/H² 鉛直三層(旧 V5)の全シーン適用** — 本設計では SAGA ビュー限定。全シーン適用は「高さ = 次数」が G1 の「高さ = posetDepth」と衝突するため、シーンごとの高さ意味の宣言(HUD)を含めて Phase V-B1 実装時に判断。

## 査読対応

15 指摘すべてを妥当と判断し反映した(不採用なし)。各指摘の裏付けは実コード・理論本文で再実測済み。

| # | 採否 | 反映箇所と要点 |
| --- | --- | --- |
| 1 [boundary/minor] | **採用** | G3(§3.2)を改訂。提案の選択肢のうち「nerve.topology に guarantee 用 verdictRef フィールドを追加し、ArchSig が emit した行にのみバッジを結ぶ」形を採用(指摘4 の 3 前提検査要件と統合するため。既存 H¹ measured_zero 行への直接束縛では定理12.4 の前提検査が ref に表現されない)。forest は structure レーンの HUD 事実表示に格下げ。原則3 と §3.1 に「structure レーンのフィールドで verdict レーンを点けない」を明文化 |
| 2 [boundary/minor] | **採用** | §3.5 schema 例と規律1 を改訂。(1) `sectionAssignments[].status` の判定語 literal を `verdictRef` に置換、(2) `globalSection.{exists,unique}` boolean と `sourceField` を廃し `verdictRef` のみに(表示は参照先の内容を反映)、(3) `conclusions.*` を「packet 結論行への ref 文字列 | null(沈黙)」に統一。規律1 に literal 禁止・boolean コピー禁止・presence は ref 解決可能性で判定、を明記。verdict 性を持たないフィールド(suppliedLayers 等)は「not a verdict」コメントで区別 |
| 3 [boundary/minor] | **採用** | §3.6 を改訂。`zeroTransport` literal を廃し `comparisonArtifactRef` + `transportVerdictRef` の参照に置換。"not-supplied" は値ではなく entry 不在(沈黙)と定義。帯の表示条件を「ref 解決 + 参照先 verdict が transport を emit」に固定。未決事項2 に束縛要件を artifact 形状確定に先行する不変条件として明文化。§4 に「規律1 は sequence manifest にも適用」を追記 |
| 4 [theory/major] | **採用** | 指摘1 と統合して G3 を改訂。定理12.4 の 3 前提(forest / no triple faces / restriction 全射性)は part_4:1437-1463 で確認。バッジの trigger を forest フラグから `guarantee.verdictRef`(計測側が 3 前提をすべて検査して emit した measured_zero 行)に変更。バッジ文言も「forest ⇒ H¹=0」から「H¹ = 0 (measured; Thm 12.4 regime)」へ(定理適用の主語を viewer から計測へ移す)。§4 の該当行も更新 |
| 5 [theory/major] | **採用** | G5 を改訂。原則4.4 逆向き(part_4:456-490、effectivity assumption 必須)を確認。gluingStatus を `classZeroVerdictRef` / `effectiveGluingVerdictRef` に分離し、融合 sheet は後者(effective-gluing 系 verdict 行)が解決できるときのみ。class 零のみでは seam 消灯 + 「obstruction class zero」チップ止まり。contract invariant として「effectiveGluingVerdictRef に class 零 verdict を入れてはならない」を明記。§4 に「class 零 ≠ 大域 section」を追加 |
| 6 [theory/major] | **採用** | G7 のラベルを「shared witness: x — joint repair must account for derived compatibility residue (Part V)」に変更(part_5:531-550 の主張範囲を確認)。detail panel に「repair 操作の可否は operation semantics の管轄外」の boundary note を固定し、操作的不可能性の文言を copy string から排除する旨を明記。§3.3 シーン6 の問い(「独立に直せるか」)はシーンの問いであって結論ラベルではない旨を注記 |
| 7 [theory/minor] | **採用** | 指摘3 と統合して §3.6 を改訂。加えて定理7.3 の equivalence 前提(part_8:522-546 で確認)を反映: 双方向 transport 帯は equivalence 前提を検査した verdict 行に限り、equivalence data の無い比較では参照先 verdict が語る片方向以上を描かない。前提検査は comparison artifact 側の管轄と明記 |
| 8 [theory/minor] | **採用** | G6 の「appendix B.5」を「appendix B.4(Square-Free Obstruction Ideal)」に修正(appendix.md:558 で確認。B.5 は Monomial Tor Conflict) |
| 9 [theory/minor] | **採用** | §3.5 サンプルを整合化: faithfulness "complete-support" を保持し(part_10 定理3.5 で十分性方向を描けることを確認)、矛盾していた nonClaim を comparison 不在の nonClaim に差し替え。faithfulness "absent" の場合の nonClaim と吸収アニメ非配線をサンプル注記に明示し、両状態を別 golden fixture とすることを §3.7-6 に追加。§3.4 [B] の r∈B¹ ビュレットに faithfulness gate をインラインで明記 |
| 10 [theory/minor] | **採用** | G3 に contract invariant を明記: `topology.b1` = nerveComplexB1(面込み複体の Betti 数、系12.3 part_4:1418-1435 の読み)、`cycleBasis` = 面で埋まらない閉路の基底。`oneSkeletonB1` を別名フィールドとして schema 例に併載(ag_measurement.rs:6321-6333 の既存 distinction に一致)。面で埋まる閉路を capacity チューブとして立てない旨を明記 |
| 11 [feasibility/major] | **採用** | 実測で確認(project_h2_coherence_to_cover_nerve = ag_measurement.rs:10245、analyze 接続 = :4337、test-lock = tests/cli.rs:2423、viewer parse = archview.html:501)。G8 を「既存フィールドの描画解禁」に書き換え Phase V-A へ移動。P6 の現状記述を「計測・投影は在る、viewer 描画のみ沈黙」に修正。v3 での `coherenceClaim` → `triangles[].coherence` は「新設」ではなく rename として §3.5 規律4 の改名リストへ移し、計測次元への contract 要求から除外 |
| 12 [feasibility/minor] | **採用** | §3.6 の閲覧手順を「cp -r archview.html + vendor/」に更新し、build-sequence.sh(:24)の同型修正を明記。§3.7-2 に随伴作業として archsig-release.yml の package 手順更新と cli.rs packaging 契約テスト(:13931 付近、examples 不在 assert を確認)の更新を列挙し、Phase V-A の作業項目に含めた |
| 13 [feasibility/minor] | **採用** | 実測で確認(structural_verdict_ref = ag_measurement.rs:5611、`structuralVerdict/{evaluator}/{law}/{method_status}` 形式)。§3.5 の全 verdictRef 例を既存安定形式に統一し、行 index 形式(#0)を廃止。規律5 として「ref 形式は既存安定形式に統一、index 形式は導入しない」を新設。SAGA 系 ref も同原則に従う旨を未決事項1 に追記 |
| 14 [feasibility/minor] | **採用** | 実測で確認(minimal_hitting_sets = ag_measurement.rs:1183、emit = :1263/:1298)。未決事項6 を解決済みとして閉じ、G6 に「既存 packet フィールドの投影のみ、evaluator 変更なし」を明記。Phase V-B1 に「計測次元への依存なし」を反映 |
| 15 [feasibility/minor] | **採用** | 実測で確認(第二 emitter = main.rs:1223、catalog 登録 = schema_catalog.rs:307/453)。§3.5 に 2 段移行(V-B1 = v2 のまま optional block 追加 / V-B2 = 改名・廃止の独立 PR)を明記し、v3 移行対象 emitter 3 箇所を列挙。§5.1 の Phase 表を V-B1/V-B2 に分割し、§5.2 のテスト破壊リスク緩和と §5.3 の emit 停止時期も同期 |
