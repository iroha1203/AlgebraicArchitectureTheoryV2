# ArchSig 計測忠実性の補強と可視化ロードマップ 設計考察ノート

日付: 2026-06-15

対象:
- `tools/archsig/src/ag_measurement.rs`(`analyze` の archmap/v2 一次経路、`build_foundation_measurement_packet_v1` と 6 つの `ag.*` 評価器)
- `tools/archsig/src/schema/measurement.rs` / `tools/archsig/src/schema/law_policy.rs`(MeasurementProfile/v1, archsig-measurement-packet/v1, 5値 verdict, CBI ledger)
- `tools/archsig/src/law_policy/registry.rs`(`ag_manifest`、評価器 law 登録)
- `docs/aat/algebraic_geometric_theory/`(9部理論本文。Part III–VIII を計測 anchor とする)

下流(可視化フェーズ)として参照する先行ノート:
- `docs/note/aat_archsig_viewer_3d_enrichment_proposal.md`(3D viewer リッチ化。本ノートは計測=主、その viewer ノートを従として位置づける)

本ノートの背骨は **計測を先に補強し、補強された計測の数学的中身に応じて正しい3D可視化を従として組む** という順序である。可視化を先に磨かない。計測なしに可視化を先行させると、計測されていない構造を viewer が描く=捏造になる。本ノート全体でこの主従関係を規律として保つ。

---

## 問い

現状 ArchSig は AAT 代数幾何版(9部)のどこまでを忠実に測れているか。可視化を磨く前に、計測の数学的中身をどこまで AG 本文に忠実化・多様化すべきか。

これは「viewer をどう豪華にするか」ではなく「**何を計測しているか、その計測が AG 本文に対してどれだけ正直か**」を先に確定する問いである。問いの立て方には少なくとも次の3候補があり、どれを採るかで補強の射程と PRD の切り方が変わる。

- **候補A: 忠実性の核を一点突破。** 「最も多用される計測(H^1 Čech の `measured_zero`、Tor proxy、section の lawful 述語)の暗黙前提・proxy を、有限 checked へ昇格する」を判定規律にする。効き: 既存 verdict の意味論的射程を深める。新しい計測軸はほぼ増やさず、`measured_zero` を支える assumption ledger と proxy を本文どおりに固める。摩擦最小・即効。ただし「測れる種類」は広がらない。
- **候補B: 沈黙ギャップを埋める広い計測拡張。** 「現状 `not_measured_silence` だが AG 本文が有限計測可能と定義している不変量(H^2 coherence、boundary residue δ、restriction-compatibility)を profile 内で新規計測する」を判定規律にする。効き: 測れる構造の種類が増え、viewer に新しい幾何(三角膜の開閉、縫い目の裂け、神経辺の段差)が解放される。射程は広いが、新 evaluator・新 fixture・新 schema 行が要り、各々で境界規律(profile 外計測しない・新 verdict 乱造しない・沈黙を侵さない)を都度引き直す必要がある。
- **候補C: 既測だが未投影の活用優先。** 「すでに完全計算されているのに viewer に届いていない analytic reading(period-stokes の stokesAudit / pairing matrix、support-transfer の Wasserstein cost、laplacian の spectral gap)を、analytic レーンの overlay として投影する」を判定規律にする。効き: 計測ロジックを一切変えず、measured-not-projected を解消する。実装最小・低リスクだが、解放されるのは proxy/modelRelative の幾何のみで、構造判定(`measured_zero/nonzero`)の忠実性は深まらない。

**推奨スタンス:** A を核に置き、B のうち最も低摩擦で本文忠実な一点(H^2 coherence)を続けて立て、C は overlay バンドルとして後置する。理由は後述の PRD 候補で詳述する。この三候補は排他ではなく優先順位の問いである。

---

## 計測忠実性マップ

9部理論の有限計測可能不変量を、現状 ArchSig での状態で分類する。状態は4値:

- `measured_faithful` — profile 内で本文どおりに忠実計測済み。
- `measured_proxy` — 計測値は出るが、本文の不変量そのものではなく proxy/上界/modelRelative。
- `measured_not_projected` — 忠実に計測済みだが viewer に届いていない。
- `not_measured_silence` — 計測していない(沈黙)。沈黙が正しい場合と、有限計測可能なのに埋めていない忠実性 gap の場合を区別する。

| 不変量 | 理論 anchor | 現状 | 忠実性ギャップ | 下流が解放する可視化 |
| --- | --- | --- | --- | --- |
| H^1 Čech 障害 `[g]`(`ag.cech-obstruction@1`) | 第IV部 定義3.2/3.3, 定理7.1/11.1 | `measured_faithful` | 計測自体は F2 1-cocycle/coboundary を XOR 伝播で厳密判定。gap は `measured_zero` の射程を支える torsor effectivity / surjective restriction が ledger に全行開示されていない点 | cocycle ribbon(seam の閉/開) |
| I_Ob^U 障害イデアル / Stanley-Reisner(`ag.square-free-repair@1`) | 第III部 定理5.6C, 系5.6D | `measured_faithful` | combinatorial に忠実。gap は restriction-compatibility(sheaf 条件の前段)を単一 context しか見ず assumed のまま放置 | forbidden cage |
| lawful locus Flat_U(X)=V(I_Δ) の arrangement | 第III部 定理5.6C, 定理11.1 | `measured_not_projected` | faces は packet 内にあるが facets(既約成分=座標部分空間 arrangement)を幾何に投影していない | lawful locus 薄板(立てる/立てない面) |
| Δ_U の facet 次元・link(boundary-local reading) | 第III部 系5.6D | `measured_not_projected` | faces/betti は計測済みだが系5.6D が挙げる link/facet 構造を invariant 行にしていない。**注意: depth/Cohen-Macaulay の語彙は本理論が anchor しないので禁止** | locus 薄板の厚み・頂点の裂け目 |
| section factorization s^* I_Ob^U=0 | 第III部 定理11.1, 定義7.2 | `not_measured_silence` | lawful の核心述語かつ Lean proved(`lawful_iff_factorsThroughLawfulLocus`)。ArchSig は section 概念を持たず generator presence で代用。**有限 checkable=沈黙ではなく gap**(ただし section データが contract に無ければ正しく沈黙) | locus 薄板上の section 着地点(緑)/cage 内の捕捉点(赤) |
| NSdepth 単調性(命題7.2C) | 第III部 定理候補7.2A, 命題7.2C | `measured_proxy` | NSdepth 値は外部 payload 依存(hitting-set 上界 proxy)。片側 monotone を計測していない。**「verdict 化」ではなく「reading 化」が正** | law universe 拡大に沿った depth 斜面 |
| H^2 triple-overlap coherence `[h]`(`ag.coherence-obstruction@1` / `ag.h2-coherence@1`) | 第IV部 定義10.1, 意味10.2;第VI部 定義16.1(banded) | `not_measured_silence` | **沈黙が正しい領域ではない。**定義10.1 は Part IV 内の有限不変量。triple-overlap face scaffolding は既に packet 内。banded abelian A=F2 に限れば有限 F2 計測可能 | 三角膜の開閉(pairwise 緑なのに中央が閉じない) |
| 高次 H^n(n≥3)/ stack / gerbe(non-abelian) | 第IV部 原則10.3;第VI部 定義16.1/定理16.2 | `not_measured_silence` | **沈黙が正しい。**n≥3 abelianized は finite-site で計算可能だが Part IV scope 外=silence_by_design。non-abelian gerbe は abelian F2 語彙外=out_of_selected_vocabulary。gap は「沈黙の線引きが typed boundary になっていない」点のみ | 描かない(沈黙を尊重、空白を埋めない) |
| Topological Debt Capacity / b_1(nerve)(`ag.cech-obstruction@1` 拡張) | 第IV部 定理12.2, 系12.3/12.5 | `measured_proxy` | C^2(triple-overlap face 数)が手元にあるのに rank-nullity 容量下界と Euler 交代和に使われていない | nerve 上の独立ループ・穴あき度メーター |
| boundary connecting hom δ: H^0(B)→H^1(`ag.boundary-residue@1`) | 第IV部 定義8.3, 定理9.2 | `not_measured_silence` | Mayer-Vietoris 分解(core/feature/boundary)を区別せず δ の像を計算していない。例9.3 が F2 有限計算として明示。**沈黙ではなく gap**(ただし core/feature/boundary ラベル付き cover という追加 contract が要る) | core/feature の二パッチと縫い目 B の裂け |
| Tor_1 = LawConflict_1(`ag.law-conflict-tor@1`) | 第V部 命題5.5, 定義5.4, 例5.6 | `measured_proxy` | degree-1 shared-support proxy。命題5.5 が要求する Taylor/lcm-multigraded free resolution を組まず、class 数を過大に読みうる | shared-witness edge ごとに分解した衝突 glyph |
| 高次 Tor_i(i≥2) | 第V部 定義5.2, 定理7.3, 定義7.4 | `not_measured_silence` | **沈黙が正しい(計測しない)が gap は型分離。**degree-1 `measured_zero` が derived-transversality(全 i>0)へ誤読されないよう typed boundary で明示すべき | degree-1 region に「高次未測定」ラベル(過剰な緑を抑止) |
| Hilbert series 干渉級数 Int_{U,V}(t) | 第V部 定義12.1, 定理12.2, 原則12.3 | `not_measured_silence` | graded monomial regime なら certified bounded inference。未実装。**audit reading であって verdict ではない** | policy_conflict 上の次数別干渉ヒストグラム |
| support-localized transfer pairing(`ag.support-transfer@1`) | 第V部 定義10.4, 定理10.5/10.6 | `measured_proxy` | transfer 行列を support 非交差 path にも無条件で埋める。support-localized 条件(定義10.4)を計測前提として検査していない | conflict cage→repair path の矢印(交差ありは実線/なしは点線) |
| Stokes audit identity(`ag.period-stokes@1`) | 第IV部 定理13.2, 原則13.3 | `measured_proxy` | 定理13.2 は厳密会計(certified bounded inference)なのに float smallness で hard Err。analytic-only に留め structural に落とせていない | 会計が閉じる loop / 残差が外向きフラックスで突出 |
| strict period pairing matrix(`ag.period-stokes@1`) | 第VII部 定義5.2/5.2A | `measured_proxy` / 計測は modelRelative analytic | 行列は完全計算され packet 内だが、どの projection も読まず viewer に出ない(measured-not-projected) | form×cycle の period landscape(analytic レーン) |
| curvature transfer spectrum / Perron-Frobenius hotspot(`ag.sheaf-laplacian@1`) | 第VIII部 定義8.9, 定理候補8.10;第VII部 原則7.3 | `measured_proxy` | 現 `curvatureTransferSpectrum` は per-cell L·cochain 値で spectrum でも T_curv でもない(名称だけ理論先取り)。principal eigenvector hotspot 未実装 | S×A 上の recurrence 熱だまり(analytic レーン) |
| Wasserstein transfer cost / transferResidue | 第VIII部 定義10.6, 定理候補10.7 | `measured_not_projected` | 完全計算され packet 内だが reading_id 名のみ harvest され量は投影されない | repair→target の obstruction mass 流(analytic レーン) |
| spectral gap λ_1^+(L_1) | 第VIII部 定義8.8, 原則8.4 | `measured_not_projected` | 計算済みだが投影されず、near-flat≠lawful の境界が viewer に無い | hodge-debt 谷の浅深(teal=measured_zero に着色しない) |
| sheaf Laplacian / Hodge / harmonic debt | 第VIII部 定義8.1, 定理8.5/8.6 | `measured_proxy`(graph-laplacian-hodge-proxy@1) | proxy 明示済み。near-flat is not lawful(原則8.4)を保つ限り忠実 | hodge-debt height-field(既存) |
| refactor-invariant transport(rho^*) | 第VIII部 定義7.1/7.2, 定理7.3;第VI部 定義12.1 | `not_measured_silence` | 単一 snapshot しか見ず二 presentation 間の transport を測らない。functoriality data があれば verdict 整合のみ有限監査可能 | 二画面 nerve 並置・対応線・不変 debt の持続色 |
| measured square monodromy μ_x(σ) / AMI_x | 第VI部 定義10.4/10.6, 定理10.5/10.7 | `not_measured_silence` | operation groupoid + coefficient transport が contract に無いので**沈黙が正しい**(原則7.4)。供給時のみ有限 analytic reading。**π1^AAT 自体は不変量にしない** | square 境界 loop の閉じない filling(analytic marker) |
| singularity / stack / gerbe(deformation regime) | 第VI部 定義5.1, 定理6.1/6.2 | `not_measured_silence` | deformation regime(L_{S/U}, T_{S/U}, Ext^1)が無いので structural singularity は**沈黙が正しい**。LawConflict_1 の non-transverse meeting count は analytic reading として語れる(God object size とは呼ばない) | obstruction concentration の analytic 熱だまり |
| 進化幾何(Part IX, temporal obstruction) | 第IX部 定義3.4, 定理4.2 | `not_measured_silence`(ArchSig 対象外) | **ArchSig の責務境界外=silence-by-design。**evolution/flow は FieldSig + SFT 側の責務。ArchSig が temporal obstruction を測ると tool 境界を越える | ArchSig viewer では描かない(FieldSig 側の責務) |

**沈黙が正しい行(侵さない):** 高次 H^n(n≥3)/ non-abelian stack-gerbe、measured square monodromy(transport 不在時)、structural singularity(deformation regime 不在時)、Part IX 進化幾何(tool 境界外)。これらは「残タスク」でも「証明不能な限界」でもなく沈黙である。必要な場合だけ typed boundary として最小限に出す。

---

## 計測補強の提案

採用案を priority 順に整理する。各案は **計測(評価器設計・verdict・境界)→ それが解放する3D可視化** の順で書く。計測が主、可視化が従である。

二系統を区別する:
- **沈黙ギャップ充填**(`not_measured_silence` → 新規 structural verdict / typed boundary)
- **既測だが未投影の活用**(`measured_proxy` / `measured_not_projected` → 忠実化または analytic overlay)

### P0(忠実性の核・即効・低摩擦)

**P0-1: H^1 Čech `measured_zero` の torsor effectivity 前提を assumption ledger 行に明示(定理11.1/12.4 忠実化)**
計測: 計算ロジック・verdict は不変。`ag.cech-obstruction@1` の assumption ledger を拡張し、定理11.1 の `local lawful sections form an effective Ob_U-torsor` / `local adjustment action is fixed and effective` / `coefficient object satisfies descent`、定理12.4 の `restriction maps are surjective` / `nerve is a forest with no triple overlap` を ledger 行にする。`nerveIsForest && !hasTripleOverlapFaces` のときだけ定理12.4 前提を `checked` へ昇格、それ以外は `assumed`。surjective restriction は意味論的性質なので常に `assumed` 固定(ArchSig は構造観測器であって意味論観測器ではない)。
境界: `measured_zero` は「選択 cover 上で 1-cocycle が coboundary」の F2 checked 事実のまま。global lawful section への持ち上げは forest+no-triple のときだけ前提が checked になり、それ以外は assumed(原則7.2 Local Success Is Not Global Lawfulness)。新 verdict ゼロ。
解放する可視化: nerve が forest かつ triple face 無しのとき `measured_zero` patch を濃い緑(確実に閉じる)、torsor effectivity が assumed のとき薄い緑(条件付き)で塗り分け。可視化は ledger の checked/assumed 内訳の従。

**P0-2: restriction-compatibility(sheaf 条件の前段)を有限 checked 化 — `ag.restriction-compatibility@1`**
計測: 沈黙ギャップ充填。各被覆辺 W_i→W_j で res_{ij}(I_Ob^U(W_i)) ⊆ I_Ob^U(W_j) を square-free 生成系の support 包含で有限判定。`measured_zero`=全辺で separated presheaf 条件成立、`measured_nonzero`=ある辺で局所イデアルが上流へ流れない構造的不整合、`not_computed`=被覆辺空/生成系欠落(U-adequate cover violated)。新 EffCoeff `finite-support-inclusion@1`。Lean `ObstructionIdeal.RestrictionCompatible.maps_selected` に正確対応。
境界: 選択 cover・選択 witness 族上の separated presheaf 条件のみ。`measured_nonzero` は「local-sum presentation が sheaf へ持ち上がらない」であって理論対象の defect ではない(sheaf image 再定義で消えうる旨を boundaryNote に明記)。cech `measured_zero` の hedge を Leray とは別に「一段だけ」assumed→checked へ昇格(Leray は依然 assumed)。新 verdict はちょうど1個。
解放する可視化: nerve の各辺を compatibility で色分けし、incompatible 辺を「局所イデアルが上流へ流れ落ちない段差」として高さ場の断層で表示。H^1 cocycle ribbon の前段(presheaf→sheaf 不全)を幾何で見せる。

**P0-3: section factorization s^* I_Ob^U=0 の有限 checked 化 — `ag.section-factorization@1`**
計測: 沈黙ギャップ充填。選択 section(witness 変数への Boolean 割当)について、activeSupport が minimalForbiddenSupports のいずれかを包含すれば s^* I_Ob^U≠0(unlawful section)、一つも包含しなければ=0(lawful section、Δ_U の face に乗る)。`measured_zero`=section-relative lawful、`measured_nonzero`=lawful locus を外れる構造証拠、`not_computed`=section データが contract に無い(沈黙)、`unknown`=部分割当で決定不能。Lean `FiniteExamples.lean` が pullback 機構(zeroEval/oneEval)を既に形式化。
境界: section-relative lawful のみ。全 section lawful・exactness 無しの5項同値・runtime/semantic 安全は非主張。section が無ければ計測せず `not_computed`(沈黙)。No-Cancellation/exactness は assumed ledger。新 verdict は既存5値を再利用。
解放する可視化: lawful locus 薄板(P1-1)の上に具体 section を「面に着地できる点(lawful 緑)か cage に捕まる点(unlawful 赤)か」として落とす。violatedForbiddenSupports を section から cage への赤い射で描く。

**P0-4: Tor_1 を真の monomial free resolution へ昇格(degree-1 proxy からの忠実化)**
計測: 既測 proxy の忠実化。`ag.law-conflict-tor@1` を内部 method `finite-monomial-tor-taylor@1` へ昇格(verdict id は据置)。I_U, I_V の生成元から Taylor 複体を組み R_W/I_V で tensor、F2 で H_1=Tor_1 の dim を取る。各 conflict class に multidegree=lcm(x_S,x_T)=witness support 合成を添付。inert だった `resolution_selector` フィールドを実効化。Lean `Proposition55DirectTheoremPackage` の assertion を計測層へ落とす。
境界: 局所 chart W 相対の monomial Tor のみ。higher Tor_i(i≥2)は沈黙、flat base change 安定性は theorem-candidate のまま、異 ambient 比較は common ambient morphism 無しなら `not_computed`(原則9.3)。F2 homology が field-coefficient reading である旨を ledger に明示。非 square-free monomial を含む cover は `unmeasured`(Taylor regime 外)。
解放する可視化: 各 Tor_1 class を左 forbidden cage と右 forbidden cage を結ぶ shared-witness edge(lcm 変数を持つ)として描き、複数 class を別 edge に分離。policy_conflict カードの単色領域を「衝突 support の glyph」へ分解。可視化は multidegree 計測の従。

### P1(沈黙ギャップ充填の本筋・高価値構造拡張)

**P1-1: H^2 triple-overlap coherence の忠実な有限 F2 計測 — `ag.coherence-obstruction@1`(banded abelian のみ)**
計測: 沈黙ギャップ充填。選択 cover の 2-skeleton 上で H^2 = ker δ2 / im δ1 を F2 で計算。triple-overlap face の section mismatch から 2-cochain h_ijk を組み、δ2 h=0(2-cocycle 条件)を先に検査してから im δ1 への帰属を F2 ガウス消去で判定。`measured_zero`=全 2-cocycle が coboundary、`measured_nonzero`=triple で壊れる concrete class([gerbe] の banded reading)、`unmeasured`=coherence witness atom 不在、`not_computed`=2-skeleton 空 / banding violated。cech と排他でなく共起可能な新 ag.* law として `ag_manifest` に追加。
境界: sheaf cohomology 全体への持ち上げは非主張(cover-relative + Leray assumed)。non-abelian gerbe(一般 Aut(Dec_U)係数)は計測対象外=banding violated で沈黙。原則4.4: nonzero group ≠ 任意 concrete class、`measured_nonzero` は representative を持つ場合のみ。pairwise H^1 が `measured_zero` でも H^2 が `measured_nonzero` になりうる二層を取り違えさせない。
解放する可視化: nerveTriangle の `coherenceClaim` を `not_visualized` から verdict へ flip、`h2CoherenceVisualized=true`(banded case のみ)。`measured_nonzero` の face を「三辺は一致するのに中央で閉じない」glowing な開いた三角膜、`measured_zero` の face を滑らかに閉じた平面膜として描く。**投影 scaffolding(faces with sharedAtomRefs)は既に packet 内にあり、これが最も低摩擦・高 payoff の沈黙反転。**

**P1-2: boundary connecting hom δ: H^0(B)→H^1 の忠実な F2 計測 — `ag.boundary-residue@1`**
計測: 沈黙ギャップ充填。cover を core/feature/boundary に分類する atom を導入し、B=C_core∩F 上の mismatch section b_U を F2 表現、Mayer-Vietoris の d^0 を core⊕F→B の restriction 行列で組み、b_U が im(d^0) に入るか(δ(b_U)=0 か)を F2 ガウス消去で判定。`measured_zero`=boundary residue が吸収され大域障害にならない、`measured_nonzero`=boundary residue が大域 H^1 class を生む。例9.3 が F2 有限計算として明示。
境界: F2 パリティは Z holonomy の mod2 還元なので coefficient=F2 を ledger に checked、Z-zero への持ち上げは assumed。定理9.2 の iff は重い仮定スタックに相対化され、coefficient 非固定時は片方向 obstruction statement(δ≠0→not globally U-flat)に退く。period-Stokes pairing(modelRelative)とは分離し δ の structural 像のみ verdict に。原則7.2 を核に「core/feature が各々 lawful でも boundary residue は消えるとは限らない」を主張。
解放する可視化: C_core と F を二パッチ、境界 B を縫い目として描く。δ=`measured_nonzero` のとき縫い目が「閉じない裂け目」として開き、内部は緑なのに縫い目だけ赤く残る feature-extension の境界残留を見せる。

**P1-3: Topological Debt Capacity の有限不変量化(`ag.cech-obstruction@1` 拡張)**
計測: 既測 proxy の忠実化。手元の dimC0/dimC1/dimC2 を定理12.2 の rank-nullity 不等式 `capacityLowerBound=max(0, dimC1−dimC0−dimC2)` と系12.5 の `eulerCharacteristic=dimC0−dimC1+dimC2`、系12.3 の `b1NerveReading` に組む。これは structural verdict を生まない reading 行(invariant)。
境界: `capacityLowerBound>0` は「H^1 に余地がある」だけで concrete class の存在を非主張(原則4.4)。Euler は「debt が消えた」ではなく cochain accounting の保存則。系12.3 の b_1 同型は定数係数 assumption に相対化。**実装注意:** 現行 `h1_dimension` は 1-skeleton b_1 で、face が loop を埋める cover では nerve 複体 b_1 とずれる→「1-skeleton reading」と明示するか face を含む reduced homology で取る。原則11.3 参照は Part IV(Cohomological Non-Claim)限定と明記(Part VII の同番号は別物)。
解放する可視化: nerve の独立ループ(b_1 本)を半透明リングとして強調し、cover 形状が許す H^1 容量を loop 数で直感化。実測 H^1 cocycle が乗る loop だけ点灯し、capacity(潜在的余地)と実測 class(点灯)を視覚的に分離。

**P1-4: 高次 H^n / stack-gerbe の沈黙を typed boundary として明示固定**
計測: 沈黙の線引き(計算を増やさない)。BoundaryStatementV1 を3層で出力: (1) `silence_by_design` scope=`Hn n>=3 abelianized`(finite-site で計算可能だが Part IV scope 外、原則10.3)、(2) `out_of_selected_vocabulary` scope=`stack/gerbe non-abelian H^2(X,Aut(Dec_U))`(abelian F2 語彙外、第VI部16.1)。両者を取り違えない三層分離が核。
境界: structural verdict を一切生まない。沈黙=boundary であって zero ではない。計測不在を残タスク化しない(CLAUDE.md のウィトゲンシュタイン的責務境界)。
解放する可視化: nerve の n≥3 単体は geometry としても描かず、scene の凡例に「higher coherence: silent by design」「non-abelian: outside this lens」のラベルのみ。**可視化は沈黙を尊重し、空白を埋めない(計測が無い所に色を付けない)。**

**P1-5: Stokes audit identity を structural verdict 化 — `ag.period-stokes-audit@1`**
計測: 既測 proxy の忠実化(過剰ヘッジの解除)。Stokes audit residual r = <dω,γ> − <ω,∂γ> を固定係数環(F2 または Q)上の厳密差として計算し、全 (form,chain) 対で r≡0 なら `measured_zero`、一対でも r≠0 なら `measured_nonzero`。現状の `residual.abs()>1e-9` hard Err(run crash)を廃止し nonzero verdict へ正規化。analytic な `strict-period-pairing@1` は別 reading で据え置き。
境界: verdict semantics は「供給された独立会計値(dOmega/boundary atom)の固定 pairing 下の内部整合性」へ正確に限定し、定理13.2 の純内部恒等式(常に 0)そのものを measured と誤認させない。厳密係数を解決できず float のみのときは `unknown` へ降格し strict-period-pairing analytic-reading に留める。外部手続きの pairing 保存は非結論(原則13.3)。
解放する可視化: release loop / feature boundary に沿った符号付き会計が閉じるかの 3D ribbon-with-residual-flux。`measured_zero` では loop が滑らかに閉じ、`measured_nonzero` では残差ベクトルが各 face で外向きフラックスとして突き出す。

**P1-6: Higher Tor_i(i≥2)の沈黙を typed boundary として明示固定**
計測: 沈黙の型分離(計算を増やさない)。degree-1 計測後、`unmeasured_support` BoundaryStatementV1(scope=`LawConflict_i for i>=2`)を必ず付し、degree-1 `measured_zero` が derived-transversality(全 i>0、定理7.3)を discharge しないことを明示。**実装注意:** depends_on_assumptions による degree-1 verdict 降格を避け、H^2 precedent に倣い boundary statement + claimScope text の degree-1 scoping のみで実装(assumption propagation を発火させない)。
境界: derived-transversality を非主張。degree-1 衝突ゼロでも高次 Tor は沈黙。H^2 silence と対称なウィトゲンシュタイン的沈黙を Tor 軸で明文化。
解放する可視化: degree-1 の measuredZeroRegion に「degree-1 相対の zero、高次 derived residue は未測定」ラベルを添え、過剰な safety 着色(全次数 transverse の緑)を抑止。可視化を追加せず沈黙を尊重。

その他の P1(同質ゆえ要点のみ): **Hilbert series 干渉級数 Int_{U,V}(t)** を audit reading として追加(graded monomial regime、structural verdict 不生成、原則12.3)→ policy_conflict 上の次数別干渉ヒストグラム。**support-localized transfer の bounded inference 接地**(定義10.4: ambient LawConflict だけから任意 direction の transfer を結論しない)→ conflict cage→repair path 矢印を交差ありで実線/なしで点線。**curvature transfer spectrum の Perron-Frobenius hotspot 忠実投影**(現 misnamed proxy を別 readingKind で並置、power-iteration で principal eigenvector)→ S×A 上の recurrence 熱だまり。**refactor-invariant transport の有限整合 reading**(二 snapshot 間の verdict transport 監査、定理7.3)→ 二画面 nerve 並置と対応線。**repair を Alexander-dual / discrete-Morse の下界 inspection として忠実化**(定理候補5.5、operation semantics ではない)→ repairMorphPath を「到達可能アニメ」でなく「下界マーカー付き inspection glyph」へ。

### P2(従属可視化・analytic overlay・条件付き)

**P2-1: lawful locus Flat_U(X)=V(I_Δ) の Stanley-Reisner arrangement 化**
計測: 既測未投影の活用。`ag.square-free-repair@1` の computedInvariants を拡張(新 verdict なし)。Δ_U の facets を maximal 抽出し、各 facet T に vanishingCoords=E_W∖T、dimension=|T| を計算。irreducibleComponentCount は invariant 行であって verdict ではない(原則3.2)。Lean `LawfulLocus.lawfulLocus=PrimeSpectrum.zeroLocus` に対応。
境界: section ごとの s^* I_Ob^U=0 判定は別計測(P0-3)、Krull 次元の意味論、AAT-flatness=total correctness(原則7.3 で明示否定)を非主張。
解放する可視化: forbidden cage(立ってはいけない)の相補として lawful locus を「立ってよい座標部分空間の和集合」の薄板配置で描く。薄板の枚数=既約成分数は計測値そのもの。P0-3 の section 着地点の土台になる。

**P2-2: NSdepth 単調性(命題7.2C)の reading 化 — `ag.nullstellensatz-depth-monotone@1`**
計測: 既測 proxy の忠実化。U⊆U' で NSdepth が非増という片側不等式を、二 law-universe scope で monotone reading として計測。**NSdepth 値そのものは hitting-set 上界 proxy 注記つき analyticReading に留め、monotone/generatorExtension の bool だけを structural computedInvariant に。**「verdict 化」を「reading 化」に直すのが正(proxy を verdict に昇格させない)。theorem-candidate regime 接続で structural_verdict_ref=None を保つ。
境界: 一般 k での Nullstellensatz、square-free 外の厳密最小表示次数、全 law universe での単調性を非主張。`measured_zero`(lawful)と `unknown`(generatorExtension violated)を NSdepth 値で混同しない。
解放する可視化: law universe を広げる軸に沿って NSdepth を高さとして並べ「証明書の深さが単調に浅くなる斜面」を描く。傾きの符号は計測した片側不等式そのもの。

**P2-3: Δ_U の facet 次元・link の組合せ reading(命題5.6D の boundary-local reading)**
計測: 既測未投影の活用。facet 次元の最小/最大、各頂点の link 連結性、pure 性を invariant 行に。**採用条件(完全性クリティックの指摘を反映): `depth` / `Reisner depth` / `Cohen-Macaulay` / `Krull depth` / `srDepthReading` という語彙を全廃し、系5.6D 準拠の中立名(`facetDimensionReading` / `linkBoundaryReading` / `linkReducedBetti` / `isPure`)へ改名する。**本理論が anchor しない外部 Reisner criterion による「depth 下界読み」を不変量の意味づけに使わない。link は「boundary-local reading の生の組合せ量」として出し depth/CM 解釈を付さない。
境界: 代数的 Krull depth/CM の証明、link が boundary-local lawfulness を完全決定すること、depth 高=安全を非主張。
解放する可視化: lawful locus 薄板に facet 次元を厚みとして与え、link 非連結な頂点を裂け目として表示。厚みは計測した facet 次元そのもの。

**P2 analytic overlay バンドル(計測ロジック不変、measured-not-projected 解消):**
- **period pairing matrix overlay** — form×cycle の period landscape(colorRole=analytic_reading 固定、measured_zero に昇格させない)。**viewer funnel `build_measurement_viewer_data_v1` の allowlist と binding scene にも新キーを追加する**(projection 関数追加だけでは届かない)。
- **Wasserstein transfer cost / transferResidue overlay** — repair→target の obstruction mass 流(modelRelative proxy、W_1 そのものでない/global 修復安全性を証明しない を nonClaim 表示)。
- **spectral gap overlay** — hodge-debt 谷の浅深(gap≈0 を measured_zero teal に着色しない、L_1 でなく proxy 固有値である旨を行 nonClaim に)。
- **per-stratum 障害集中(singularity concentration)reading** — context ごとの LawConflict_1 non-transverse meeting count(deformationRegime=not_provided を boundary で明示、God object size / repair difficulty とは呼ばない)。

### P3(整備寄り)

**P3-1: common ambient assumption ledger の violated 伝播精緻化** — coefficient-compatibility 行を def9.1 に紐づけて追加(現行の単一 coefficient モデルでは不整合が起きえないので実質ドキュメント行)。coefficientRef/comparisonMorphismRef の schema 拡張は contract が admit しない計測軸の製造に傾くため、本クラスタには含めず別 Issue で input モデル拡張の是非から問い直す。

---

## 境界規律チェック

各補強が境界を侵していないことを確認する。チェック項目: profile 外計測 / 新規 verdict 乱造 / 沈黙侵犯 / π1 復活 / proxy の verdict 化。

- **profile 外計測しない。** すべての補強は archmap/v2 + LawPolicy + MeasurementProfile が供給する語彙内に scope する。global semantic safety / 全 runtime / 未来予測は計測しない。P0-2/P0-3/P1-2 は追加 contract(restriction 辺、section 割当、core/feature/boundary ラベル)を要求するが、これは profile 内の新しい有限 witness family の宣言であって profile 外計測ではない。contract が無ければ正しく `not_computed`(沈黙)。
- **新規 verdict を乱造しない。** 5値 structural verdict(measured_zero/nonzero/unmeasured/unknown/not_computed)は不変。新 structural verdict 行を出すのは P0-2(restriction-compatibility, 1個)、P0-3(section-factorization)、P1-1(coherence-obstruction)、P1-2(boundary-residue)、P1-5(period-stokes-audit)のみで、各々ちょうど1法則・選択 cover に scope。P0-1/P0-4/P1-3/P1-6/P2 系は verdict を増やさない(ledger 拡張 / 内部 method 昇格 / invariant・reading 追加 / typed boundary)。
- **沈黙を侵さない。** 高次 H^n(n≥3)/ non-abelian stack-gerbe、measured square monodromy(transport 不在時)、structural singularity(deformation regime 不在時)、Part IX は沈黙のまま。P1-1 は「設計済みの planned silence(selectedH2 not_measured)を banded abelian に限って解除」するのであって、原理的沈黙(non-abelian / sheaf 全体)は侵さない。P1-4/P1-6 はむしろ沈黙を typed boundary として明示固定する補強。
- **π1^AAT を復活させない。** 基本群 monodromy を絶対不変量として計測対象にしない。`holonomyLikeGapMarker` は cech の restriction-path closure gap であって monodromy verdict ではない(既存 fence を維持)。P2 の measured square monodromy μ_x(σ) は operation groupoid + coefficient transport が profile に固定された局所有限量のみで、π1^AAT presentation 自体は boundary(原則9.6: H を変えれば異なる reading)。
- **proxy を verdict 化しない。** analytic reading(period, transfer, laplacian, spectrum, Wasserstein, NSdepth 値)は AgAnalyticReadingV1 に隔離し structural_verdict を push しない。theorem-candidate reading は structural_verdict_ref=None を強制(`check_analytic_regime_boundary`)。P2-2 は完全性クリティックの指摘を受け「NSdepth 値=proxy reading / monotone bool=structural」に分離。P2-3 は depth/CM 語彙を全廃して誤読を塞ぐ。

**`measured_zero` を無ヘッジで主張する根拠の再確認。** measured_zero は次の4条件で支えられる: ① VerdictData zero=true & non_zero=false(`check_structural_verdict_data`)、② evaluator 要求の MeasurementProfile 固定値(coefficient=F2, effCoeff, zero/nonZeroPredicate, certSelector, witnessFamily)を満たし site/cover refs が解決、③ assumption ledger の checked 前提が成立し Leray/acyclicity・U-adequate cover は assumed としてヘッジが台帳に残る、④ depends_on_assumptions に violated が無い。これにより measured_zero は「選択 profile/cover 相対の確定 zero」として主張でき、sheaf-cohomology 全体や semantic safety へは持ち上げない(assumed のまま=沈黙の境界)。P0-1 はこの ④ の透明性を上げ、P0-2 は ③ の hedge を Leray とは別に一段 checked へ昇格する。違反した assumption は依存する measured 行のみを `not_computed` へ正規化し、unmeasured/unknown/not_computed は決して measured_zero と混同されない。

**完全性クリティックの指摘の反映。** (a) Part IX temporal obstruction は計測可能候補だが ArchSig 責務境界外(FieldSig/SFT 側)なので本ノートでは silence-by-design として扱い計測補強に含めない。(b) section-factorization(P0-3)は新 verdict 種別を増やす方向に流れやすいので既存5値の射程に収め、section ごと membership は input contract が section を供給する場合のみ。(c) NSdepth 単調性は「verdict 化」を「reading 化」に直す(P2-2)。(d) Stanley-Reisner depth/link は depth/CM 語彙を全廃して理論が licence しない代数幾何的意味の付与を排除(P2-3)。(e) H^2 coherence は invariant 散文の `ker d^1/im d^0` を `ker d^2/im d^1` へ訂正し、δ2 h=0 cocycle 条件を im δ1 判定前の明示ゲートとして追加(P1-1)。

---

## 可視化との接続(下流)

補強された各計測が、先行 viewer ノート(`docs/note/aat_archsig_viewer_3d_enrichment_proposal.md`)のどの可視化案を「正しく」駆動するかを示す。**計測が先に値・verdict を確定し、可視化はその従として色・開閉・厚み・高さを決める。** 計測なしに可視化を先行させると捏造になる。

| viewer 可視化案 | 正しく駆動する計測 | 計測なしに先行させると |
| --- | --- | --- |
| コホモロジー鉛直三層(H^0/H^1/H^2) | H^0/H^1=既存 cech、H^2=**P1-1 coherence-obstruction**(banded F2) | H^2 層を triangle の見た目だけで「開いている」と描くと、coherence を計測していないのに coherence failure を主張する捏造 |
| 曲率膜 / hodge-debt height-field | sheaf-laplacian proxy(既存)+ **P2 spectral gap overlay** | near-flat の谷を teal(measured_zero)で塗ると near-flat≠lawful を侵犯 |
| 三角膜の開閉 | **P1-1 coherence verdict**(`measured_zero`=閉じた膜 / `measured_nonzero`=開いた膜) | verdict 無しに膜を開閉させると H^2 を測ったことにしてしまう |
| 縫い目の裂け | **P1-2 boundary-residue δ verdict** | core/feature 分解と δ 像を測らずに縫い目を裂くと Mayer-Vietoris を捏造 |
| b_1 閉路リング | **P1-3 Topological Debt Capacity**(b_1 nerve reading) | capacity と実測 class を分離せず全ループ点灯すると原則4.4 違反(具体 class ≠ nonzero group) |
| lawful locus 薄板 + section 着地点 | **P2-1 arrangement**(薄板)+ **P0-3 section-factorization**(着地点) | section を測らず点を面に置くと lawful を捏造 |
| Tor 交差 glyph | **P0-4 Taylor resolution**(multidegree=lcm) | degree-1 proxy のまま分解すると過大な class 数を描く |
| 周期メーター / ribbon-flux | **P1-5 Stokes audit verdict**(閉/フラックス突出)+ **P2 period landscape**(analytic) | float smallness で「閉じた」と描くと厳密会計を proxy で偽装 |
| スペクトル峰 / recurrence 熱だまり | **P2 curvature transfer spectrum**(Perron-Frobenius hotspot、別 readingKind) | misnamed per-cell 値を spectrum として描くと理論先取りの捏造 |
| 神経辺の段差 | **P0-2 restriction-compatibility verdict** | separated 条件を測らず段差を描くと sheaf 条件を偽装 |

**色レーン分離の規律。** structural verdict(measured_zero/nonzero)は構造色(teal/amber)、analytic reading(period, transfer, laplacian, spectrum, Wasserstein, concentration)は analytic_reading 色で別レーンに保つ。viewer は新しい structural verdict を作らない(`build_measurement_viewer_data_v1` の projectionBoundary 明文を継承)。沈黙領域(高次 H^n / stack-gerbe / monodromy transport 不在 / singularity deformation 不在 / Part IX)は描かず、必要時のみ凡例に typed boundary ラベルを出す。

---

## 棚卸し(見送り)

棄却された案を沈黙として正直に残す。

- **Decomposition groupoid の有限近似と descent obstruction reading(`ag.decomposition-descent@1`)— 見送り。** 理由三点: (1) 理論誤読 — H^1 overlap reading を gerbe(H^2 triple-overlap, 一般 non-abelian)の「前段」と framing するが、gerbe class は H^1 の部分計測ではなく、H^2 沈黙を H^1 で半分埋める誤導を内包する。(2) 沈黙の侵犯と新 verdict 乱造 — 中核計測の実体は既存 `ag.cech-obstruction@1` を係数替えした H^1 Čech の再皮膜で、新 structural verdict を正当化する独立な不変量を語っていない。(3) 境界の緩み — decompositionLabels/decompositionIsomorphisms は ArchMap 観測 atom ではなく authored decomposition contract で、measurement 層に持ち込むと観測/計測境界を侵す。建設的代替: decomposition descent を語りたいなら、まず H^2 triple-overlap coherence(P1-1)を本筋として PRD 化し selectedH2 の沈黙フラグを反転する方が理論忠実・低摩擦。本案の H^1 edge reading は P1-1 の banding 入力妥当性チェックに従属する補助計算として、structural verdict を push しない形に限定するなら検討余地がある。
- **Part IX temporal obstruction(Ob_t)の ArchSig 計測 — 見送り(tool 境界外)。** AG 本文が定義4.2 Temporal Descent Criterion で有限 F2 計測可能候補として与えるが、evolution/flow 計測は FieldSig + SFT 側の責務。ArchSig が temporal obstruction を測ると tool 境界を越える。ArchSig にとっては silence-by-design であり残タスクではない。
- **Margin / Margin Stability(定義12.4・定理12.5)、Architectural Dehn function(定義12.6・定理12.7)、persistence/zigzag barcode(定義6.2・定理候補6.3)— 当面見送り。** いずれも有限計測可能な certified bounded inference または analytic reading だが、本ロードマップの核(I_Ob/Flat/H^1/H^2/Tor の structural verdict 系)から外れる stability/distance reading であり、忠実性の核を固めた後の analytic 拡張として別 Issue 棚卸しに回す。
- **coefficientRef / comparisonMorphismRef の schema 拡張(P3 由来)— 見送り。** 現行の単一 coefficient・単一 common ambient モデルでは不整合が表現できず、新設は contract が admit しない計測軸の製造に傾く。input モデル拡張の是非から問い直す別 Issue 案件。

---

## PRD 候補

計測優先で切り出せる PRD を複数 framing で提示する。各 framing は問い案・含む計測・受け入れ条件の方向性(評価器 + schema + fixture + test、projectionBoundary 維持)・その後の可視化フェーズとの接続を述べる。最後にどの framing で PRD 化するか選んでほしい。

### Framing α: H^2 coherence を核に据える(沈黙ギャップ充填・最低摩擦・最大 viz payoff)

- **問い案:** 「ArchSig は AG Part IV 定義10.1 の H^2 triple-overlap coherence を、banded abelian F2 に限れば忠実に計測できる。設計済みの planned silence(selectedH2 not_measured)を、どこまで本文忠実に解除すべきか」
- **含む計測:** P1-1(coherence-obstruction、structural verdict)を核に、P1-4(高次 H^n / stack-gerbe の typed boundary)を sibling として同梱。
- **受け入れ条件の方向性:** 新 evaluator `ag.coherence-obstruction@1` + MeasurementProfile/v1 行 + 新 fixture(pairwise-compatible/triple-incompatible witness を持つ archmap_v2 × law_policy ペア)+ #[test](δ2 h=0 cocycle ゲート、im δ1 membership、measured_zero/nonzero、banding violated→not_computed、projectionBoundary)。invariant 散文 `ker d^2/im d^1` の訂正と cocycle ゲート追加を AC に明記。non-abelian は banding violated で沈黙、5値 verdict・CBI ledger・projectionBoundary を既存規律のまま継承。
- **可視化フェーズとの接続:** nerveTriangle の `coherenceClaim` flip と `h2CoherenceVisualized=true` は別 PRD の viewer フェーズ。三角膜の開閉(viewer ノート)を「正しく」駆動する計測が先に確定する。**投影 scaffolding が既に packet 内にあるので計測 PRD 完了直後に viewer PRD へ繋げられる。**

### Framing β: 忠実性の核を一点束ねる(候補A 中心・即効・低リスク)

- **問い案:** 「最も多用される計測(H^1 Čech の measured_zero、Tor、section の lawful 述語)の暗黙前提・proxy を、AG 本文と Lean に正確対応させて有限 checked へ昇格する。どこまでを一つの PRD に束ねるべきか」
- **含む計測:** P0-1(torsor effectivity ledger)+ P0-2(restriction-compatibility)+ P0-4(Tor Taylor resolution)+ P0-3(section-factorization)。verdict を増やすのは P0-2/P0-3 のみ。
- **受け入れ条件の方向性:** P0-1 は ledger 行のみ(計算・verdict 不変、forest/no-triple で checked 昇格、surjective restriction は assumed 固定)。P0-2 は新 EffCoeff `finite-support-inclusion@1` + 1 verdict。P0-4 は内部 method 昇格 + multidegree、非 square-free は unmeasured。P0-3 は witnessAssignment atom 規約 + total/partial→unknown + section 不在→not_computed の test-lock。各々で「measured_zero を無ヘッジ主張する4条件」と assumption ledger を AC に固定。
- **可視化フェーズとの接続:** lawful locus 薄板(P2-1)→ section 着地点(P0-3)→ Tor glyph(P0-4)→ nerve 段差(P0-2)→ 確実に閉じる patch の濃淡(P0-1)。計測が確定した順に viewer 案を駆動できる。

### Framing γ: Mayer-Vietoris boundary residue 単独(構造拡張・高 viz payoff・中コスト)

- **問い案:** 「feature extension の core/feature が各々 lawful でも boundary residue が大域障害になりうる。定義8.3 の connecting hom δ を F2 で忠実計測し、縫い目の裂けを正しく駆動すべきか」
- **含む計測:** P1-2(boundary-residue δ、structural verdict)単独。
- **受け入れ条件の方向性:** 新 evaluator `ag.boundary-residue@1` + core/feature/boundary 分類 atom 規約 + boundary mismatch atom + #[test](δ=0/≠0、coefficient=F2 を ledger checked・Z-zero 持ち上げは assumed、coefficient 非固定時は片方向 obstruction statement、period-Stokes modelRelative との分離、π1 非復活)。原則7.2 の引用を Part IV に訂正。
- **可視化フェーズとの接続:** 縫い目=裂け目メタファ(viewer ノート)を δ verdict が駆動。core/feature 二パッチと B 縫い目の幾何は計測完了後の viewer PRD。

### Framing δ: 既測未投影の analytic overlay バンドル(候補C・実装最小・低リスク)

- **問い案:** 「すでに完全計算されているのに viewer に届いていない analytic reading を、structural verdict と取り違えない analytic レーンとして投影する。どこまでを一括にすべきか」
- **含む計測:** P2 overlay バンドル(period pairing matrix / Wasserstein cost / spectral gap / curvature spectrum hotspot / singularity concentration)。計測ロジックは一切変えない。
- **受け入れ条件の方向性:** projection 関数追加 + `build_measurement_viewer_data_v1` の allowlist と binding scene 拡張(projection 関数だけでは viewer に届かない)+ #[test](colorRole=analytic_reading 固定で measured_zero に昇格しない、structural verdict 件数不変、regime=analytic-measurement、nonClaim 表示)。near-flat≠lawful / W_1 そのものでない / God object size でない を nonClaim に固定。
- **可視化フェーズとの接続:** 周期メーター・スペクトル峰・mass 流(viewer ノート)を analytic レーンで解放。**ただし構造判定の忠実性は深まらない**ので、Framing α か β を先行させた上での補完として位置づけるのが妥当。

---

**選択のお願い:** どの framing で PRD 化するか選んでほしい。推奨は **Framing α(H^2 coherence 核)を最初の PRD** に据えること — 沈黙ギャップ充填でありながら投影 scaffolding が既に揃っていて摩擦最小、かつ viewer ノートの三角膜可視化を最も劇的に解放する。その後に Framing β(忠実性の核束ね)で measured_zero の射程を本文どおり固め、Framing γ / δ を後続に回す順序が、計測=主・可視化=従の背骨に最も忠実である。複数 framing を組み合わせる切り方(例: α + P1-4 を最初の1本、β を次の1本)も可能なので、スコープの広狭も含めて指定してほしい。
