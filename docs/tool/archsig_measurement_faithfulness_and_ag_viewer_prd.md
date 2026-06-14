# ArchSig 計測忠実性補強と AG-faithful Viewer 統合 PRD — 計測を先に忠実化し、その計測に応じて正しい3D可視化を従として組む

この PRD は二つの作業を一本に束ねる。第一に ArchSig(`tools/archsig/src/ag_measurement.rs` の `analyze` 一次経路と 6 つの `ag.*` 評価器、`tools/archsig/src/schema/measurement.rs` / `law_policy.rs`、`tools/archsig/src/law_policy/registry.rs` の `ag_manifest`)を AAT 代数幾何版(`docs/aat/algebraic_geometric_theory/` の 9 部)に**忠実化・多様化**する(ワークストリーム M)。第二に、その忠実化された計測に**応じて** viewer(`tools/archsig/viewer/archsig-atom-viewer.html` 単一 HTML / Three.js r0.164.1、`build_measurement_viewer_data_v1` / `gluing_geometry_projection_v1` の projection)を AG-faithful に組み直す(ワークストリーム V)。

design backing は二系統の設計ノートである。計測は `docs/note/aat_archsig_measurement_faithfulness_reinforcement.md`(P0-1..4 / P1-1..6 / その他 P1 / P2-1..3 / P2 overlay / P3-1 の評価器設計・verdict・境界)、可視化は `docs/note/aat_archsig_viewer_3d_enrichment_proposal.md`(T1-1..6 / T2-1..6 / T3-1..5 / T4-1..3 の Three.js 実装方針)である。各要求はこの二ノートの該当節に接地する。

背骨の宣言を冒頭に置く。**計測=主、可視化=従。** 各 V 要求は駆動する M 要求(または既存実装データ)を必ず名指し、その M が land する前に viewer がその構造を描くのは捏造として禁止する。house style は `docs/tool/archsig_v0_4_0_algebraic_geometry_measurement_prd.md` と `docs/tool/archsig_viewer_gluing_geometry_prd.md` に従う(問い / 中心方針 / 背景 / アウトカム UC / 設計原則 P / 要求 R / スコープ / Non-Goals / Acceptance Criteria / 検証コマンド)。応答・本文は日本語、評価器 id・ファイル名・定理番号・Three.js API はそのまま用いる。

## 問い

この PRD のすべての要求は、次の問いに仕える。問いは採否の判定規律として機能する。

```text
主問い:
  計測=主・可視化=従。ArchSig を AAT 代数幾何版(9部)の数学に忠実化・多様化し、
  その確定した計測に応じてのみ正しい3D可視化を従として組めるか
  ——可視化を先に磨かず、計測されていない構造を viewer に描かせないか。
```

「viewer をどう豪華にするか」ではなく「**何を計測しているか、その計測が AG 本文に対してどれだけ正直か**」を先に確定する。可視化を計測に先行させると、計測されていない構造を viewer が描く=捏造になる。この主従関係を全要求が守る。

主問いには、次の従う問いが続く。これらが各要求・各 framing の採否を読む規律である。

```text
忠実性の核を、暗黙前提・proxy を有限 checked へ昇格して深められるか?       (M1, M4, M9, M12)
沈黙ギャップ(H^2 / boundary δ / restriction-compat / section)を、
  profile 内の新規 structural verdict として本文忠実に埋められるか?         (M2, M3, M5, M6)
沈黙(高次 H^n / non-abelian / monodromy transport 不在 / Part IX)を、
  侵さず typed boundary として明示固定できるか?                            (M8 と各 M の境界節)
既測だが未投影の analytic reading を、structural と取り違えず投影できるか?  (M14, V18)
そして —— 確定した各計測に、viewer は形・色・開閉・高さを従として正しく割り当てるか?
  計測が land する前に viewer がその幾何を描いていないか?                   (V0 と各 V の駆動 M 名指し)
```

問いに仕えない計測・可視化は、それ自体に価値があっても本 PRD に入れない。π1^AAT 系 monodromy verdict の不復活、proxy の verdict 化禁止、沈黙の赤エラー化撤廃は、この規律の適用例である。

## 中心方針

本 PRD は二つのワークストリームを**順序規律**で結ぶ。

```text
ワークストリーム M(計測=主):
  ArchSig を AG 本文の有限計測仕様へ忠実化・多様化する。
  - 忠実性の核を深める(暗黙前提 → ledger 行、proxy → 有限 checked):
      M1 H^1 torsor effectivity ledger / M4 Tor Taylor resolution /
      M9 Stokes audit verdict 化 / M12 NSdepth monotone reading 化
  - 沈黙ギャップを新規 structural verdict で埋める(各々ちょうど1 verdict):
      M2 restriction-compatibility / M3 section-factorization /
      M5 H^2 coherence-obstruction / M6 boundary-residue δ
  - 沈黙を typed boundary として明示固定する(verdict を増やさない):
      M8 高次 H^n / non-abelian stack-gerbe / 高次 Tor_i
  - 既測未投影の analytic reading を投影する(計測ロジック不変):
      M7 Topological Debt Capacity / M10 reading 群 / M11 arrangement /
      M13 facet/link 中立名 reading / M14 analytic overlay bundle / M15 ledger 精緻化

ワークストリーム V(可視化=従):
  各 V は「駆動する M(または既存実装データ)」を必ず名指す。
  駆動 M が land した後にのみ、その構造を viewer が描く。
  V1-V4 は器(PBR / bloom / 沈黙描画 / ラベル・座標)= 既存データで成立。
  V5-V18 は AG 量が形を駆動する本体= 各々の駆動 M に依存。
```

二つの規律を全要求が守る。第一に **捏造禁止**: 計測なしに viewer が構造を描かない、packet に無い量を補間・推測で埋めない、沈黙領域に色を付けない。第二に **境界の一括前払い**: 境界(coverage / exactness / profile 相対性 / Leray acyclicity)は input contract 時に CBI assumption ledger へ宣言し、ledger 記録後の結論は profile 内で肯定形に言い切る。viewer は新しい structural verdict を作らない(`gluing_geometry_projection_v1` の `projectionBoundary` と `cli.rs:1297-1301` の test-locked 境界を維持)。

推奨スタンス(ノートの選択に従う): M5(H^2 coherence 核)を最初に立て、M1-M4(忠実性の核束ね)で `measured_zero` の射程を本文どおり固め、M6 以降と V を後続に置く。これが計測=主・可視化=従の背骨に最も忠実である。

## 背景

**計測側の現状(`docs/note/aat_archsig_measurement_faithfulness_reinforcement.md` の忠実性マップ)。** ArchSig v0.4.0 は H^1 Čech 障害評価器(`ag.cech-obstruction@1`、`ag_measurement.rs:1379-1382`)を `measured_faithful` で稼働させ、F2 1-cocycle/coboundary を XOR 伝播で厳密判定する。しかし忠実性に三種のギャップがある。第一に **proxy/暗黙前提**: `measured_zero` を支える torsor effectivity / surjective restriction が ledger に全行開示されていない(M1)、Tor_1 が degree-1 shared-support proxy で Taylor resolution を組んでいない(M4)、Stokes audit が float smallness で hard Err する(M9、`residual.abs()>1e-9`)、NSdepth が hitting-set 上界 proxy のまま(M12)。第二に **沈黙ギャップ(有限計測可能なのに未計測)**: H^2 triple-overlap coherence(M5、定義10.1、scaffolding は既に packet 内)、boundary connecting hom δ(M6、定義8.3 / 例9.3)、restriction-compatibility(M2、sheaf 条件の前段)、section factorization s^* I_Ob^U=0(M3、Lean proved `lawful_iff_factorsThroughLawfulLocus`)が `not_measured_silence` のまま。第三に **既測未投影**: period pairing matrix / Wasserstein cost / spectral gap / curvature spectrum hotspot / singularity concentration が packet 内に完全計算されながら viewer に届いていない(M14)。一方で **沈黙が正しい行**(高次 H^n n≥3 / non-abelian stack-gerbe / monodromy transport 不在 / singularity deformation 不在 / Part IX 進化幾何)は侵さず、typed boundary として明示固定する必要がある(M8)。

**可視化側の現状(`docs/note/aat_archsig_viewer_3d_enrichment_proposal.md` の現状診断)。** viewer は二層で「クオリティがもう一つ」である。器の欠落: `createRenderer()`(L1001-1018)が toneMapping / 環境マップ / shadowMap / EffectComposer / fog をすべて欠き、PBR が Lambert に退化し、`emissive` 4 箇所が bloom 不在で光らない(V1-V4)。本体(最重要)の欠落: レイアウトを `hashText` とゴールデン角 `2.399963229728653`(L2078)が支配し、AG 値は `value*0.08` で薄く足されるだけ、`axisMetricBindings` の実 metric は `xScale=46+(hashText%17)`(L1456-1458)で希釈される。結果、view mode を変えても「同じスパイラルの再配色」に見え、AG 構造の幾何的差異が伝わらない。加えて沈黙を赤エラー化する境界違反がある: cocycle gap を `0xff6b6b`(L1640)、blockedRegions を `0xff6b6b` wireframe(L1687)で描いており、これは沈黙を失敗として主役化している。`aatGeometryOverlays` の器は空きのまま残る。

**先行 PRD との関係。** 既存 PRD #2082(`archsig_viewer_gluing_geometry_prd.md`)は MERGED 済みで、PR #2088/#2094/#2103/#2110/#2116 により nerve / cocycle ribbon / locus field / obstruction cage / repair morph の**静的幾何描画**と axisMapping HUD・visual encoding 固定・scene 単位 non-claim を提供している。本 PRD はその上位に立ち、(1) 計測そのものの AG 本文への忠実化(M、#2082 のスコープ外)、(2) 表現品質レイヤー(V1-V4、#2082 が立てていない)、(3) AG 量による空間形状の駆動(V5-V18、#2082 は描くが配置主係数を hash から実 metric へ移していない)を扱う。`gluing_geometry_projection_v1` の `projectionBoundary`(no structural verdict)と test-locked 境界は維持する。

## アウトカム

本 PRD 完了時にユーザー(コードベースを計測・可視化するアーキテクチャ責任者)が得る成果をユースケースとして定義する。各 UC は M/V 要求 ID への traceability を持ち、計測が解放する可視化を従として書く。

### UC1. H^1 `measured_zero` を、何を checked し何を assumed したかまで透明に言い切れる(M1 / V5)
計測: `ag.cech-obstruction@1` の assumption ledger に torsor effectivity / surjective restriction / descent / 定理12.4 前提行が立ち、`nerveIsForest && !hasTripleOverlapFaces` のとき forest 前提が `checked` へ昇格、surjective restriction は `assumed` 固定。計算・verdict は不変。
可視化(従): V5 のコホモロジー鉛直三層が、forest かつ triple face 無しの `measured_zero` patch を確実に閉じる層として、torsor effectivity が assumed の patch を条件付きとして塗り分ける。ledger の checked/assumed 内訳が色の従。

### UC2. 「局所は全部合法なのに triple で閉じない」を、H^2 verdict 付きで指摘できる(M5 / V3, V5, V11)
計測: 新評価器 `ag.coherence-obstruction@1` が banded abelian F2 で H^2 = ker δ2 / im δ1 を計算し、δ2 h=0 cocycle ゲート後に im δ1 帰属を判定。`measured_zero`(全 2-cocycle が coboundary)/ `measured_nonzero`(triple で壊れる concrete class)/ `not_computed`(banding violated)。non-abelian は banding violated で沈黙。
可視化(従): V5 の天井層と V3 の H^2 三角面が、verdict が確定した後にのみ膜を開閉する。`measured_nonzero` の face を「三辺一致なのに中央が閉じない」glowing な開いた三角膜、`measured_zero` を滑らかに閉じた膜として描く。V11 の degree スクラブが H^2 層を剥離する。M5 が land する前に膜を開閉させると H^2 を測ったことになる捏造。

### UC3. feature extension の縫い目残留を、boundary δ verdict として見られる(M6 / V13)
計測: `ag.boundary-residue@1` が core/feature/boundary 分類 atom 上で Mayer-Vietoris d^0 を組み、boundary mismatch section が im(d^0) に入るか(δ=0 か)を F2 で判定。coefficient=F2 を ledger checked、Z-zero 持ち上げは assumed。
可視化(従): V13 の assembly snap が、`value=1` の seam を snap し損ねる縫い目として残す。core/feature が緑なのに縫い目だけ赤く残る境界残留を、δ verdict が駆動する。

### UC4. 修復計画を、proxy でなく真の Tor multidegree と support 座標で受け取る(M4 / V8, V15)
計測: `ag.law-conflict-tor@1` の内部 method を `finite-monomial-tor-taylor@1` へ昇格(verdict id 据置)、各 conflict class に multidegree=lcm(x_S,x_T) を添付。非 square-free は `unmeasured`。
可視化(従): V8 の support repair morph が `supportVariables` を実座標軸として cage→lawful 連続変形を見せる(not automatic repair / lower-bound)。V15 の二 lawful loci 交差が、非横断 residue(Tor_1≠0)で余剰塊を見せ、repair で質量を移送する。multidegree 計測の従として class を別 edge に分離。

### UC5. 既測の analytic reading を、structural と取り違えず連続量で追える(M14 / V6, V16, V17, V18)
計測: period pairing matrix / Wasserstein transfer cost / spectral gap λ1 / curvature spectrum hotspot / singularity concentration を packet→viewer へ投影(`build_measurement_viewer_data_v1` の allowlist + binding scene 拡張)。colorRole=analytic_reading 固定、structural verdict 不昇格。
可視化(従): V18 の analytic overlay(period landscape / Wasserstein mass 流 / spectral gap 谷深)、V17 のスペクトル峰(measured-zero の lawful plain 中心、峰は副次)、V16 の周期 Stokes メーター、V6 の曲率膜の谷深が、analytic レーン色で structural と分離して立つ。near-flat を measured_zero teal に着色しない。

### UC6. 沈黙を、赤エラーでなく霧の奥・すりガラスとして正しく見られる(M8 / V3, V11)
計測: M8 が高次 H^n(n≥3、silence_by_design)/ non-abelian stack-gerbe(out_of_selected_vocabulary)/ 高次 Tor_i(unmeasured_support)を BoundaryStatementV1 三層で明示固定。verdict 不生成、assumption propagation 不発火。
可視化(従): V3 が現状の沈黙赤エラー化(blockedRegions `0xff6b6b` L1687 / cocycle gap L1640)を撤廃し、measured を焦点面の手前・unmeasured を霧の奥(FogExp2+BokehPass)へ、H^2 三角面をすりガラスへ後退させる。V11 が H^2 層を灰色沈黙のまま保つ。沈黙領域に色を付けない。

### UC7. view mode を変えても「同じ対象を別 reading で見ている」が、実量駆動の形として読める(M14 駆動 + V9)
計測: axisMetricBindings の実 metric を主係数化し、各 view の位置を実量へ接地する(demote-hash)。
可視化(従): V9 の view mode 間レイアウト morph が、全 clear を廃止し InstancedMesh 位置を補間する。demote-hash(hash jitter を従へ下げる)を独立 AC として切り出す。これが伴って初めて morph が「同じ atom を別 reading で見る」を意味として駆動する。

## 設計原則

### P1. 計測=主、可視化=従(背骨)
計測を先に補強し、補強された計測の数学的中身に応じて可視化を従として組む。各 V 要求は駆動 M を名指し、M が land する前にその構造を viewer が描かない。計測なしの可視化先行は捏造である。これが採否の判定規律(問い)の実装である。

### P2. 沈黙を描かない・侵さない
沈黙領域(高次 H^n n≥3 / non-abelian stack-gerbe / monodromy transport 不在 / singularity deformation 不在 / Part IX 進化幾何)は計測対象化せず(M8 が typed boundary で明示固定)、viewer は描かず凡例の typed boundary ラベルに留める(V3 / V11)。沈黙を赤エラー・残タスク・欠落警告として主役化しない。現状の `0xff6b6b` 赤化(L1640 / L1687)を撤廃する。

### P3. analytic と structural の色レーン分離
structural verdict(measured_zero/nonzero)は構造色(teal/amber)、analytic reading(period / transfer / laplacian / spectrum / Wasserstein / concentration / NSdepth 値)は analytic_reading 色で別レーンに保つ。near-flat を measured_zero に着色しない(原則8.4)。M14 / V6 / V17 / V18 でこの分離を最も厳格に適用する。

### P4. projectionBoundary 維持(no new structural verdict)
viewer は新しい structural verdict / curvature / cohomology class を導出しない。`gluing_geometry_projection_v1` の `projectionBoundary`("It adds no structural verdict, H2 coherence claim, or monodromy verdict.")と `cli.rs:1297-1301` の test-locked 境界を全 V が越えない。M14 系の per-object scalar 配線も、測られた量を運ぶ projection であって verdict を作らない。

### P5. proxy を verdict 化しない・π1 を復活させない
analytic reading は AgAnalyticReadingV1 に隔離し structural_verdict_ref=None を強制する。M12(NSdepth)は「verdict 化」を「reading 化」へ直す。π1^AAT 系 monodromy を絶対不変量として計測対象にしない。`holonomyLikeGapMarker`(V10)は cech の restriction-path closure gap であって monodromy verdict ではない(既存 fence 維持)。

### P6. 新規 verdict を乱造しない(notes が明示した分だけ)
5値 structural verdict(measured_zero / measured_nonzero / unmeasured / unknown / not_computed)は不変。新 structural verdict を出すのは M2(restriction-compatibility)/ M3(section-factorization)/ M5(coherence-obstruction)/ M6(boundary-residue)/ M9(period-stokes-audit)の5評価器のみ、各々ちょうど1法則・選択 cover に scope。それ以外の M は ledger 拡張 / 内部 method 昇格 / invariant・reading 追加 / typed boundary に留める。

### P7. profile 外を計測しない
すべての M は archmap/v2 + LawPolicy + MeasurementProfile が供給する語彙内に scope する。global semantic safety / 全 runtime / 未来予測は計測しない。M2 / M3 / M6 が要求する追加 contract(restriction 辺・section 割当・core/feature/boundary ラベル)は profile 内の新 witness family 宣言であって、contract が無ければ正しく `not_computed`(沈黙)。

### P8. 境界の一括前払い(boundary is paid once)
境界(coverage / exactness / profile 相対性 / Leray acyclicity)は AG 本文の核心だが、結論文ごとに but 節で払うと tool は何も言い切れなくなる。本 PRD は `archsig_v0_4_0_algebraic_geometry_measurement_prd.md` の同名節を継承し、「境界は input contract 時に一度だけ払う」規律でこの緊張を解く。

```text
boundary is paid once, at input contract time:
  ArchMap v2 + MeasurementProfile + LawPolicy が境界を宣言する。
  CBI assumption ledger が仮定の checked / assumed を記録する。
  M1-M9 が足す新 ledger 行・新 verdict の前提(torsor effectivity / Leray /
  coefficient=F2 / banding / surjective restriction 等)も、すべてこの入力契約時の台帳に積む。

conclusions are unconditional inside the profile:
  ledger 記録後の結論(各 evaluator の verdict)は profile 内で肯定形に言い切る。
  結論文にヘッジ・but 節・non-conclusion 列挙を入れない。
```

成立根拠は第VIII部 verdict discipline である。`unmeasured` / `unknown` が `measured_zero` から型として分離されている(原則3.2 Verdict Boundary)からこそ、`measured_zero` は profile 内で無条件の主張として言い切れる(その具体機構が P9)。境界を気にして結論を弱めるのではなく、境界を型・台帳へ押し出して結論を強くする。可視化側もこの前払いを継承する: viewer は各 visual ごとに境界を払い直さず、計測が払った境界(ledger / verdict / projectionBoundary)をそのまま投影し、語れない領域は短い silence boundary として最小限に置く(失敗・残タスク扱いしない、P2)。

### P9. measured_zero を無ヘッジで主張する4条件
`measured_zero` は次の4条件で支えられる: ① VerdictData zero=true & non_zero=false、② evaluator 要求の MeasurementProfile 固定値を満たし site/cover refs が解決、③ assumption ledger の checked 前提が成立し Leray/acyclicity・U-adequate cover は assumed として台帳にヘッジが残る、④ depends_on_assumptions に violated が無い。M1 は ④ の透明性を、M2 は ③ の hedge を Leray とは別に一段 checked へ昇格する。

### P10. 3D を操作できなくても同じ意味が読める
幾何 richness は detail panel / insight queue のテキスト表現を置き換えない(insight viewer R22 継承)。3D を回せない読者にも同じ where(どの cover / cocycle / atom / locus)が届く。

### P11. no-build 単一 HTML を維持する
viewer はビルド工程を追加せず、Three.js は現行の importmap 経由 `three/addons/` 読み込み方式を踏襲する。WebGL/WebGPU 両経路を保つ(V1)。

## 要求

本 PRD の要求は二ワークストリームに分かれる。**M(計測=主)が先に land し、V(可視化=従)は対応する計測 M に gated される。** 計測なき構造を viewer が描くのは捏造として禁止する。

### ワークストリーム M: 計測の忠実化(主)

### M0. リリース定義 — 計測忠実性補強 + AG-faithful 3D Viewer 改善を一本に束ねる

本 PRD は二つの仕事を一本に束ねる。(1) ArchSig が AAT 代数幾何版(9部)の数学をどこまで忠実に測れているかを補強する**計測ワークストリーム M**(`tools/archsig/src/ag_measurement.rs` の `build_foundation_measurement_packet_v1` と `ag.*` 評価器群、`schema/measurement.rs` の 5値 verdict / CBI ledger、`law_policy/registry.rs` の `ag_manifest`)、(2) その補強された計測の数学的中身に応じて 3D viewer を正しくする**可視化ワークストリーム V**(`tools/archsig/viewer/archsig-atom-viewer.html`、Three.js r0.164.1 単一HTML no-build、`gluing_geometry_projection_v1`)。

背骨は **計測=主、可視化=従** の順序規律である。計測なしに可視化を先行させると、計測されていない構造を viewer が描く=捏造になる。この規律は全 M / V 要求が従う採否の判定規律であり、本 PRD のすべての claim はこの順序で読む。

二ワークストリーム宣言と順序規律:
- ワークストリーム M(計測補強): P0-1..4(忠実性の核・本要求 M1-M4)/ P1-1..6(沈黙ギャップ充填・本筋)/ その他P1(reading 群)/ P2-1..3 と P2 overlay(従属・analytic)/ P3-1(整備)。新規 structural verdict は notes が明示した分(P0-2 restriction-compatibility 1個、P0-3 section-factorization、P1-1 coherence-obstruction、P1-2 boundary-residue、P1-5 period-stokes-audit)だけ、各々ちょうど1法則・選択 cover に scope する。それ以外は ledger 拡張 / 内部 method 昇格 / invariant・reading 追加 / typed boundary のいずれかで verdict を増やさない。5値 verdict 種別(`measured_zero` / `measured_nonzero` / `unmeasured` / `unknown` / `not_computed`)自体は不変で、第6の値を追加しない。
- ワークストリーム V(可視化追従): 各 V 要求は「駆動する計測 M 要求」を必ず名指しし、その M が land する前に viewer がその構造を描くのを捏造として禁止する。viewer の `projectionBoundary`(`gluing_geometry_projection_v1` の "It adds no structural verdict"、`cli.rs` の assert)を維持し、viewer は新しい structural verdict を作らない。

境界規律(全要求が継承): ArchSig は Lean 証明器でなく measurement layer。profile 外(global semantic safety / 全 runtime / 未来予測)を計測対象化しない。沈黙(高次 H^n(n>=3)/ non-abelian stack-gerbe / monodromy transport 不在 / singularity deformation 不在 / Part IX 進化幾何)を侵さず、必要時のみ typed boundary として最小限に出す。π1^AAT を絶対不変量として復活させない。proxy / modelRelative を structural verdict 化しない。応答・本文は日本語(評価器 id・ファイル名・定理番号・Three.js API はそのまま)。

受け入れ観点:
- 問いが冒頭に立てられ、各要求・各計測の採否を「計測=主・可視化=従」の規律と source note の問いで読む旨が明記されている。
- 計測ワークストリーム M と可視化ワークストリーム V が別ワークストリームとして宣言され、各 V 要求が駆動する M 要求 id を名指しし、M が land する前に viewer がその構造を描かない順序規律が明記されている。
- 本 PRD が新規 structural verdict を出す要求と、その個数(計測 note が明示した分のみ)・scope(1法則 / 選択 cover)が列挙され、それ以外の要求が verdict を増やさず 5値種別を不変に保つことが明記されている。
- 沈黙が正しい領域(高次 H^n / non-abelian stack-gerbe / monodromy transport 不在 / singularity deformation 不在 / Part IX)を残タスク化せず typed boundary として扱う方針が明記されている。
- viewer の projectionBoundary(no new structural verdict)維持と、計測なしに viewer が描かない捏造禁止が明記されている。

依存: 後続の全 M 要求(M1-M15)と全 V 要求(V0-V18)が本リリース定義に従属する。

### M1. P0-1 H^1 Čech measured_zero の torsor effectivity / surjective restriction 前提を CBI ledger 行に明示

`ag.cech-obstruction@1` の `measured_zero` が「選択 cover 上で 1-cocycle が coboundary」という F2 checked 事実から global lawful section の存在へ持ち上がる射程を、CBI assumption ledger 上で透明にする(定理11.1 / 12.4 忠実化)。計算ロジック・verdict・packet 数値はすべて不変で、本要求が触るのは assumption ledger 行のみである。

計測=評価器設計・verdict semantics・境界: ledger を拡張し、定理11.1 の `local lawful sections form an effective Ob_U-torsor` / `local adjustment action is fixed and effective` / `coefficient object satisfies descent`、定理12.4 の `restriction maps are surjective` / `nerve is a forest with no triple overlap` を ledger 行にする。昇格規則は構造観測に限定する: `nerveIsForest && !hasTripleOverlapFaces` のときだけ定理12.4 の forest 前提を `checked` へ昇格し、それ以外は `assumed`。surjective restriction は意味論的性質なので ArchSig(構造観測器であって意味論観測器ではない)は常に `assumed` 固定とする。verdict semantics は据置で、`measured_zero` は依然「選択 profile / cover 相対の F2 checked zero」であり、global lawful section への持ち上げは forest+no-triple のときだけ前提が checked になる(原則7.2 Local Success Is Not Global Lawfulness)。Leray は依然 assumed のままヘッジを台帳に残す。

新規 structural verdict: ゼロ。本要求は ledger 行の追加のみで、5値 verdict・packet computedInvariants・analyticReadings を一切変えない。

受け入れ観点(testable):
- 定理11.1 / 12.4 の上記5前提が `ag.cech-obstruction@1` 実行時の assumptionLedger に theoremRef("part4/11.1" 等)付きで出力される。
- `nerveIsForest && !hasTripleOverlapFaces` の fixture で定理12.4 forest 前提が `checked`、それ以外(triple overlap あり、または forest でない)の fixture で `assumed` になることを test が固定する。
- surjective restriction 行が forest/no-triple であっても常に `assumed` のままで `checked` に昇格しないことを test が固定する。
- 同一 archmap 入力に対し本要求前後で structuralVerdict・computedInvariants・analyticReadings の packet がバイト同一(ledger 区画以外不変)であることを test が固定する。

依存: M0(リリース定義)。V 側で「確実に閉じる patch の濃淡(濃い緑=forest+no-triple で checked / 薄い緑=torsor effectivity assumed)」を駆動する。

### M2. P0-2 restriction-compatibility evaluator `ag.restriction-compatibility@1`(新 EffCoeff `finite-support-inclusion@1`)

sheaf 条件の前段である separated presheaf 条件(restriction-compatibility)を有限 checked 化する沈黙ギャップ充填。各被覆辺 W_i->W_j で `res_{ij}(I_Ob^U(W_i)) ⊆ I_Ob^U(W_j)` を square-free 生成系の support 包含で有限判定する新 evaluator を `ag_manifest` に登録する。Lean `ObstructionIdeal.RestrictionCompatible.maps_selected` に正確対応する。

計測=評価器設計・verdict semantics・境界: 新 EffCoeff `finite-support-inclusion@1` を導入し、各 cover 辺で局所イデアル生成系の support が上流へ包含されるかを判定する。verdict semantics(既存5値を再利用、新種別なし): `measured_zero`=全辺で separated presheaf 条件成立、`measured_nonzero`=ある辺で局所イデアルが上流へ流れない構造的不整合、`not_computed`=被覆辺空 / 生成系欠落(U-adequate cover violated、沈黙)。境界: 選択 cover・選択 witness 族上の separated presheaf 条件のみに scope し、`measured_nonzero` は「local-sum presentation が sheaf へ持ち上がらない」であって理論対象の defect ではない(sheaf image 再定義で消えうる旨を boundaryNote に明記)。追加する被覆辺 contract は profile 内の有限 witness family の宣言であって profile 外計測(global semantic safety / runtime)ではなく、contract が無ければ正しく `not_computed`(沈黙)に落ちる。本 evaluator は cech `measured_zero` の hedge を Leray とは別に「一段だけ」assumed->checked へ昇格する(Leray は依然 assumed)。

新規 structural verdict: ちょうど1個。`ag.restriction-compatibility@1` の single law、選択 cover に scope する separated presheaf 条件の verdict のみ。5値 verdict 種別自体は不変で、新しい verdict 種別は追加しない。

受け入れ観点(testable):
- 新 evaluator `ag.restriction-compatibility@1` が `ag_manifest` に登録され、新 EffCoeff `finite-support-inclusion@1` が MeasurementProfile/v1 行として宣言できる。
- 全辺で support 包含が成立する fixture で `measured_zero`、ある辺で包含が破れる fixture で `measured_nonzero`(どの辺か source refs 付き)、被覆辺空 / 生成系欠落の fixture で `not_computed` を返すことを test が固定する。
- `measured_nonzero` の boundaryNote が「sheaf image 再定義で消えうる、理論対象の defect ではない」を含むことを test が固定する。
- 新 structural verdict が `ag.restriction-compatibility@1` の single law・選択 cover に scope し、他 evaluator の verdict 件数を増やさず 5値種別を不変に保つことを test が固定する。

依存: M0(リリース定義)。V 側で「神経辺の段差(局所イデアルが上流へ流れ落ちない断層)」を駆動する。

### M3. P0-3 section-factorization evaluator `ag.section-factorization@1`(s^* I_Ob^U=0 の有限 checked、section 不在は沈黙)

lawful の核心述語 `s^* I_Ob^U=0`(Lean `lawful_iff_factorsThroughLawfulLocus` で proved)を、選択 section が contract に供給されたときだけ有限 checked 化する沈黙ギャップ充填。section データが無ければ正しく沈黙する(計測しない)。Lean `FiniteExamples.lean` の pullback 機構(zeroEval/oneEval)に対応する。

計測=評価器設計・verdict semantics・境界: 選択 section(witness 変数への Boolean 割当 = witnessAssignment atom)について、activeSupport が minimalForbiddenSupports のいずれかを包含すれば `s^* I_Ob^U != 0`(unlawful section)、一つも包含しなければ `=0`(lawful section、Δ_U の face に乗る)を有限判定する。verdict semantics(既存5値 `measured_zero` / `measured_nonzero` / `unmeasured` / `unknown` / `not_computed` を再利用、新種別なし): `measured_zero`=section-relative lawful、`measured_nonzero`=lawful locus を外れる構造証拠(violatedForbiddenSupports 付き)、`not_computed`=section データが contract に無い(沈黙)、`unknown`=部分割当で決定不能。境界: section-relative lawful のみに scope し、全 section lawful・exactness 無しの5項同値・runtime/semantic 安全は非主張。No-Cancellation/exactness は assumption ledger に assumed として記録する。

新規 structural verdict: 種別を増やさない(既存5値 `measured_zero` / `measured_nonzero` / `unmeasured` / `unknown` / `not_computed` を再利用)。`ag.section-factorization@1` の single law、選択 section に scope する。

受け入れ観点(testable):
- witnessAssignment atom(Boolean 割当)規約が定義され、total 割当で `measured_zero`(全 forbidden support を回避)/`measured_nonzero`(ある forbidden support を包含、violatedForbiddenSupports 付き)を返すことを test が固定する。
- partial 割当で決定不能のとき `unknown` を返すことを test が固定する。
- section データが contract に無いとき `not_computed`(沈黙、残タスク扱いしない)を返すことを test が固定し、section 不在を「未完了」と表現しない。
- No-Cancellation/exactness が assumption ledger に assumed として記録され、5項同値・全 section lawful・semantic 安全を結論しないことを boundaryNote が固定する。

依存: M0(リリース定義)。M2 / P2-1(lawful locus arrangement)の薄板上に section 着地点を落とす可視化の前提となる。V 側で「lawful locus 薄板上の section 着地点(lawful 緑 / cage 捕捉 赤)」を駆動する。

### M4. P0-4 Tor_1 を真の monomial Taylor resolution `finite-monomial-tor-taylor@1` へ昇格(verdict id 据置、higher Tor_i 沈黙)

`ag.law-conflict-tor@1` の degree-1 shared-support proxy を、命題5.5 が要求する Taylor/lcm-multigraded free resolution へ昇格する既測 proxy の忠実化。verdict id は据置で、内部 method を `finite-monomial-tor-taylor@1` へ差し替え、class 数を過大に読む proxy 誤差を解消する。Lean `Proposition55DirectTheoremPackage` の assertion を計測層へ落とす。

計測=評価器設計・verdict semantics・境界: I_U, I_V の生成元から Taylor 複体を組み R_W/I_V で tensor、F2 で H_1=Tor_1 の dim を取る。各 conflict class に multidegree=lcm(x_S, x_T)=witness support 合成を添付し、inert だった `resolution_selector` フィールドを実効化する。verdict semantics は据置(verdict id 不変)。境界: 局所 chart W 相対の monomial Tor のみに scope し、higher Tor_i(i>=2)は沈黙、flat base change 安定性は theorem-candidate のまま、異 ambient 比較は common ambient morphism 無しなら `not_computed`(原則9.3)。F2 homology が field-coefficient reading である旨を ledger に明示する。非 square-free monomial を含む cover は `unmeasured`(Taylor regime 外)。

新規 structural verdict: ゼロ。verdict id 据置で内部 method 昇格のみ。computedInvariants に multidegree=lcm を添付するが verdict 種別・件数は不変。higher Tor_i は M8(P1-6)の typed boundary で別途扱う(本要求では degree-1 verdict を降格させない)。

受け入れ観点(testable):
- 内部 method が `finite-monomial-tor-taylor@1` になり、Taylor 複体 + R_W/I_V tensor + F2 H_1 で Tor_1 dim を計算することを test が固定する。
- proxy が過大に読んでいた fixture(shared-support は重複するが実 Tor_1 class 数がより少ない)で、Taylor 計算後の class 数が proxy 値以下になることを test が固定する。
- 各 conflict class に multidegree=lcm(x_S, x_T) が computedInvariants として添付され、resolution_selector が実効化(inert でない)されることを test が固定する。
- 非 square-free monomial を含む cover で `unmeasured`(Taylor regime 外)、common ambient morphism 不在で `not_computed` + `no_common_ambient` を返すことを test が固定する。
- F2 homology が field-coefficient reading である旨が assumption ledger に明示され、higher Tor_i / flat base change を結論しないことを boundaryNote が固定する。

依存: M0(リリース定義)、M8(P1-6 higher Tor_i typed boundary、degree-1 measured_zero が derived-transversality へ誤読されないよう sibling で固定)。V 側で「shared-witness edge ごとに分解した Tor 交差 glyph(multidegree=lcm)」を駆動する。

### M5. H^2 triple-overlap coherence evaluator 'ag.coherence-obstruction@1'(banded abelian F2)

意図: 設計済みの planned silence(`selectedH2 not_measured`)を、banded abelian 係数 A=F2 に限って忠実に解除する。第IV部 定義10.1 の triple-overlap coherence は Part IV 内の有限不変量であり、投影 scaffolding(`triangles[].sharedAtomRefs` を持つ 2-skeleton)は既に packet 内にある。これが最も低摩擦・高 payoff の沈黙反転である(design note P1-1)。

計測(評価器設計): 選択 cover の 2-skeleton 上で H^2 = ker δ2 / im δ1 を F2 で計算する。triple-overlap face の section mismatch から 2-cochain h_ijk を組み、まず δ2 h=0(2-cocycle 条件)を明示ゲートとして検査し、合格した cocycle についてのみ im δ1 への帰属を F2 ガウス消去で判定する。invariant 散文は `ker d^1/im d^0` ではなく `ker d^2/im d^1` を正とする(design note 完全性クリティック(e))。`ag.cech-obstruction@1` と排他でなく共起可能な新 ag.* law として `ag_manifest` に追加する。

verdict semantics: 既存5値を再利用し新規 structural verdict 行をちょうど **1個**(`ag.coherence-obstruction@1`、選択 cover・banded abelian F2 に scope)出す。`measured_zero`=全 2-cocycle が coboundary、`measured_nonzero`=triple で壊れる concrete class([gerbe] の banded reading、representative を持つ場合のみ)、`unmeasured`=coherence witness atom 不在、`not_computed`=2-skeleton 空 / banding violated。原則4.4 に従い nonzero group ≠ 任意 concrete class とし、representative を持つときだけ nonzero を主張する。本評価器が出すのはこの1行のみで、H^1(`ag.cech-obstruction@1`)verdict を一切変更しない。

境界: sheaf cohomology 全体への持ち上げは非主張(cover-relative + Leray assumed を CBI ledger に記録)。non-abelian gerbe(一般 Aut(Dec_U)係数)は計測対象外=banding violated で `not_computed`(沈黙、M8 の `out_of_selected_vocabulary` typed boundary が引き受ける)。pairwise H^1 が `measured_zero` でも H^2 が `measured_nonzero` になりうる二層を取り違えさせない。

受け入れ観点:
- δ2 h=0 cocycle ゲートが im δ1 membership 判定の前段として実装され、cocycle でない 2-cochain は membership 検査に進まないことを test で固定する。
- pairwise-compatible だが triple-incompatible な witness を持つ fixture で `measured_nonzero` + representative を返し、全 cocycle が coboundary な fixture で `measured_zero` を返す。
- banding violated(non-abelian 係数指定)入力で `not_computed` を返し、新 structural verdict を生成しないことを test で固定する。
- coherence witness atom 不在の fixture で `unmeasured`、2-skeleton 空の fixture で `not_computed` を返し、両者を取り違えないことを test で固定する。
- invariant 散文が `ker d^2/im d^1` であり `ker d^1/im d^0` を含まないことを検査する。
- 新 structural verdict が `ag.coherence-obstruction@1` の1行のみで、`ag.cech-obstruction@1`(H^1)と共起する fixture で H^1 verdict が変化しないことを test で固定する(verdict 件数 = 既存 + 1)。
- CBI ledger に Leray=assumed が記録され、coefficient=F2 が ledger に明示される。

M→V 依存: 本評価器は `ag.coherence-obstruction@1` structural verdict 1行(scope=選択 cover・banded abelian F2)を生成する。これが V 系の「三角膜の開閉」可視化を駆動する唯一の根拠であり、`measured_zero`=閉じた膜 / `measured_nonzero`=開いた膜の対応は本 verdict が land した後にのみ許される(verdict 無しの膜開閉は H^2 捏造)。banding violated / `unmeasured` / `not_computed` の face は描かない(沈黙)。

依存: M8(banding violated / non-abelian gerbe を `out_of_selected_vocabulary` typed boundary が引き受ける)、M7(dimC2 = triple-overlap face 数を Topological Debt Capacity reading と共有しうる)。

### M6. boundary-residue δ evaluator 'ag.boundary-residue@1'(Mayer-Vietoris d^0, F2)

意図: feature extension の core/feature が各々 lawful でも boundary residue が大域障害になりうる。第IV部 定義8.3 の connecting hom δ: H^0(B)→H^1 を F2 で忠実計測し、原則7.2(Local Success Is Not Global Lawfulness)を核に「core/feature が各々 lawful でも boundary residue は消えるとは限らない」を語る(design note P1-2、例9.3 が F2 有限計算として明示)。

計測(評価器設計): cover を core/feature/boundary に分類する atom を導入し、B=C_core∩F 上の mismatch section b_U を F2 表現する。Mayer-Vietoris の d^0 を core⊕F→B の restriction 行列で組み、b_U が im(d^0) に入るか(δ(b_U)=0 か)を F2 ガウス消去で判定する。`measured_zero`=boundary residue が吸収され大域障害にならない、`measured_nonzero`=boundary residue が大域 H^1 class を生む。

verdict semantics: 新 structural verdict 行を **1個**(`ag.boundary-residue@1`、選択 cover・core/feature/boundary 分類された witness 族に scope)出す。coefficient=F2 は ledger に `checked` 行、Z holonomy への持ち上げ(Z-zero)は別の `assumed` 行(F2 パリティは Z holonomy の mod2 還元)として二行で分離記録する。定理9.2 の iff は重い仮定スタックに相対化され、coefficient 非固定時は片方向 obstruction statement(δ≠0→not globally U-flat)に退く。

境界: period-Stokes pairing(modelRelative, M9 / analytic レーン)とは分離し、δ の structural 像のみを verdict に出す。π1^AAT を復活させない(boundary residue は restriction 構造の有限計測であって monodromy verdict ではない。`Z holonomy` の語は mod2 還元元としての ledger assumption に留め、絶対 monodromy 不変量として計測対象化しない)。core/feature/boundary ラベルが contract に無ければ正しく `not_computed`(沈黙、profile 内の新しい有限 witness family 宣言の不在)。

受け入れ観点:
- core/feature/boundary 分類 atom と boundary mismatch atom の規約を持ち、ラベル不在時に `not_computed` を返すことを test で固定する。
- δ=0 fixture(boundary residue が im(d^0) に入る)で `measured_zero`、δ≠0 fixture で `measured_nonzero` を返す。
- coefficient=F2 が ledger に `checked` 行、Z-zero 持ち上げが別の `assumed` 行として二行に分離記録されることを test で確認する。
- coefficient 非固定時に両方向 iff を主張せず片方向 obstruction statement(δ≠0→not globally U-flat)に退くことを test で固定する。
- 新 structural verdict が `ag.boundary-residue@1` の1行のみで、period-Stokes modelRelative reading と schema 上分離していることを確認する(verdict 件数 = 既存 + 1)。
- 引用が原則7.2(Part IV)を正とし、π1 系 verdict・`Z holonomy` の絶対 monodromy verdict を生成しないことを確認する。

M→V 依存: 本評価器は `ag.boundary-residue@1` structural verdict 1行(scope=選択 cover・core/feature/boundary 分類 witness 族)を生成する。これが V 系の「縫い目の裂け / core-feature 二パッチ」可視化を駆動する唯一の根拠であり、`measured_nonzero` での縫い目 B の裂けは本 verdict が land した後にのみ許される(δ を測らず縫い目を裂くと Mayer-Vietoris 捏造)。`not_computed` 時は縫い目を描かない(沈黙)。

依存: なし(独立評価器)。

### M7. Topological Debt Capacity 不変量(rank-nullity capacityLowerBound / Euler / b1NerveReading)

意図: 手元にある dimC0/dimC1/dimC2 を、第IV部 定理12.2 の rank-nullity 不等式・系12.5 の Euler 交代和・系12.3 の b_1 同型に組み、cover 形状が許す H^1 容量(潜在的余地)と実測 class を分離する reading にする(design note P1-3、現状は C^2 が手元にあるのに rank-nullity に使われていない)。

計測(評価器設計): `capacityLowerBound = max(0, dimC1 − dimC0 − dimC2)`(定理12.2 rank-nullity)、`eulerCharacteristic = dimC0 − dimC1 + dimC2`(系12.5)、`b1NerveReading`(系12.3)を invariant 行として `ag.cech-obstruction@1` の computedInvariants に追加する。b_1 は既存 `reduced_simplicial_homology_f2` を nerve に適用するか face を含む reduced homology で取り、1-skeleton b_1 と nerve 複体 b_1 のずれを明示する(face が loop を埋める cover で乖離するため)。

verdict semantics(reading 行): structural verdict を **生成しない**(invariant/reading のみ)。`capacityLowerBound>0` は「H^1 に余地がある」だけで concrete class の存在を非主張(原則4.4)。Euler は「debt が消えた」ではなく cochain accounting の保存則。系12.3 の b_1 同型は定数係数 assumption に相対化する。本 reading は `ag.cech-obstruction@1` の H^1 verdict を一切変更しない。

境界: 現行 `h1_dimension` は 1-skeleton b_1 であり、face が loop を埋める cover では nerve 複体 b_1 とずれるため、出力を「1-skeleton reading」と明示するか face を含む reduced homology で取る。原則11.3 参照は Part IV(Cohomological Non-Claim)限定と明記する(Part VII の同番号は別物)。

受け入れ観点:
- `capacityLowerBound = max(0, dimC1 − dimC0 − dimC2)` と `eulerCharacteristic = dimC0 − dimC1 + dimC2` が computedInvariants 行として出力され、structural verdict 件数が増えないことを test で固定する。
- 1-skeleton b_1 と nerve 複体 b_1 が別フィールド(または明示ラベル付き)で区別され、face が loop を埋める fixture で両者が乖離することを test で示す。
- `capacityLowerBound>0` が concrete class 存在を主張せず capacity と実測 class が分離していることを確認する。
- b_1 同型読みに定数係数 assumption が ledger / boundary に相対化されていることを確認する。
- 原則11.3 参照が Part IV 限定であることを散文で明記する。

M→V 依存: 本ブロックは structural verdict を生成しない reading(invariant)ブロックである。V 系の「b_1 閉路リング / 穴あき度メーター」可視化は本 invariant(`capacityLowerBound` / `b1NerveReading`)だけを駆動でき、capacity(潜在的余地)と実測 class(`ag.cech-obstruction@1` の点灯 loop)を視覚的に分離する。全ループ点灯で capacity と実測 class を混同させると原則4.4 違反であり、本 reading は新 verdict を作らないので viewer も projectionBoundary(no new structural verdict)を維持する。

依存: M5(dimC2 = triple-overlap face 数を coherence evaluator と共有しうる)。

### M8. 沈黙の typed boundary 明示固定(higher H^n / non-abelian stack-gerbe / higher Tor_i)

意図: 計算を増やさず、沈黙の線引きを typed boundary として明示固定する。三系統の沈黙を取り違えない三層分離が核(design note P1-4 + P1-6)。既存 `BoundaryStatementV1`(kind: `silence_by_design` / `out_of_selected_vocabulary` / `unmeasured_support`)を所定 scope に紐づける。

計測(boundary 出力設計): `BoundaryStatementV1` を三層で出力する。(1) `silence_by_design` scope=`Hn n>=3 abelianized`(finite-site で計算可能だが Part IV scope 外、原則10.3)。(2) `out_of_selected_vocabulary` scope=`stack/gerbe non-abelian H^2(X,Aut(Dec_U))`(abelian F2 語彙外、第VI部16.1、M5 の banding violated を引き受ける)。(3) `unmeasured_support` scope=`LawConflict_i for i>=2`(degree-1 `measured_zero` が derived-transversality(全 i>0、定理7.3)を discharge しないことを明示、M4 の degree-1 Tor を補完)。

verdict semantics(typed boundary): structural verdict を **一切生成しない**。沈黙=boundary であって zero ではない。degree-1 verdict の `depends_on_assumptions` による降格を避け、H^2 precedent に倣い boundary statement + claimScope text の degree-1 scoping のみで実装し、assumption propagation を発火させない(design note P1-6 実装注意)。計測不在を残タスク化しない(CLAUDE.md のウィトゲンシュタイン的責務境界)。沈黙を non-conclusion 一覧として主役化せず、結論の近くに最小限の typed boundary として置く。

境界: derived-transversality・higher H^n・non-abelian gerbe を非主張。degree-1 衝突ゼロでも高次 Tor は沈黙。H^2 silence と Tor 軸の沈黙を対称なウィトゲンシュタイン的沈黙として明文化する。三層はいずれも既存 `BoundaryStatementV1` kind の再利用であり、新 boundary kind も新 verdict も作らない。

受け入れ観点:
- 三層の BoundaryStatementV1 が各々正しい kind(`silence_by_design` / `out_of_selected_vocabulary` / `unmeasured_support`)と scope text で出力され、取り違えがないことを test で固定する。
- higher H^n / non-abelian gerbe / higher Tor_i のいずれも structural verdict を生成せず、新 boundary kind を追加しないことを確認する(structural verdict 件数不変、kind 集合不変)。
- degree-1 `measured_zero` が boundary statement + claimScope text の scoping のみで degree-1 へ scope され、`depends_on_assumptions` を発火させない(degree-1 verdict が降格しない)ことを test で固定する。
- 沈黙が non-conclusion 一覧の主役化でなく typed boundary(最小限)として扱われることを確認する。

M→V 依存: 本ブロックは structural verdict も新 boundary kind も生成しない sibling typed-boundary ブロックである。V 系は本三層の typed boundary を「凡例の minimal label」(higher coherence: silent by design / non-abelian: outside this lens / higher Tor: unmeasured)としてのみ投影でき、n≥3 単体・non-abelian face・higher Tor 領域に geometry や色を描かない(空白を埋めない=沈黙の尊重)。M5 の H^2 開閉膜・M4 の degree-1 Tor glyph が land した範囲の外側を本 boundary が typed に閉じる。

依存: M4(degree-1 monomial Tor を `unmeasured_support`(higher Tor_i)で補完)、M5(non-abelian banding violated を `out_of_selected_vocabulary` で受ける)。

### M9. Stokes audit identity の structural verdict 化 'ag.period-stokes-audit@1'

意図: 第IV部 定理13.2 は厳密会計(certified bounded inference)なのに、現状 `ag.period-stokes@1` は `residual.abs()>1e-9` の hard Err(run crash)で過剰ヘッジしている。この過剰ヘッジを解除し、Stokes audit residual を固定係数環上の structural verdict へ正規化する(design note P1-5)。

計測(評価器設計): Stokes audit residual r = <dω,γ> − <ω,∂γ> を固定係数環(F2 または Q)上の厳密差として全 (form,chain) 対で計算する。全対で r≡0 なら `measured_zero`、一対でも r≠0 なら `measured_nonzero`。現状の `residual.abs()>1e-9` hard Err(run crash)を廃止し nonzero verdict へ正規化する。analytic な `strict-period-pairing@1`(第VII部 定義5.2/5.2A の period pairing matrix)は別 reading として据え置く。

verdict semantics: 新 structural verdict 行を **1個**(`ag.period-stokes-audit@1`、供給された独立会計値の固定 pairing 下の内部整合性に scope)出す。verdict semantics は「供給された独立会計値(dOmega/boundary atom)の固定 pairing 下の内部整合性」へ正確に限定し、定理13.2 の純内部恒等式(常に 0)そのものを measured と誤認させない。厳密係数を解決できず float のみのときは `unknown` へ降格し strict-period-pairing analytic-reading に留める。本評価器が出すのはこの1行のみで、analytic `strict-period-pairing@1` を structural verdict 化しない。

境界: 外部手続きの pairing 保存は非結論(原則13.3)。analytic period pairing matrix(modelRelative, M14 overlay が投影)とは別レーンに保つ。float hard Err(run crash)を廃止することで、空 packet や係数未解決でも crash させず `unknown` / 沈黙へ正規化する。

受け入れ観点:
- 全 (form,chain) 対で固定係数環上の厳密 residual を計算し、全対 r≡0 で `measured_zero`、一対でも r≠0 で `measured_nonzero` を返すことを test で固定する。
- 現状の `residual.abs()>1e-9` hard Err(run crash)が廃止され、nonzero が verdict として正規化されることを test で確認する(nonzero 入力で crash せず `measured_nonzero` を返す)。
- 空 packet / 厳密係数未解決(float のみ)時に crash せず `unknown` へ降格し strict-period-pairing analytic reading に留まることを test で固定する。
- 新 structural verdict が `ag.period-stokes-audit@1` の1行のみで(verdict 件数 = 既存 + 1)、analytic `strict-period-pairing@1`(period pairing matrix)は別 reading として verdict 化されないことを確認する。
- 定理13.2 の純内部恒等式そのものを measured と誤認させない claimScope が散文に明記される。
- 外部手続きの pairing 保存(原則13.3)を非結論として扱う。

M→V 依存: 本評価器は `ag.period-stokes-audit@1` structural verdict 1行(scope=供給された独立会計値の固定 pairing 下の内部整合性)を生成する。これが V 系の「周期メーター / ribbon-with-residual-flux」可視化を駆動する唯一の structural 根拠であり、`measured_zero`=滑らかに閉じる loop / `measured_nonzero`=外向き residual フラックスの突出は本 verdict が land した後にのみ許される(float smallness で「閉じた」と描くと厳密会計を proxy で偽装)。period pairing matrix の landscape は M14 overlay が analytic_reading 色で別レーン投影し、本 verdict と取り違えない。

依存: M14(P2 overlay が period pairing matrix を analytic_reading 色で投影し、本 verdict と別レーンに保つ)。

### M10. その他 P1 reading 群 — Hilbert 干渉級数 / support-transfer bounded inference / curvature spectrum hotspot / refactor-invariant transport / repair 下界 inspection を忠実化(structural verdict 不生成 or analytic レーン)

**意図.** design note P1 後半「その他の P1(同質ゆえ要点のみ)」が挙げた5つの低価値・同質クラスタを一括で忠実化する。いずれも既測 proxy の忠実化または analytic reading 追加であり、新規 structural verdict は一切作らない。`measured_zero` の射程を深める核(M1-M4)や沈黙反転の本筋(M5-M6)とは別に、proxy/未投影 reading を AG 本文の前提検査つき bounded inference へ正しく落とす整備束として位置づける。

**計測(評価器設計・verdict semantics・境界).**
- **(a) Hilbert 干渉級数 Int_{U,V}(t)**(第V部 定義12.1/定理12.2/原則12.3): graded monomial regime に限り、policy_conflict 上の衝突を次数別に分解した干渉級数を `AgAnalyticReadingV1` の audit reading として出力する。**verdict ではなく audit reading**(原則12.3)。非 graded / 非 monomial regime は `not_computed` 相当の reading 不在。
- **(b) support-localized transfer の bounded inference 接地**(第V部 定義10.4/定理10.5-10.6): 既存 `ag.support-transfer@1` の transfer 行列を、定義10.4 の support-localized 条件(support 非交差 path に無条件で行列値を埋めない)を **計測前提として検査**してから埋める。ambient LawConflict だけから任意 direction の transfer を結論しない。proxy/modelRelative のまま、structural verdict は不変。
- **(c) curvature transfer spectrum の Perron-Frobenius hotspot 忠実投影**(第VIII部 定義8.9/定理候補8.10、第VII部 原則7.3): 現 `curvatureTransferSpectrum`(per-cell L·cochain 値で spectrum でも T_curv でもない misnamed proxy)を温存したまま、power-iteration による principal eigenvector hotspot を **別 readingKind** で並置する。hotspot は本要求で新規計算する(現状未実装)であり、theorem-candidate regime なので `regime: theorem-candidate` flag + `structural_verdict_ref=None` を強制(`check_analytic_regime_boundary`)。
- **(d) refactor-invariant transport の有限整合 reading**(第VIII部 定理7.3、第VI部 定義12.1): functoriality data(二 presentation 間の対応)が contract に供給されたときのみ、二 snapshot 間の **既存 verdict transport 整合**を有限監査する analytic reading。新 verdict を生成・transport せず、既に land した verdict を読むだけ。供給が無ければ沈黙(`not_computed` 相当の reading 不在、単一 snapshot しか見ない既存挙動)。
- **(e) repair を Alexander-dual / discrete-Morse の下界 inspection として忠実化**(定理候補5.5): repairMorphPath を「到達可能アニメ」や operation semantics ではなく「下界マーカー付き inspection glyph」へ意味を矯正。修復の組合せ的下界・候補であって修復の意味論ではない(原則5.3)。theorem-candidate gating に従う。

**境界.** (a)(c)(e) は analytic レーンに隔離し proxy を structural verdict に昇格させない。(b)(d) は前提検査・既存 verdict 読みを増やすだけで verdict は不変。全項で **新規 structural verdict ゼロ**。support 非交差 path への無条件 transfer 結論、principal eigenvector hotspot の verdict 化、refactor transport を functoriality data 無しで結論すること、repair の operation semantics 化は禁止。**(d) は v0.4.0 PRD Non-Goals が v0.5.0 以降へ送った「refactor transport / functoriality 系 evaluator(verdict 生成器)」を立てるものではない。** (d) は functoriality data 供給時に **既存 verdict の transport 整合だけを読む analytic audit reading** に scope を限定し、verdict 生成・transport 計測評価器は本要求に含めない(その evaluator の是非は別 release で問い直す)。

**受け入れ観点(testable).**
- Hilbert 干渉級数が graded monomial regime のみで audit reading として出力され、非 graded regime で reading が出ない(verdict を生成しない)ことを test で固定する。
- support-transfer evaluator が support 非交差 path に対し transfer 行列値を埋めず、定義10.4 前提検査の有無で出力が変わることを test で固定する。
- curvature hotspot reading が `regime: theorem-candidate` flag 付きで出力され、`structural_verdict_ref=None` であり既存 misnamed proxy と別 readingKind で共存することを test で固定する。
- refactor transport reading が functoriality data 供給時のみ出力され、不在時は沈黙(reading が出ない)こと、および新 verdict を生成しない(既存 verdict の整合読みに留まる)ことを test で固定する。
- repair inspection glyph が下界マーカー reading として出力され「自動修復ではない / lower-bound inspection aid」non-claim を伴うことを test で固定する。
- 本要求の追加で structural verdict 件数が増えないこと(5値 verdict 集合・件数不変)を test で固定する。

**依存.** M0(リリース定義・計測=主/可視化=従の順序規律)。(b) は M8(higher Tor_i typed boundary)と沈黙の整合を共有。(c)(e) の analytic レーン隔離は M14(analytic overlay)の colorRole 規律と整合。(c) の hotspot は本要求で新規 land するため、M14 のスペクトル hotspot overlay 投影はこの(c)着地後に限る(land 前 viewer 投影は捏造)。

### M11. P2-1 lawful locus Flat_U(X)=V(I_Δ) の Stanley-Reisner arrangement 不変量化(facets / vanishingCoords / dimension / irreducibleComponentCount、新 verdict なし)

**意図.** design note P2-1 を実装する。既測未投影の活用であり、lawful locus を「立ってよい座標部分空間の和集合」として arrangement 不変量に落とす。`ag.square-free-repair@1` の `computedInvariants` を拡張するのみで、**新 structural verdict は作らない**。M14 の薄板 overlay と M3(section-factorization)の section 着地点の土台になる計測である。

**計測(評価器設計・verdict semantics・境界).**
- 拡張先は既存 `ag.square-free-repair@1`(verdict 不変)。Δ_U の facets を maximal 抽出し、各 facet T に対し `vanishingCoords = E_W ∖ T`、`dimension = |T|` を計算して `computedInvariants` 行にする。
- `irreducibleComponentCount`(既約成分数 = 座標部分空間 arrangement の薄板枚数)を **invariant 行**として出力する。これは原則3.2 の verdict ではなく計測値そのもの。
- Lean `LawfulLocus.lawfulLocus = PrimeSpectrum.zeroLocus` に対応づける(第III部 定理5.6C / 定理11.1)。lawful locus = 零点集合 V(I_Δ)。
- verdict semantics: 本要求は VerdictData を新設しない。出力は `computedInvariants` の arrangement 不変量行(facets / vanishingCoords / dimension / irreducibleComponentCount)に限る。

**境界.** section ごとの s^* I_Ob^U=0 判定は別計測(M3)であり本要求は行わない。Krull 次元の代数幾何的意味、AAT-flatness = total correctness(原則7.3 で明示否定)は非主張。`irreducibleComponentCount` を「安全度」や verdict と読まない。arrangement は選択 cover・選択 witness family 相対の有限不変量に scope する。

**受け入れ観点(testable).**
- square-free fixture で facets が maximal face として抽出され、各 facet の `vanishingCoords = E_W ∖ T` と `dimension = |T|` が `computedInvariants` に出力されることを test で固定する。
- `irreducibleComponentCount` が invariant 行として出力され、structural verdict として出力されない(VerdictData を持たない)ことを test で固定する。
- 本要求の追加で `ag.square-free-repair@1` の verdict 件数・5値集合が不変であることを test で固定する。
- AAT-flatness = total correctness / Krull 次元意味づけを主張する文言が出力に含まれないことを test で固定する。

**依存.** M0。M3(section-factorization)の section 着地点はこの arrangement 薄板を土台にする。M14(analytic overlay)が薄板を viewer へ投影する駆動計測元。

### M12. P2-2 NSdepth 単調性(命題7.2C)の reading 化 — `ag.nullstellensatz-depth-monotone@1`(値=proxy analytic、monotone/generatorExtension bool のみ structural invariant、verdict 化しない)

**意図.** design note P2-2 を実装する。既測 proxy の忠実化であり、命題7.2C の片側単調性(U⊆U' で NSdepth 非増)を二 law-universe scope で reading として計測する。完全性クリティックの指摘どおり「**verdict 化」を「reading 化」に直す**のが正で、proxy を structural verdict に昇格させない。

**計測(評価器設計・verdict semantics・境界).**
- 新 reading id `ag.nullstellensatz-depth-monotone@1`。U⊆U' の二 law-universe scope で NSdepth の片側不等式(非増)を monotone reading として計測。
- **値の分離が核**: NSdepth 値そのものは hitting-set 上界 proxy 注記つき `analyticReading`(AgAnalyticReadingV1)に留める。`monotone`(片側不等式成立)と `generatorExtension`(U⊆U' で生成系が拡張保存)の **bool だけ** を `structural computedInvariant` にする。NSdepth スカラー値を structural に出さない。
- theorem-candidate regime 接続で `structural_verdict_ref = None` を保つ(verdict を生成しない)。
- verdict semantics: 本要求は新 structural verdict を作らない。`measured_zero`(lawful)と `unknown`(generatorExtension violated)を NSdepth 値で混同しないことを reading 層で保証する。

**境界.** 一般 k での Nullstellensatz、square-free 外の厳密最小表示次数、全 law universe での単調性は非主張。NSdepth 値は proxy であり「直せなさの絶対深さ」や verdict と読まない。monotone bool は二 scope 相対の片側不等式そのものに scope する。

**受け入れ観点(testable).**
- NSdepth スカラー値が `analyticReading` にのみ出力され、proxy 注記(hitting-set 上界)を伴い、`computedInvariant` に値として現れないことを test で固定する。
- `monotone` / `generatorExtension` の bool のみが structural `computedInvariant` に出力され、これらが VerdictData(5値 verdict)を生成しないことを test で固定する。
- `ag.nullstellensatz-depth-monotone@1` reading が `structural_verdict_ref = None` であることを `check_analytic_regime_boundary` 系 test で固定する。
- generatorExtension violated の scope で NSdepth 値が `measured_zero` と混同されないことを test で固定する。
- 本要求の追加で structural verdict 件数が不変であることを test で固定する。

**依存.** M0。proxy の analytic レーン隔離は M14 の colorRole=analytic_reading 規律、および M10(c) の theorem-candidate gating と整合。NSdepth は M11 の arrangement(I_Δ / I_Ob)計測と同じ square-free regime を共有。

### M13. P2-3 Δ_U facet/link の中立名 reading(facetDimensionReading / linkBoundaryReading / linkReducedBetti / isPure)— depth / Cohen-Macaulay / Reisner / srDepth 語彙を全廃

**意図.** design note P2-3 を実装する。既測未投影の活用であり、系5.6D が挙げる Δ_U の facet 次元・link 構造を invariant 行にする。**完全性クリティックの指摘を反映し、本理論が anchor しない外部 Reisner criterion による「depth 下界読み」を意味づけに使わない**。link は boundary-local reading の生の組合せ量として出し、depth/CM 解釈を一切付さない。

**計測(評価器設計・verdict semantics・境界).**
- 拡張先は既存 square-free / locus 計測(verdict 不変)。facet 次元の最小/最大、各頂点の link 連結性、pure 性を invariant 行にする。
- **語彙の全廃が採用条件**: `depth` / `Reisner depth` / `Cohen-Macaulay` / `Krull depth` / `srDepthReading` という語彙を出力・schema・コメントから全廃し、系5.6D 準拠の中立名 `facetDimensionReading` / `linkBoundaryReading` / `linkReducedBetti` / `isPure` へ改名する。
- link は「boundary-local reading の生の組合せ量」として出力し、depth/CM 解釈を付さない。
- verdict semantics: 本要求は新 structural verdict を作らない。出力は中立名 invariant 行のみ。

**境界.** 代数的 Krull depth/CM の証明、link が boundary-local lawfulness を完全決定すること、depth 高 = 安全は非主張。中立名 invariant は選択 cover・選択 witness family 相対の生の組合せ量に scope し、外部 Reisner criterion の意味づけを輸入しない。

**受け入れ観点(testable).**
- `facetDimensionReading`(facet 次元の最小/最大)・`linkBoundaryReading`・`linkReducedBetti`・`isPure` が invariant 行として出力されることを test で固定する。
- 出力・schema・コメントに `depth` / `Reisner` / `Cohen-Macaulay` / `Krull depth` / `srDepth` 文字列が存在しないことを禁止語 scan / test で固定する。
- link reading が depth/CM 解釈を伴わない生の組合せ量として提示され、verdict(VerdictData)を生成しないことを test で固定する。
- 本要求の追加で structural verdict 件数・5値集合が不変であることを test で固定する。

**依存.** M0。中立名 facet 次元・link reading は M11(arrangement facets / dimension)と同じ Δ_U 構造を別側面から読む計測で、M11 の facets 抽出を前提に共有する。M14 が facet 次元を viewer 薄板の厚みへ投影する駆動計測元。

### M14. P2 overlay — analytic overlay projection bundle(period pairing matrix / Wasserstein transfer cost / spectral gap λ1 / curvature spectrum hotspot / singularity concentration)を packet→viewer 投影

**意図.** design note の「P2 analytic overlay バンドル」を実装する。既に計算済みなのに viewer に届いていない analytic reading(measured_not_projected)を、structural verdict と取り違えない analytic レーンとして投影する。**計測ロジックは一切変えない**。本要求は計測ノートの一部だが、駆動する計測(period-stokes / support-transfer / laplacian / law-conflict 評価器の出力)が packet に存在する値を viewer に運ぶ投影であり、捏造禁止規律(計測 land 前に viewer が構造を描かない)を満たす。**ただし overlay (4) curvature spectrum hotspot は M10(c) で新規 land する計測値であり、本要求の既存 measured_not_projected(period landscape / Wasserstein / spectral gap)とは状態が異なる**。viewer 側の実体は viewer ノート Framing 4(T2-5/T2-6/T4-1/T4-3)が消費する。

**計測(packet→viewer 投影設計・verdict semantics・境界).**
- 投影対象5種: (1) **period pairing matrix overlay**(form×cycle の period landscape、既存 packet 実在値)、(2) **Wasserstein transfer cost / transferResidue overlay**(repair→target の obstruction mass 流、既存 packet 実在値)、(3) **spectral gap λ1 overlay**(hodge-debt 谷の浅深、既存 packet 実在値)、(4) **curvature spectrum hotspot overlay**(Perron-Frobenius、別 readingKind。**M10(c) が land する計測値に依存**)、(5) **per-stratum 障害集中(singularity concentration)reading**(context ごとの LawConflict_1 non-transverse meeting count)。
- **配線の核**: projection 関数追加だけでは viewer に届かない。`build_measurement_viewer_data_v1` の **allowlist** と **binding scene**(`attach_gluing_scene_geometry` 等の law-conflict-tor / period-stokes arm)を拡張し、新キーを `aatGeometryOverlays` 配下へ運ぶ。
- `colorRole = analytic_reading` を固定し、measured_zero(teal)へ昇格させない。`gluing_geometry_projection_v1` の `projectionBoundary`(no structural verdict)と `cli.rs` の test-locked「does not create a new structural verdict」境界を維持する。
- nonClaim 必須表示: period は modelRelative(比較同型未証明)、Wasserstein は W_1 そのものでない/global 修復安全性を証明しない、spectral gap は L_1 でなく proxy 固有値(gap≈0 を measured_zero teal に着色しない)、curvature hotspot は theorem-candidate proxy、singularity concentration は `deformationRegime=not_provided` を boundary で明示し God object size / repair difficulty とは呼ばない。
- **投影順序規律(捏造禁止)**: overlay (4) hotspot は M10(c) の hotspot 計測が land した後にのみ投影し、M10(c) land 前に viewer が hotspot 構造を描かない(未着地計測の投影は捏造)。overlay (1)(2)(3)(5) は既存 packet 値の投影なので本要求内で完結する。

**境界.** structural verdict を新規に作らない・昇格させない。near-flat ≠ lawful(原則8.4)、W_1 そのものでない、God object size でないを nonClaim に固定。専用 profile 不在時の空 packet では沈黙挙動(赤エラー化せず reading が出ない)。viewer projectionBoundary(no new structural verdict)を維持。overlay (4) の land 前投影禁止は捏造禁止規律の適用であり、M10(c) 未着地時は (4) を出さず沈黙する。

**受け入れ観点(testable).**
- 5種 overlay が `colorRole=analytic_reading` 固定で投影され、measured_zero へ昇格しないことを test で固定する。
- `build_measurement_viewer_data_v1` の allowlist と binding scene に新キーが追加され、projection 関数追加だけでなく viewer まで届くことを test で固定する。
- 本要求の追加で structural verdict 件数が不変(`projectionBoundary` no-structural-verdict 維持)であることを `cli.rs` test-locked 文言とともに test で固定する。
- 各 overlay が regime=analytic-measurement の nonClaim(modelRelative / proxy / 非保存 / not_provided)を伴うことを test で固定する。
- 専用 profile 不在の空 packet で各 overlay が沈黙(赤エラー化しない、reading 空)になることを test で固定する。
- overlay (4) hotspot が M10(c) の hotspot 計測値不在時には投影されず沈黙する(land 前投影しない)ことを test で固定する。

**依存.** M0。駆動計測元: M9(Stokes audit)が period landscape の analytic 側 strict-period-pairing を据置で供給、M10(c)(curvature hotspot)・M10(b)(support-transfer)の analytic reading を投影、M11(arrangement 薄板)・M13(facet 次元厚み)の invariant を viewer 形状へ運ぶ。**overlay (4) は M10(c) が land する前に投影してはならない(計測=主/可視化=従の順序規律)**。singularity concentration は M8(higher Tor_i typed boundary)の沈黙と deformationRegime=not_provided の boundary を共有。

### M15. P3-1 common ambient assumption ledger の violated 伝播精緻化(coefficient-compatibility 行)。schema 拡張(coefficientRef 等)は別 Issue 送り

**意図.** design note P3-1 を実装する。整備寄りの最小要求であり、CBI assumption ledger に coefficient-compatibility 行を定義9.1(common ambient pair)に紐づけて追加し、violated 伝播の精緻化を行う。現行の単一 coefficient モデルでは不整合が実質起きえないので、これは主にドキュメント行・台帳透明性の補強である。

**計測(ledger 設計・verdict semantics・境界).**
- 拡張先は既存 CBI assumption ledger(R10)。`theoremRef` を定義9.1(common ambient)に紐づけた **coefficient-compatibility** assumption 行を追加する。
- 単一 coefficient モデル下では `status=checked`(または assumed)で実質ドキュメント行。`violated` が立った場合の伝播は既存規律どおり、依存する measured 行のみを `not_computed` へ正規化する(measured_zero と混同しない)。
- **schema 拡張は本要求に含めない**: `coefficientRef` / `comparisonMorphismRef` の schema 拡張は、contract が admit しない計測軸の製造に傾くため別 Issue 送り(input モデル拡張の是非から問い直す)。本要求は ledger 行の追加と violated 伝播精緻化に scope を限定する。
- verdict semantics: 本要求は新 structural verdict を作らない。ledger 行(theoremRef / assumption / status / checkedBy / assumedBy)の追加と既存 not_computed 正規化規律の適用のみ。

**境界.** coefficientRef / comparisonMorphismRef の schema 新設は禁止(別 Issue)。multi-coefficient / multi-ambient の計測軸を製造しない。ledger 行は結論文に反映せず assumptions 区画に留める(境界の一括前払い)。

**受け入れ観点(testable).**
- coefficient-compatibility assumption 行が定義9.1 紐づけ(theoremRef)で ledger の assumptions 区画に出力されることを test で固定する。
- coefficient-compatibility が violated のとき、依存する common ambient / Tor 系 measured 行のみが `not_computed` へ落ち、measured_zero と混同されないことを test で固定する。
- 本要求の追加で `coefficientRef` / `comparisonMorphismRef` の schema field が新設されない(schema 不変)ことを test で固定する。
- ledger 行が結論文に反映されず assumptions 区画に留まることを test で固定する。
- 本要求の追加で structural verdict 件数・5値集合が不変であることを test で固定する。

**依存.** M0。M5/M4 の common ambient 前提(no_common_ambient → not_computed)と同じ定義9.1 を共有し、coefficient-compatibility はその ambient ledger の透明性を補う。M8(typed boundary)の沈黙規律と整合し、violated を残タスク化しない。

### ワークストリーム V: 計測に応じた3D可視化(従)

### V0. Viewer フェーズ規律 — 各 V は駆動計測 M の land 後にのみ有効化する

**意図**: この PRD は「計測=主・可視化=従」を背骨とする(measurement note の冒頭規律)。各 V 要求は packet が実際に語る量だけを幾何にし、計測されていない構造を viewer が描く=捏造を全要求で禁じる規律をここで一括宣言する。

**規律(全 V 要求が従う contract)**:
- 各 V 要求は「駆動する計測 M-id」を必ず名指す。その M(または既存 v2 packet データ)が land する前に、その M が定義する構造を viewer が幾何として描いてはならない(measurement note『可視化との接続』表の「計測なしに先行させると」列を侵犯と判定する)。
- 新規データ不要の V(V1 PBR基盤 / V2 selective bloom / V3 沈黙描画 / V4 ラベル・空間文脈 等)は、既存 v2 artifact(`aatGeometryOverlays.gluingGeometry` 配下の nerve / cocycleRibbon / locusField / forbiddenCages / repairMorphs / atomGlyphs と atomNodes / axisMetricBindings)だけで成立する旨をブロック内に明記する。実データが空に解決される field(viewer `buildAatContext` L1852-1977 が読む `signatureAxes` / `pathPairs` / `loops` / `holonomyReadings` / `spectrumReport` 等の旧 v0 経路。これらは現 v2 runtime artifact に出力されず空配列へ解決される)へ依存して描いてはならない。
- viewer は新しい structural verdict を作らない。`gluing_geometry_projection_v1` が出力する `projectionBoundary`(`ag_measurement.rs:2455` / `:2620`、「does not create a new structural verdict」「It adds no structural verdict, H2 coherence claim, or monodromy verdict」)と、それを assert する test-locked 境界(`tools/archsig/tests/cli.rs:1297-1301`、各 scene の `projectionBoundary` が「does not create a new structural verdict」を含むこと・「must keep visual richness below verdict level」)を全 V が継承する。bloom / 高さ / 厚み / 開閉は projection であって verdict ではない。
- 沈黙(高次 H^n n≥3 / non-abelian stack-gerbe / monodromy transport 不在 / singularity deformation 不在 / Part IX 進化幾何)を描かない。沈黙は赤エラー・残タスク・欠落警告として主役化せず、必要時のみ凡例に typed boundary ラベルを最小限出す。`measured_zero`(lawful)と `unmeasured` を別レーン・別色で分離し、unmeasured を lawful 着色しない。
- analytic reading(period / transfer / laplacian / spectrum / Wasserstein / NSdepth 値)は structural verdict と別色レーンに保ち取り違えさせない。proxy / modelRelative を structural verdict 化しない。π1^AAT を復活させない(holonomy-like 表示は restriction/cover path の exploratory view に留め、`closureGapEncoding` の `nonClaim`「monodromy verdict is not generated」を継承する)。

**受け入れ観点**:
- 各 V 要求ブロックが、自身を駆動する M-id(または「既存 v2 packet データ / 新規データ不要」)を明記し、その依存が満たされない場合の沈黙挙動(空表示=赤エラー化しない)を持つ。
- 駆動 M が未 land の V は viewer 上で無効(その構造を描画しない)であり、land 後に有効化される段階的活性が観察可能である。
- viewer 描画から新しい structural verdict / curvature class / cohomology class が導出されないことを、既存 `projectionBoundary`(`ag_measurement.rs:2455`/`:2620`)と test-locked 境界文言(`tools/archsig/tests/cli.rs:1297-1301`)の維持で確認できる。
- 沈黙領域は幾何で「埋め」られず、blocked/unmeasured は明示的な見え(霧の奥 / すりガラス / 破れた縁)として残る。
- structural verdict 色レーンと analytic_reading 色レーンが分離され、proxy/modelRelative が structural verdict として描かれない。

**依存**: 後続の全 V 要求がこの規律を継承する。本ブロックは可視化フェーズ全体の前提宣言であり、駆動する計測 M 要求を持たない(個別の M land 順に依存しない)。

### V1. PBR基盤刷新 — ACESFilmic + RoomEnvironment IBL + 3点照明 + 接地影 + Fog(新データ不要)

**意図**: viewer ノート T1-1。現 `createRenderer()`(L1001-1018)は素の `WebGLRenderer`(L1014)を返すだけで toneMapping / 環境マップ / shadowMap / fog がゼロ件(grep で確認)、`MeshStandardMaterial`(15箇所)が事実上 Lambert に退化している。レンダリングパイプラインの欠落を埋め、atom 球と幾何が環境反射とソフトな接地影で床に立つ「器」を premium に底上げする。

**駆動計測 M-id**: なし(新規データ不要)。本要求は既存 `atomNodes` と全 `aatGeometryOverlays.gluingGeometry` の見えを底上げするだけで、packet の構造を新たに描かない。したがって駆動 M を持たず、V0 規律の「新規データ不要」枠で成立する。器の刷新であって意味は駆動しない(viewer ノート問い候補 A:見栄え優先)ことをブロックに明記し、「形が意味を駆動する」核は V2 以降が担う。

**見える像**: atom 球と幾何が `RoomEnvironment` IBL の環境反射と `ShadowMaterial` のソフト接地影を得て床に立つ。ハイライトが白飛びせず ACESFilmic のフィルミック階調になる。距離 Fog で camera far の奥行きが残る。CSS の `filter: saturate/contrast`(L124)と走査線オーバーレイ(L66-82)による2D偽装に依存しない本物の3D表現になる。

**Three.js 方針**: `createRenderer()` の WebGL/WebGPU 両経路に `toneMapping=THREE.ACESFilmicToneMapping`・`toneMappingExposure≈1.05` を設定。WebGPU 経路に `setPixelRatio(Math.min(dpr,2))` を追加し `resize()`(L1024)で再適用。`PMREMGenerator.fromScene(new RoomEnvironment())`(`three/addons` 経由)を `scene.environment` に設定(データURI HDRI 不要)。L951-954 の2灯を key(`DirectionalLight` castShadow / `PCFSoftShadowMap`)+ fill(`HemisphereLight`)+ rim の3灯に拡張。y≈-24 の不可視床(`ShadowMaterial`)で contact shadow を受ける。`scene.fog=new THREE.Fog(0x0d1015, 600, 2600)`。

**境界**: 新規 structural verdict を作らず V0 の projectionBoundary(`ag_measurement.rs:2455`/`:2620`、test-lock `tools/archsig/tests/cli.rs:1297-1301`)を維持。照明・反射・影・fog は表現品質のみで、量・verdict・色レーンの意味づけを変えない。fog 色は既存 background と一致させ measured/unmeasured の色分離(V3)を侵さない。

**受け入れ観点**:
- `createRenderer()` 出力の `toneMapping` が `ACESFilmicToneMapping` に設定され、`toneMappingExposure` が約 1.05 である(grep でゼロ件だった状態の解消)。
- `scene.environment` が `RoomEnvironment` の PMREM で設定され、`MeshStandardMaterial` の metalness/roughness が反射に寄与する。
- key/fill/rim の3灯構成が存在し、`castShadow`/`receiveShadow` が有効で y≈-24 の `ShadowMaterial` 床に接地影が落ちる。
- `scene.fog` が設定され camera far までの奥行きフォグが描かれる。WebGPU 経路で `setPixelRatio(min(dpr,2))` が `resize()` でも再適用される。
- 新規 Rust データを一切消費せず、no-build 単一 HTML(importmap 経由 `three/addons/`)が維持される。新しい structural verdict が増えない(`tools/archsig/tests/cli.rs:1297-1301` 維持)。

**依存**: V0(フェーズ規律)。V2(selective bloom)・V3(fog/DOF による沈黙後退)・V4(ヴィネット)の前提インフラ(器)を提供する。

### V2. Selective Bloom — 計測済み H^1 証拠のみを発光させる

**意図**: viewer ノート T1-2。現状 `emissive` は4箇所(L1521/1640/1743/1751)あるが bloom 不在で「光って見えない」。暗いシーンで計測済み H^1 証拠だけが本物の光のにじみを伴い、lawful/measured-zero は落ち着いた反射体、unmeasured は光らず沈黙する。H^1 一次 verdict 軸(headline conclusion code `MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` / `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE`, `ag_measurement.rs:1385-1395`)を視覚的中心に据える。

**駆動計測 M-id**: 既存 v2 packet データで成立(新規データ不要)。発光対象は既存 `cocycleRibbon.closureGapEncoding.visible`(Rust 側 `class_nonzero && !nonzero_edges.is_empty()`, `ag_measurement.rs:2635`)/ `nerve.triangles[].sharedAtomRefs` / `forbiddenCages` / `repairMorphs`。これら計測済み証拠が packet に無いシーンでは発光対象が存在せず、bloom は何も光らせない(=計測なき発光の捏造をしない)。lawful/unmeasured は発光対象に含めない。

**見える像**: `closureGapEncoding.visible=true` の cocycle seam・nerve の sharedAtom マーカー・obstruction cage・repair marker だけが光のにじみを伴う。headline H^1(seam/loop)が最強トーン、`forbiddenCages`(H^0寄り)/ `repairMorphs`(candidate)は弱トーン。lawful/measured-zero は反射体のまま、unmeasured は沈黙する。

**Three.js 方針**: `three/addons/postprocessing/` から `EffectComposer` / `UnrealBloomPass` / `OutputPass`。`animate()`(L1038)の `renderer.render` を composer に置換。bloom layer 方式(発光対象に `obj.layers.enable(1)`、darken→bloomComposer→合成)。`strength≈0.7` と控えめに。headline と candidate でトーンを分け、可能なら強度を `aggregateReadings.HolMass` / `curvatureValue` で連続変調し「二値発光」から「量の発光」へ。

**境界**: 発光は計測済み証拠への projection であって verdict ではない(V0 維持、projectionBoundary `ag_measurement.rs:2455`/`:2620`、test-lock `tools/archsig/tests/cli.rs:1297-1301`)。`forbiddenCages`/`repairMorphs` の弱トーンは headline H^1 と混同させない。発光の連続変調は packet 実量(HolMass/curvatureValue)に接地し、無ければ離散トーンに留め捏造しない。lawful/unmeasured を発光させない(沈黙と肯定的結論の地を保つ)。

**受け入れ観点**:
- bloom が `EffectComposer`+`UnrealBloomPass`+`OutputPass` で実装され、`animate()` の描画が composer 経由になる。
- bloom layer に登録されるのは `closureGapEncoding.visible=true` の seam・`sharedAtomRefs` を持つ nerve マーカー・`forbiddenCages`・`repairMorphs` のみで、lawful/measured-zero/unmeasured は登録されない。
- headline H^1(seam/loop)が最強トーン、forbiddenCages/repairMorphs が弱トーンで、トーン分離が観察できる。
- 計測済み H^1 証拠が無いシーン(`closureGapEncoding.visible=false` 等)では発光対象がゼロで、bloom が新しい構造を捏造しない。
- 新規 Rust データを消費せず、新しい structural verdict を生成しない(`tools/archsig/tests/cli.rs:1297-1301` 維持)。

**依存**: V0(フェーズ規律)、V1(PBR基盤=暗いシーンと composer パイプラインの前提)。V3(measured 専用 emissive の予約)と整合する。

### V3. 沈黙の描画 — measured 手前 / unmeasured 霧の奥 + H^2 三角面すりガラス(赤エラー化撤廃)

**意図**: viewer ノート T1-3 + T1-4。ウィトゲンシュタイン的境界(語り得る/語り得ない)を被写界深度として実装し、沈黙を「失敗の赤」でなく「遠くて見えない霧の奥」「verdict を載せないすりガラス」として後退させる。現状コードが沈黙を `0xff6b6b` 赤 wireframe で表示している境界違反(blockedRegions L1687 / cocycle gap 経路 L1640)を撤廃する。

**駆動計測 M-id**: 既存 v2 packet データで成立(新規データ不要)。深度・かすれは per-object status 由来 — `locusField.fieldRows[].status` / `nerve.triangles[].coherenceClaim`(現状 `not_visualized`, `ag_measurement.rs:5929`)/ `cocycleRibbon.closureGapEncoding.visible` / `h2CoherenceVisualized=false`(`ag_measurement.rs:5940`)。H^2 coherence verdict は計測されていない(沈黙)ため、H^2 三角面は存在を描くが coherence の開閉・色・verdict を一切載せない(将来 H^2 coherence を land させる計測 M が land するまで coherence を描けば捏造)。

**見える像**: 焦点面に measured 幾何が鮮鋭・接地影付きで立つ。`coherenceClaim=not_visualized` の三角面・unmeasured 域は奥の depth 帯へ配置され指数霧に溶け DOF でかすむ。nerve 三角面は半透明・低彩度・微細ノイズの「すりガラス」になり、輪郭は破線、hover でも verdict バッジは付かず「H^2 coherence: silence by design(未測定)」の控えめなツールチップのみ。沈黙が赤エラーでなく後退として見える。

**Three.js 方針**: `scene.fog=FogExp2(0x0d1015, …)` を既存 background と一致(V1 の Fog と協調)。`EffectComposer`+`BokehPass`、focus を `controls.target` 追従。depth は per-object status からカメラ視線方向への射影でバイアス(world-z 単純加算でなく)。H^2 三角面は現 nerve material(opacity 0.34)を専用 silence material(低彩度グレー、opacity≈0.12、ハッチ `CanvasTexture` の alphaMap、`depthWrite=false`)へ置換。現状の emissive マーカー+shared-atom ラベル(L1516-1532)と solid/bright outline(L1564-1568)を減光・除去し、発光は measured 専用(V2)に予約。

**境界**: 現状の `blockedRegions` 赤 wireframe(`0xff6b6b` L1687)と cocycle gap の赤エラー化(L1640 経路)を撤廃する。H^2 三角面は存在のみ描き coherence verdict / 色を載せず `h2CoherenceVisualized=false`(`ag_measurement.rs:5940`)を厳守(H^2 coherence 計測 M が land する前は coherence を描かない)。沈黙を残タスク・欠落警告として主役化しない。measured_zero の薄色を霧の奥の silence と混同させない(深度の連続量で分離)。projectionBoundary(`ag_measurement.rs:2455`/`:2620`、test-lock `tools/archsig/tests/cli.rs:1297-1301`)を維持。

**受け入れ観点**:
- `blockedRegions` の `0xff6b6b` 赤 wireframe 表示(L1687)と cocycle gap の赤エラー化が撤廃され、沈黙が赤で描かれない。
- `FogExp2` と `BokehPass` で measured(focus 面・鮮鋭)と unmeasured(霧の奥・かすみ)が depth 連続量で分離され、深度バイアスが per-object status(`locusField.status` / `coherenceClaim` / `closureGapEncoding.visible`)由来である。
- nerve 三角面が silence material(低彩度グレー、opacity≈0.12、ハッチ alphaMap、`depthWrite=false`、破線輪郭)で描かれ、emissive/bright outline が除去され発光が measured 専用に予約される。
- H^2 三角面の hover でも verdict バッジが付かず、`h2CoherenceVisualized=false`(`ag_measurement.rs:5940`)が維持され coherence の開閉/色を載せない(H^2 coherence 計測 M 未 land 時)。
- BokehPass の focus が `controls.target` を追従し、視点移動で焦点面=measured が保たれる。

**依存**: V0(フェーズ規律)、V1(Fog/postprocess インフラ)、V2(measured 専用発光の予約と整合)。将来 H^2 coherence 計測 M が land した時に後続 viewer 要求が三角面へ verdict を載せる前段として、本要求は「存在を描くが沈黙を保つ」状態を固定する。

### V4. ラベル非散乱と空間文脈 — 共有アトラス・距離フェード・衝突回避 + 3D基準グリッド・座標プレート・ヴィネット・カメラトゥイーン

**意図**: viewer ノート T1-5 + T1-6。(1) ラベルが重ならず近いものだけ鮮明・遠いものは霧と同調してフェードし、top insight だけ常時表示される(現 `createTextSprite` L1576 は毎回 512x128 CanvasTexture を新規生成し散乱)。(2) 床の基準グリッド・座標プレート・ヴィネット・カメラトゥイーンで空間文脈を与え、view mode 切替を瞬間消去でなく連続遷移にする。ラベルは reading への索引であって verdict ではない。

**駆動計測 M-id**: 既存 v2 packet データで成立(新規データ不要)。ラベルは `atomNodes[].labels` / `priorityScore`(v2 実在、top atom=100/その他=10, `ag_measurement.rs:6365`)。H^1 top insight は `cocycleRibbon.holonomyLikeGapMarker`(実出力あり、`ag_measurement.rs:2634`)経由に限定し、`nonzeroHolonomyLoops[].loopId`(v2 未投影=grep ゼロ件)や `spectrumReport` ラベル(v2 未投影)に依存しない。空間文脈は `axisMapping` / `axisMetricBindings`(`ag_measurement.rs:2447`)/ `nonConclusions` / `distance_boundary`(v2 実在)。grid・プレートは hash 主導の擬似座標を権威付けせず、将来の実 metric 主係数化へ差し替える前提で設計する。

**見える像**: ラベルが重ならず、近距離は高コントラスト鮮明、遠距離は霧色でフェード。`priorityScore=100` の top insight のみ常時表示。measured は高コントラスト、unmeasured は霧色で控えめ。床に淡い発光グリッドと軸ラベル付き座標プレート。view mode 切替がカメラトゥイーン+crossfade で連続的に。四隅は控えめなヴィネットで中心の肯定的結論へ視線が集まる。HUD に「座標は視覚投影であり意味距離・因果・等価ではない」を明記。

**Three.js 方針**: `createTextSprite`(L1576)を共有アトラス方式へ(毎回生成を廃止)。距離フェードは `vector.project(camera)` の簡易グリッド占有判定で衝突を間引き、`priorityScore` 順で優先。空間文脈は自作グリッド(`LineSegments`+fog で遠方フェード)を床に。view mode 遷移は `renderScene` で全消去前にカメラ位置を保持し、自作 lerp で `camera.position` と `controls.target` を新シーンの bounding sphere へトゥイーン。ヴィネットは OutputPass 後の薄い `ShaderPass`。

**境界**: ラベル・グリッド・プレートは projection であって verdict でない(V0 維持、projectionBoundary `ag_measurement.rs:2455`/`:2620`、test-lock `tools/archsig/tests/cli.rs:1297-1301`)。`priorityScore` は packet 由来の表示優先度であり structural 順位ではない。grid 線間隔・目盛が hash 主導の `sceneAxisPosition` 軸スケールに整合する事実を踏まえ、grid が擬似座標を権威付けしない(将来の実 metric 差し替えを前提に設計)。HUD の座標非主張注記を必須化し、軸が意味距離・因果・等価でないことを明示。unmeasured ラベルを霧色で控えめにし lawful と混同させない。

**受け入れ観点**:
- ラベルが共有アトラス方式で描かれ(毎回 CanvasTexture 新規生成を廃止)、距離フェード+衝突回避により重ならず、`priorityScore` 順で間引きされ top insight が常時表示される。
- H^1 top insight ラベルが `cocycleRibbon.holonomyLikeGapMarker` 経由に限定され、v2 未投影の `nonzeroHolonomyLoops`/`spectrumReport` に依存しない。
- 床に `LineSegments` の基準グリッドと軸ラベル付き座標プレートが描かれ、fog で遠方フェードし、HUD に「座標は視覚投影であり意味距離・因果・等価ではない」注記が表示される。
- view mode 切替が瞬間消去でなく `camera.position`/`controls.target` の lerp トゥイーン+crossfade で連続遷移する。
- ヴィネットが OutputPass 後の `ShaderPass` で実装され、中心の肯定的結論へ視線を誘導する。
- grid/プレートが新しい structural verdict を作らず、擬似座標を権威付けしない(`tools/archsig/tests/cli.rs:1297-1301` 維持、実 metric 差し替え前提の設計)。

**依存**: V0(フェーズ規律)、V1(fog/postprocess インフラ)。V4 の demote-hash 注記は後続の axisMetricBindings 実 metric 主係数化で本格化する前段であり、本要求では grid が擬似座標を権威付けしない設計に留める。

### V5. コホモロジー次数の鉛直三層(H^0 地表 / H^1 中層リボン / H^2 沈黙のガラス天井)

シーンを degree で物理的に三層へ分割し、view mode を変えても「同じスパイラルの再配色」に見える hash 主導レイアウトを degree 駆動の鉛直階層へ置き換える(T2-1、本ノート最有力・高接地)。最下層 y≈-20 が H^0(context 球 / `atomGlyphs`、source_backed が静かに発光)、中層 y≈0〜30 が H^1(`cocycleRibbon` の supportEdge が頂点パッチ間を結ぶ捻れリボン、`value=1` の mismatch 辺だけ太く明るく、閉路があれば closureGap が「閉じない帯」=視覚の主役)、最上層 y≈55 が H^2(nerve triple-overlap 三角面を極薄半透明ガラスとして頭上に浮かべる。色も verdict も載らない意図的な灰色の沈黙面)。系12.3 `H^1(U,k)=b_1(N(U))` と part_4 §4 意味4.2 の degree 階層に接地し、headline は `MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` / `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE`。

**駆動する計測 M-id**: H^0/H^1 層は既存 v2 artifact(`nerve.vertices/edges/triangles`、`cocycleRibbon.supportEdges[].value`、`closureGapEncoding`、`atomGlyphs[].semanticAnchor`)で**新規データ不要**。H^2 天井層は **M5(`ag.coherence-obstruction@1` H^2 triple-overlap coherence)** が land する**前**は verdict を一切載せず灰色ガラスの「存在のみ」に留める。M5 未 land の段階で三角面を「開いている/閉じている」と描けば coherence を測っていないのに coherence failure を主張する捏造になる(計測ノート可視化接続表の H^2 行)。M5 land 後に初めて V11(degree スクラブ)経由で verdict 着色へ繋ぐ。

**Three.js 方針**: `renderNerveGeometry` / `renderCocycleRibbon` を新規 `cohomologyDegreeLayer(degree)` で y バンドへ強制配置し、`sceneAxisPosition`(L1444-1465)の hash 由来 y を degree 固定 y で上書きする(x/z 平面の hash は本要求のスコープ外、demote-hash は V9)。中層 tube radius=`lerp(0.4, 2.2, edge.value)`、selective bloom(V2)は H^1 リボン emissive のみ。天井は `MeshPhysicalMaterial({transmission:0.9, opacity:0.12, color:0x6b7280, depthWrite:false})` の「沈黙のガラス」。projectionBoundary(no new structural verdict)維持。

**受け入れ観点**:
- degree が鉛直階層を駆動する: H^0/H^1/H^2 が固定 y バンド(地表/中層/天井)に分離し、`sceneAxisPosition` の hash 由来 y が degree 固定 y で上書きされている(同 degree の要素が hash で y 方向に散らばらない)。
- 中層 H^1 リボンの太さが `cocycleRibbon.supportEdges[].value` で連続変調され、`value=1` の mismatch 辺が太く明るく、`closureGapEncoding.visible` のループが「閉じない帯」として主役化する。
- 凡例に `edge.value` が `len(supportAtomRefs)%2` の離散 mismatch パリティ marker であり連続コホモロジー量ではない旨を明記し、太さ・bloom を「H^1 強度の連続スケール」と誤読させない(T2-1 接地強化(1))。
- H^2 天井ガラスは M5 land 前は verdict も色も載せず、hover/選択でも verdict テキストを出さず `sharedAtomRefs` 数の事実提示に留める(T2-1 接地強化(2))。
- selective bloom が H^1 リボンの emissive のみに当たり、H^2 天井・H^0 地表は発光しない。

**依存**: V0(フェーズ規律)、V2(selective bloom = H^1 リボンのみ発光)、M5(H^2 天井の verdict 着色は M5 land 後)。後続 V9(demote-hash で x/z を実 metric へ)、V11(degree スクラブ)が本層構造を共有する。

### V6. 実測曲率場の heightmap 曲面(signedCurvature が膜を変形し lawful locus が盆地になる)

現 `locusField` の「個別シリンダー柱」を一枚の弾性膜に置換し、audit 中核ギャップ(曲率値が形として読めない)を直接解消する(T2-2、本命)。`signedCurvature>0` の cell は山、`<0` は谷、`measuredZeroRegion` は膜が y=0 に接地する平らな盆地(=lawful locus、零点集合 `Flat_U(X)=V(I_Ob)`)、`blockedRegion` は補間せず破れた縁として残す。色は `harmonicMass` のヒートマップ、`distanceToFlatness` が谷への落差。near-flat と lawful を段差で区別する(part_7 §7.2 obstruction valuation `κ_U(X)`、part_3 §6-7、原則10.3 near-flat≠lawful)。現在の architecture を一つの光る点で示し、盆地(lawful)上か斜面(curvature>0)上かが一目で分かる。

**駆動する計測 M-id**: 膜変形の主係数 `locusField.fieldRows[].{signedCurvature,harmonicMass,distanceToFlatness,height,status}` / `measuredZeroRegions` / `blockedRegions` は既存 v2 artifact に runtime 実在(既存の sheaf-laplacian proxy `graph-laplacian-hodge-proxy@1` が laplacian fixture を analyze で materialize 済み、`signedCurvature` `[1.0,-1.0]` 等)で**新規データ不要**。ただし `signedCurvature` / `harmonicMass` / `distanceToFlatness` は AgAnalyticReadingV1 の **proxy/analytic reading であって structural verdict ではない**(本理論 anchor は graph-laplacian-hodge-proxy)。膜の高さ・色は計測値を読みやすく投影する従であり、膜から新たな structural verdict を導出しない(projectionBoundary = no new structural verdict 維持、proxy を verdict 化しない)。**M14(spectral gap overlay、P2 analytic)** は谷の浅深を analytic レーンで副次的に補強する別駆動で、M14 が land する**前**は spectral gap で谷深を着色しない(`gap≈0` を `measured_zero` の teal に着色すると near-flat≠lawful を侵犯する、計測ノート可視化接続表)。gap 着色は M14 land 後、analytic 固定色レーン(V18)でのみ行う。

**Three.js 方針**: `renderLocusField`(L1648)を全面改修。fieldRows を x ソートし `BufferGeometry` 格子の頂点 y を `signedCurvature` で IDW 補間、`computeVertexNormals()` で連続法線。`vertexColors` で `harmonicMass` を `Lut('cooltowarm')` 着色(analytic_reading 色レーン)、SSAO で谷の窪みを深める。`measuredZeroRegion` は y クランプ+弱 emissive、`blockedRegion` は三角形を間引いて穴+破線縁にし、現状の沈黙赤エラー化(`0xff6b6b`)を撤廃する(V3 と協調)。

**受け入れ観点**:
- `signedCurvature` が膜頂点 y を駆動する: `>0`=山 / `<0`=谷 / `measuredZeroRegion`=y≈0 接地の平らな盆地、として膜が変形し、`harmonicMass` が `cooltowarm` ヒートマップで着色される。
- 膜の高さ・色が proxy/analytic reading の projection であり structural verdict を新規生成しない(projectionBoundary 維持)。膜変形を「証明された lawful 度の連続スケール」と誤読させない non-claim を凡例に明記する。
- 測定セル(`signedCurvature` を持つ fieldRow)を離散頂点として明示し、IDW 補間面は「measured 点を結ぶ window であり点間は測定でない」と non-claim 明記する(T2-2 接地強化(A)、補間が形を捏造して見えるのを防ぐ)。
- `blockedRegion` を補間で滑らかに埋めず三角形間引きの穴+破線縁として残し、現状の `0xff6b6b` 赤 wireframe による沈黙赤エラー化を撤廃する(near-flat/flat/blocked を取り違えさせない)。
- `measuredZeroRegions` は verdict 由来で x 座標を持たないため、盆地は `signedCurvature≈0` のセル位置から導き「zeroRegion の x 範囲で y=0 接地」を仮定しない(T2-2 接地強化(B))。
- M14 land 前は spectral gap で谷深を着色せず、`gap≈0` を `measured_zero` teal に着色しない(near-flat≠lawful、原則8.4)。

**依存**: V0(フェーズ規律)、V3(沈黙の描画=blocked を赤エラー化しない)、M14(谷深の spectral gap 着色は M14 land 後・V18 の analytic レーンで)。

### V7. Čech 単体複体の b_1 を光る閉路として描く(系12.3 H^1≅b_1)

nerve を本物の単体複体として立てる(T2-3、忠実性最高・系12.3 に逐語接地)。context = 球頂点(半径∝`atomRefs` 数)、pairwise overlap = 辺チューブ(太さ∝`supportAtomRefs` 数)、triple overlap = `sharedAtomRefs` を持つ塗り三角面(coherence 色は付けない=沈黙)。核心は b_1: nerve グラフの独立サイクルをグラフ理論で抽出し、その閉路を1本の光るループで縁取る(これが `H^1(U,k)≅b_1` の幾何的本体)。`value=1` の mismatch 辺が閉路を closureGap として「閉じなくさせている」箇所を強調する(part_4 §3 §12、系12.3 L1415-1432、H^1 一次 verdict 軸)。

**駆動する計測 M-id**: nerve 構造 `nerve.vertices[].atomRefs` / `edges[].supportAtomRefs/.value` / `triangles[].sharedAtomRefs` は既存 v2 artifact に実在(base archmap_v2 fixture で triangle 確認済)。b_1 は viewer 側の純粋な位相計算(spanning tree + 基本サイクル復元、union-find + BFS、80辺上限で軽量)で導出でき、入力 contract を拡張しない。**M7(`ag.cech-obstruction@1` 拡張 Topological Debt Capacity、`capacityLowerBound`/`b1NerveReading`/`eulerCharacteristic`)** が land すると、viewer 側 graph b_1 を Rust 側の nerve 複体 b_1 reading と整合させ、capacity(潜在的余地)と実測 class(点灯)の分離(原則4.4)を packet 由来の値で駆動できる。M7 land 前は viewer 側 graph cycle basis のみで描き、ループ発光を「H^1 verdict として読ませない」境界を厳守する(graph cycle ≠ H^1 verdict)。

**Three.js 方針**: 新規 `renderNerveSimplicialComplex`。b_1 抽出は spanning tree + non-tree edge ごとの基本サイクル復元、各サイクルを `CatmullRomCurve3`(閉ループ)→`TubeGeometry` の発光リング、selective bloom(V2)を発光リングのみに。filled/unfilled は triangle boundary で商を取った 2-複体の b_1 として実装。projectionBoundary(no new structural verdict)維持。

**受け入れ観点**:
- nerve が単体複体として立つ: 頂点半径が `atomRefs` 数、辺チューブ太さが `supportAtomRefs` 数、triple overlap が `sharedAtomRefs` を持つ塗り三角面(coherence 色なし)で描かれる。
- 独立サイクル(b_1 本)が光る閉ループとして抽出・縁取りされ、selective bloom が発光リングのみに当たる。
- `value=1` の mismatch 辺が閉路を closureGap として「閉じなくさせている」箇所が強調される。
- triple overlap 三角面に coherence 色・verdict を載せない(H^2 沈黙)。M7 land 前は viewer 側 graph cycle basis のみで描き、ループ発光は新規 structural verdict を生成しない(projectionBoundary 維持)。
- viewer 側 b_1 は「定数係数 k・標準 restriction 下の N(U) の reading」であり MeasurementProfile 相対の headline H^1 verdict とは別 reading である旨を loop 近傍に minimal boundary として明記する(T2-3 接地強化[A]、part_8 §3.3、原則2.5/4.4。graph cycle≠H^1 verdict)。
- M7 land 後は capacity(潜在的余地)を全ループ点灯でなく実測 class が乗るループだけ点灯させて分離し、原則4.4(具体 class ≠ nonzero group)を侵さない。

**依存**: V0(フェーズ規律)、V2(selective bloom = 発光リングのみ)、M7(capacity reading land 後に capacity/実測 class 分離)。V5(三層の中層 H^1)・V13(assembly snap の b_1 発光)と b_1 抽出ロジックを共有する。

### V8. support repair morph(supportVariables を実座標軸に、cage から lawful locus への連続変形)

Repair を obstruction cage から lawful locus への support repair morph として描く(T4-2)。`forbiddenCages[].supportVariables`(例 `x_checkout/x_inventory/x_payment`)を実座標軸として張った部分空間に各 cage が壊れた線の simplex として浮き、repairMorph 再生で `fromAtomRefs` の cage が `toCandidate` へ向かって連続変形し、支持変数から外れた軸の cage が緑の lawful 領域に着地する。「どの変数を落とせば lawful か」が空間位置として読める。常時 nonClaim「not automatic repair / lower-bound inspection aid」。square-free 障害イデアルの minimal forbidden support を coordinate subspace arrangement の cage として(Stanley-Reisner regime、定理5.6C / part_3 L697-724、part_5 L712 support repair)。

**駆動する計測 M-id**: cage と morph の駆動データ `forbiddenCages[].{supportVariables,atomRefs,lineRole}` / `repairMorphs[].{fromAtomRefs,fromCageRefs,toCandidateRef,samplePhase,supportVariables,nonClaim}` は既存 v2 artifact に実在(square_free fixture で和集合ちょうど3変数を確認)で**新規 Rust 変更不要**。**M4(`ag.law-conflict-tor@1` を真の monomial free resolution へ昇格、multidegree=lcm(x_S,x_T)=witness support 合成)** が land すると、cage の simplex を各 Tor_1 class 単位へ分離し、複数 conflict を別 simplex として描き分けられる。M4 land 前は square-free forbiddenCages の `supportVariables` だけで描き、class 分解は行わない(measure していない class 数を捏造しない)。

**Three.js 方針**: `renderRepairMorphs`(L1723)と `renderForbiddenCages`(L1696)を統合。cage は `supportVariables.length` 次元を3軸へ写像(2変数→辺、3変数→三角形 simplex、4変数以上は hash 退行を禁じる決定論写像)。morph は現 lerp を頂点モーフへ拡張。緑の lawful 着地面=`Flat_U` を結論の視覚中心に据える。projectionBoundary(no new structural verdict)維持。

**受け入れ観点**:
- `forbiddenCages[].supportVariables` が実座標軸を張り、各 cage が `supportVariables.length` に応じた simplex(2変数→辺 / 3変数→三角形)として配置され、hash 由来座標で配置されない。
- repairMorph 再生で `fromAtomRefs` の cage が `toCandidateRef` へ連続変形し、緑の lawful 着地面(`Flat_U`)が結論の視覚中心に保たれる。
- 「cobordism」「mass-preserving / 質量を保ったまま」を用いず、常時 nonClaim「support repair: 支持変数を落とす連続変形 / not automatic repair / lower-bound inspection aid」を併記する(T4-2 必須補強(1)、理論に存在せず part_5 L43 の非保存と矛盾する捏造を排除)。
- supportVariables 和集合が4変数以上のとき決定論写像で3軸へ畳み hash 退行しない(T4-2 必須補強(3))。
- M4 land 前は cage を Tor_1 class 単位へ分解せず、square-free forbiddenCages の `supportVariables` だけで描く(measure していない class 数を捏造しない)。

**依存**: V0(フェーズ規律)、M4(multidegree=lcm の Taylor resolution land 後に class 分解)。V15(二 lawful loci の交差と Tor residue)と repair の質量移送語彙の境界を共有する(本要求は mass-preserving 語を使わない)。

### V9. view mode 間レイアウト morph と demote-hash

view mode 切替を「全 clear→ゴールデン角スパイラル再構築」から「同じ atom 群が次レイアウトへ連続的に流れる morph」へ変える。これは design note(viewer)T3-1 の audit 最重要指摘への正面回答であり、独立して demote-hash(`axisMetricBindings` の実 metric を主係数、hash jitter を従)を切り出すことで、morph が「同じ atom を別 reading で見る」を意味として駆動するようにする。

駆動計測 M-id: **本要求は新規計測を駆動源に持たない viewer 内 reform であり、駆動 M を名指さないこと自体が正しい**(M依存なし=既存 v2 artifact の再配置のみ)。全 view の `nodePosition` 系を `axisMetricBindings`(measurement packet の axisMapping を実 metric に解決した binding)へ接地し、`atomNodes` / `axisMetricBindings` / 各 view nodePosition(いずれも v2 実在)だけを使う。新規 Rust データは不要で、新しい計測軸も verdict も生まない。実 metric が hash を主係数として上書きしていない限り morph は「美しい無意味シャッフル」に堕すため、demote-hash の達成を V9 の前提条件として固定する。計測なき構造を新たに描かない(捏造禁止): morph 軌跡を「点がどう動いたか」という verdict として読ませてはならない(non-claim)。

見える像と Three.js 方針: `renderScene` の全 clear→再構築(L2899)を改め、atom InstancedMesh(L1146)のインスタンス位置を破棄せず次 view の `nodePosition` へ `easeInOutCubic`(約900ms, Clock 駆動)で補間。geometry overlay は morph 中 crossfade。カメラは scene 別推奨位置へ lerp + lookAt slerp。projectionBoundary(no new structural verdict)維持。

受け入れ観点(testable):
- view mode 切替時に atom InstancedMesh のインスタンスが破棄・再生成されず、開始位置から目標位置へ連続補間される(軌跡が描かれる)ことを test が固定する。
- demote-hash が独立 AC として満たされる: 各 view の x/z 平面位置の主係数が `axisMetricBindings` の実 metric であり、hash jitter は従の微小項に降格している(hashText が支配しない)ことを test が確認する。
- 実 metric を持たない軸は morph 後も決定論的(hash 由来のランダム再配置ではない)で、同一入力で同一レイアウトに収束する。
- morph 中の geometry overlay は crossfade し、瞬間消去のカット編集が発生しない。
- HUD/legend に「座標と軌跡は視覚 projection であり意味距離・因果・等価・verdict ではない」non-claim が表示される。
- 新 structural verdict が増えていない(projectionBoundary 維持)ことを test が固定する。

依存: V0(Viewer フェーズ定義/projectionBoundary 維持)。後続の V10/V11(時間軸操作)が morph 済みレイアウトを前提として読めるため、V9 が demote-hash の土台を提供する。

### V10. Holonomy traversal — 閉じなさをフレーム周回で見せる

cocycle ribbon の閉路に沿ってフレーム三面体を周回させ、一巡して戻ったとき初期姿勢に重ならない「閉じなさ」をアニメで示す。design note(viewer)T3-2。H^1 一次 verdict 軸(`MEASURED/NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE`)の幾何的本体を時間で読ませる。

駆動計測 M-id: 既存 `cocycleRibbon.closureGapEncoding.visible`(core 計測 `ag.cech-obstruction@1` の既存出力。Rust `class_nonzero && !nonzero_edges.is_empty()`)を駆動源として名指す。この closureGap が measurement packet に land している閉路だけにフレーム周回のズレを発生させ、closureGap=false(measured_zero)の閉路はフレームがピタリ重なって静止する——**計測なき閉路にズレを描けば捏造になる**この関係を test で固定する(計測=主、可視化=従)。ズレ角の精密駆動には任意で `holonomyTwist` スカラー(`BoundaryHolonomyAxisResidualV0` の v0→v2 配線、または `aggregateReadings.HolMass` を edge へ写す)を追加できるが、これは**既測 residual を viewer へ運ぶ projection であって新 structural verdict ではない**(projectionBoundary 維持)。無い場合は edge.value(parity)由来の離散 twist に留め「unmeasured magnitude」注記を付す。π1^AAT を復活させない(holonomy-like 表示は restriction/cover path の exploratory view に限定)。

見える像と Three.js 方針: 既存 `renderCocycleRibbon` の `CatmullRomCurve3` curve を保持し、`animate()`(L1038)内で `getPointAt(t)`/`getTangentAt(t)` でフレーム三面体を周回。t が 1 を跨ぐ瞬間に始点ゴーストを残置し初期姿勢との差を見せる。closureGap ループの末端でギャップマーカーが明滅。常時「restriction/cover path の探索ビュー」ラベル。

受け入れ観点(testable):
- `closureGapEncoding.visible=true` の閉路でのみフレームが一巡後に初期姿勢からズレ、`visible=false` の閉路ではフレームが重なって静止することを test が固定する。
- `holonomyTwist` スカラーが packet に無い場合、ズレ角は edge.value の parity 由来の離散値に留まり、「twist 強度は unmeasured magnitude(parity 由来)」注記が表示される。`holonomyTwist` が land している場合も新 structural verdict 件数が増えない(projectionBoundary 維持)ことを test が確認する。
- holonomy-like 表示が exploratory view ラベルを伴い、monodromy/π1 verdict を一切提示しない。
- フレーム周回・ゴースト残置はアニメ projection であって closureGap verdict 以上の主張を生成しない(projectionBoundary 維持)。
- closureGap が無い packet では本ビューが沈黙し、赤エラー化しない。

依存: V0、V9(morph 済みレイアウト上で ribbon が安定して読めること)。closureGap データ源は core 計測 `ag.cech-obstruction@1` の既存出力に依存し、land しない間は本ビューは沈黙する。

### V11. cohomology degree スクラブ — H^0/H^1/H^2 層の剥離

縦の degree スライダー(0→1→2)で H^0 地表・H^1 中層リボン・H^2 沈黙ガラスを時間スライスとして剥離する。design note(viewer)T3-3。コホモロジー次数の階層(part_4 §4)を時間操作で読ませ、H^2 は色も verdict も付かない灰色の沈黙のまま立ち上げる。

駆動計測 M-id: H^0 は既存 `atomGlyphs`/`atomNodes`/`locusField.fieldRows`、H^1 は既存 `cocycleRibbon`/`nerve.edges` を駆動源とする。H^2 層の verdict(measured_zero=閉じた膜/measured_nonzero=開いた膜)は **M5(`ag.coherence-obstruction@1`、design note 計測 P1-1、banded abelian F2 限定の H^2 triple-overlap coherence)** が land したときに限り色・開閉を載せる。M5 不在時に triangle の見た目だけで H^2 を「開いている/閉じている」と描くと coherence を計測していないのに failure を主張する捏造になるため(計測=主、可視化=従)、M5 未投影の間は H^2 層を `h2CoherenceVisualized=false` の灰色沈黙ガラス(色なし・verdict なし)に固定する。non-abelian gerbe(M5 の banding violated 域)は計測対象外として沈黙を侵さない。注: `obstructionCircuits` は v2 未出力なので H^0 のデータ源に使わない。

見える像と Three.js 方針: 3 Group(layerH0/H1/H2)に振り分け、slider 値 s∈[0,2] に `smoothstep` 補間で focus 層を主役化、focus 以外は opacity*0.25(focus+context)。H^2 層は `MeshPhysicalMaterial({transmission, opacity≈0.12, color:0x6b7280, depthWrite:false})` の沈黙ガラスで、hover でも「H^2 coherence: silence by design / 未測定」のみ表示。

受け入れ観点(testable):
- スライダー s∈[0,2] で focus 層が連続補間で主役化し、他層が opacity*0.25 で context として残る(隠さない)ことを test が確認する。
- M5(`ag.coherence-obstruction@1`)が packet に投影されている場合に限り、H^2 face が verdict 由来の開閉(measured_nonzero=開いた膜/measured_zero=閉じた膜)を取ることを test が固定する。
- M5 未投影時、H^2 層は灰色・無 verdict のガラスのまま立ち上がり、coherence failure/success を一切主張せず赤エラー化しない。
- H^0 層が `obstructionCircuits` を使わず実在データ(`atomGlyphs`/`atomNodes`/`locusField.fieldRows`)で構成される。
- degree 層分離・剥離は projection であって新 structural verdict を生成しない(projectionBoundary 維持)ことを test が固定する。

依存: V0、V9(層の鉛直配置が hash でなく degree 固定で読めること)、M5(`ag.coherence-obstruction@1` の H^2 coherence 計測。land しない間は沈黙ガラスに留め描き込まない)。

### V12. findings シネマティックツアー — 結論バッジへ着地

`tourState` を活かし、カメラが各 finding ステップの highlightRefs へシネマティックに飛び、対象を中央に据えて focus+context で他を減光し、最終ステップで肯定的結論バッジに寄って締める guided reading を実装する。design note(viewer)T3-4。H^1 一次 verdict を中心とした reading を時間で導く。

駆動計測 M-id: 既存 `tours[].steps[].{sceneId,caption,highlightRefs}`(v2 実在)と headline conclusion code(`NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` 等の既存 verdict code であって新 verdict ではない)を駆動源とする。新規 Rust データ不要・新規計測なし。caption は packet 由来 `step.caption` を逸脱せず、viewer 側で煽り文言や未計測の主張を創作しない(packet 由来逸脱禁止=計測なき主張を描かない)。highlightRefs から world 座標が逆引きできないステップは scene 全景へフォールバックし、沈黙を捏造で埋めない。

見える像と Three.js 方針: 既存 `activeTourState`(L975)/`startTour`(L3062)/`renderTourStep`(L3073)を拡張。highlightRefs から `userData.item` を逆引きして world 座標へ camera/target を lerp トゥイーン、該当幾何がステップでパルス発光、字幕はローワーサード。手動ドラッグで pause、Resume で再開。最終ステップは headline 肯定的結論バッジへ寄る。focus+context の減光に下限を設け、H^2 三角面・blocked 領域を「隠す」のでなく「控えめに残す」。

受け入れ観点(testable):
- Start tour で各ステップの highlightRefs に対応する world 座標へカメラ/ターゲットがトゥイーンし、対象がパルス発光する。
- 字幕が `step.caption` を逐語的に表示し、viewer 側で創作した文言を含まない(packet 由来逸脱禁止)ことを test が固定する。
- 手動ドラッグで pause、Resume で続行でき、最終ステップが既存 headline conclusion code のバッジに着地する(新 verdict code を創作しない)。
- highlightRefs から座標が引けないステップは scene 全景へフォールバックし、空ステップを捏造の発光で埋めない。
- focus+context の減光に下限があり、H^2 三角面・blocked 領域が完全には消えず控えめに残る(沈黙を尊重)。
- ツアーは projection であって新 structural verdict を生成しない(projectionBoundary 維持)。

依存: V0、V9(ツアー先のレイアウトが安定)。V2(selective bloom)は任意の前提であり、land していれば結論バッジ/パルスの発光を計測済み証拠に限定して活用できるが、未 land でもツアーは発光なしで成立し赤エラー化しない(V2 を必須前提にしない)。

### V13. 貼り合わせ assembly snap — seam で snap し損ねる

scene 再生時に nerve の頂点パッチが外側から定位置へ飛来し overlap 辺で吸着して一枚に綴じる。整合する辺は密着し、不整合の辺は微小隙間を残して振動する seam として見せる。design note(viewer)T3-5。descent/gluing(part_2 §9-11)を空間操作として読ませる。

駆動計測 M-id: **M2(`ag.restriction-compatibility@1`、design note 計測 P0-2、restriction-compatibility seam verdict)** を seam の snap/非 snap の駆動源として名指す(これは T3-5 が parity のみで描いていた seam を、land した structural verdict へ正しく接地する補強であり、計測=主の背骨に沿う)。M2 が land している辺で incompatible(局所イデアルが上流へ流れない構造的不整合=`measured_nonzero`)のとき snap し損ねる seam を、compatible(`measured_zero`)のとき密着を描く。**M2 が land していない辺で seam を裂いて見せれば捏造になる**(計測なき構造を描かない)。加えて既存 `nerve.vertices`/`edges` の飛来・吸着レイアウトを使う。**境界注記2点(必須)**: (1) 完成後に発光する b_1 個の閉路は viewer 側 graph cycle basis であって packet の H^1 量ではない——「graph cycle, H^1 verdict ではない」non-claim を発光近傍に併記し、新 structural verdict を生まない(projectionBoundary 維持)。(2) M2 が未投影の間、`edge.value` は `(support_atom_refs.len() % 2)` の parity marker なので seam を「貼り合わない経路」と断じず「value(parity)で色分けした overlap seam」と legend に明示し、parity を verdict と取り違えさせない(proxy/parity を verdict 化しない)。

見える像と Three.js 方針: `renderNerveGeometry`(L1467)の頂点に開始位置(法線方向外側 +120)と目標位置を userData 格納し `easeOutBack` で飛来→snap。M2 incompatible 辺は目標位置に微小隙間+振動を残す。完成後 b_1 個の閉路が一拍発光(graph cycle 注記つき)。

受け入れ観点(testable):
- scene 再生で nerve 頂点パッチが外側から定位置へ飛来し、overlap 辺で吸着する。
- M2(`ag.restriction-compatibility@1`)が投影されている辺で incompatible(`measured_nonzero`)のとき seam が snap し損ねて微小隙間+振動を残し、compatible(`measured_zero`)のとき密着することを test が固定する。
- M2 未投影時、seam は `edge.value` の parity による色分けに留まり「貼り合わない経路」という verdict を主張せず、legend に parity marker である旨が明示される。
- 完成後の b_1 発光近傍に「graph cycle であって H^1 verdict ではない」non-claim が表示される。
- 飛来・snap・b_1 発光は projection であって新 structural verdict を生成しない(projectionBoundary 維持)ことを test が固定する。
- 計測されていない辺で seam を裂いて見せず、沈黙を赤エラー化しない。

依存: V0、V9(nerve レイアウトの安定)、M2(`ag.restriction-compatibility@1` の seam 計測。land しない間は parity seam に留め verdict を主張しない)。V7(Čech b_1 光る閉路)と b_1 抽出ロジックを共有しうる。

### V14. Čech 神経を呼吸する fiber bundle(curvature 駆動 base+fiber、共起 fixture が land するまで gated)

意図: nerve の各 context パッチを base 円盤、その上に立つ section を縦の fiber 柱として描き、`signedCurvature` が柱の高さ・色を駆動し、`closureGapEncoding.visible` の overlap 辺だけが太く発光する dashed seam になる(T2-4)。被覆 × section の積空間そのものを立体化し、平行移動の holonomy ズレを base を渡る3Dパスとして見せる。

駆動計測 M-id と捏造関係: この V は **既存 nerve(`ag.cech-obstruction@1`)+ `locusField.fieldRows[].signedCurvature`(`graph-laplacian-hodge-proxy@1` 由来の analytic reading)** の二系が **同一 packet に共起すること**を前提とする。現行 fixture は排他(laplacian fixture は curvature あり/nerve・seam なし、cech_h1 fixture は nerve・seam あり/curvature なし)で、両者は同じ packet に出力されない。したがって本 V は **共起 fixture(cover を持つ archmap に `graph-laplacian-hodge-proxy@1` reading を同時付与し `nerve.vertices` と `fieldRows[].signedCurvature`/`cellRef` を共存させる新 fixture)が land するまで gated/保留**とする。共起データが無いまま base 上に curvature 駆動 fiber を立てれば、curvature を測っていない nerve に高さを捏造することになる。curvature 未測定の柱に色温度を付けるのも捏造であり、明示沈黙(色温度オフ)で扱う。**`signedCurvature` は proxy analytic reading であって structural verdict ではないので、柱高・色温度を structural verdict に昇格させず、viewer は新規 structural verdict を作らない(`projectionBoundary` の no-structural-verdict を継承)。**

Three.js 方針: `renderNerveGeometry`(L1467)を base+fiber bundle へ拡張。fiber 柱は `InstancedMesh` + `setColorAt`、柱高は `lerp(baseHeight, topHeight, signedCurvature)`。`fieldRows[].cellRef → nerve vertex(contextRef/atomRefs)` を結ぶ写像を viewer 側で定義し、対応が引けない柱は明示沈黙(描かない/色温度オフ)。closureGap seam と `signedCurvature>閾値` の柱のみ selective bloom(V2 bloom layer 共有)。triple-overlap 三角面は V3 の沈黙すりガラス(灰色・無発光・透明)を流用。

受け入れ観点:
- 共起 fixture(cover + `signedCurvature` 同一 packet)が無いとき本 V は描画されず gated 状態(空表示=沈黙、赤エラー化しない)であることをテストで固定する。
- 共起 fixture が land したとき、各 fiber 柱の高さ・色が当該 `cellRef` の `signedCurvature` で決まり、`cellRef→vertex` 写像が引けない柱は色温度オフの明示沈黙になる。
- `closureGapEncoding.visible=true` の overlap 辺だけが太い dashed seam として発光し、`visible=false` の辺・非 H^1 構造は発光しない。
- triple-overlap 三角面は V3 沈黙ガラスのまま verdict も色も載らず(`coherenceClaim='not_visualized'`/`h2CoherenceVisualized=false` を尊重)。
- curvature 未測定時の柱は「curvature の代わり」を示唆せず色温度オフの沈黙で、measured-zero と取り違えない凡例注記がある。
- fiber 柱の高さ・色(`signedCurvature` proxy)は analytic レーンに留まり、`projectionBoundary` の no-structural-verdict を維持して structural verdict 件数が本 V 追加で増えないことをテストで固定する。
- selective bloom は seam と閾値超え柱のみで lawful/unmeasured には当たらない(V2 bloom 規律を継承)。

依存: V0(フェーズ規律: 駆動計測 land 後のみ有効)、V2(selective bloom layer)、V3(沈黙すりガラス/赤エラー化撤廃)。共起 fixture は本 V の land 前提であり、それ自体は計測側 Issue として別に切る。

### V15. 二 lawful loci の交差と非横断 residue(Tor_1≠0 の余剰塊、repair で質量移送)

意図: 二つの法世界(`lawPair: law:checkout / law:inventory`)の lawful locus を交わる2枚の半透明曲面で描き、共有 common ambient を交差線として可視化する。横断的なら交差線は鋭く residue ゼロ、非横断(`measured_nonzero`=Tor_1≠0)のとき交差部に綺麗に消えない余剰の塊(transferred obstruction)が膨らみ、repair で一方の軸を動かすと質量がもう一方の軸へ流れる(T2-5)。高次 Tor は描かず凡例に一行「高次は沈黙」。

駆動計測 M-id と捏造関係: 駆動は **M4(Tor_1 を真の monomial free resolution へ昇格、multidegree=lcm(x_S,x_T)=witness support 合成)** と、その投影として **`ag.law-conflict-tor@1` の `verdict=measured_nonzero` / `computedInvariants.commonAmbient`(ambientRef/atomRef/lawPair/sourceRefs)を `aatGeometryOverlays.lawConflict` へ運ぶ projection(M14系の overlay 配線)**。現状 `commonAmbient/lawPair` は packet にあるが `aatGeometryOverlays` に未投影で、`build_measurement_viewer_data_v1` 周辺 + `attach_gluing_scene_geometry` の law-conflict-tor arm に projection 追加が要る。この projection が land する前に交差 residue 塊を描けば、Tor_1 を測っていないのに非横断 obstruction を主張する捏造になる。**common ambient morphism が無い異 ambient 比較は M4 で `not_computed`(原則9.3)なので、common ambient が解決しない packet では交差面・residue を描かず沈黙する(異 ambient 横断性を捏造しない)。**

Three.js 方針: 新規 scene `law-conflict-tor`(`viewerVisualScenes` に kind=law_conflict が既存・geometry 未配線)と `renderLawConflictIntersection`。lawful locus は緩い `PlaneGeometry` 2枚、common ambient は2平面の解析的交線(`LineGeometry`)。residue 塊の膨らみ・移送フロー量は **packet 実測の離散量(LawConflict class 本数・共有 support 数)に束ね**、連続質量スカラーは捏造しない。質量移送は既存 `updateRepairMorphAnimation` の lerp 機構を流用。`PlaneGeometry` は連続サンプルが packet に無いための近似である旨を non-claim 明示し、膨らみは verdict でなく projection と凡例に書く。viewer は新規 structural verdict を作らず `projectionBoundary` の no-structural-verdict を維持する。

受け入れ観点:
- `aatGeometryOverlays.lawConflict` projection が land する前は scene が空表示=沈黙(赤エラー化しない)で residue 塊を描かないことをテストで固定する。
- common ambient(`commonAmbient.ambientRef`)が解決しない packet では交差面・residue を描かず沈黙し、異 ambient 横断性を主張しない(原則9.3 の `not_computed` を尊重)。
- `verdict=measured_nonzero` のときのみ交差部に residue 塊が膨らみ、`commonAmbient` の `lawPair`/`sourceRefs` が glyph と凡例に source 付きで現れる。
- residue 塊の大きさ・移送フロー量が LawConflict class 本数/共有 support 数の離散量に束ねられ、連続質量スカラーを表示しない(凡例に projection であり verdict でないと明記)。
- 2枚の locus 曲面が `PlaneGeometry` 近似である旨が non-claim に表示され、連続な lawful locus を測ったと誤読させない。
- 高次 Tor_i(i≥2)は描かれず凡例に「高次は沈黙」の一行のみ(M4 で typed boundary 化された higher-Tor silence を侵さない)。
- residue/移送の projection 追加で structural verdict 件数が増えず `projectionBoundary` の no-structural-verdict が維持されることをテストで固定する。
- repair による質量移送が片軸→他軸の lerp として動き、`not automatic repair / lower-bound` 系の non-claim を併記する。

依存: V0、V8(repair morph の supportVariables 座標・lerp 機構の共有)、M4(Tor multidegree)、`aatGeometryOverlays.lawConflict` projection(M14系)。projection は本 V の land 前提で計測側 Issue として別に切る。

### V16. 周期 Stokes 会計メーター(cycleBasis 周回と residual=0 整合を中央に)

意図: `cycleBasis` の各サイクルを閉ループ(リング)として描き、リングに沿って周回する光の弧が流れ、`periodPairingMatrix` の値が一周で蓄積する積分量としてメーターに現れる。Stokes 会計は各辺に正負フロー矢印を流し、`dΩintegral` と `boundaryPeriod` が一致して residual=0 のとき辺が緑に整合し、中央に「Stokes 恒等式 checked, max residual 0.0」という肯定的結論を控えめに据える(T2-6)。SAFE を画面の中心にする規律の周期版。

駆動計測 M-id と捏造関係: 駆動は **M9(Stokes audit identity を structural verdict 化、residual r=⟨dω,γ⟩−⟨ω,∂γ⟩ を固定係数環上の厳密差として全 (form,chain) 対で判定、`measured_zero`/`measured_nonzero`)** と、その値を `aatGeometryOverlays.periodStokes` へ運ぶ projection(`cycleBasis/forms/periodPairingMatrix/stokesAudit.pairs[].(dOmegaIntegral,boundaryPeriod,residual)/maxAbsoluteResidual/status='checked'` を v2 へ)。これらは `evaluate_period_stokes_v1` が実出力(`residual.abs()>1e-9` でハードエラーなので `checked` は真に residual=0)するが v2 `aatGeometryOverlays` に未投影で、`build_measurement_viewer_data_v1` への投影追加が要る。専用 profile(`ag.period-stokes` 行)が無い一般 packet では `cycleBasis` が空(唯一の fixture は単一 context・cover で b_1=0、ループ自体が無い)であり、メーターを描けばモデルが存在しないのに周期を測ったと偽装する捏造になる。**周回弧・pairing は `modelRelative`/`nonConclusion` の analytic reading であって structural verdict ではなく、M9 の structural verdict(辺の緑/フラックス突出)とは別レーンに保つ。M9 が厳密係数を解けず float のみで `unknown` へ降格した packet ではメーターを structural 整合として描かず analytic reading に留める。**

Three.js 方針: 新規 scene `period-stokes` と `renderPeriodMeter`。周回弧は `animate()`(L1038)の時間 t で開始角を回す。selective bloom を周回弧のみに(V2 bloom layer)。`modelRelative=true` の擬円周モデル相対量であり絶対 period でない旨と、`nonConclusion`(structural verdict でない)を凡例に必須表示。residual=0 整合は scene の中央焦点に据える(SAFE 中心化の周期版)。viewer は新規 structural verdict を作らず `projectionBoundary` の no-structural-verdict を維持する。

受け入れ観点:
- `aatGeometryOverlays.periodStokes` projection が land する前、または `cycleBasis` が空の一般 packet では scene が空表示=沈黙(赤エラー化しない)で周回弧・メーターを描かないことをテストで固定する。
- `status='checked'` かつ `maxAbsoluteResidual=0` のとき各辺が緑に整合し、中央に「Stokes 恒等式 checked, max residual 0.0」の肯定的結論バッジが控えめに出る。
- `residual≠0` の対がある辺は緑にならず該当 face で残差が外向きフラックスとして突出する(M9 の measured_nonzero 由来)。
- M9 が `unknown`(厳密係数不解決・float のみ)へ降格した packet ではメーターを structural 整合(緑)として描かず analytic reading に留めることをテストで固定する。
- 周回弧の蓄積量が `periodPairingMatrix` の実値で駆動され、`modelRelative`(擬円周モデル相対)である旨が凡例に明示され絶対 period と取り違えない。
- `nonConclusion`(structural verdict でない analytic reading)が凡例に表示され、周期メーターが structural verdict に昇格せず、外部手続きの pairing 保存を主張しない non-claim(原則13.3)を併記する。
- periodStokes projection 追加で structural verdict 件数が増えず `projectionBoundary` の no-structural-verdict が維持されることをテストで固定する。
- selective bloom は周回弧のみで lawful/unmeasured 域に漏れない(V2 規律継承)。

依存: V0、V2(bloom layer)、M9(Stokes audit verdict)、`aatGeometryOverlays.periodStokes` projection。projection は本 V の land 前提で計測側 Issue として別に切る。

### V17. スペクトル峰の再設計(measured-zero の lawful plain を中心、峰は局所逸脱として副次)

意図: transfer operator の固有モード地形を描くが、**視覚的中心は hotspot ではなく measured-zero の平らで安定した lawful plain** に置き、峰は局所的逸脱として副次的に描く(T4-1 の再設計版)。`NO_MEASURED_H1_OBSTRUCTION` を中心化し、再発する curvature 障害の中心(hotspot)は脈動発光する副次要素に留める。現案のまま hotspot を主役化すると規律違反になるため、再設計を前提とする。

駆動計測 M-id と捏造関係: 駆動は **M10(curvature transfer spectrum の Perron-Frobenius hotspot 忠実投影、misnamed per-cell proxy を別 readingKind で並置し power-iteration で principal eigenvector を取る)** と、その `topHotspots/topEigenmodes/transferEdges` を `aatGeometryOverlays` へ運ぶ projection(現状 `architectureSpectrumReport`/measurement packet に実在するが v2 `aatGeometryOverlays` 未出力)。捏造禁止が二重に効く: (1) **`curvatureStatus` フィールドは live measurement 経路の `topHotspots[]` に存在しない**(dead な v0 `cli/atom_viewer.rs` 経路にのみ残る名)ので使わず、report レベルの `status:needsReview`/`measurementStatus:proxy` を visual に明示し analytic-reading-not-verdict boundary を付す。(2) **measured-zero(cv=0)と unmeasured を別色・別レイヤで区別し、measured-zero を『描かず沈黙』にしない**(実 fixture の hotspot は `[1,0,0,0]` で 3/4 が cv=0=SAFE であり、これを描かないと SAFE を画面から消す規律違反になる)。projection 前に峰を描けば spectrum を測っていないのに固有地形を捏造することになる。**地形(峰・lawful plain)は spectrum proxy/analytic reading であって structural verdict ではないので analytic レーンに固定し、structural verdict に昇格させない。**

Three.js 方針: spectrum scene を `axisRef` ベースの決定論配置にして golden-angle 擬似ランダム依存を断つ。measured-zero セル(cv=0)を平らな lawful plain として scene 中心に主役化(淡い肯定色)、峰は principal eigenvector の局所逸脱として副次高さ・脈動発光(V2 bloom)。`spectralRadius` は文字列(`typed_evaluator.rs` の `spectralRadiusKind`/string 値)なので数値パース経路を Rust 側で明示し proxy を失わない。`transferEdges` の weight は峰間の尾根線。viewer は新規 structural verdict を作らず `projectionBoundary` の no-structural-verdict を維持する。

受け入れ観点:
- M10 の `aatGeometryOverlays` spectrum projection が land する前は scene が空表示=沈黙(赤エラー化しない)で峰を描かないことをテストで固定する。
- measured-zero セル(cv=0)が平らな lawful plain として scene 中心に描かれ、unmeasured とは別色・別レイヤで区別され、measured-zero が「描かず沈黙」にされない。
- 峰(principal eigenvector hotspot)は副次的な局所逸脱として描かれ scene 重心を奪わず、`NO_MEASURED_H1_OBSTRUCTION` 系の SAFE が視覚中心に残る。
- `curvatureStatus` フィールドを参照・表示せず、`status:needsReview`/`measurementStatus:proxy` を visual に明示して analytic-reading-not-verdict boundary を付す。
- 峰・lawful plain・尾根線が analytic レーン色(structural と別)に固定され、spectrum projection 追加で structural verdict 件数が増えず `projectionBoundary` の no-structural-verdict が維持されることをテストで固定する。
- 水平配置が `axisRef` 由来の決定論配置で golden-angle 擬似ランダムに依存しない(同入力で同配置を再現)。
- `spectralRadius` 文字列が数値としてパースされ proxy を失わず、analytic レーン色(structural と別)で表示される。

依存: V0、V2(bloom layer)、M10(curvature spectrum hotspot)、`aatGeometryOverlays` spectrum projection。projection と `spectralRadius` 数値パースは本 V の land 前提で計測側 Issue として別に切る。

### V18. analytic overlay 可視化(period landscape / Wasserstein mass 流 / spectral gap 谷深、analytic レーン固定)

意図: 既に完全計算されているのに viewer に届いていない analytic reading を、structural と取り違えない analytic レーンの overlay として投影・可視化する(P2 analytic overlay バンドル)。三つの像: (1) form×cycle の period landscape、(2) repair→target の obstruction mass 流(Wasserstein)、(3) hodge-debt 谷の浅深(spectral gap)。計測ロジックは一切変えず measured-not-projected を解消する従属可視化。

駆動計測 M-id と捏造関係: 駆動は **M14(P2 analytic overlay バンドル: period pairing matrix overlay / Wasserstein transfer cost overlay / spectral gap overlay を projection 追加し `build_measurement_viewer_data_v1` の allowlist と binding scene に新キーを追加。projection 関数追加だけでは viewer に届かない)**。各 overlay は **analytic レーン色(`colorRole=analytic_reading`)に固定** し、measured_zero(teal)へ昇格させない。捏造禁止: spectral gap≈0 を measured_zero teal に着色しない(near-flat≠lawful、原則8.4)、Wasserstein は W_1 そのものでない/global 修復安全性を証明しない を nonClaim 表示、period landscape は modelRelative。projection が land する前に overlay を描けば未投影 reading を捏造することになり、analytic を structural 色で塗れば structural verdict を偽装することになる。**本 V は計測ロジックを変えず projection だけを足すので新規 structural verdict を作らず、沈黙領域(高次 H^n / non-abelian stack-gerbe / monodromy transport 不在 / singularity deformation 不在 / Part IX)を侵さない。spectral gap 谷は L_1 そのものでなく proxy 固有値である旨も nonClaim に保つ。**

Three.js 方針: 各 overlay を専用レーン(analytic_reading 色レーン)に分離して描き structural レーン(teal/amber)と混ぜない。period landscape は form×cycle 格子の高さ場、Wasserstein mass 流は repair→target の流量アニメ(離散 cost に束ね連続質量を捏造しない)、spectral gap は hodge-debt 膜の谷の浅深(V6 曲率膜と同レイヤだが gap≈0 を teal に着色しない)。viewer は `projectionBoundary` の no-structural-verdict を維持する。

受け入れ観点:
- M14 の各 projection(allowlist + binding scene の新キー)が land する前は当該 overlay が空表示=沈黙で描かれないことをテストで固定する。
- 三 overlay すべてが `colorRole=analytic_reading` の固定色レーンで描かれ、measured_zero(teal)/measured_nonzero(amber)の structural 色を使わず、structural verdict 件数が overlay 追加で増えず `projectionBoundary` の no-structural-verdict が維持されることをテストで固定する。
- spectral gap≈0 を measured_zero teal に着色せず、near-flat≠lawful の nonClaim と、谷が L_1 でなく proxy 固有値である旨の nonClaim を行に表示する。
- Wasserstein mass 流が離散 cost に束ねられ、W_1 そのものでない/global 修復安全性を証明しない nonClaim を表示する。
- period landscape が modelRelative である旨を表示し絶対 period と取り違えない。
- monodromy transport 不在・singularity deformation 不在・高次 H^n・Part IX の沈黙領域には overlay を描かず、計測ロジックを変えないことをテストで固定する(沈黙侵犯・新 verdict 乱造をしない)。
- 沈黙領域(該当 reading 未供給)で overlay が赤エラー化せず空のまま沈黙する。

依存: V0、V6(曲率膜レイヤと spectral gap 谷深の共有)、M14(P2 analytic overlay バンドルの projection 配線)。projection は本 V の land 前提で計測側 Issue として別に切る。

## フェーズとマイルストーン

計測優先で α(H^2 核)→ β(P0 忠実性核)→ γ / δ の順を踏襲する。各フェーズで対応する M が land した後にのみ、その駆動 V を解放する。V0-V4 の器は既存データで成立するため、計測フェーズと並行して先行できる(ただし駆動 M に依存する本体 V5-V18 は M land 待ち)。

### Phase 1(α: H^2 coherence 核 + 器の最小セット)
**計測 M:** M0(リリース定義)、M5(H^2 coherence-obstruction、banded abelian F2)、M8(高次 H^n / non-abelian / 高次 Tor_i の typed boundary、M5 の sibling として同梱)、M7(Topological Debt Capacity、既存 C^2 を rank-nullity へ)、M15(common ambient ledger 精緻化)。
**可視化 V(器、駆動 M 不要 or M5/M7/M8 待ち):** V1(PBR 基盤、新データ不要)、V2(Selective Bloom、既存計測済み証拠のみ発光)、V3(沈黙描画・赤エラー撤廃、M5 land 後に H^2 膜・M8 の typed boundary 凡例)、V4(ラベル非散乱・空間文脈、既存データ)、V5(コホモロジー鉛直三層、既存 H^0/H^1 + M5 の H^2 層)、V7(b_1 光る閉路、M7 + 既存 nerve)、V11(degree スクラブ、M5 land 後に H^2 灰色沈黙層)。
依存: V3 の H^2 三角面開閉・V5 の天井層・V11 の H^2 剥離は M5 が land するまで「存在は描くが verdict は載せない」沈黙ガラスに留める。

### Phase 2(β: P0 忠実性核)
**計測 M:** M1(H^1 torsor effectivity ledger)、M2(restriction-compatibility、新評価器 + 1 verdict + 新 EffCoeff `finite-support-inclusion@1`)、M3(section-factorization、新評価器 + 1 verdict)、M4(Tor Taylor resolution 昇格、multidegree=lcm)、M11(lawful locus arrangement、既測未投影)、M13(facet/link 中立名 reading、depth/CM 語彙全廃)。
**可視化 V:** V8(support repair morph、M4 + 既存 forbiddenCages/repairMorphs)、V9(view mode morph + demote-hash 独立 AC、全 view 位置を実量へ)、V13(assembly snap、M2 の seam + 既存 nerve)、V6(曲率膜、既存 locusField + M14 spectral gap で谷浅深 — M14 は Phase 3 だが膜本体は既存データで先行可)。
依存: V13 の縫い目残留は M2 が land 後に restriction-compatibility seam を駆動。V8 の cage→lawful 変形は M4 の multidegree を従に。section 着地点(P0-3 系)は M3 land 後。

### Phase 3(γ / δ: 構造拡張 + analytic overlay 投影)
**計測 M:** M6(boundary-residue δ、新評価器 + 1 verdict、γ 系)、M9(Stokes audit verdict 化、float hard Err 廃止)、M10(reading 群: Hilbert 干渉級数 / transfer bounded inference 接地 / curvature spectrum Perron-Frobenius hotspot / refactor-invariant transport / repair の Alexander-dual・discrete-Morse 下界 inspection)、M12(NSdepth monotone reading 化)、M14(analytic overlay bundle 投影、δ 系)。
**可視化 V:** V10(Holonomy traversal、既存 cocycleRibbon.closureGap)、V12(findings シネマティックツアー、tourState)、V14(呼吸する fiber bundle、要共起 fixture cover+laplacian、無ければ gated)、V15(二 lawful loci 交差、M4 + M14 系 law-conflict-tor 投影)、V16(周期 Stokes メーター、M9)、V17(スペクトル峰、M10 curvature spectrum hotspot)、V18(analytic overlay 可視化、M14)。
依存: V16 は M9 land 後、V17 は M10 の hotspot land 後、V18 は M14 の投影 land 後にのみ解放。V14 は cover と signedCurvature を共起させる新 fixture が無ければ gated/保留(捏造しない)。

## スコープ

**含む(計測 M):** AAT 代数幾何版(9部)の有限計測可能不変量の忠実化・多様化全数。

- 忠実性の核昇格: M1(H^1 torsor effectivity ledger 行)/ M4(Tor degree-1 proxy → Taylor resolution + multidegree=lcm)/ M9(Stokes audit float hard Err → nonzero verdict)/ M12(NSdepth proxy → monotone reading)。
- 沈黙ギャップ充填(新 structural verdict 各1): M2(restriction-compatibility + 新 EffCoeff `finite-support-inclusion@1`)/ M3(section-factorization、既存5値再利用)/ M5(H^2 coherence-obstruction、banded abelian F2、新 `ag.*` law)/ M6(boundary-residue δ、Mayer-Vietoris d^0)。
- 沈黙の typed boundary 明示固定: M8(高次 H^n n≥3 silence_by_design / non-abelian stack-gerbe out_of_selected_vocabulary / 高次 Tor_i unmeasured_support、BoundaryStatementV1、verdict 不生成)。
- 既測未投影の活用 / reading 化: M7(Topological Debt Capacity rank-nullity / Euler / b1NerveReading)/ M10(Hilbert 干渉級数 / transfer bounded inference 接地 / curvature spectrum Perron-Frobenius hotspot / refactor-invariant transport / repair 下界 inspection)/ M11(lawful locus Stanley-Reisner arrangement)/ M13(facet/link 中立名 reading)/ M14(analytic overlay bundle 投影 + allowlist + binding scene 拡張)/ M15(common ambient coefficient-compatibility ledger 行)。

**含む(可視化 V):** 忠実化された計測に応じた viewer 改善全数。

- 器(V0 定義 + V1 PBR 基盤 / V2 Selective Bloom / V3 沈黙描画・赤エラー撤廃 / V4 ラベル・空間文脈)。
- コホモロジー幾何(V5 鉛直三層 / V7 b_1 光る閉路 / V11 degree スクラブ / V13 assembly snap)。
- 場・交差・周期(V6 曲率膜 / V8 support repair morph / V14 fiber bundle / V15 二 loci 交差 / V16 周期 Stokes メーター / V17 スペクトル峰)。
- 時間・操作(V9 view mode morph + demote-hash / V10 Holonomy traversal / V12 シネマティックツアー)。
- analytic overlay 可視化(V18)。

**含まない:** v0.4.0 packet 意味論・5値 verdict discipline・assumption ledger の基本構造変更(M2/M3/M5/M6/M9 の新 verdict 追加を除く)。新 schema field の input モデル拡張(coefficientRef / comparisonMorphismRef は M15 で別 Issue 送り)。viewer の build 工程追加。insight viewer PRD R9-R17 の scene 機能要件の再定義。詳細は Non-Goals に列挙する。

## Non-Goals

本 PRD は次を目標にしない。これらは沈黙・別 Issue・別 PRD の領域である。

- **profile 外計測。** global semantic safety / 全 runtime / 未来予測を計測対象化しない。ArchSig は measurement layer であって Lean 証明器ではない(CLAUDE.md 境界規律)。M2/M3/M6 が要求する追加 contract は profile 内の新 witness family 宣言であって profile 外計測ではない。

- **新 verdict の乱造。** notes が明示した5評価器(M2 / M3 / M5 / M6 / M9)以外に新 structural verdict を出さない。M1/M4/M7/M8/M10-M15 は verdict を増やさない(ledger / 内部 method / invariant / reading / typed boundary)。5値以外の第6 verdict を追加しない。

- **沈黙の侵犯。** 高次 H^n(n≥3、abelianized は計算可能だが Part IV scope 外)、non-abelian stack-gerbe(abelian F2 語彙外)、monodromy transport 不在時の measured square monodromy、singularity deformation regime 不在時の structural singularity、Part IX temporal obstruction は沈黙のまま。M5 は banded abelian に限った planned silence 解除であって原理的沈黙を侵さない。M8/M6 はむしろ沈黙を typed boundary として明示固定する。

- **π1^AAT の復活。** 基本群 monodromy を絶対不変量として計測対象にしない。`holonomyLikeGapMarker`(V10)は restriction-path closure gap であって monodromy verdict ではない(既存 fence 維持)。

- **proxy の verdict 化。** analytic reading(period / transfer / laplacian / spectrum / Wasserstein / NSdepth 値 / singularity concentration)を structural verdict へ push しない。M12 は NSdepth を「reading 化」に直す。theorem-candidate reading は structural_verdict_ref=None を強制。

- **Lean 対応の要求。** AG 定理ラベルの Lean 台帳登載は並行プロジェクトであり、本 PRD の completion 条件にしない。Rust と Lean の型対応を要求しない(ArchSig は Rust tooling であって Lean 証明器ではない)。

- **FieldSig 責務(Part IX)。** Part IX 進化幾何 / temporal obstruction(Ob_t)の時間方向計測は FieldSig + SFT 側の責務であり、ArchSig にとっては silence-by-design。ArchSig が temporal obstruction を測ると tool 境界を越える。

- **viewer の projectionBoundary 侵犯。** viewer から新しい structural verdict / curvature / cohomology class を導出しない。M14 系の per-object scalar 配線も測られた量を運ぶ projection に留め、`gluing_geometry_projection_v1` の `projectionBoundary` と test-locked 境界を維持する。

- **input モデル拡張(M15 由来)。** coefficientRef / comparisonMorphismRef の schema 拡張は contract が admit しない計測軸の製造に傾くため本 PRD に含めず、別 Issue で input モデル拡張の是非から問い直す。

- **棚卸し見送り案。** Decomposition groupoid descent reading、Margin / Architectural Dehn function / persistence-zigzag barcode、フローライン(勾配ベクトル捏造)、構造的 verdict での全幾何支配的駆動は本 PRD のスコープ外。

## Acceptance Criteria / 完了条件

各 AC は testable(評価器 + schema + fixture + test、verdict 件数、projectionBoundary 維持、measured_zero 無ヘッジ4条件、沈黙の typed boundary、viewer の駆動計測依存、no-build 単一 HTML 維持、golden UX 視覚回帰)とし、M/V 要求 ID へ紐づける。

**ワークストリーム M(計測=主)の AC:**

- AC-M0(M0): リリース定義に計測=主/可視化=従の順序規律と二ワークストリーム宣言が明記され、各計測の採否を冒頭の問いで読む規律が立てられている。
- AC-M1(M1): `ag.cech-obstruction@1` の assumption ledger に torsor effectivity / surjective restriction / descent / 定理12.4 前提行が追加され、`nerveIsForest && !hasTripleOverlapFaces` のとき forest 前提が `checked`、surjective restriction が `assumed` 固定、計算・verdict が不変であることを test が固定する。
- AC-M2(M2): 新評価器 `ag.restriction-compatibility@1` が新 EffCoeff `finite-support-inclusion@1` で各被覆辺の support 包含を判定し、verdict ちょうど1個(separated presheaf)、被覆辺空/生成系欠落で `not_computed` を返し、fixture + test が揃う。
- AC-M3(M3): 新評価器 `ag.section-factorization@1` が s^* I_Ob^U=0 を有限 checked し、section 不在で `not_computed`(沈黙)、部分割当で `unknown`、既存5値再利用を test が固定する。
- AC-M4(M4): `ag.law-conflict-tor@1` が内部 method `finite-monomial-tor-taylor@1` へ昇格(verdict id 据置)、各 class に multidegree=lcm 添付、非 square-free で `unmeasured`、higher Tor_i 沈黙を test が固定する。
- AC-M5(M5): 新評価器 `ag.coherence-obstruction@1` が banded abelian F2 で H^2 = ker δ2 / im δ1 を計算し、δ2 h=0 cocycle ゲートを im δ1 判定前に置き、`measured_zero`/`measured_nonzero`、non-abelian は banding violated で `not_computed`、verdict ちょうど1個、fixture(pairwise-compatible / triple-incompatible)+ test が揃い、invariant 散文 `ker d^2/im d^1` の正しさを確認する。
- AC-M6(M6): 新評価器 `ag.boundary-residue@1` が core/feature/boundary 分類 atom 上で Mayer-Vietoris d^0 を組み δ を F2 判定、coefficient=F2 を ledger checked / Z-zero 持ち上げ assumed、verdict ちょうど1個、period-Stokes modelRelative との分離と π1 非復活を test が固定する。
- AC-M7(M7): Topological Debt Capacity が capacityLowerBound / eulerCharacteristic / b1NerveReading を reading 行(structural verdict 不生成)として出力し、1-skeleton b_1 vs nerve 複体 b_1 を明示する。
- AC-M8(M8): BoundaryStatementV1 が高次 H^n(silence_by_design)/ non-abelian stack-gerbe(out_of_selected_vocabulary)/ 高次 Tor_i(unmeasured_support)の三層を区別し、verdict 不生成・assumption propagation 不発火を test が固定する。
- AC-M9(M9): `ag.period-stokes-audit@1` が float hard Err(`residual.abs()>1e-9`)を廃止し固定係数で nonzero verdict を出し、analytic strict-period-pairing は別 reading で据え置かれる。
- AC-M10(M10): Hilbert 干渉級数 audit reading / transfer 定義10.4 前提検査 / curvature spectrum Perron-Frobenius hotspot(別 readingKind, power-iteration)/ refactor-invariant transport reading / repair の Alexander-dual・discrete-Morse 下界 inspection が、すべて structural verdict 不生成 or analytic レーンで出力される。
- AC-M11(M11): lawful locus arrangement(facets / vanishingCoords / dimension / irreducibleComponentCount)が computedInvariant として出力され verdict を持たない。
- AC-M12(M12): `ag.nullstellensatz-depth-monotone@1` が NSdepth 値を proxy analyticReading に隔離し、monotone / generatorExtension bool のみを structural computedInvariant とし、structural_verdict_ref=None を保つ。
- AC-M13(M13): Δ_U facet/link が中立名(facetDimensionReading / linkBoundaryReading / linkReducedBetti / isPure)で reading 化され、depth / Cohen-Macaulay / Reisner / srDepth 語彙が全廃されていることを scan が確認する。
- AC-M14(M14): analytic overlay bundle(period pairing matrix / Wasserstein cost / spectral gap λ1 / curvature spectrum hotspot / singularity concentration)が `build_measurement_viewer_data_v1` の allowlist + binding scene 拡張で投影され、colorRole=analytic_reading 固定、structural verdict 件数不変、measured_zero に昇格しないことを test が固定する。
- AC-M15(M15): common ambient assumption ledger に coefficient-compatibility 行(def9.1 紐づけ)が追加され、coefficientRef 等の schema 拡張が本 PRD に含まれない(別 Issue 送り)ことが明記される。
- AC-M共通: 新 structural verdict は M2/M3/M5/M6/M9 の5評価器に限定され各々ちょうど1個、5値以外の verdict が追加されておらず、measured_zero が無ヘッジ4条件(①-④)で支えられ、violated 時に依存 verdict のみ `not_computed` へ正規化されることを test が固定する。

**ワークストリーム V(可視化=従)の AC:**

- AC-V0(V0): 各 V が駆動 M(または既存実装データ)を名指し、計測なき構造を描かない捏造禁止・projectionBoundary 維持・沈黙を描かない規律が明記される。
- AC-V1(V1): `toneMapping=ACESFilmic` + RoomEnvironment IBL(PMREM)+ 3点照明 + 接地影(ShadowMaterial)+ Fog が WebGL/WebGPU 両経路で設定され、新データ不要、no-build 単一 HTML が維持される。
- AC-V2(V2): Selective Bloom(EffectComposer + UnrealBloomPass、bloom layer)が計測済み証拠(closureGapEncoding / sharedAtomRefs / forbiddenCages / repairMorphs)のみ発光させ、lawful / unmeasured は発光しない。
- AC-V3(V3): 沈黙描画が現状の赤エラー化(blockedRegions `0xff6b6b` L1687 / cocycle gap L1640)を撤廃し、measured を焦点面手前・unmeasured を霧の奥(FogExp2 + BokehPass)・H^2 三角面をすりガラスへ後退させる(駆動: M5 land 後に H^2 膜 / M8 の typed boundary 凡例)。
- AC-V4(V4): ラベル非散乱(共有アトラス + 距離フェード + 衝突回避、priorityScore 優先)と空間文脈(3D 基準グリッド / 座標プレート / ヴィネット / view mode カメラトゥイーン)が成立する。
- AC-V5(V5): コホモロジー鉛直三層(H^0 地表 / H^1 中層リボン / H^2 沈黙ガラス天井)が degree 固定 y で hash y を上書きする(駆動: 既存 H^0/H^1 + M5 の H^2 層)。
- AC-V6(V6): 実測曲率場 heightmap 膜(signedCurvature が膜変形、measuredZeroRegion=盆地=lawful locus、blockedRegion=破れた穴)が立ち、IDW 補間 non-claim を明記する(駆動: 既存 locusField + M14 spectral gap で谷浅深)。
- AC-V7(V7): Čech 単体複体の b_1 が光る閉路(spanning tree + 基本サイクル、filled triple 面)として描かれ、graph cycle≠H^1 verdict の境界注記を持つ(駆動: M7 + 既存 nerve)。
- AC-V8(V8): support repair morph(supportVariables を実座標軸、cage→lawful 連続変形、not automatic repair / lower-bound)が動き、mass-preserving / cobordism 語を使わない(駆動: M4 + 既存 forbiddenCages/repairMorphs)。
- AC-V9(V9): view mode 間レイアウト morph(全 clear 廃止、InstancedMesh 位置補間)と demote-hash(axisMetricBindings 実 metric を主係数化、hash jitter を従へ)が独立 AC として成立する(駆動: 全 view の位置を実量へ)。
- AC-V10(V10): Holonomy traversal(フレームをループ周回、閉じなさをアニメ)が成立し、holonomyTwist スカラー無き場合は離散 twist + unmeasured magnitude 注記に留める(駆動: 既存 cocycleRibbon.closureGap)。
- AC-V11(V11): cohomology degree スクラブ(H^0/H^1/H^2 を時間スライダーで剥離、H^2 は灰色沈黙)が成立する(駆動: M5)。
- AC-V12(V12): findings シネマティックツアー(tourState 活用、highlightRefs へカメラトゥイーン、終点=肯定的結論バッジ)が成立し、caption が packet 由来を逸脱しない。
- AC-V13(V13): 貼り合わせ assembly snap(パッチ飛来→吸着、value=1 辺は snap し損ね seam)が成立し、b_1 発光=graph cycle 注記・edge.value=parity 注記を持つ(駆動: M2 + 既存 nerve)。
- AC-V14(V14): Čech 神経の呼吸する fiber bundle(base 円盤 + section fiber 柱、signedCurvature 駆動、H^1 seam)が、cover+laplacian 共起 fixture を伴って成立する。fixture 無ければ gated/保留(捏造しない)。
- AC-V15(V15): 二 lawful loci の交差と非横断 residue(Tor_1≠0 で余剰塊、repair で質量移送)が成立し、PlaneGeometry 近似 non-claim・離散量束ねを明記する(駆動: M4 + M14 系 law-conflict-tor 投影)。
- AC-V16(V16): 周期 Stokes 会計メーター(cycleBasis 周回、residual=0 整合を中央、Stokes 恒等チェック)が成立し、modelRelative 注記を持つ(駆動: M9)。
- AC-V17(V17): スペクトル峰(measured-zero の lawful plain を中心、峰は局所逸脱として副次)が成立し、curvatureStatus 捏造禁止・measured-zero と unmeasured 分離を test が確認する(駆動: M10)。
- AC-V18(V18): analytic overlay 可視化(period landscape / Wasserstein mass 流 / spectral gap 谷深)が analytic レーン色固定で立ち、structural と取り違えない(駆動: M14)。
- AC-V共通: 全 V が駆動 M land 後にのみ構造を描き、projectionBoundary(no new structural verdict)を維持し、golden UX 視覚回帰ケースが追加され `cargo test` が通る。

## 検証コマンド

CLAUDE.md の検証コマンドに準拠する。変更範囲に応じて選び、迷う場合は広めに実行する。

```bash
# ArchSig 計測(M)変更の検証
cargo test --manifest-path tools/archsig/Cargo.toml

# FieldSig handoff への波及確認
cargo test --manifest-path tools/fieldsig/Cargo.toml

# AG 計測の一次 workflow(新 evaluator / ledger / overlay の end-to-end)
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .tmp/archsig-analyze

# viewer(V)変更の目視確認(no-build 単一 HTML を維持)
python3 -m http.server 0 --directory tools/archsig/viewer

# PR 前に常に
git diff --check

# hidden / bidi Unicode scan(変更ファイルに対して)
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>

# 禁止語 scan(M13 の depth/CM 語彙全廃、V8 の mass-preserving/cobordism 不使用、
#            V17 の curvatureStatus 捏造禁止を確認)
rg -n "Cohen-Macaulay|Reisner|srDepth|Krull depth|mass-preserving|cobordism|curvatureStatus" \
  tools/archsig/src tools/archsig/viewer

# website への波及確認(docs-only 変更でも tool schema / copy 影響を確認)
python3 -m http.server 0 --directory website
```

docs-only 変更でも Lean status、tool schema、website copy への影響を確認する。新 evaluator(M2/M3/M5/M6/M9)追加時は schema_catalog と fixture の追加、golden UX 視覚回帰ケースの追加を test で固定する。
