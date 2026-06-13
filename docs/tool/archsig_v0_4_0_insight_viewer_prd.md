# ArchSig v0.4.0 Insight & Algebraic Geometry Viewer PRD

Related core PRD: `docs/tool/archsig_v0_4_0_algebraic_geometry_measurement_prd.md`
Target implementation surface: `tools/archsig/viewer/archsig-atom-viewer.html` / `archsig-measurement-packet/v1` / `archsig-analysis-summary/v2`

---

## 問い

この PRD のすべての要求は、次の問いに仕える。

```text
問い:
  コードベースは AAT 代数幾何によってどのように可視化され、
  どのようなインサイトを得られるか?
```

この問いは、既存の ArchSig v0.4.0 core PRD が立てた問いを、ユーザー体験側へ拡張する。

```text
v0.4.0 core PRD:
  局所的にはすべて合法なのに、全体は歪んでいる ——
  それを、誰の主観にも頼らず測り、ヘッジなしに言い切れるか?

本 PRD:
  その測定結果を、コードベースの構造・貼り合わせ・障害・修復候補・境界として
  ユーザーが見て、理解し、次の判断に使えるか?
```

本 PRD は、AAT 代数幾何による計測を「正しい artifact」として出すだけでなく、ユーザーが次を答えられる状態を目指す。

```text
- 今、このコードベースで何が起きているか?
- それは局所違反なのか、全体の貼り合わせの歪みなのか?
- どの Atom / context / cover / law / source が関与しているか?
- どの修復候補から見ればよいか?
- どこまでが measured で、どこからが assumed / unknown / not_computed なのか?
- この結果を PR review / CI / リファクタ計画でどう使えるか?
```

---

## 位置づけ

この PRD は、ArchSig v0.4.0 の追加 PRD である。既存の `ArchSig v0.4.0 Algebraic Geometry Measurement PRD` を置き換えない。

既存 PRD の責務は、AG measurement path の中核を成立させることである。

```text
ArchMap v2
  -> MeasurementProfile v1
  -> typed AG evaluators
      Cech / Stanley-Reisner / Tor / Laplacian / period / transfer
  -> archsig-measurement-packet/v1
  -> conclusion-first summary / viewer
```

本 PRD の責務は、その後段の projection layer を定義することである。

```text
archsig-measurement-packet/v1
  -> archsig-analysis-summary/v2
  -> archsig-insight-report/v1
  -> archsig-insight-brief.md
  -> Viewer visual scenes
  -> LLM / review handoff blocks
```

本 PRD は、新しい数学的 evaluator を追加しない。measurement packet に含まれない claim を生成しない。structural verdict と analytic reading の分離、5値 verdict discipline、CBI assumption ledger、theorem-candidate gating は既存 PRD の規律をそのまま引き継ぐ。

---

## 背景と課題

現在の v0.4.0 PRD は、理論・schema・evaluator の正しさを中心に構成されている。これは release の中核として妥当である。一方で、実際に ArchSig を使うユーザーは、H^1、Tor、NSdepth、harmonic mass、period pairing そのものを見たいのではなく、それらを通じてコードベースについての判断を得たい。

現状の課題は次である。

```text
- PRD が理論寄りで、ユーザー体験の要求が薄い。
- 出力 artifact が多く、ユーザーがどこから読めばよいか分かりにくい。
- summary / viewer が「結果の表示」に寄っており、「インサイトの提示」になりきっていない。
- Three.js Viewer はあるが、3D 空間の座標やモードに十分な意味が与えられていない。
- AAT 代数幾何の核心である context / cover / gluing / H^1 / repair dual が、視覚体験として伝わりにくい。
- `unknown` / `unmeasured` / `not_computed` / `assumed` が、ユーザーにとって読める境界になっていない。
```

したがって本 PRD は、ArchSig v0.4.0 の UX を次の方向へ改善する。

```text
Before:
  計測結果を見る。
  数値・verdict・artifact をユーザーが読み解く。

After:
  コードベースを AAT 代数幾何の意味空間として見る。
  ArchSig が top insight、根拠、次に見る場所、境界を提示する。
```

---

## Product Goal

ArchSig v0.4.0 の出力を、アーキテクチャ責任者・レビュアー・リファクタ担当者が、次の判断に使える状態にする。

```text
1. 結論を読む。
2. Top insight を把握する。
3. 3D Viewer で、コードベースの構造・貼り合わせ・歪みを見る。
4. 根拠となる source / atom / context / law / evaluator を確認する。
5. 測定境界と non-claims を確認する。
6. 次に見る箇所・修復候補を決める。
```

v0.4.0 core が「測定器」だとすれば、本 PRD は「診断画面」と「意味空間 Viewer」を定義する。

---

## 対象ユーザー

### U1. アーキテクチャ責任者

コードベース全体の歪み、ポリシー衝突、修復優先度を知りたい。数学的詳細よりも、「どこが問題で、どの判断に使えるか」を必要とする。

### U2. PR / CI レビュアー

CI artifact として出た ArchSig 結果を読み、merge 可否や追加調査の要否を判断したい。短時間で conclusion、boundary、action を把握したい。

### U3. リファクタ実行者

具体的なファイル、Atom、context、repair candidate を辿り、どこから修正するかを決めたい。Viewer 上で該当箇所を絞り込み、source refs をコピーできる必要がある。

### U4. ArchSig / AAT 開発者

出力 artifact が正しく UX surface に投影されているかを fixture で検証したい。理論語彙と engineer-facing 語彙の対応を保ちたい。

---

## ユースケース

### UC1. 最初の30秒で「何が起きているか」を把握する

状況: ユーザーは ArchSig の出力 artifact を開いた。JSON や詳細な数学用語を読む前に、今回の結果を把握したい。

出力:

```text
Read this first:
  Conclusion: GLOBAL_GLUE_MISMATCH_MEASURED
  Meaning: Local rules mostly hold, but cross-context glue mismatch was measured.
  Where to look: auth/session <-> api/middleware
  Next action: Inspect mismatch support.
  Boundary: Profile-relative. Leray acyclicity assumed. 2 supports unmeasured.
```

アウトカム: ユーザーは、結論・意味・最初に見る場所・境界を短時間で把握できる。

### UC2. AAT 代数幾何の「貼り合わせ」を Viewer で見る

状況: 局所 context では law violation が少ないが、全体として architecture drift が疑われる。

出力:

```text
Viewer:
  - context を patch として表示
  - cover overlap を seam として表示
  - restriction direction を arrow として表示
  - H^1 mismatch support を glowing ribbon として表示
```

アウトカム: ユーザーは「局所的には合法だが、全体の貼り合わせが壊れている」を、抽象語ではなく空間上の seam として理解できる。

### UC3. 修復候補を obstruction support と同じ空間で見る

状況: 障害が多数あり、どこから手をつけるべきか分からない。

出力:

```text
Viewer:
  - minimal forbidden supports を cage / simplex として表示
  - minimal repair hitting sets を cut / handle として表示
  - lower bound を gauge として表示
  - 「自動修復ではない」non-claim を表示
```

アウトカム: ユーザーは、修復候補がどの obstruction support を横切るかを理解し、リファクタ計画の出発点にできる。

### UC4. Policy conflict を common ambient として見る

状況: 新しい law を導入したいが、既存 law universe と構造的に衝突するかを知りたい。

出力:

```text
Viewer:
  - law universe A / B を sheet として表示
  - common ambient を中央領域として表示
  - conflict class を bridge / knot として表示
  - common ambient がない場合は not_computed blocker として表示
```

アウトカム: ユーザーは、衝突の有無だけでなく「どの witness / context に衝突が載るか」を確認できる。

### UC5. Architecture debt を analytic field として見る

状況: 負債の量と分布を見たいが、合否判定と混同したくない。

出力:

```text
Viewer:
  - harmonic mass を heat / glow として表示
  - distance-to-flatness を height / contour として表示
  - spectral gap を landscape として表示
  - lawful / unlawful には昇格しない
```

アウトカム: ユーザーは、analytic reading を debt field として観察できる。ただし structural verdict との混同は避けられる。

### UC6. 測定境界を読める台帳として見る

状況: 結果を CI / review で使いたいが、どこまで信じてよいかを確認したい。

出力:

```text
Boundary scene:
  checked     -> solid surface
  assumed     -> translucent surface
  unmeasured  -> fog
  unknown     -> grey unresolved region
  not_computed -> blocking wall with reason code
  violated    -> broken red boundary
```

アウトカム: ユーザーは、結論がどの profile / assumption / coverage の内側で成立しているかを理解できる。

### UC7. Source evidence へ着地する

状況: Insight を見た後、具体的にどのコードを確認すべきか知りたい。

出力:

```text
Source Evidence:
  - source files / symbols を path neighborhood に配置
  - Atom と source refs を線で接続
  - source refs を copyable block として表示
```

アウトカム: ユーザーは、抽象的な AAT 構造から、具体的なファイル・symbol・line に着地できる。

---

## Design Principles

### P1. Insight-first, proof-linked

画面と summary の先頭には、数値や理論名ではなく、ユーザーが判断できる insight を出す。

```text
悪い:
  H^1 dimension = 2

良い:
  局所規約違反は少ないが、2つの context 間で貼り合わせ不整合が測定された。
  影響箇所: auth/session, api/middleware
  次に見る場所: cocycle support refs
```

ただし、すべての insight は packet 内の structural verdict、computed invariant、analytic reading、source refs、assumption ledger に辿れる必要がある。

### P2. 3D 空間は装飾ではなく、意味を持つ座標系にする

Viewer の各 scene は、必ず `userQuestion` と `axisMapping` を持つ。

```json
{
  "sceneId": "cech-gluing",
  "title": "Cover & Gluing",
  "userQuestion": "Which local contexts fail to glue globally?",
  "axisMapping": {
    "x": "source locality / module neighborhood",
    "y": "context rank / restriction depth",
    "z": "obstruction intensity / mismatch class weight"
  }
}
```

X/Y/Z の意味は scene ごとに変わってよい。ただし、Viewer の axis HUD と legend に必ず表示する。

### P3. Engineer-facing vocabulary first

Viewer / summary の primary label は、AG 数学節名ではなくエンジニアが読める語彙にする。

```text
H^1 obstruction
  -> Global glue mismatch

minimal repair hitting set
  -> Minimal repair candidate

CBI assumption ledger
  -> Measurement boundary

Tor conflict
  -> Policy conflict

harmonic mass
  -> Architecture debt mass
```

詳細パネル、raw artifact、debug view では AG 語彙を保持する。

### P4. Conclusion and boundary are separated

結論文にヘッジを混ぜない。ただし boundary は隠さない。結論の隣に、短い boundary digest を置く。

```text
Conclusion:
  GLOBAL_GLUE_MISMATCH_MEASURED

Boundary digest:
  Profile-relative. Leray acyclicity assumed. 3 supports unmeasured.
```

### P5. Every important claim has a “where”

Top insight には必ず場所を付ける。

```text
- source refs
- atom refs
- context refs
- cover refs
- law refs
- evaluator refs
- artifact refs
```

場所がない insight は、Top insight に昇格できない。

### P6. Action is not auto-fix

Action Queue は「次に見る / 検討する候補」であり、自動修復ではない。repair hitting set は「修復の意味論」ではなく「組合せ的候補」であることを UI 上でも明示する。

### P7. Unknown is visible, but not dominant

`unknown`、`unmeasured`、`not_computed` は重要だが、レポート冒頭を占有しない。Top insight の後に boundary digest として示し、詳細は Boundary scene で読めるようにする。

### P8. Visual scene は数学的 claim ではなく projection である

Viewer の morph、ribbon、patch、field、cage は、measurement packet の情報を理解するための projection である。Viewer の描画から新しい structural verdict を導出してはならない。

---

## Scope

この PRD のスコープは次である。

```text
- archsig-insight-report/v1 の定義。
- Insight Card / Action Queue / Boundary Digest / Viewer Visual Scene の schema 定義。
- archsig-insight-brief.md の生成。
- Viewer の information architecture 改善。
- AAT 代数幾何概念を表す rich 3D scene の定義。
- Top Insight から Viewer scene / Evidence Detail へ遷移する guided exploration。
- Source refs の copyable 表示。
- Boundary / assumption / omitted detail の読める可視化。
- UX surface の validation と golden fixtures。
```

---

## Non-Goals

この PRD は次を目標にしない。

```text
- AG evaluator の数学的意味論を変更する。
- structural verdict を analytic reading から導出する。
- theorem-candidate reading を certified conclusion に昇格する。
- monodromy / boundary holonomy 系 verdict を復活させる。
- 自動修復を提供する。
- 修復安全性を結論する。
- trend / noise resistance / stability を主張する。
- 複数実行間の進化計測を v0.4.0 の certified feature にする。
- GitHub PR comment integration、dashboard hosting、チーム共有機能を完成させる。
- Viewer を汎用コードナビゲーション IDE にする。
- LLM が自由解釈で新しい結論を生成することを許す。
```

本 PRD が扱うのは、既存 packet に含まれる measured / assumed / unknown / not_computed な情報を、ユーザーが誤読しにくく、探索しやすい形で提示することである。

---

## Artifact Overview

### A1. 新しい projection artifact

`archsig-insight-report/v1` を追加する。

```text
archsig-measurement-packet/v1
  -> archsig-analysis-summary/v2
  -> archsig-insight-report/v1
      -> headline
      -> insightCards
      -> actionQueue
      -> boundaryDigest
      -> viewerVisualScenes
      -> guidedTours
      -> copyBlocks
  -> archsig-insight-brief.md
  -> atom viewer data / reportPane
```

`archsig-insight-report/v1` は新しい計測結果ではない。packet の projection であり、packet に存在しない claim を生成してはならない。

### A2. Schema sketch

```json
{
  "schema": "archsig-insight-report/v1",
  "reportId": "insight:...",
  "sourcePacketRef": "archsig-measurement-packet:...",
  "generatedAt": "...",
  "outputArtifacts": {
    "summaryRef": "archsig-analysis-summary.json",
    "briefRef": "archsig-insight-brief.md",
    "viewerDataRef": "archsig-atom-viewer-data.json"
  },
  "headline": {
    "conclusionCode": "GLOBAL_GLUE_MISMATCH_MEASURED",
    "title": "Global glue mismatch measured",
    "summary": "Local rules mostly hold, but cross-context mismatch was measured.",
    "decisionState": "needs_attention",
    "primaryVerdictRefs": ["verdict:h1:..."],
    "boundaryDigestRef": "boundary-digest:main"
  },
  "insightCards": [],
  "actionQueue": [],
  "boundaryDigest": {},
  "viewerVisualScenes": [],
  "guidedTours": [],
  "copyBlocks": {},
  "rankingBasis": []
}
```

---

## Insight Card Model

### R1. Top Findings を typed Insight Cards に置き換える

Viewer と summary の `Top Findings` は、汎用 item list ではなく、typed `InsightCard` の配列として扱う。

```json
{
  "id": "insight:h1-glue-mismatch:001",
  "kind": "global_glue_mismatch",
  "severity": "high",
  "title": "Global glue mismatch between auth and api contexts",
  "oneLine": "Local checks pass, but selected cover has nonzero H^1 support across auth/session and api/middleware.",
  "whyItMatters": "This indicates architecture drift not visible as a local law violation.",
  "evidence": {
    "structuralVerdictRefs": ["verdict:cech-h1:main"],
    "computedInvariantRefs": ["invariant:h1:main"],
    "analyticReadingRefs": [],
    "assumptionRefs": ["assumption:leray"],
    "sourceRefs": [],
    "atomRefs": [],
    "contextRefs": [],
    "coverRefs": []
  },
  "nextAction": {
    "label": "Inspect mismatch support",
    "kind": "inspect",
    "targetRefs": ["support:cocycle:001"]
  },
  "viewerNavigation": {
    "sceneId": "cech-h1-mismatch",
    "highlightRefs": {
      "atomRefs": [],
      "contextRefs": [],
      "sourceRefs": []
    }
  },
  "tourRefs": ["tour:h1-glue-mismatch:001"],
  "rankingBasis": [
    "measured_nonzero structural verdict",
    "has context refs",
    "has next inspection action"
  ],
  "nonClaims": [
    "This does not prove the extraction is complete.",
    "This does not automatically identify a safe repair."
  ]
}
```

### R2. Insight Card kinds

v0.4.0 で最低限扱う card kind は次とする。

```text
global_glue_mismatch
  H^1 measured_nonzero に対応。

no_measured_glue_mismatch
  H^1 measured_zero に対応。ただし unmeasured support は boundary に出す。

minimal_repair_candidate
  Alexander dual / hitting set に対応。

repair_lower_bound
  essential repair lower bound に対応。

policy_conflict
  monomial Tor / LawConflict に対応。

deep_obstruction_certificate
  Nullstellensatz certificate / NSdepth に対応。

architecture_debt_mass
  harmonic mass / distance-to-flatness に対応。structural verdict ではない。

measurement_boundary
  assumption ledger / coverage gaps / omitted detail に対応。

validation_failure
  schema validation / Stokes audit / manifest validation に対応。

not_computed_blocker
  violated assumption、no common ambient、missing profile などに対応。
```

### R3. Insight ranking を定義する

Top insight の順序は実装依存にしない。次の ranking rule を固定する。

```text
1. validation_failure
2. measured_nonzero structural verdict
3. not_computed due to violated assumption
4. high-severity repair lower bound / minimal repair candidate
5. policy conflict
6. architecture debt mass / analytic reading
7. measurement boundary
8. measured_zero confirmation
```

同順位では次を優先する。

```text
- source refs / context refs が多い。
- repair candidate を持つ。
- CI decision に関係する。
- omitted / unmeasured が少なく、説明可能性が高い。
```

この ranking は「重要度の UX ヒューリスティック」であり、数学的順序ではない。v0.4.0 では deterministic な固定 ranking とし、profile 側の重み付け override は入れない。ranking result は report top-level と各 Insight Card の `rankingBasis` として artifact に記録する。

### R4. Insight claim validation

Insight Card は schema validation だけでなく、claim validation を通す。

```text
- insight.evidence.structuralVerdictRefs が存在しない measured claim は禁止。
- analytic reading だけから lawful / unlawful を言う insight は禁止。
- sourceRefs / atomRefs / contextRefs のいずれもない high severity insight は禁止。
- not_computed を failure と表示する場合、reason code が必須。
- repair_candidate は nonClaims を必須にする。
- theorem-candidate reading は structural conclusion に昇格禁止。
- monodromy verdict を生成禁止。
```

---

## Summary / Brief UX

### R5. Summary の先頭を “Read this first” にする

`archsig-analysis-summary/v2` または派生 Markdown には、先頭に次の block を出す。

```md
## Read this first

Conclusion: GLOBAL_GLUE_MISMATCH_MEASURED

What it means:
Local architecture rules are not enough to explain the current structure.
ArchSig measured a cross-context glue mismatch under the selected profile.

Where to look first:
1. auth/session <-> api/middleware
2. user/repository <-> permission/policy

Next action:
Inspect the mismatch support and compare it with the minimal repair candidates.

Boundary:
Profile-relative. Leray acyclicity is assumed. 2 supports were unmeasured.
```

この block では AG 用語を primary にしない。必要に応じて `Details: H^1 measured_nonzero` のように二次情報として添える。

### R6. “Why this matters” を必須にする

Top 3 insight には `whyItMatters` を必須にする。

```text
- 何が起きているか。
- なぜコードベース上のリスクなのか。
- どの判断に使えるか。
```

`whyItMatters` は packet に存在する計測結果の言い換えに限定する。新しい因果推論や開発方針の断定は禁止する。

### R7. `archsig-insight-brief.md` を標準 artifact に含める

v0.4.0 では、次の Markdown artifact を `analyze --out-dir` の標準の出力 artifact として生成する。

```text
archsig-insight-brief.md
```

`archsig-insight-brief.md` は独立 artifact とし、run manifest / artifact links / viewer report pane から参照できるようにする。CLI stdout に全文を直接出す必要はない。`archsig-analysis-summary/v2` は同じ内容を構造化して保持してよいが、brief の canonical file は `archsig-insight-brief.md` とする。

構成:

```md
# ArchSig Insight Brief

## Read this first
## Top insights
## Where to look
## Suggested next inspections
## Repair candidates
## Measurement boundary
## Artifact links
## Raw technical details
```

この brief は GitHub comment / Slack / issue に貼れる粒度を目指すが、integration 自体は本 PRD のスコープ外とする。

### R8. LLM handoff block を生成する

LLM に後続分析を依頼するため、brief の末尾に copyable block を出す。

```md
## LLM handoff

Use the following ArchSig result as bounded evidence.
Do not infer beyond the listed claims and boundaries.

Conclusion:
...

Top insights:
...

Boundary:
...

Source refs:
...
```

LLM handoff block は新しい分析を行わない。packet から導出された claim と boundary を転記する。

---

## Viewer Information Architecture

### R9. Viewer を “Insight -> Scene -> Evidence” に再構成する

Viewer は、単なる 3D Atom map ではなく、次の流れで使えるようにする。

```text
Insight Card
  -> related visual scene
  -> highlighted atoms / contexts / seams
  -> source refs / evaluator refs / boundary refs
```

UI は次の領域を持つ。

```text
1. Header / Decision Bar
   conclusion, validation, boundary digest, artifact links

2. Left Panel / Insight Queue
   ranked Insight Cards

3. Center / Atom Map
   3D map, selected insight highlight, filters

4. Right Panel / Evidence Detail
   selected atom / context / law / source refs / non-claims

5. Bottom Panel / Report
   full report, artifacts, validation, omitted detail
```

現在の report panel は維持してよいが、初期状態ではユーザーが読むべき順序を明確にする。

```text
Before:
  Overview / Top Findings / Distance Diagnosis / Action Queue / Coverage...

After:
  Read this first / Insight Queue / Where to look / Why / Next action / Boundary
```

### R10. Detail panel は “What / Why / Where / Boundary” に統一する

どの object を選択しても、Detail panel は次の形で表示する。

```text
What:
  これは何か。

Why:
  なぜ重要か。

Where:
  atom / context / source refs。

Measurement:
  verdict / invariant / analytic reading refs。

Boundary:
  assumed / unknown / not_computed / non-claims。

Next:
  inspect / compare / open repair candidate。
```

---

## Viewer Visual Scene Contract

### R11. `viewerVisualScenes` を追加する

`archsig-insight-report/v1` に、Viewer が意味付き 3D scene を構成するための projection を追加する。

```json
{
  "viewerVisualScenes": [
    {
      "sceneId": "cech-gluing",
      "kind": "cover_gluing",
      "title": "Cover & Gluing",
      "userQuestion": "Where does local structure fail to glue globally?",
      "axisMapping": {
        "x": "source neighborhood",
        "y": "context rank",
        "z": "mismatch intensity"
      },
      "primaryRefs": {
        "insightRefs": [],
        "atomRefs": [],
        "contextRefs": [],
        "coverRefs": [],
        "sourceRefs": []
      },
      "layers": [
        {
          "layerId": "layer:cech-gluing:mismatch-seams",
          "kind": "overlap_seam",
          "geometryRole": "ribbon",
          "encodingRef": "encoding:mismatch",
          "clickTargetKind": "cechMismatchSeam",
          "refs": {
            "insightRefs": [],
            "atomRefs": [],
            "contextRefs": [],
            "coverRefs": [],
            "sourceRefs": [],
            "artifactRefs": []
          },
          "omissionPolicy": "preserve_for_top_insight"
        }
      ],
      "visualEncodings": [
        {
          "encodingId": "encoding:mismatch",
          "colorRole": "measured_nonzero",
          "shapeRole": "ribbon",
          "lineRole": "thick_glowing_line",
          "textRole": "mismatch label"
        }
      ],
      "boundaryDigestRef": "boundary-digest:main"
    }
  ]
}
```

`layers` は Viewer が描画する意味単位であり、Three.js 側の暗黙推論だけに任せない。各 layer は最低限次を持つ。

```text
layerId:
  report 内で一意な layer id。

kind:
  context_patch / cover_patch / overlap_seam / cocycle_ribbon /
  forbidden_support_cage / repair_candidate_cut / law_conflict_bridge /
  boundary_wall / source_node など。

geometryRole:
  patch / seam / ribbon / cage / cut / wall / node / arrow など。

encodingRef:
  `visualEncodings` 内の encoding id。

clickTargetKind:
  Detail panel に渡す scene object kind。

refs:
  insight / atom / context / cover / source / artifact refs。

omissionPolicy:
  preserve_for_top_insight / omittable_background / aggregate_if_large。
```

`visualEncodings` は色だけでなく shape / line / text role を持ち、R16 の color-only 禁止を machine-checkable にする。

### R12. Scene transition は意味のある morph として実装する

単なる再描画ではなく、Atom の位置が scene 間で滑らかに移動する。

```text
Overview
  -> Site / Cover:
     Atom cluster expands into context patches.

Site / Cover
  -> Gluing:
     overlaps become visible seams.

Gluing
  -> H^1:
     mismatch seams become cocycle ribbons.

Obstruction
  -> Repair:
     forbidden cages remain, repair cuts appear.

Boundary
  -> Source:
     fogged regions collapse into missing / omitted source refs.
```

この morph は数学的 claim ではなく、ユーザーの理解補助である。`animationPurpose: "navigation"` として扱う。

### R13. Click target は Atom だけでなく scene object に拡張する

クリック可能対象:

```text
- Atom
- context patch
- cover patch
- overlap seam
- cocycle ribbon
- forbidden support cage
- repair candidate cut
- law conflict bridge
- boundary wall
- source node
```

各 object は `userData` に最低限次を持つ。

```json
{
  "kind": "cechMismatchSeam",
  "refs": {
    "atomRefs": [],
    "contextRefs": [],
    "sourceRefs": [],
    "artifactRefs": []
  },
  "detailTitle": "...",
  "detailSummary": "..."
}
```

---

## Core Viewer Scenes

### V1. Overview Constellation

#### ユーザーの問い

```text
このコードベース全体で、まず何を見るべきか?
```

#### Axis mapping

```text
X axis:
  source locality / module neighborhood

Y axis:
  architecture layer or atom family rank

Z axis:
  insight priority / measured severity
```

#### 表示要素

```text
- Top insight beacons
- source cluster
- context cluster
- measured_nonzero support
- not_computed blockers
- unmeasured fog
```

#### Acceptance

Viewer 初期表示はこの scene にする。3D 空間上で一番目立つものは「数が多い Atom」ではなく、「ユーザーが最初に見るべき insight」である。

### V2. Atom Family Space

#### ユーザーの問い

```text
Atom family ごとに、コードベースの意味成分はどう分布しているか?
```

#### Axis mapping

```text
X axis:
  source locality

Y axis:
  atom family
  authority / trust / permission / state / effect / relation / semantic / capability ...

Z axis:
  observation status or evidence strength
```

#### 表示要素

```text
- family bands
- observed / inferred / partial / missing status
- high-priority Atom
- sourceRefCount / objectRefCount based radius
```

#### 目的

ユーザーに「このコードベースはどの意味成分に偏っているか」を見せる。例: permission / trust / effect が密集しているが、contractSpecification が薄い、など。

### V3. Finite Poset Site Scene

#### ユーザーの問い

```text
ArchMap v2 の contexts / covers は、どのような site として観測されているか?
```

#### Axis mapping

```text
X axis:
  source neighborhood

Y axis:
  poset rank
  lower = local / specific
  higher = global / aggregate

Z axis:
  coverage density or context size
```

#### 表示要素

```text
- context nodes
- context regions
- atom membership
- restriction arrows
- cover membership
- uncovered regions
```

#### Interaction

context をクリックすると、その context に属する Atom と source refs を表示する。cover を選択すると、cover に含まれる contexts が patch として点灯する。

### V4. Cover & Gluing Scene

#### ユーザーの問い

```text
局所 context どうしは、どこで貼り合っているか?
どの貼り合わせが壊れているか?
```

#### Axis mapping

```text
X axis:
  context neighborhood / source locality

Y axis:
  context rank / restriction depth

Z axis:
  gluing mismatch intensity
```

#### 視覚文法

```text
Context:
  translucent surface / patch

Overlap:
  seam / lens / shared boundary

Restriction map:
  directed tube / arrow

Successful gluing:
  smooth seam

Mismatch:
  twisted seam / broken seam / red-orange ripple
```

#### 表示要素

```text
- cover patches
- pairwise overlaps
- triple overlaps
- restriction arrows
- mismatch markers
- cocycle representative support
```

#### 重要ルール

この scene は monodromy verdict として表示しない。v0.4.0 では monodromy 系 reading は復活させず、Čech cover-relative gluing の可視化として扱う。

### V5. Čech H^1 Mismatch Scene

#### ユーザーの問い

```text
局所的には合法なのに、全体ではどの mismatch class が残っているか?
```

#### 視覚文法

```text
0-cochains:
  context-local labels / local sections

1-cochains:
  overlap seams on context pairs

cocycle representative:
  closed oriented ribbon

coboundary-explainable part:
  dimmed / flattenable ribbon

nonzero H^1 class:
  persistent glowing loop or seam network
```

#### 表示要素

```text
- H^1 measured_zero / measured_nonzero badge
- cocycle representative
- affected context pairs
- affected atom refs
- source refs
- cover-relative boundary note
```

#### Interaction

H^1 insight をクリックすると、この scene に遷移し、該当する mismatch support だけを表示する。

```text
Click insight:
  GLOBAL_GLUE_MISMATCH_MEASURED

Viewer response:
  - dim unrelated atoms
  - show cover patches
  - draw mismatch seams
  - focus camera on affected context pairs
  - open Evidence Detail
```

### V6. Obstruction / Forbidden Support Scene

#### ユーザーの問い

```text
どの Atom の組み合わせが forbidden support を作っているか?
```

#### 視覚文法

```text
Atom:
  point

Forbidden support:
  red translucent simplex / cage

Obstruction ideal generator:
  labeled support cell

Multiple overlapping supports:
  stacked shards / dense obstruction region
```

#### 表示要素

```text
- minimal forbidden supports
- obstruction ideal generators
- affected laws
- affected atom families
- source refs
```

#### Interaction

forbidden support をクリックすると、support に含まれる Atom、関連 law、source refs を Evidence Detail に表示する。

### V7. Repair Dual Scene

#### ユーザーの問い

```text
どこに触れば、測定済み obstruction support をすべて横切れるか?
```

#### 視覚文法

```text
Forbidden supports:
  red cages

Repair candidate:
  blue / gold cut plane or handle

Essential lower bound:
  minimum number gauge

Candidate alternatives:
  parallel cut sets
```

#### 重要ルール

repair candidate は「自動修復」ではない。UI上でも必ず以下のように表示する。

```text
This is a combinatorial repair candidate.
It is not a semantic refactor guarantee.
```

#### Interaction

repair candidate を選択すると、次を表示する。

```text
- candidate set に含まれる Atom
- intersected forbidden supports
- lower bound
- non-claims
- source refs
```

### V8. Law Conflict / Tor Scene

#### ユーザーの問い

```text
どの law universe 同士が、どの witness 上で構造的に衝突しているか?
```

#### 視覚文法

```text
Left sheet:
  law universe A

Right sheet:
  law universe B

Center:
  common ambient

Conflict class:
  bridge / knot / intersection filament

No common ambient:
  scene is blocked, not empty
```

#### 表示要素

```text
- law pair
- common ambient status
- Tor class support
- witness variables
- context refs
- reason code if not_computed
```

#### Acceptance

common ambient がない場合、衝突が「ない」と表示してはいけない。`not_computed: no_common_ambient` を Blocking scene として表示する。

### V9. Hodge Debt Field Scene

#### ユーザーの問い

```text
アーキテクチャ負債は、どこにどの形で溜まっているか?
```

#### 視覚文法

```text
Exact component:
  flattenable flow

Harmonic component:
  persistent ridge / island

Coexact component:
  local swirl / residual turbulence

Harmonic mass:
  heat / glow intensity

Distance-to-flatness:
  height or contour
```

#### 重要ルール

near-flat を lawful と表示しない。analytic reading は structural verdict ではない。

#### Viewer label

```text
AG internal:
  harmonic mass
  distance-to-flatness
  spectral gap

Viewer label:
  debt mass
  flatness distance
  spectrum landscape
```

ただし stability claim は出さない。

### V10. Period / Stokes Audit Scene

#### ユーザーの問い

```text
周期・境界の accounting は、計測パイプライン内で整合しているか?
```

#### 視覚文法

```text
Cycle:
  closed ribbon

Period value:
  ribbon thickness / side heatmap

Boundary:
  filled surface

Stokes audit:
  pass = sealed surface
  fail = cracked surface and evaluator error
```

#### 表示要素

```text
- cycle basis
- period pairing matrix
- Stokes audit result
- evaluator error if audit mismatch
```

#### 重要ルール

Stokes audit 不一致は計測結果ではなく evaluator 実装バグとして扱う。

### V11. Transfer / Repair Flow Scene

#### ユーザーの問い

```text
修復候補を動かすと、どの support に副作用が伝播しうるか?
```

#### 視覚文法

```text
Repair operation:
  moving handle / path

Support-localized transfer:
  directed flow

Transfer residue:
  residual glow

Wasserstein transfer cost:
  path thickness / cost label
```

#### 重要ルール

transfer reading から「副作用なし」を結論してはいけない。UI label も `No side effect` ではなく `Measured transfer residue` とする。

### V12. Boundary / Assumption Scene

#### ユーザーの問い

```text
どこまでが測定済みで、どこから先は仮定・未測定・計算不能か?
```

#### 視覚文法

```text
checked:
  solid surface

assumed:
  translucent surface

unmeasured:
  fog

unknown:
  grey unresolved region

not_computed:
  blocking wall with reason code

violated:
  red broken boundary
```

#### 表示要素

```text
- checked assumptions
- assumed assumptions
- violated assumptions
- unmeasured supports
- omitted detail counts
- validation failures
```

#### UX

Boundary scene は、ユーザーに不安を与えるためではなく、結論をどの境界内で読めるかを理解させるための scene とする。

### V13. Source Evidence Scene

#### ユーザーの問い

```text
この insight は、最終的にどのコードに接地しているか?
```

#### Axis mapping

```text
X axis:
  path / directory neighborhood

Y axis:
  symbol / file depth

Z axis:
  evidence role
  source / derived / inferred / omitted
```

#### 表示要素

```text
- source files
- symbols
- atom-source links
- insight-source links
- copyable source refs
```

#### UX

source ref は必ずコピー可能にする。

```text
Copy source refs:
src/auth/session.ts:42 validateSession
src/api/middleware.ts:18 requireAuth
```

---

## Viewer Mode Taxonomy

### R14. 既存 view mode を primary / advanced / legacy に分類する

現状の多数の view mode をそのまま横並びにすると、ユーザーは「何を見ればよいか」が分からない。UI 上は次の分類にする。

```text
Primary scenes:
  Overview
  Site / Cover
  Gluing / H^1
  Obstruction
  Repair
  Boundary
  Source

Advanced scenes:
  Atom Family Space
  Law Axes
  Hodge Debt Field
  Spectrum Landscape
  Period / Stokes
  Transfer Flow
  Projection
  Evidence Density

Legacy / compatibility scenes:
  Molecule map
  Density
```

既存の view mode は消さずに、AG v0.4.0 の scene 名へ再配置する。

```text
curvature
  -> Hodge Debt Field

holonomy
  -> Cover path / restriction path view
  ※ monodromy verdict ではない

obstructionLoops
  -> Čech mismatch / obstruction support

spectrum
  -> Hodge spectrum / debt field

flatness
  -> Flatness distance field

aatAxes
  -> Atom Family / Law Axis Space

sources
  -> Source Evidence Scene

risk
  -> Boundary / Assumption Scene
```

---

## Visual Encoding Contract

### R15. 色・形・線・透明度の意味を固定する

Viewer 全体で、visual encoding を統一する。

```text
Color:
  green / teal:
    measured_zero, checked, smooth gluing

  red / ember:
    measured_nonzero, mismatch, obstruction, violated

  yellow / gold:
    assumed, warning, repair candidate

  blue:
    source evidence, navigation, selected support

  violet:
    derived / analytic reading

  grey:
    unknown, unmeasured, omitted

Shape:
  sphere:
    Atom

  translucent patch:
    context / cover element

  ribbon:
    cochain / cocycle / cycle

  cage / simplex:
    forbidden support

  cut / handle:
    repair candidate

  wall / fog:
    boundary / not_computed / unmeasured region

Line:
  thin line:
    ordinary relation

  arrow:
    restriction / transfer direction

  thick glowing line:
    selected insight support

  broken line:
    missing / blocked relation
```

### R16. Color だけに依存しない

すべての重要状態は、色だけでなく label / icon / line style / detail text でも判別できるようにする。

---

## Guided Exploration

### R17. Top Insight から guided tour を開始できる

Top Insight には `Start tour` ボタンを持たせる。

例:

```text
Tour: Global glue mismatch

Step 1:
  Show selected cover patches.

Step 2:
  Show overlap seams.

Step 3:
  Highlight mismatch support.

Step 4:
  Show affected source refs.

Step 5:
  Show repair candidates and boundary.
```

### Tour schema

```json
{
  "tourId": "tour:h1-glue-mismatch:001",
  "title": "Global glue mismatch",
  "insightRefs": ["insight:h1-glue-mismatch:001"],
  "steps": [
    {
      "sceneId": "site-cover",
      "caption": "These contexts form the selected cover.",
      "highlightRefs": { "contextRefs": [] }
    },
    {
      "sceneId": "cech-gluing",
      "caption": "This seam carries the measured mismatch.",
      "highlightRefs": { "contextPairRefs": [], "atomRefs": [] }
    },
    {
      "sceneId": "source-evidence",
      "caption": "These source refs support the measurement.",
      "highlightRefs": { "sourceRefs": [] }
    }
  ]
}
```

Top Insight の `Start tour` は、Insight Card の `tourRefs` または Tour の `insightRefs` で接続する。どちらか一方だけでなく、生成時の validation では相互参照が一致することを確認する。

---

## Action Queue

### R18. Action Queue を “next inspection” と “repair candidate” に分ける

Action Queue は自動修復リストではない。次の2種類に分ける。

```text
next_inspection
  まず見るべき source / atom / context / law。

repair_candidate
  minimal repair hitting set や lower bound に基づく候補。
```

Action item schema:

```json
{
  "id": "action:inspect-h1-support:001",
  "kind": "next_inspection",
  "title": "Inspect H^1 mismatch support",
  "reason": "This support explains the top measured global mismatch.",
  "targetRefs": {
    "sourceRefs": [],
    "atomRefs": [],
    "contextRefs": [],
    "insightRefs": []
  },
  "expectedUserOutcome": "Decide whether the mismatch reflects intended coupling or architecture drift.",
  "nonClaims": [
    "This action does not guarantee a valid repair."
  ]
}
```

### R19. Repair candidates must show lower-bound language

Repair candidate 表示は、必ず「候補」「下界」「自動修復ではない」を明示する。

```text
Minimal repair candidate:
  Touching one of these atom sets intersects all measured forbidden supports.

Lower bound:
  At least 2 independent support changes are required under this profile.

Boundary:
  This is a combinatorial candidate, not a semantic refactor guarantee.
```

---

## Boundary UX

### R20. Boundary を “読める台帳” にする

CBI assumption ledger、coverage gaps、omitted detail は raw JSON のままではなく、次の3分類で表示する。

```text
Checked
  tool が有限検査でき、checked になった仮定。

Assumed
  profile / law-policy / archmap author が宣言した仮定。

Blocking
  violated / missing / no_common_ambient など、結論を not_computed に落としたもの。
```

Viewer では Blocking を常に Decision Bar に表示する。Assumed は Boundary panel に表示する。Checked は詳細折りたたみでよい。

### R21. False clean claim を禁止する

`H^1 measured_zero` であっても、unmeasured / unknown / not_computed が存在する場合、次のような文言は禁止する。

```text
禁止:
  Architecture is clean.
  No architecture issue exists.
  Codebase is lawful.
```

許可:

```text
NO_MEASURED_GLUE_MISMATCH_UNDER_PROFILE
No measured H^1 glue mismatch was found under the selected profile.
Boundary: 2 supports were unmeasured.
```

---

## Accessibility / Usability

### R22. Viewer must be readable without 3D interpretation

3D map は補助であり、唯一の理解手段にしない。同じ情報は Insight Queue / Evidence Detail / Brief で読める必要がある。

Acceptance:

```text
- 3D canvas を見なくても Top 3 insight と source refs が分かる。
- color だけに依存せず、label / icon / text で status が分かる。
- keyboard で Insight Queue を移動できる。
- selected insight の source refs を keyboard でコピーできる。
```

### R23. Large graph degradation を明示する

大規模 codebase では Viewer が省略・集約表示を行ってよい。ただし省略は必ず `omittedDetailCounts` と UI の Omitted Detail に反映する。閾値は Atom 数だけでなく、edge / context membership / cover overlap / scene layer object / label の量も見る。

```text
<= 2k atoms:
  full geometry, ribbons, patches, labels

2k - 10k atoms:
  instanced atom rendering, limited labels, top insight objects only

10k+ atoms:
  aggregated clusters, top insight supports always preserved

50k+ atoms:
  overview cluster mode by default
```

`omittedDetailCounts` は最低限次を object kind 別に持つ。

```text
- omittedAtoms
- omittedEdges
- omittedContextMemberships
- omittedCoverOverlaps
- omittedSceneLayerObjects
- omittedLabels
- omittedSourceRefs
- omittedReasons
```

Top Insight evidence pinning は省略より優先する。ただし pinned objects が device budget を超える場合は、Top Insight ごとに preserved / aggregated / omitted の内訳と reason code を出す。

### R24. Top Insight evidence は省略しない

省略が必要な場合でも、Top Insight に関係する Atom / context / source / seam は省略対象にしない。

```text
Can omit:
  background edges
  low-priority atoms
  non-selected analytic detail
  dense labels

Must not omit:
  selected insight support
  measured_nonzero support
  not_computed blocker
  source refs for top insight
  repair candidate support
```

---

## Validation and Fixtures

### R25. Golden UX fixtures を追加する

既存 v0.4.0 golden fixture に加えて、UX surface の fixture を追加する。

```text
F1. H^1 measured_nonzero
  Expected:
    GLOBAL_GLUE_MISMATCH_MEASURED
    global_glue_mismatch card
    deterministic rankingBasis recorded
    Cover & Gluing scene
    H^1 mismatch ribbon
    scene layer for mismatch seam has refs and encoding
    source/context support shown
    action: inspect mismatch support
    guided tour is linked by insightRefs / tourRefs

F2. H^1 measured_zero with unmeasured support
  Expected:
    NO_MEASURED_GLUE_MISMATCH_UNDER_PROFILE
    boundary digest mentions unmeasured support
    no false “architecture is clean” wording

F3. Repair candidates exist
  Expected:
    minimal_repair_candidate card
    Repair Dual scene
    lower-bound language shown
    auto-fix language absent

F4. Common ambient missing
  Expected:
    policy conflict insight is not produced
    not_computed_blocker card exists
    Law Conflict scene shows blocking reason
    reason: no_common_ambient

F5. Validation failure
  Expected:
    Decision Bar shows blocking validation
    top insight is validation_failure
    measured conclusions are not visually promoted

F6. Boundary assumption ledger
  Expected:
    checked / assumed / blocking are visually separated
    violated assumption causes dependent verdict display to become not_computed

F7. Large graph cluster mode
  Expected:
    top insight support remains visible
    omitted counts are shown by object kind
    pinned top insight support records preserved / aggregated / omitted status
```

---

## Success Metrics

```text
M1. First Answer Time
  ユーザーが Viewer または brief を開いてから 30 秒以内に、
  「何が起きているか」「次に見る場所」を把握できる。

M2. Top Insight Traceability
  Top 3 insight の 100% が verdict / invariant / source refs / boundary に辿れる。

M3. No False Clean Claim
  unmeasured / unknown / not_computed が存在する場合、
  “architecture is clean” 相当の文言を出さない。

M4. Actionability
  measured_nonzero の structural verdict には、
  少なくとも1つの next_inspection action が存在する。

M5. Viewer Comprehension
  3D map を操作しなくても、brief と report panel だけで
  conclusion / top insights / source refs / boundary が読める。

M6. Boundary Visibility
  violated assumption または validation failure がある場合、
  Decision Bar に blocking state が表示される。

M7. Rich Scene Meaningfulness
  各 primary scene が userQuestion と axisMapping を持ち、
  X/Y/Z の意味が UI 上で確認できる。
```

---

## Acceptance Criteria

- `archsig-insight-report/v1` が生成される。
- `archsig-insight-brief.md` が独立 artifact として生成され、manifest / viewer artifact links から参照できる。
- Insight Card schema が定義され、Top Findings / Action Queue / Boundary Digest が typed surface になる。
- Insight ranking は v0.4.0 では deterministic な固定 ranking とし、`rankingBasis` が report と card に記録される。
- Summary / brief の先頭に `Read this first` block が出る。
- Top 3 insight に `whyItMatters` と evidence refs が存在する。
- Viewer に Decision Bar / Insight Queue / Evidence Detail が存在する。
- Viewer の各 mode / scene が `userQuestion` と `axisMapping` を持つ。
- Viewer scene の `layers` / `visualEncodings` が、scene object、refs、click target、omission policy を表す。
- X/Y/Z の意味が Viewer 上に表示される。
- Overview scene で Top Insight が空間上の beacon として表示される。
- Site / Cover scene で contexts、covers、restriction arrows が表示される。
- Cover & Gluing scene で overlap seam と gluing mismatch が表示される。
- H^1 scene で cocycle representative support が ribbon / seam として表示される。
- Obstruction scene で minimal forbidden supports が cage / simplex として表示される。
- Repair scene で minimal repair hitting set が cut / handle として表示される。
- Repair scene には「自動修復ではない」non-claim が常に表示される。
- LawConflict scene で common ambient がない場合、空表示ではなく blocking reason が表示される。
- Hodge Debt scene では harmonic mass / distance-to-flatness が analytic reading として表示され、lawful / unlawful に昇格しない。
- Boundary scene で checked / assumed / unknown / unmeasured / not_computed / violated が視覚的に区別される。
- Source Evidence scene で source refs をコピーできる。
- Top Insight から guided tour を開始でき、Insight Card の `tourRefs` と Tour の `insightRefs` が相互に検証される。
- 3D canvas を操作しなくても、Detail panel と Insight Queue で同じ意味が読める。
- 10k atoms 以上では cluster / aggregation に劣化し、Top Insight evidence は保持される。
- theorem-candidate reading は structural conclusion として表示されない。
- monodromy verdict は復活させず、holonomy-like 表示は restriction path / cover path の exploratory view として扱う。
- `H^1 measured_zero + unmeasured support` の fixture で、false clean claim が出ない。
- `not_computed` の reason code が Viewer / brief に表示される。
- 大規模 graph で省略が起きた場合、object kind 別の omitted counts が Viewer と brief に出る。
- 既存 `archsig-measurement-packet/v1` の意味論、5値 verdict discipline、assumption ledger を変更しない。

---

## Implementation Plan

### Phase 1. Artifact projection

```text
- archsig-insight-report/v1 schema を追加する。
- measurement packet / summary から Insight Card を生成する pure function を追加する。
- deterministic ranking と rankingBasis 生成を追加する。
- claim validation を追加する。
- archsig-insight-brief.md を生成する。
- run manifest / artifact links へ archsig-insight-brief.md を追加する。
- LLM handoff block を生成する。
```

### Phase 2. Viewer information architecture

```text
- Decision Bar を追加する。
- Existing Top Findings を Insight Queue に変更する。
- Evidence Detail を What / Why / Where / Boundary に統一する。
- Source refs copy block を追加する。
- Boundary panel を Checked / Assumed / Blocking に分ける。
```

### Phase 3. Visual Scene Contract

```text
- viewerVisualScenes schema を追加する。
- 各 scene に userQuestion / axisMapping / layers / visualEncodings / boundaryRefs を持たせる。
- scene layer の refs / clickTargetKind / omissionPolicy を validation する。
- 既存 view mode を scene taxonomy に再配置する。
- axis-hud を scene contract から描画する。
- legend を scene ごとに切り替える。
```

### Phase 4. Gluing visualization

```text
- context patch を translucent geometry として表示する。
- cover overlap seam を line / ribbon として表示する。
- restriction arrow を表示する。
- H^1 mismatch support を glowing seam として表示する。
- cocycle representative の refs を Detail panel に接続する。
```

### Phase 5. Obstruction / Repair visualization

```text
- forbidden support を cage / simplex として表示する。
- repair hitting set を cut / handle として表示する。
- repair non-claims を Detail panel と brief に表示する。
```

### Phase 6. Guided tour

```text
- Insight Card から scene transition を起動する。
- Insight Card の tourRefs と Tour の insightRefs の相互参照を検証する。
- camera fit / dim unrelated / highlight refs を実装する。
- tour steps を artifact に記録する。
```

### Phase 7. Large graph strategy

```text
- cluster mode を追加する。
- top insight support pinning を実装する。
- object kind 別 omitted counts を Boundary scene と Report に表示する。
```

### Phase 8. Fixtures and regression tests

```text
- UX golden fixtures F1-F7 を追加する。
- false clean claim regression test を追加する。
- repair candidate wording test を追加する。
- not_computed blocker display test を追加する。
- theorem-candidate promotion ban test を追加する。
```

---

## Open Questions

```text
Q1. source refs の editor jump 形式は VS Code / JetBrains / plain text のどれを先に出すか?

Q2. Viewer の primary mode 名は英語固定にするか、日本語 / 英語切替を持つか?

Q3. LLM handoff block は FieldSig handoff と統合するか、ArchSig 単独 artifact にするか?

Q4. context patch / overlap seam の geometry は、artifact 側で座標 hints を持つか、Viewer 側で deterministic layout するか?

Q5. H^1 cocycle representative の ribbon 表示に、orientation / coefficient value をどこまで出すか?

Q6. Large graph cluster mode の threshold は固定値にするか、device capability を見て調整するか?
```

---

## Completion Definition

この PRD は、ユーザーが Viewer または brief を見たときに、次を自力で答えられる状態をもって完了とする。

```text
- 今回の ArchSig は何を結論したか?
- その結論はどの profile / boundary の内側か?
- コードベースは AAT 代数幾何によって、どの意味空間として可視化されているか?
- 局所 context と全体の貼り合わせは、どこで一致し、どこで壊れているか?
- 最初に見るべき source / atom / context はどこか?
- それはなぜ重要か?
- 次の調査または修復候補は何か?
- 何を結論してはいけないか?
```

v0.4.0 core の completion が「測れること」だとすれば、本 PRD の completion は **測定結果が、ユーザーにとって見える構造・読める境界・使えるインサイトになること**である。
