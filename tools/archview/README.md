# ArchView

ArchViewは、ArchMapに記録されたAtom / Context / Coverを3Dのarchitecture geometryとして構成し、
コードベース理解、ArchSig分析結果の表示、改善箇所の特定を一つの操作空間でつなぐ
Atom-native Architecture Atlasである。

## Product responsibilities

### Architecture

ArchMapを直接読み、次を表示する。

- Coverと、それに含まれるContext
- Context membershipと`restrictsTo`
- exact `subject` equalityによる表示上のAtom grouping
- Atomの`kind / subject / axis / predicate / object`
- Atomから`sources`の`path / symbol / line`への接続

ArchitectureはArchSig analysisなしで成立する。subject groupingは新しいarchitectural factを生成しない。

### Analysis

既存ArchSig run artifactを、Architectureと同じAtom geometry上へoptional overlayとして重ねる。

- local observationとmeasured support
- agreement / mismatch / unmeasured / not computed
- section、gluing、H1 support、obstruction support
- comparison、gate decision、明示されたrepair target

別の3D worldを作らず、camera、selection、semantic zoom、InspectorをArchitectureと共有する。
overlayのidentityまたはdigestが現在のArchMapと一致しない場合はfail-closedで拒否する。

### Improve

findingからAtomとsource refsを経由して、確認対象を次の4種類に分ける。

| Type | Meaning |
| --- | --- |
| Direct evidence | findingの直接根拠となったsource |
| Boundary participant | mismatchやrestrictionの一方を構成するsource |
| Candidate change point | ArchSigまたはRepairPlanが明示した変更候補 |
| Validated hypothetical repair | targetと選択obstructionを結ぶchecked contractが明示したrepair。現行comparisonのrun-local resultとは分けて扱う |

source解決精度はmethod / symbol / line / file / unresolvedとして表示する。
method metadataが明示されないsourceはsymbol名からmethodを推測せず、
`METHOD GRANULARITY UNAVAILABLE`を表示する。
evidence locationを自動的にcandidate change pointへ昇格しない。

## Input contract

### Required architecture base

`archmap/v0.5.4`の既存フィールドを直接使う。

```text
sources
atoms
contexts
covers
```

新しいauthoritative world modelは作らない。表示高速化のためのindexや座標はruntime stateであり、
永続contractではない。

### Optional analysis overlay

利用可能な既存artifactだけを読む。

```text
normalized-archmap.json
archsig-analysis-summary.json
archsig-insight-report.json
archsig-measurement-packet.json
archsig-comparison-report.json
archsig-gate-report.json
archsig-run-manifest.json
archsig-atom-viewer-data.json
```

normalized Atom IDからsource Atom IDへの対応には`normalized-archmap.json`を使う。
文字列類似や空間上の近さから対応を推測しない。

## Geometry and interaction

semantic zoomは次の5段階とする。

```text
Cover → Context → Subject → Atom → Source
```

- Contextはlocal architecture chartとして描く。
- `restrictsTo`だけをdirection付きrestrictionとして描く。
- 複数Contextへの明示membershipはshared supportとして描く。
- section valueが供給された場合だけfiber pointまたはsheetを描く。
- measured mismatchが供給された場合だけbroken sheetを描く。
- explicit H1 supportがある場合だけnon-closing ribbonを描く。
- minimality evidenceがある場合だけobstruction circuitと呼ぶ。
- repair dataがある場合だけrepair morphismを描く。

camera orbit、pan、zoom、Top / Isometric / Front view、focus、resetを提供する。
camera回転は許可するが、測定されていないdirectionやflowをglyph animationで表現しない。

## Fidelity

すべてのvisual elementはprovenanceを持つ。

```text
ArchMap atom / context / cover
ArchSig artifact row
source ref
visual channel origin
```

visual channelは次に区分する。

- `measured`: supplied measurementが直接駆動する。
- `derived`: supplied dataから決定論的に導出する。
- `layout`: 読みやすさのための配置であり、diagnostic meaningを持たない。
- `decoration`: interactionまたは演出であり、measurementを運ばない。

禁止事項:

- ArchMapにないAtom、Context、relation、sourceを描く。
- random layoutや文字列類似からarchitecture relationを生成する。
- scalar fieldなしでterrainやcontourを描く。
- direction dataなしでflowを描く。
- repair dataなしでrepair arrowを描く。
- unmeasuredをmeasured zeroまたはsafeとして表示する。
- unresolved refを無言で捨てる。

## UI model

トップレベルは`Architecture / Analysis / Improve`の3モードに限定する。
同じgeometry、camera、selection、semantic zoom、Inspectorを共有する。

一般表示では平易な用語を使い、AAT用語とraw conclusion codeはtechnical detailsで確認できる。
3DとOutline / Table表示のselectionを同期し、keyboard操作、high contrast、reduced motionへ対応する。

## Current implementation

現在の`archview.html`は再構築前のno-build Three.js viewerである。
`archsig-atom-viewer-data.json`、summary、manifest、gate report、
`archview-sequence/v0.5.4`を読み、ArchSigが供給したanalysis geometryを表示する。

ゼロベース再構築中のapplicationは`rebuild/`にある。Paper AtlasのTop Bar、
Scope Explorer、3D Atlas、Inspector、source drawer、Three.js camera、
Architecture / Analysis / Improveの共通mode stateを持つ。`archmap/v0.5.4`を直接検証し、
選択Coverに含まれるContext plate、`restrictsTo` connector、shared support、
exact subject group、Atom kind別glyphを決定論的に配置する。
Cover → Context → Subject → Atom → Sourceのselectionとbreadcrumb、structured search、
各levelのInspectorから、明示されたsource親参照を辿って`path / symbol / line`へ到達できる。
restrictionとshared supportはScope Explorerまたは3D上で選択でき、導出元とvisual channelをInspectorへ表示する。
未解決source refはAtomを消さず、入力警告と`UNRESOLVED` source targetとして表示する。
source本文・snippetは読み込まない。

Top Barの`Load ArchSig run`は既存analyze run directoryを任意入力として受け取り、manifest、
normalized ArchMap、measurement packet、summary、insight reportを一括検証する。全artifactの
中核artifactの`schema / runId / toolVersion / inputDigests / profileRef`、現在のArchMap digest、
normalized ID対応を検査し、compatibleなrunだけを受理する。comparison reportとgate reportが同じdirectoryに
ある場合は既存shapeを検査し、現在のrunおよびmeasurement packetへのdigest bindingを照合する。不正JSON、schema不一致、
identity不一致、未解決IDはそれぞれ表示し、analysisを部分的に描画しない。ArchMapを読み直すとanalysisは
通常の未読込状態へ戻る。

```bash
python3 -m http.server 8000 --directory tools/archview/rebuild
```

`http://localhost:8000/`を開く。既定では小規模なpayment vertical-slice fixtureを読む。
`?archmap=<同一originのJSON path>`で別のArchMapを指定でき、Top Barの`Load ArchMap`から
ローカルJSONも読み込める。`?analysis=<同一originのrun directory path>`またはTop Barの
`Load ArchSig run`からanalysisを追加できる。browser testは次で実行する。

```bash
node tools/archview/foundation_browser_e2e.cjs tools/archview/rebuild
```

Analysis / Improveではfindingを選択すると、local facts、shared relations、global result、
source evidenceの4段階説明を表示し、同じgeometry上のsupportを強調する。
source targetはpath → symbol → line → supporting Atomの順に辿れる。
comparisonとgateは対応artifactが入力された場合だけ表示し、明示されたrepair targetと
evidence locationを別の状態として扱う。comparisonのrecord transitionはrun-local resultとして表示し、
targetと選択obstructionを結ぶchecked contractなしにvalidated repairへ昇格しない。

現行viewer-data handoffは移行中のruntime contractであり、ArchViewのproduct identityではない。

## Local preview

現行実装はArchSigの出力ディレクトリと同じ場所から配信する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_ag_v052.json \
  --out-dir .tmp/archview-preview
cp tools/archview/archview.html .tmp/archview-preview/
python3 -m http.server 8000 --directory .tmp/archview-preview
```

`http://localhost:8000/archview.html`を開く。

## Verification

ArchViewの検証は`tools/archview/`が所有するbrowser / UI testで行う。
ArchSigのRust testからArchViewのUI、scene、内部関数を検査しない。

現行HTMLではlocal previewを開き、読み込んだartifact名、report pane、source landing、
console error、empty / malformed / digest mismatchの明示拒否を確認する。再構築時に
Architecture / Analysis / Improveのacceptance testを`tools/archview/`配下へ追加する。

再構築applicationのbrowser testは、ArchMapの正常・empty・malformed・unresolved入力、
WebGL / bootstrap failure、3 modeとcamera、5段階selection、structured search、
表示factのArchMap追跡、同一入力でのlayout/source順序の決定性、Architecture理解5問、
Analysis / Improveのbrowser probeを検査する。参加者task testの実施結果は対応Issue / PRへ記録する。

```bash
git diff --check
```

## Release

現行ArchSig release archiveは次を同梱する。

```text
archview/
  archview.html
  README.md
```

現行HTMLはThree.js CDNを使うため、ローカルHTTP server経由で開く。
