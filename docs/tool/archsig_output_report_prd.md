# ArchSig Output / Viewer PRD

この PRD は、ArchSig `analyze` の出力を、LLM 向け summary、人間向け Atom Viewer、
必要時だけ保存する raw artifact へ分離するための要求を定義する。

現行 `analyze` は、validation report、`archsig-analysis-packet.json`、
`archsig-analysis-detail-index.json`、`llm-interpretation-packet.json` を固定で出力する。
この形は、分析の再現性と FieldSig handoff には有効だが、通常利用では大きい packet / detail
index がストレージ容量を食い、ユーザーが最初に読むべき出力も分かりにくい。

中心方針は次である。

```text
ArchMap + LawPolicy
  -> ArchSig analyze
  -> LLM-readable summary JSON
  -> Atom Viewer data projection
  -> optional raw artifacts for evidence store / FieldSig handoff
```

ArchSig は analysis packet を捨てるわけではない。packet は bounded current AAT structural
state の evidence store であり、FieldSig handoff の契約でもある。ただし、通常の人間レビューや
LLM 解釈では、packet を常に保存・閲覧することを前提にしない。

## 要求

### R0. 出力 contract を三層に分ける

ArchSig は、出力を次の三層として扱わなければならない。

- **summary**: LLM が最初に読む structured JSON。
- **atom viewer**: release bundle に同梱された固定 HTML app と、run ごとに生成される
  viewer data projection。上段に 3D Atom visualization、下段に分析結果 report pane を持つ。
- **raw artifacts**: analysis packet、detail index、LLM interpretation packet、必要な sidecar。

この分離は責務の分離である。

- summary は、短く安定した schema を持つ LLM reading surface である。
- atom viewer は、ArchMap / LawPolicy / ArchSig output を固定 HTML app で 3D visual
  projection と分析 report pane の両方から読む human exploration surface である。
- raw artifacts は、詳細 evidence、schema validation、再分析、FieldSig handoff のための
  storage surface である。

ArchSig の通常 workflow は、人間や LLM が raw packet JSON を直接読むことを first path にしない。

### R1. raw artifact 保存を opt-in にする

`analyze` は、通常モードで大きな raw artifact を保存しない。

通常モードで保存する artifact は、少なくとも次である。

- `archsig-analysis-summary.json`
- `archsig-atom-viewer-data.json`
- `archsig-run-manifest.json`
- `archmap-validation.json`
- `law-policy-validation.json`
- `archsig-analysis-validation.json`

次の artifact は、明示オプションを指定した場合だけ保存する。

- `archsig-analysis-packet.json`
- `archsig-analysis-detail-index.json`
- `llm-interpretation-packet.json`

想定 CLI は次である。

```bash
archsig analyze \
  --archmap .archsig/archmap.json \
  --law-policy .archsig/law-policy.json \
  --out-dir .archsig/analyze
```

```bash
archsig analyze \
  --archmap .archsig/archmap.json \
  --law-policy .archsig/law-policy.json \
  --out-dir .archsig/analyze \
  --emit-raw-artifacts
```

`--emit-raw-artifacts` の名前は実装時に `--artifact-retention full` のような enum 型 option に
置き換えてもよい。ただし、通常利用で raw packet が暗黙保存されないことを仕様として固定する。

Viewer data 生成は通常 workflow の一部である。固定 viewer app は raw packet 全体をブラウザへ
渡さず、デフォルト生成される軽量な viewer data projection を読む。

### R2. summary を LLM-readable output として再定義する

`analysis-summary` は、人間と LLM の両用 surface ではなく、主に LLM-readable structured output
として定義する。

summary は次を満たさなければならない。

- 安定した JSON schema を持つ。
- `verdict`、`qualityMeasurement`、`measurementStatusSummary`、`dominantFindings`、
  `actionQueue`、`coverageGapSummary`、`measurementBasis`、`metadata` を上位に置く。
- 文章量よりも、短い bounded string、stable id、source refs、detail refs を優先する。
- raw packet が保存されていなくても、summary 単体で LLM が主要診断を解釈できる。
- raw packet が保存されている場合は、`detailRefs` / `packetRefs` / manifest refs から詳細へ
  到達できる。

summary は natural-language report ではない。LLM が後段で説明、issue、review comment、
repair plan へ翻訳するための structured artifact である。

### R3. 人間向け report を Atom Viewer に統合する

ArchSig は、人間向けの first-class surface を固定 `archsig-atom-viewer.html` に統合する。
独立した `archsig-report.html` は生成しない。

Atom Viewer は次の二段 layout を持つ。

- **3D pane**: Atom distribution、molecule boundary、law axis、coverage / obstruction overlay を
  WebGPU-backed Three.js scene として表示する。
- **report pane**: verdict、top findings、action queue、coverage boundary、artifact list を
  人間向けに表示する。

report pane は viewer data と summary を読む。raw packet が保存されていない場合も、viewer data
と summary だけで主要診断を読めなければならない。raw packet が保存されている場合は、保存済み
artifact への相対リンクを表示してよい。

### R4. Atom Viewer report pane の初期 layout を定義する

Atom Viewer の report pane は、少なくとも次の section を持つ。

#### Overview

ArchMap、LawPolicy、実行時刻、schema version、validation status、summary verdict、
measurement status count を表示する。

#### Top Findings

`dominantFindings`、重要な law-axis pressure、spectrum hotspot、bridge pressure、
architectural hole、nonzero monodromy / boundary residual などを、重要度順に表示する。

#### Action Queue

人間が次に見るべき source refs、coverage blocker、repair candidate、operation precondition を
短いカードまたは table として表示する。

#### Coverage And Boundaries

coverage gap、exactness assumption、projection loss、unmeasured evidence、non-conclusions を
まとめて表示する。

#### Artifacts

保存された artifact を表示する。

- summary JSON
- validation reports
- raw packet / detail index / LLM interpretation packet
- run manifest

保存されていない artifact については、未生成であることと、再実行時に指定すべき option を表示する。

### R5. report pane は source ref と detail ref を読みやすくする

report pane は、AAT reading の抽象語だけで終わらず、reviewer が source-level 確認へ進める
構造を持つ。

少なくとも次を表示する。

- finding id
- claim / reading
- why it matters
- measured status
- severity または priority
- source refs
- observation refs
- coverage blockers
- next validation steps
- detail refs

source refs が多い場合は、代表 sample と count を表示する。全 ref の再掲は report の責務ではない。
raw detail が必要な場合は、optional raw artifacts へ進む。

### R6. run manifest を導入する

`analyze` は、出力 directory に `archsig-run-manifest.json` を保存する。

manifest は、少なくとも次を記録する。

- schema version
- command name
- ArchMap input path
- LawPolicy input path
- output mode
- generated artifact list
- omitted artifact list
- raw artifact retention setting
- validation result summary
- summary path
- atom viewer app path if available
- atom viewer data path if generated
- raw packet path if generated
- detail index path if generated

manifest は、Atom Viewer と LLM summary の bridge である。Atom Viewer は manifest を元に、
どの artifact が保存され、どれが opt-in で省略されたかを report pane に明示できる。

### R7. Atom Viewer を bundle 同梱の WebGPU-backed static HTML app として定義する

ArchSig は、任意の human visual analysis surface として、release bundle に固定の
`archsig-atom-viewer.html` を同梱する。

Atom Viewer は、ユーザーがブラウザで固定 HTML app を開き、`archsig-atom-viewer-data.json`
などの viewer data を読み込むことで、ArchMap、LawPolicy、ArchSig analysis result を 3D 空間へ
投影する viewer である。Atom distribution、molecule boundary、law-relative reading、
coverage gap、repair focus を探索できる。さらに同じ画面の下段 report pane で、分析結果、
coverage boundary、次アクション、artifact 状態を読める。

Atom Viewer は次を満たさなければならない。

- Three.js を使い、WebGPU を優先する。
- WebGPU が使えない環境では、実装可能なら WebGL fallback を用意する。
- Three.js runtime は CDN から読み込むことを基本とする。
- release bundle は固定 viewer HTML と viewer static assets を含む。Three.js runtime の同梱は
  必須ではない。
- offline / air-gapped 利用が必要な場合は、local Three.js fallback を追加できる設計にする。
- run ごとに `archsig-atom-viewer.html` を生成しない。
- viewer data は file picker、同一 directory の既定ファイル、または drag-and-drop で読み込める。
- viewer は 3D pane と report pane を同じ page に持つ。
- viewer は analysis engine ではなく、既存 output の visual projection である。
- viewer は source truth、theorem metric、FieldSig forecast の代替ではない。

Viewer の入力は、ブラウザが直接 raw packet を読むのではなく、run ごとに生成された
`archsig-atom-viewer-data.json` とする。

### R8. Atom Viewer data projection を定義する

大きな repository では `archsig-analysis-packet.json` が 100MB 級になりうる。ブラウザに raw
packet を読ませると、parse time、memory、layout computation、GC pause が viewer UX を壊す。

そのため、Atom Viewer は `archsig-atom-viewer-data-v0` という軽量 projection artifact を読む。

viewer data は少なくとも次を持つ。

- schema version
- source artifact refs
- layout settings
- atom nodes
- molecule groups
- law axis overlays
- boundary / coverage overlays
- obstruction / signature overlays
- selected ArchSig analysis overlays
- report pane sections
- source ref samples
- omitted detail counts
- truncation / sampling policy

viewer data は raw packet のコピーではない。Atom、molecule、overlay、edge、label、色、サイズ、
report pane の要約、source sample、detail ref だけを含む。

### R9. Atom Viewer の初期 visual mapping を定義する

初期 viewer は、AAT 的な意味を失わない範囲で単純な 3D mapping を採用する。

- point: Atom observation
- cluster / hull: molecule または computed molecule reading
- edge: molecule membership、semantic relation、source / observation relation
- color: law-relative status、coverage status、measured / blocked / unmeasured
- size: support count、obstruction contribution、review priority
- halo: hotspot、coverage gap、nonzero monodromy、boundary residual
- layer toggle: LawPolicy axis、obstruction circuit、signature axis、spectrum hotspot、
  bridge pressure、homotopy hole、repair candidate

3D 距離は theorem metric ではない。layout は AAT concept を読むための visual projection であり、
数学的埋め込みの証明ではない。

### R10. Atom Viewer は大規模 repository 向けに制限を持つ

Viewer data generator は、ブラウザが扱えるサイズへ出力を制御しなければならない。

少なくとも次の制御を持つ。

- maximum atom nodes
- maximum edges
- maximum labels
- maximum source ref samples per node / overlay
- maximum overlay items per layer
- top-N priority selection
- molecule / subsystem aggregation
- omitted count and reason
- optional focus filter

大きな ArchMap では、全 Atom を 3D に出すことを成功条件にしない。成功条件は、重要な分布、
boundary、molecule、obstruction、coverage gap、repair focus をブラウザで探索できるサイズへ
bounded に投影することである。

raw packet や detail index が保存されている場合、viewer は detail refs を表示してよい。ただし、
viewer 内で 100MB 級 packet を parse して深掘りすることを要求しない。

### R11. FieldSig handoff は raw artifact opt-in として残す

FieldSig は引き続き `archsig-analysis-packet-v0` を bounded current AAT structural state として読む。
したがって、FieldSig handoff を行う workflow では raw packet 保存が必要である。

ArchSig docs と CLI help は、次を明記しなければならない。

- 通常の ArchSig review では summary と Atom Viewer の report pane を読む。
- FieldSig handoff、詳細 evidence store、packet validation fixture 更新では
  `--emit-raw-artifacts` を使う。
- raw ArchMap を FieldSig forecast truth として読ませない。

### R12. Atom Viewer は schema claim を広げない

Atom Viewer は、新しい分析 claim を発明しない。

viewer は summary と packet から読める事実を、人間が読みやすい順番と視覚表現に変換する。
viewer data generator と viewer app は、次をしてはならない。

- coverage gap を measured zero として表示する。
- validation failure を visual polish で隠す。
- raw packet が保存されていないのに detail が存在するかのようにリンクする。
- ArchSig analysis を merge safety、global architecture truth、Lean theorem discharge として
  表示する。
- 3D layout 上の近さを、AAT theorem、semantic equivalence、causal relation として表示する。

### R13. docs、skills、tests を同時に更新する

この変更は CLI artifact contract を変えるため、実装時には次を合わせて更新する。

- `tools/archsig/docs/commands.md`
- `tools/archsig/README.md`
- `docs/tool/README.md`
- `docs/tool/llm_native_e2e_workflow.md`
- `tools/archsig/skills/archsig-reader`
- `tools/archsig/tests/cli.rs`
- 必要な fixtures / snapshots

tests は少なくとも次を固定する。

- `analyze` 通常モードは summary、manifest、validation reports を出力する。
- `analyze` 通常モードは viewer data を出力する。
- `analyze` 通常モードは raw packet、detail index、LLM interpretation packet を保存しない。
- `analyze --emit-raw-artifacts` は raw packet、detail index、LLM interpretation packet を保存する。
- release bundle は固定の `archsig-atom-viewer.html` を含む。
- Atom Viewer は raw packet を HTML 内へ埋め込まない。
- Atom Viewer data は node / edge / overlay / report pane / omitted count を持つ。
- Atom Viewer は CDN 版 Three.js を読み込める。
- offline fallback を実装する場合、CDN なしでも viewer を起動できる。
- Atom Viewer report pane は verdict、top findings、action queue、coverage boundary、artifact list を含む。
- manifest は generated / omitted artifact を正しく記録する。
- validation failure 時も、可能な範囲で summary / manifest / viewer data が生成され、
  failure status が report pane に表示される。

## 非目標

- 独立した `archsig-report.html` を生成すること。
- `analyze` が run ごとに Atom Viewer HTML を生成すること。
- Atom Viewer が raw packet 全体をブラウザで読むこと。
- 3D layout を AAT theorem metric として扱うこと。
- viewer data generator が新しい analysis engine になること。
- raw packet を廃止すること。
- FieldSig handoff contract を summary や viewer data に置き換えること。
- viewer report pane を merge approval / rejection decision にすること。
- viewer を website manual の代替にすること。

## 実装順

1. `analysis-summary` の責務を LLM-readable structured output として docs に固定する。
2. `archsig-run-manifest-v0` の schema / builder を追加する。
3. `archsig-atom-viewer-data-v0` の schema / builder を追加する。
4. release bundle に同梱する Three.js ベースの固定 `archsig-atom-viewer.html` app を追加する。
5. viewer app に上段 3D pane と下段 report pane を実装する。
6. `analyze` 通常モードを summary / viewer data / manifest first に変更する。
7. `--emit-raw-artifacts` を追加し、既存 packet / detail-index / LLM interpretation 保存を opt-in にする。
8. CLI tests と fixtures を更新する。
9. README、command guide、E2E docs、skills の reading order を更新する。

## 成功条件

- 通常の `archsig analyze` が、LLM に読ませる summary、Atom Viewer data、manifest を直接生成する。
- 大きな packet / detail-index は、明示オプションなしでは保存されない。
- raw artifact を保存しなくても、Atom Viewer report pane は主要診断、coverage boundary、
  次アクションを読める。
- raw artifact を保存した場合、Atom Viewer report pane と manifest から packet / detail index へ
  辿れる。
- 固定 Atom Viewer app は release bundle に含まれ、ブラウザは raw packet ではなく軽量 viewer data
  を読む。
- Atom Viewer は Atom 分布、molecule grouping、law axis overlay、coverage / obstruction /
  repair focus を探索でき、同じ画面で分析結果 report pane を読める。
- 100MB 級 packet を前提にしても、viewer data は bounded な node / edge / overlay projection として
  生成される。
- FieldSig handoff に必要な `archsig-analysis-packet-v0` contract は維持される。
- 出力 contract が docs、CLI help、tests、skills で一致する。
