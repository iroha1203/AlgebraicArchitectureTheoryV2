# Tooling Roadmap

Roadmap は mutable planning である。ここには phase、拡張候補、標準化 target を置く。
数学本文や stable schema の中に進捗管理を混ぜない。

## Roadmap management

tooling の進捗、実装候補、未実装 gap はこの文書で管理する。
第一級理論本文は `docs/aat/mathematical_theory/README.md`,
`docs/sft/aat_interface.md`, `docs/sft/software_field_theory.md` に置き、
ここには tool artifact、CLI、CI、schema、fixture、validator、empirical / operational
workflow の計画だけを書く。

進捗を記録するときは、次を分ける。

| 種別 | 読み |
| --- | --- |
| implemented pipeline | 実入力から artifact を生成する CLI / workflow がある。 |
| schema + validator | artifact schema、fixture、validator はあるが、実入力からの推論は限定的。 |
| advisory report | reviewer / CI が読む補助情報であり、formal claim ではない。 |
| empirical / operational | dataset、calibration、feedback 用 artifact。因果 theorem ではない。 |
| planned gap | 第一級文書が要求するが、まだ実装されていない tooling 能力。 |

## Current status snapshot

2026-05-10 時点の ArchSig は、AAT diagnostic / governance tooling としては
MVP を越えている。SFT forecast engine としても、schema / validator に加えて
Markdown PRD / Spec / Issue / AI proposal から `ForecastConeSkeleton` と
`ConsequenceEnvelope` を生成する bounded pipeline が実装済みである。

| 領域 | 現在地 | 主な gap |
| --- | --- | --- |
| Sig0 extraction | Lean / Python import graph、policy、runtime edge evidence を Sig0 にできる。 | call graph、data dependency、framework semantics は adapter boundary。 |
| AIR / Feature Extension Report | signature、coverage、claim boundary、obstruction witness、theorem precondition を report にできる。 | 任意 invariant 全体の自動判定ではない。 |
| PR / CI governance | signature diff、policy decision、PR comment、baseline suppression がある。 | organization ごとの policy calibration と運用 feedback は継続課題。 |
| AI-generated change boundary | AI session metadata、generated patch provenance、human review boundary、formal claim block を扱う。 | proposal support 全体の制御や shortcut distribution の推定は未完成。 |
| Empirical feedback | PR history、feature dataset、outcome linkage、B10 operational artifacts がある。SFT calibration / benchmark protocol は `docs/tool/sft_calibration_benchmark.md` で定義する。 | 実 dataset での継続 calibration と hypothesis refresh の運用。 |
| Architecture dynamics | PR force、trajectory、dynamics metrics、field snapshot、operation proposal log の schema / validator と bounded SFT forecast pipeline がある。GitHub Issue JSON / AI proposal JSON adapter は supplied JSON artifact の正規化として実装済み。 | 実 dataset での calibration と framework semantics adapter。 |
| Lifecycle decision | repair / migration / contraction / deletion を SFT lifecycle governance の decision surface として定義する。 | decision artifact schema、fixture、validator、実 dataset calibration は未実装。market / staffing success prediction は扱わない。 |

## Tooling capability surface and remaining gaps

ArchSig の現状を、実行可能な command / artifact / workflow と remaining gaps に分ける。
これは website 向けの公開導線ではなく、tooling roadmap 上の capability boundary である。

| Surface | Current tooling capability | Remaining gaps |
| --- | --- | --- |
| ArchSig Core | `scan`、`validate`、`snapshot`、`signature-diff` による Sig0 と revision diff。Lean / Python import graph、policy JSON、runtime edge evidence を明示入力として扱う。 | call graph、data dependency、dynamic import、plugin loading、framework convention は adapter boundary。完全な architecture model 抽出は主張しない。 |
| ArchSig Review | AIR、validate-air、theorem-check、Feature Extension Report、policy decision、PR comment、baseline suppression。review / CI の補助 report として読む。 | organization policy calibration、review practice tuning、任意 invariant の完全判定は未完成。formal claim promotion は Lean theorem refs と precondition が揃う場合だけ。 |
| FieldSig SFT | Markdown PRD / Spec / Issue / AI proposal、GitHub Issue JSON、AI proposal JSON から `ArtifactDescriptor`、`OperationSupportEstimate`、`ForecastConeSkeleton`、`ConsequenceEnvelope`、validation report を生成する B13 pipeline。`docs/tool/software_field_reconstruction_protocol.md` は trace-grounded `SoftwareFieldEstimate` の evidence boundary を定義し、`docs/tool/sft_calibration_benchmark.md` は forecast item と observed refs の照合 protocol を定義し、`docs/tool/ai_proposal_governance.md` は AI proposal governance の allowed support / shortcut witness / review feedback boundary を定義する。 | real dataset calibration、framework semantics adapter。forecast、AI policy compliance、review pass は probability、causal proof、architecture lawfulness、global safety を結論しない。 |
| FieldSig Operational | PR history dataset、Feature Extension dataset、outcome linkage、B10 daily ledger、calibration review、team threshold、ownership boundary、repair adoption、incident correlation、hypothesis refresh artifacts。`SoftwareFieldEstimate` 用 trace inventory は unavailable / private / unknown remainder を保持する。 | 実運用 dataset の継続収集、confounder 管理、incident / rollback / MTTR との組織別接続。 |
| SFT Lifecycle | `LifecycleDecisionModel` / `EndOfLifeDecision` は repair、migration、contraction、deletion の selected inputs と non-conclusions を整理する planned decision surface。 | `lifecycle-decision-report-v0` 相当の schema / command は未実装。人間の意図、market success、project management recommendation は結論しない。 |

## Phase B0: AIR and boundary

- AIR v0 を固定する。
- claim level、measurement boundary、non-conclusions を schema に入れる。
- measured zero と unmeasured を validator で分ける。

## Phase B1: Static Feature Extension Report

- static extractor、policy input、signature diff、AIR、Feature Extension Report を接続する。
- hidden interaction、forbidden static edge、coverage gap を witness として出す。

## Phase B2: Runtime integration

- runtime edge evidence を artifact として受ける。
- protected / unprotected / forbidden runtime path を分ける。
- runtime completeness を non-conclusion として保持する。

## Phase B3: Semantic integration

- semantic diagram、observation result、nonfillability witness を扱う。
- semantic measured zero と unmeasured を分ける。

## Phase B4: Generated-change provenance

- ai session metadata、generated patch、human review boundary を AIR に入れる。
- generated change を formal claim に昇格しない guardrail を検査する。

## Phase B5: Repair and synthesis prototype

- obstruction witness から repair candidate を提示する。
- no-solution certificate と synthesis constraint の artifact boundary を固定する。

## Phase B6: Empirical validation

- Feature Extension Report と outcome dataset を接続する。
- review cost、incident scope、rollback、MTTR などとの correlation を empirical claim として扱う。

Phase B6 の最小仮説は次である。

| ID | Hypothesis |
| --- | --- |
| H1 | `non_split` feature extension は review cost や follow-up fix の増加と相関する。 |
| H2 | hidden interaction witness は semantic defect や rollback と相関する。 |
| H3 | runtime exposure witness は incident scope や MTTR と相関する。 |
| H4 | split extension と判定された PR は後続変更で再利用・置換・移行しやすい。 |
| H5 | Feature Extension Report は architecture review の合意形成を速める。 |

これらは empirical hypothesis であり、Lean theorem ではない。現行の仮説管理は
`docs/aat/proof_obligations.md` と GitHub Issues で行い、旧 evaluation query は archive の
`docs/archive/2026-05-09-first-class-docs/design/b6_empirical_hypothesis_evaluation.md` に残す。

## Phase B7: PR review integration

- signature diff、policy decision、PR comment summary を CI / review flow に接続する。
- organization policy に基づく pass / warn / fail / advisory を出す。

## Phase B8: Extractor / policy ecosystem

- framework adapter、custom rule plugin、law policy template、measurement unit registry を整備する。
- extractor completeness を主張せず、adapter boundary を schema に残す。

## Phase B9: Schema standardization and compatibility

- schema catalog を固定する。
- migration で field mapping、deprecated fields、new assumptions、non-conclusions を保持する。

## Phase B10: Operational feedback loop

- report outcome daily ledger、calibration record、team threshold policy、ownership boundary monitor、
  repair adoption record、incident correlation monitor、hypothesis refresh cycle を扱う。
- operational feedback は empirical / process artifact として扱い、causal theorem へ昇格しない。

## Phase B11: Architecture Dynamics tooling

- architecture field snapshot、operation proposal log、PR force report、signature trajectory report、
  architecture dynamics metrics report を扱う。
- probabilistic operation distribution は empirical reading とし、finite support / bounded script の
  formal core と分ける。
- 現状は schema + validator / fixture 中心であり、実入力からの forecast 推論は次 phase に分ける。

## Phase B12: SFT forecasting MVP

SFT 側の次の主対象は、ArchSig-SFT Forecaster である。
これは AAT theorem を強めるものではなく、選択された boundary の下で
artifact action、operation support、forecast boundary、missing invariant を report する
tooling layer として実装する。

最小 pipeline は次である。

```text
PRD / Spec / Issue / AI proposal
  -> ArtifactDescriptor
  -> OperationSupportEstimate
  -> bounded ForecastCone skeleton
  -> ConsequenceEnvelope report
  -> review / CI / issue decomposition recommendation
```

最小出力は次を含める。

- action class candidates
- candidate operation families
- affected architecture regions
- comparable signature axes
- expected axis delta ranges
- selected obstruction witness candidates
- missing invariant / missing boundary items
- typed boundary failures
- reviewer next actions
- theorem boundary items
- forecast non-conclusions
- unknown / unmodeled remainder

初期実装では、probability や causal forecast は出さない。
まず finite support、bounded horizon、selected operation family、source refs、
measurement boundary を持つ level 3 相当の cone skeleton を作る。
calibration 済みの weighting や field update は B10 / B11 artifact と接続した後に扱う。

現在は `artifact-descriptor-v0`、`operation-support-estimate-v0`、
`forecast-cone-skeleton-v0`、`consequence-envelope-report-v0`、
`sft-review-summary-v0`、`forecast-calibration-hook-v0` が schema + validator として実装済みである。
`OperationSupportEstimate` は descriptor refs、candidate operation families、policy
constraints、support disposition、governance action refs、known forbidden support、unknown remainder、confidence / evidence
boundary を保持する。`ForecastConeSkeleton` は finite support と bounded horizon に相対化した
path class candidates、gluing evidence、governance intervention、typed boundary failure を保持する。`ConsequenceEnvelope` は affected architecture
regions、comparable signature axes、expected axis delta ranges、selected obstruction
witness candidates、missing boundary、typed boundary failure、reviewer action、theorem boundary、review / CI recommendation を
report projection として保持する。この projection は一つ以上の bounded cone skeleton
から reviewer-facing envelope を作る片方向写像であり、path classes、affected regions、
comparable axes、unknown remainder、forecast non-conclusions を落とさず引き継ぐ。
`SftReviewSummary` は `ConsequenceEnvelope` から opened futures、closed futures、
boundary failures、next actions、LLM judgement contract を evidence refs と boundary refs 付きで
生成する deterministic projection である。
`ForecastCalibrationHook` は forecast item refs と B10 / B11 の observed artifact refs を
対応付ける。いずれも accepted PR history、actual future support、global policy safety、
future trajectory safety、forecast correctness、causal proof、cone family の一意復元、
Lean theorem claim、merge approval は主張しない。

B12.5 の calibration hook は、`docs/tool/sft_calibration_benchmark.md` の protocol で読む。
そこでは calibration set、held-out validation set、prospective set を分け、review mediation と
AI shortcut detection を別 benchmark として扱う。matched / unmatched / unavailable /
private / notComparable を区別し、false positive / false negative review は empirical policy
input として保存する。real dataset がない段階では forecast quality、probability weighting、
causal proof、global risk reduction を結論しない。

## Phase B14: AI proposal governance

AI-mediated software evolution は、B13 の AI proposal adapter 出力と B10 / B11 の
review / CI / operational feedback を接続して扱う。最小設計は
`docs/tool/ai_proposal_governance.md` で管理する。

```text
prompt / policy boundary
  + AI proposal JSON / patch refs
  + AAT theorem boundary
  + SFT forecast artifacts
  -> allowed / forbidden / unknown operation support
  -> shortcut witness report
  -> review / CI mediation record
  -> posterior field update note
  -> calibration / benchmark linkage
```

この phase の出力は reviewer-facing governance artifact であり、AI agent の一般的安全性、
prompt / policy compliance からの architecture lawfulness、review pass / CI pass からの
semantic preservation、または autonomous coding policy の本番 correctness を主張しない。

## Phase B15: Lifecycle decision surface

Lifecycle decision は、repair、migration、contraction、deletion を同じ比較面に置く
SFT governance artifact として扱う。目的は project management の自動推薦ではなく、
選択された architecture signature trajectory、runtime / incident evidence、
ownership / staffing boundary、`ConsequenceEnvelope` family を束ね、intervention ごとの
known support、obstruction witness、missing evidence、unknown remainder を読めるようにすること
である。

最小 input / output boundary は次である。

```text
ArchitectureSignature trajectory
  + ConsequenceEnvelope family
  + runtime / incident evidence refs
  + ownership / staffing boundary refs
  + migration / repair support refs
  -> lifecycle decision report
  -> intervention comparison
  -> missing boundary / calibration hook
```

最小 report は、repair、migration、contraction、deletion それぞれについて selected inputs、
affected regions、field capacity impact、runtime risk boundary、ownership boundary、
calibration refs、non-conclusions を保持する。schema、fixture、validator、CLI はまだない。
将来実装する場合でも、human intention、market success、staffing availability の予測、
future trajectory safety、global risk reduction、forecast correctness は non-conclusions として
保持する。

## Phase B16: Closed-loop SFT workbench

Closed-loop SFT workbench は、B10 operational feedback、B12 / B13 SFT forecast artifact、
AI proposal governance、lifecycle decision surface、future adapters、calibration hook を
一つの review cycle に束ねる deployed workflow の最小設計である。目的は自動判断ではなく、
入力、bounded forecast、governance intervention、observed outcome、calibration input を
同じ artifact graph として追跡できるようにすることである。

最小 input / output boundary は次である。

```text
PRD / design memo / Issue / AI proposal refs
  + codebase / ArchitectureSignature snapshot refs
  + review / CI / PR / incident / ownership trace refs
  + AI agent policy refs
  -> SFT forecast artifact bundle
  -> ConsequenceEnvelope / governance / lifecycle projections
  -> review / CI / issue decomposition intervention refs
  -> observed outcome refs
  -> ForecastCalibrationHook + B10 operational feedback refs
  -> field update note / hypothesis refresh input
```

### B16 dependency map

| 依存 | workbench での役割 | 境界 |
| --- | --- | --- |
| B10 operational feedback | outcome ledger、calibration review、threshold、ownership、incident correlation、hypothesis refresh を保存する。 | correlation と operational observation であり、causal theorem ではない。 |
| B12 / B13 SFT forecast | descriptor、support estimate、cone skeleton、envelope report を生成する。 | bounded forecast artifact であり、probability や forecast correctness ではない。 |
| calibration hook | forecast item refs と observed refs を対応付ける。 | match / unmatched / unavailable / private / notComparable を保存するだけで、自動採点しない。 |
| future adapters | GitHub Issue、AI proposal、framework semantics、runtime / incident trace を正規化する。 | supplied evidence adapter であり、private field 復元や extractor completeness を主張しない。 |
| governance / lifecycle projections | review / CI / issue decomposition、AI proposal constraint、repair / migration / deletion comparison を出す。 | reviewer-facing intervention surface であり、自動 governance correctness ではない。 |

### B16 phase plan

| Phase | 成果物 | 次の実装 Issue 候補 |
| --- | --- | --- |
| B16.0 artifact inventory | B10 / B12 / B13 / governance / lifecycle artifact refs と missing adapters の一覧。 | workbench run manifest schema を作る。 |
| B16.1 offline workbench bundle | 1 件の PRD / Issue / AI proposal から forecast bundle、governance projection、feedback refs を手動結合する。 | `workbench-run-manifest-v0` fixture / validator。 |
| B16.2 review-loop dry run | envelope と governance projection を review / CI checklist、issue decomposition refs に接続する。 | review intervention record schema。 |
| B16.3 calibration join | observed refs を `ForecastCalibrationHook` と B10 artifact に接続する。 | calibration join report / benchmark fixture。 |
| B16.4 deployed pilot | scheduler、team threshold、ownership / incident monitor と接続する。 | prospective dataset と organization-specific calibration policy。 |

B16 は real organization deployment、automatic governance correctness、forecast quality、
AI safety、global risk reduction を完了条件にしない。これらは実 dataset と prospective
validation が揃った後の empirical research task として扱う。

### B12 milestones

| Milestone | 目標 |
| --- | --- |
| B12.1 ArtifactDescriptor | PRD / Issue / AI proposal の action class、scope、source refs、missing evidence を schema 化する。schema + validator 実装済み。 |
| B12.2 OperationSupportEstimate | candidate operation family、policy constraints、known forbidden support、unknown remainder を出す。schema + validator 実装済み。 |
| B12.3 ForecastCone skeleton | finite support と bounded horizon に相対化した path class skeleton を保持する。schema + validator 実装済み。 |
| B12.4 ConsequenceEnvelope report | signature axis、obstruction candidate、missing boundary、review / CI recommendation をまとめる。schema + validator 実装済み。 |
| B12.5 Calibration hook | observed PR / review / CI / outcome artifact と forecast item を対応付ける hook を置く。schema + validator 実装済み。 |

## Phase B13: SFT forecaster implemented pipeline

B12 では `ArtifactDescriptor` から `ForecastCalibrationHook` までの artifact
schema、fixture、validator を固定した。B13 ではこれを implemented pipeline に進め、
PRD / Spec / Issue / AI proposal などの実入力から B12 artifact 群を生成する。

目的は、SFT の forecast を一点予測や causal theorem として扱うことではない。
実 artifact から、選択された source refs、operation support、finite support、
bounded horizon、forecast boundary、unknown remainder、non-conclusions を保持した
tooling estimate を生成し、review / CI / issue decomposition が読める
`ConsequenceEnvelope` へ接続することである。

最小 pipeline は次である。

```text
real PRD / Spec / Issue / AI proposal
  -> ArtifactDescriptor builder
  -> OperationSupportEstimate generator
  -> ForecastConeSkeleton generator
  -> ConsequenceEnvelope generator
  -> end-to-end sft-forecast command
```

この phase は B12 の schema + validator を利用する。新しい theorem claim は作らず、
tooling output は `empirical hypothesis / tooling validation` として扱う。
特に次を non-conclusions として保持する。

- generated descriptor は ground truth architecture object ではない。
- operation support estimate は accepted PR history や actual future support ではない。
- forecast cone skeleton は probability、global risk reduction、trajectory-level safety を主張しない。
- consequence envelope は causal artifact action の一意同定や Lean theorem proof ではない。
- SFT review summary は LLM / reviewer judgement の入力であり、最終 judgement や merge approval ではない。
- end-to-end command の成功は extractor completeness や forecast correctness を意味しない。

### B13 milestones

| Issue | Milestone | 目標 |
| --- | --- | --- |
| #741 | B13 parent | ArchSig-SFT Forecaster を実入力 pipeline に接続する親 Issue。 |
| #746 | B13.1 ArtifactDescriptor builder | Markdown PRD / Spec と、supplied GitHub Issue JSON / AI proposal JSON から `artifact-descriptor-v0` を生成する CLI builder は実装済み。JSON adapter は authenticated fetch や model evaluation を行わない。 |
| #744 | B13.2 OperationSupportEstimate generator | `artifact-descriptor-v0` から `operation-support-estimate-v0` を生成する。 |
| #743 | B13.3 ForecastConeSkeleton generator | `operation-support-estimate-v0` と bounded horizon config から `forecast-cone-skeleton-v0` を生成する CLI generator は実装済み。 |
| #742 | B13.4 ConsequenceEnvelope generator | `forecast-cone-skeleton-v0` から reviewer / CI / issue decomposition が読める `consequence-envelope-report-v0` を生成する CLI generator は実装済み。 |
| #1182 | SFT review summary | `consequence-envelope-report-v0` から `sft-review-summary-v0` を生成し、opened futures / closed futures / boundary failures / next actions を reviewer-facing に射影する CLI は実装済み。 |
| #745 | B13.5 end-to-end sft-forecast | 中間 artifact、final `ConsequenceEnvelope`、`SftReviewSummary` を生成する `sft-forecast` command と Coupon PRD fixture は実装済み。 |

## Standardization targets

- artifact schema naming
- claim boundary vocabulary
- measurement boundary vocabulary
- non-conclusion preservation
- schema compatibility policy
- example fixture set
- report consumer contract
- forecaster input / output contract
- forecast boundary vocabulary


## FieldSig boundary

FieldSig lives in `tools/fieldsig` and owns SFT software evolution measurement artifacts: `software-field-measurement-v0`, forecast / intent artifacts, workflow evidence refs, operational feedback, governance candidates, unknown remainder, and calibration hooks. ArchSig remains the AAT structural telemetry generator and passes evidence through JSON artifact refs. FieldSig validation is not a Lean proof, forecast correctness proof, probability claim, causal theorem, or replacement for CI, tests, and human review.
