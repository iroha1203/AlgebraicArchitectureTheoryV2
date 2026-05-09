# Tooling Roadmap

Roadmap は mutable planning である。ここには phase、拡張候補、標準化 target を置く。
数学本文や stable schema の中に進捗管理を混ぜない。

## Roadmap management

tooling の進捗、実装候補、未実装 gap はこの文書で管理する。
第一級理論本文は `docs/aat/mathematical_theory.md`,
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
MVP を越えている。一方で、SFT forecast engine としては schema と validator が先行しており、
PRD / Issue / AI proposal から `ForecastCone` や `ConsequenceEnvelope` を生成する
pipeline は未完成である。

| 領域 | 現在地 | 主な gap |
| --- | --- | --- |
| Sig0 extraction | Lean / Python import graph、policy、runtime edge evidence を Sig0 にできる。 | call graph、data dependency、framework semantics は adapter boundary。 |
| AIR / Feature Extension Report | signature、coverage、claim boundary、obstruction witness、theorem precondition を report にできる。 | 任意 invariant 全体の自動判定ではない。 |
| PR / CI governance | signature diff、policy decision、PR comment、baseline suppression がある。 | organization ごとの policy calibration と運用 feedback は継続課題。 |
| AI-generated change boundary | AI session metadata、generated patch provenance、human review boundary、formal claim block を扱う。 | proposal support 全体の制御や shortcut distribution の推定は未完成。 |
| Empirical feedback | PR history、feature dataset、outcome linkage、B10 operational artifacts がある。 | 実 dataset での calibration と hypothesis refresh の運用。 |
| Architecture dynamics | PR force、trajectory、dynamics metrics、field snapshot、operation proposal log の schema / validator がある。 | 実 artifact から bounded forecast を生成する forecaster。 |

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
- theorem boundary items
- forecast non-conclusions
- unknown / unmodeled remainder

初期実装では、probability や causal forecast は出さない。
まず finite support、bounded horizon、selected operation family、source refs、
measurement boundary を持つ level 3 相当の cone skeleton を作る。
calibration 済みの weighting や field update は B10 / B11 artifact と接続した後に扱う。

現在は `artifact-descriptor-v0`、`operation-support-estimate-v0`、
`forecast-cone-skeleton-v0`、`consequence-envelope-report-v0`、
`forecast-calibration-hook-v0` が schema + validator として実装済みである。
`OperationSupportEstimate` は descriptor refs、candidate operation families、policy
constraints、known forbidden support、unknown remainder、confidence / evidence
boundary を保持する。`ForecastConeSkeleton` は finite support と bounded horizon に相対化した
path class candidates を保持する。`ConsequenceEnvelope` は affected architecture
regions、comparable signature axes、expected axis delta ranges、selected obstruction
witness candidates、missing boundary、theorem boundary、review / CI recommendation を
report projection として保持する。`ForecastCalibrationHook` は forecast item refs と
B10 / B11 の observed artifact refs を対応付ける。いずれも accepted PR history、actual
future support、global policy safety、future trajectory safety、forecast correctness、
causal proof、Lean theorem claim は主張しない。

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
- end-to-end command の成功は extractor completeness や forecast correctness を意味しない。

### B13 milestones

| Issue | Milestone | 目標 |
| --- | --- | --- |
| #741 | B13 parent | ArchSig-SFT Forecaster を実入力 pipeline に接続する親 Issue。 |
| #746 | B13.1 ArtifactDescriptor builder | Markdown PRD / Spec から `artifact-descriptor-v0` を生成する CLI builder は実装済み。GitHub Issue JSON / AI proposal JSON は今後の拡張候補。 |
| #744 | B13.2 OperationSupportEstimate generator | `artifact-descriptor-v0` から `operation-support-estimate-v0` を生成する。 |
| #743 | B13.3 ForecastConeSkeleton generator | `operation-support-estimate-v0` と bounded horizon config から `forecast-cone-skeleton-v0` を生成する CLI generator は実装済み。 |
| #742 | B13.4 ConsequenceEnvelope generator | `forecast-cone-skeleton-v0` から reviewer / CI / issue decomposition が読める `consequence-envelope-report-v0` を生成する CLI generator は実装済み。 |
| #745 | B13.5 end-to-end sft-forecast | 中間 artifact と final `ConsequenceEnvelope` を生成する `sft-forecast` command と Coupon PRD fixture を追加する。 |

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
