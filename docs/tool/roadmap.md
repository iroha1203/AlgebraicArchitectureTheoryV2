# Tooling Roadmap

Roadmap は mutable planning である。ここには phase、拡張候補、標準化 target を置く。
数学本文や stable schema の中に進捗管理を混ぜない。

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

これらは empirical hypothesis であり、Lean theorem ではない。現行の case-study output は
`docs/empirical/` に置き、旧 evaluation query は archive の
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

## Standardization targets

- artifact schema naming
- claim boundary vocabulary
- measurement boundary vocabulary
- non-conclusion preservation
- schema compatibility policy
- example fixture set
- report consumer contract
