---
status: picked
goal: G-sft-conway-01
exploration_role: unifier
candidate_type: bridge
capability_category:
  - restricted-span
  - finite-quotient-shadow
  - quotient-style-receiver
  - conway-obstruction
  - finite-witness
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
rival_advantage: CODEOWNERS / org-network analysis can expose owner mismatch, but not a finite quotient-style class whose zero/nonzero condition is tied to explicit owner-uniform family boundary generators.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
origin: G-sft-conway-01 Cycle 17
tags: [conway, owner-uniform, quotient, restricted-span]
created: 2026-07-04
---

# Owner-uniform family quotient receiver

## 主張

Cycle 15/16 の owner-uniform family obstruction を、有限 `ZMod 2` receiver 上の quotient-style class として固定する。
owner-uniform coherent support witness を explicit boundary generator として扱い、その generator がある family では
selected defect が boundary subgroup に入り、generator がない restricted two-fork family では selected finite receiver 上で
defect が非零に残る。

これは selected finite quotient-style receiver であり、true sheaf `H^1`、arbitrary-cover naturality、functorial quotient は主張しない。

## 候補種別

`bridge`

## 依拠

- `Formal/AG/Research/SFT/ConwayBoundaryQuotient.lean`
- `Formal/AG/Research/SFT/ConwayBoundaryGenerator.lean`
- `Formal/AG/Research/SFT/ConwayRestrictedCoherentFamily.lean`
- `Formal/AG/Research/SFT/ConwayOwnerUniformSubfamilyDescent.lean`
- `Formal/AG/Research/SFT/ConwayOwnerUniformFamilyQuotient.lean`

## 非自明性

Cycle 15/16 は owner-uniform support の predicate receiver を固定した。この候補は、その predicate をそのまま
boundary subgroup に入れるのではなく、`OwnerUniformFamilyBoundaryGenerator` という explicit provenance を
置き、selected defect の vanishing / nonvanishing と接続する。full quotient object や sheaf cohomology へは
進まないが、owner-uniform obstruction を quotient-style receiver の語彙に載せる。

## 数学的興味

local subfamily support と full-family owner-uniform support failure の差を、有限 coefficient class として残せる。
これは future true quotient / `H^1` へ進む前に、どの obstruction が selected finite receiver 上で非零に残るかを
明確にする。

## GOAL への前進

finite quotient-style receiver frontier へ、overclaim しない finite shadow を追加する。Cycle 17 の成果は
「owner-uniform support failure が finite quotient-style receiver で非零に読める」という bridge である。

## ライバルに対する有効性

Team Topologies、CODEOWNERS、org-network analysis、AI review は owner mismatch を指摘できる。
この候補の差分は、owner-uniform support の有無を explicit generator boundary と selected class の
zero/nonzero theorem として保存する点にある。

## SCORE 見込み

- `score_reason`: Cycle 15/16 の restricted owner-uniform obstruction を finite quotient-style receiver に上げる。
- `dullness_risk`: boundary subgroup を `if owner-uniform support then top else bot` と直接定義すると Cycle 3 の再包装になる。explicit generator provenance と zero/nonzero theorem を残す必要がある。
- `proof_or_evidence_plan`: `OwnerUniformFamilyBoundaryGenerator`、`OwnerUniformFamilyBoundarySubgroup`、`OwnerUniformFamilyClassVanishes`、`OwnerUniformFamilyNonzeroClass` を定義し、vanishing iff generator / support、restricted two-fork nonzero、singleton subfamilies zero を証明した。
- `threshold_fit`: Cycle 17 は Issue #2962 の残り 260 に対して +110 見込みで、threshold 到達には次 cycle が必要である。
- `g3_quality_condition`: `OwnerUniformFamilyBoundarySubgroup` は support predicate の `if/top/bot` 化ではなく、explicit generator 由来の `AddSubgroup.closure` で定義する。

## Target Theorem 寄与

- `target_theorem`: not-applicable
- `target_support_node`: not-applicable
- `target_progress`: not-applicable
- `proof_obligation_delta`: not-applicable
- `target_completion_role`: not-applicable

## CS / SWE への帰結

共有 owner-uniform witness がある family は finite receiver 上で zero、局所 support があっても full-family witness がない
family は nonzero として区別できる。

## 証明・根拠の見込み

Lean で次を証明した。

- `OwnerUniformFamilyDefect`
- `OwnerUniformFamilyBoundaryGenerator`
- `OwnerUniformFamilyBoundarySubgroup`
- `OwnerUniformFamilyClassVanishes`
- `OwnerUniformFamilyNonzeroClass`
- `ownerUniformFamilyClass_vanishes_iff_support`
- `restrictedTwoForkFamily_ownerUniformFamilyClass_nonzero`
- `restrictedApiSingletonFamily_ownerUniformFamilyClass_vanishes`
- `restrictedDbSingletonFamily_ownerUniformFamilyClass_vanishes`
- `selectedOwnerUniformFamilyQuotientPackage`

## 審判メモ

- 厳密性: pass。`lake env lean`、module build、`FormalAGResearch`、full `lake build` が通過。
- 研究価値: revise accept。G2 は base 55 / final 110 を保守採点として推奨。
- repo 全体価値: pass。owner-uniform local/global gap を finite quotient-style receiver に統合した。
- ライバル比較: pass。local mismatch visualization ではなく、same receiver 上の singleton zero / full nonzero theorem を返す。

## 関連

- `research/ideas/g-sft-conway-01-owner-uniform-restricted-family.md`
- `research/ideas/g-sft-conway-01-owner-uniform-subfamily-descent.md`

## 進捗ログ

- 2026-07-04: Cycle 17 候補として作成。
- 2026-07-04: `Formal/AG/Research/SFT/ConwayOwnerUniformFamilyQuotient.lean` で Lean 証明を追加し、+110 として採点。
