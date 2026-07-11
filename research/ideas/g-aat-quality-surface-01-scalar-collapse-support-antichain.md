---
status: picked
goal: G-aat-quality-surface-01
candidate_type: orientation
capability_category: ridge-fold, atom-supported-quality-geometry, repair-potential, multi-axis-signature
expected_base_score: 80
expected_evidence_multiplier: 2.0
expected_final_score: 160
evidence_stage: proved-in-research
origin: G1-quality-surface-cycle-2
tags: [quality-surface, scalar-collapse, reading-fold, atom-support, repair]
created: 2026-06-20
cycle: 2
lean: proved-in-research
---

# Scalar-collapse separation by support antichains

## 主張

有限 certificate calculus において、certificate tuple の `selectedViolationCount` への scalar projection と
同じ verdict を持つ二つの certificate が、
異なる selected minimal atom support antichain と異なる repair hitting requirement を持つ例を構成できる。
従って scalar reading は atom-supported certificate geometry の support / repair frontier を復元できない。

## 候補種別

`orientation`

## 依拠

- `research/goals/G-aat-quality-surface-01.md` の `G-aat-quality-surface-01`
- `docs/note/aat_quality_surface.md` の reading fold、scalar-collapse counterexample、Atom support
- cycle 1 の `Formal/AG/Research/QualitySurface/SupportHitting.lean`

## 非自明性

単なる同点例ではなく、同じ scalar fiber 内で selected minimal support antichain と repair hitting number が変わることを固定する。
これにより、reading fold は UI 上の projection artifact ではなく、certificate geometry から scalar reading への quotient
で失われる構造情報として現れる。

## 数学的興味

cycle 1 は local repair が minimal support family 全体を hit する必要を示した。cycle 2 は、その repair frontier が
scalar reading では見えないことを有限反例として示す。Quality Surface を単一高さの曲面として読むのではなく、
support antichain と repair requirement を保持する certificate geometry として読む理由を与える。

## GOAL への前進

scalar-collapse counterexample を埋め、ridge-fold / atom-supported-quality-geometry / repair-potential / multi-axis-signature のカテゴリを増やす。
first phase portfolio の support-local repair theorem に続く二つ目の必須 frontier になる。

## SCORE 見込み

- `score_reason`: Lean で finite reading fold と support / repair frontier の分離を証明できれば、scalar-collapse counterexample として強い。
- `dullness_risk`: reading を恣意的に定数関数にするだけでは弱い。reading は certificate tuple の `selectedViolationCount` への scalar projection として明示し、同じ reading / verdict の下で support antichain と hitting number が異なることを固定する。
- `proof_or_evidence_plan`: finite atom type と two-certificate universe を置く。一方は support antichain `{a}`、hitting number 1、もう一方は support antichain `{b}`, `{c}`、hitting number 2 を持つ。certificate tuple から `selectedViolationCount` を scalar reading として射影し、同じ scalar reading と同じ verdict を持つこと、support family と hitting number が異なること、各 support family が nonempty antichain であること、repair hitting requirement が selected support family の branch shape と対応すること、したがって scalar reading が support / repair frontier に faithful でないことを Lean Research 側で証明する。

## CS / SWE への帰結

同じ品質点や violation count を持つ二つの判定でも、修正が hit すべき atom family と repair frontier は変わりうる。
そのため Quality Surface の UI は scalar reading だけでなく、背後の support antichain と repair requirement を保持する必要がある。

## 証明・根拠の見込み

Lean では `ToyCertificate` を二つ用意し、full certificate tuple に
`selectedViolationCount`、`verdict`、`selectedSupportFamily`、`repairHittingRequirement`
を持たせる。`scalarReading` は `selectedViolationCount` への projection として定義し、
`scalarReading c₁ = scalarReading c₂` と `verdict c₁ = verdict c₂` を示す。同時に、
`supportFamily c₁ ≠ supportFamily c₂`、`repairHittingNumber c₁ = 1`、
`repairHittingNumber c₂ = 2`、`repairHittingNumber c₁ ≠ repairHittingNumber c₂` を証明する。
加えて `supportFamily` が nonempty antichain であることと、`repairHittingNumber` が selected
support family の one-branch / two-branch shape に対応することを固定する。
最後に、それらをまとめた `scalarReading_not_faithful_to_supportRepair` という finite witness theorem を置く。

## 審判メモ

- 厳密性:
- 研究価値:
- repo 全体価値:

## 関連

- `Minimal-support hitting theorem for local repair`
- `Finite profile-curvature detector on a square cell`
- `Finite trace-locus example distinguishing zero from unmeasured`

## 進捗ログ

- 2026-06-20: cycle 2 の G1 候補生成から審判対象として作成。
- 2026-06-20: G2 三審判後に picked。A の revise を受け、scalar reading を `selectedViolationCount` への projection として固定した。
- 2026-06-20: G3 axiom check / 形式化品質監査 pass。G4 SCORE 監査 confirm: base 80, multiplier 2.0, penalty 0, final 160。
