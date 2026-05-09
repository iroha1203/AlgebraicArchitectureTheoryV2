# Repair Suggestion

Repair suggestion は、obstruction witness から候補 operation を提示する artifact である。
repair を実行したこと、または repair が theorem として成立したことを意味しない。

## Repair rule registry

`repair-rule-v0` は registry 側の rule である。特定 report 上の source witness や
coverage gap への trace は持たない。

```text
repair-rule-v0 :=
  repairRuleId
  + targetWitnessKind
  + proposedOperation
  + requiredPreconditions
  + expectedEffect
  + preservedInvariants
  + possibleSideEffects
  + proofObligationRefs
  + patchStrategy
  + confidence
  + relativeTo
  + nonConclusions
```

## Feature report repair suggestion

Feature Extension Report に出る repair suggestion は、registry rule を report context へ
適用した output である。こちらは source witness、coverage gap、traceability を持つ。

```text
FeatureReportRepairSuggestion :=
  suggestionId
  + repairRuleId?
  + sourceWitnessRefs
  + sourceCoverageGapRefs
  + targetWitnessKind
  + proposedOperation
  + requiredPreconditions
  + expectedEffect
  + preservedInvariants
  + possibleSideEffects
  + proofObligationRefs
  + patchStrategy
  + confidence
  + traceability
  + nonConclusions
```

## Proposed operations

```text
split
isolate
contract
replace
protect
migrate
manual
```

`repair` は selected obstruction を減らす候補であり、全 signature axis を改善するとは限らない。

## Expected effects

```text
remove
reduce
localize
translate
transfer
```

`transfer` は、obstruction が消えずに別の layer や axis へ移る可能性を示す。

## Side-effect boundary

repair suggestion は、possible side effects と non-conclusions を保持する。

```text
possible side effects:
  new runtime exposure
  semantic behavior change
  migration cost
  compatibility break
  complexity transfer
```

side effect が未評価なら、`unmeasured` として保持する。

## Patch strategy

```text
manual
assisted
generated
```

generated patch の場合も、human review boundary と provenance を失わない。
