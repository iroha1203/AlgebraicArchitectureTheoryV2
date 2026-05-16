# Reports

Reports は AIR、Signature artifact、policy、runtime evidence、semantic evidence、
theorem precondition check を読んで、人間と automation が扱える summary を作る。

## Feature Extension Report

```text
feature-extension-report-v0 :=
  schemaVersion
  + schemaCompatibility?
  + input
  + architectureId
  + revision
  + feature
  + reviewSummary
  + architectureSummary
  + runtimeSummary
  + interpretedExtension
  + generatedPatchSummary
  + splitStatus
  + preservedInvariants
  + changedInvariants
  + introducedObstructionWitnesses
  + eliminatedObstructionWitnesses
  + complexityTransferCandidates
  + semanticPathSummary
  + theoremPackageRefs
  + theoremPreconditionSummary
  + coverageGaps
  + theoremPreconditionChecks
  + dischargedAssumptions
  + undischargedAssumptions
  + unsupportedConstructs
  + repairSuggestions
  + empiricalAnnotations
  + nonConclusions
```

Feature Extension Report の中心は、feature addition が selected universe で split と読めるか、
split しないならどの obstruction witness があるかである。

## Obstruction Witness

```text
obstruction-witness-v0 :=
  witnessId
  + layer
  + kind
  + extensionRole
  + extensionClassification
  + components
  + edges
  + paths
  + diagrams
  + operation?
  + evidence
  + theoremReference?
  + claimLevel
  + claimClassification
  + measurementBoundary
  + nonConclusions
  + repairCandidates
```

obstruction witness は error message ではなく、repair、classification、no-solution、
complexity transfer、coverage gap に接続するための artifact である。

## Architecture Drift Ledger

```text
architecture-drift-ledger-v0 :=
  ledgerEntryId
  + observedAt
  + architectureId
  + revisionRef?
  + subjectRef
  + witnessFingerprint?
  + policyRef?
  + aggregationWindow
  + source
  + metricId
  + layer
  + measuredValue?
  + measurementBoundary
  + evidenceRefs
  + confidence
  + status
  + suppression?
  + repairCandidates
  + linkedWitnessRefs
  + linkedClaimRefs
  + nonConclusions
```

drift ledger は、日次 scan、scheduled scan、manual review、incident review などから
obstruction や metric drift を蓄積する。

## Policy Decision Report

```text
policy-decision-report-v0 :=
  inputReports
  + organizationPolicy
  + decision
  + blockingReasons
  + warningReasons
  + advisoryReasons
  + suppressedFindings
  + nonConclusions
```

policy decision は organization policy に相対化される。数学的 lawfulness そのものではない。

## PR Comment Summary

PR comment summary は report の読みやすい projection である。
source artifact ではなく presentation artifact として扱う。

```text
pr-comment-summary-v0 :=
  reportRefs
  + summaryMarkdown
  + blockingItems
  + warningItems
  + unmeasuredItems
  + nonConclusions
```

## Operational feedback artifacts

Operational feedback は report outcome と後続 outcome を結び、threshold calibration や
hypothesis refresh に使う。

```text
report-outcome-daily-ledger-v0
calibration-review-record-v0
team-threshold-policy-v0
ownership-boundary-monitor-v0
repair-adoption-record-v0
incident-correlation-monitor-v0
hypothesis-refresh-cycle-v0
```

これらは empirical / operational artifact であり、causal theorem を直接主張しない。
Trace-grounded `SoftwareFieldEstimate` reconstruction では
`docs/tool/software_field_reconstruction_protocol.md` に従い、PRD / Issue / PR / review / CI /
incident / ownership trace を observed、derived、unavailable、private、unknown、notComparable に
分類する。unavailable / private / unknown remainder は measured zero ではなく、
complete `SoftwareField` reconstruction も主張しない。
SFT forecast の calibration / benchmark では、`docs/tool/sft_calibration_benchmark.md` に従い、
forecast item refs と observed PR / review / CI / outcome refs を held-out trace として照合する。
false positive / false negative review は review mediation と AI shortcut detection を分けて記録し、
private / unavailable / missing data を measured zero に丸めない。
