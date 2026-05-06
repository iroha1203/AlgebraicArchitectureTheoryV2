# Architecture Signature Artifacts

Signature artifact は、architecture quality を単一スコアに潰すものではない。
selected axes を measurement boundary とともに保持する multi-axis artifact である。

## Architecture Signature artifact

```text
archsig-sig0-v0 :=
  schemaVersion
  + root
  + componentKind
  + components
  + edges
  + policies
  + signature
  + metricStatus
  + policyViolations
  + runtimeEdgeEvidence
  + runtimeDependencyGraph
  + unsupportedConstructs
```

`Sig0Document` は top-level `coverage` や `nonConclusions` を持たない。
Sig0 の coverage / exactness boundary は `metricStatus`、`unsupportedConstructs`、
runtime 関連 field、後段の validation / AIR / report 側で読む。
`signature` の値だけでは判断しない。

## Detectable values / reported axes

reported axes は、tool が検出または保持できる値の catalog である。

| Axis group | Examples |
| --- | --- |
| Static structure | component count, relation count, cycle flag, SCC size, max depth, forbidden edge count |
| Feature extension | added components, changed relations, hidden interaction witness, split status |
| Runtime | runtime edge count, unprotected path, protected path, exposure witness |
| Semantic / homotopy | semantic diagram count, filler claim, nonfillability witness, observation mismatch |
| Policy / law | adopted law, measured violation, missing policy evidence |
| Coverage / theorem boundary | measured axes, unmeasured axes, missing preconditions, exactness assumptions |
| Empirical / process outcome | review outcome, repair adoption, incident correlation boundary |
| Operational feedback | daily drift, suppression, threshold policy, calibration record |

## Measurement status

```text
metricStatus.axis.measured = true
  -> selected universe で測定済み

metricStatus.axis.measured = false
  -> 未測定

value = null
  -> 未測定、比較不能、対象外、または private boundary
```

placeholder の `0` を risk zero と読まない。

## Signature diff

Signature diff は before / after の差分 artifact である。

```text
signature-diff-report-v0 :=
  beforeRef
  + afterRef
  + deltaSignature
  + metricDeltaStatus
  + improvedAxes
  + worsenedAxes
  + unmeasuredAxes
  + attributionCandidates
  + nonConclusions
```

before と after の coverage が異なる場合、delta は `notComparable` になりうる。

## Non-conclusions

Signature artifact は、次を主張しない。

```text
global architecture quality
extractor completeness
semantic completeness
runtime completeness
causal incident reduction
formal theorem discharge
```
