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
| AAT / SFT projection | ArchMap AAT-facing preservation checklist, ArchMap-derived SFT operation support |
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

## SFT forecast report artifacts

### SFT Grand theorem to ArchSig review judgement surface

| SFT concept | ArchSig deterministic evidence | Missing artifact / boundary state | LLM / reviewer judgement |
| --- | --- | --- | --- |
| finite operation support | `operation-support-estimate-v0.candidateOperationFamilies[]`, `policyConstraints[]`, `supportDisposition` | `knownForbiddenSupport[]`, `unknownRemainder[]`, undefined support | Decide whether support is governed, risky, blocked, or still needs evidence. |
| bounded ForecastCone | `forecast-cone-skeleton-v0.finiteSupportRefs[]`, `boundedHorizon`, `pathClassCandidates[]` | horizon refs missing, support refs dangling, probability boundary missing | Read path classes as bounded futures, not probability predictions. |
| local future gluing | `forecast-cone-skeleton-v0.gluingEvidence[]` | `typedBoundaryFailures[].failureKind = "unglued-local-futures"` or missing gluing refs | Decide whether local futures can be reviewed together or must remain separate next actions. |
| governance intervention | `forecast-cone-skeleton-v0.governanceInterventions[]`, `architecture-policy-v0.sftGovernance` | unsupported governance cut, missing policy refs, policy undefined | Choose reviewer action: cut future, allow conditionally, request policy, or keep unknown. |
| typed boundary failure | `forecast-cone-skeleton-v0.typedBoundaryFailures[]`, `consequence-envelope-report-v0.typedBoundaryFailures[]` | missing observation boundary, undefined operation support, missing invariant, unsupported governance cut | Return bounded judgement with evidence refs; do not convert unknown into measured zero. |
| consequence envelope | `consequence-envelope-report-v0.affectedArchitectureRegions[]`, `comparableSignatureAxes[]`, `missingBoundaryItems[]`, `reviewerActions[]` | missing boundary items, unknown remainder, theorem boundary items | Translate report items into opened futures, closed futures, boundary failures, and next actions. |
| review judgement input | `sft-review-summary-v0` | evidence refs or boundary refs missing | LLM / reviewer returns judgement only with cited evidence and confidence boundary. |

PR review input is diff / repository evidence plus ArchMap, AIR, theorem-check, policy, feature,
PR quality, and optional `sft-review-summary-v0`. It produces review cues for changed code and
must not become merge approval. PRD / SPEC review input is IntentMap, ArchMap, AlignmentMap,
operation support, ForecastCone, ConsequenceEnvelope, and `sft-review-summary-v0`. It produces
planning actions for opened futures, missing invariants, unresolved decisions, and governance
interventions. Both surfaces preserve evidence refs, boundary refs, unknown remainder, and
non-conclusions; neither surface proves future safety or Lean theorem claims.

`forecast-cone-skeleton-v0` は finite support refs、bounded horizon、path class
candidates、gluing evidence、governance intervention、typed boundary failure、
forecast boundary、unknown remainder を保持する tooling artifact である。
`archmap-sft-input` から生成した `operation-support-estimate-v0` を入力にする場合、
`source:archmap:*` refs、missing evidence、private / unavailable / unsupported boundary を
そのまま cone と envelope へ渡す。ArchMap confidence は review priority であり probability ではない。

`consequence-envelope-report-v0` は、一つ以上の bounded cone skeleton から
reviewer-facing report を作る projection artifact である。affected architecture regions、
comparable signature axes、axis delta ranges、obstruction candidates、missing / theorem
boundary、typed boundary failure、reviewer action、review / CI recommendation をまとめるが、
projection 後も unknown remainder と forecast non-conclusions を保持する。

`sft-review-summary-v0` は `consequence-envelope-report-v0` から opened futures、
closed futures、boundary failures、next actions、LLM judgement contract を生成する。
これは judgement-ready summary であり、LLM / reviewer が evidence refs と boundary refs を
引用して判断するための入力である。

この envelope は cone family の一意復元、point prediction、probability、causal proof、
forecast correctness、Lean theorem witness、merge approval を主張しない。


## FieldSig boundary

FieldSig lives in `tools/fieldsig` and owns SFT software evolution measurement artifacts: `software-field-measurement-v0`, forecast / intent artifacts, workflow evidence refs, operational feedback, governance candidates, unknown remainder, and calibration hooks. ArchSig remains the AAT structural telemetry generator and passes evidence through JSON artifact refs. FieldSig validation is not a Lean proof, forecast correctness proof, probability claim, causal theorem, or replacement for CI, tests, and human review.
