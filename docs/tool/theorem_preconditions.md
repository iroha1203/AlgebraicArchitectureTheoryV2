# Theorem Precondition Checks

Theorem precondition checker は、tool artifact から formal theorem を直接証明するものではない。
tool output が theorem package の前提を満たしているか、満たしていないなら何が足りないかを
report する。

## Input

CLI の `theorem-check` は、実装上は AIR JSON path だけを直接入力に取る。

```text
archsig theorem-check --air <air.json> --out <report.json>
```

signature、policy、witness、coverage / exactness metadata は、AIR 内の artifact refs、
evidence refs、claims、coverage layers、non-conclusions として読む。
次の形は概念上の入力境界であり、CLI option の一覧ではない。

```text
theorem precondition input :=
  AIR
  + signature artifact
  + policy artifact
  + witness artifact
  + coverage / exactness metadata
  + theorem package reference
```

## Check result

```text
theorem-precondition-check-v0 :=
  theoremRef
  + subjectRef
  + requiredAssumptions
  + dischargedAssumptions
  + missingPreconditions
  + coverageGaps
  + exactnessGaps
  + blockedFormalClaimPromotion
  + nonConclusions
```

## Report soundness

Report soundness は、report が入力 artifact と claim boundary を正しく反映することを意味する。
architecture が lawful であることを意味しない。

```text
report soundness:
  report claim
  -> supported by evidence refs
  -> bounded by measurement boundary
  -> preserves non-conclusions
```

## Witness traceability

obstruction witness は、source evidence、artifact ref、claim ref、repair candidate へ辿れる必要がある。

```text
witness
  -> evidence
  -> source location / observation / policy rule
  -> claim
  -> report
```

traceability が切れている witness は、formal claim の前提にも measured claim の根拠にも使わない。

## Coverage / exactness checker

coverage / exactness checker は、未測定軸と測定済み 0 を分ける。

```text
coverage ok:
  selected universe declared
  + measured axes declared
  + unmeasured axes declared
  + unsupported constructs declared
  + exactness assumptions declared
```

coverage gap は failure とは限らない。claim boundary の一部として report する。

## ArchMap precondition reading

ArchMap から来る theorem precondition は、Lean theorem witness ではなく candidate として読む。

```text
ArchMap precondition candidate :=
  selected source universe
  + target architecture universe
  + object / relation preservation claims
  + semantic diagram / nonfillability claims
  + law / policy boundary claims
  + flatness precondition refs
  + coverage / exactness / non-conclusions
```

Lean で使う場合は、`Formal/Arch/Signature/ArchMap.lean` の `ArchMapModel` と
`ArchMapPreservationPackage` に対応する field を明示的に与える。`archmap` validation report は、
source refs、claim boundary、semantic coverage、formal promotion guardrail を検査するが、
`ArchMapPreservationPackage` の field を証明しない。

`archmap` validation report と `theorem-check` report は、ArchMap 由来の candidate を
`leanPreservationPreconditionChecklist` / `archmapPreservationPreconditionChecklist`
として保持する。対応 vocabulary は、object / relation / semantic diagram /
semantic commutation / nonfillability witness / law-policy / flatness precondition /
coverage-exactness boundary を Lean package field 名で示す。v0 の tooling vocabulary は、
contract observation と event projection を `SemanticDiagramPreservation`、semantic non-commutation
と saga compensation を `NonfillabilityWitnessPreservation`、runtime/static disagreement、
framework convention、dynamic plugin blind spot を `CoverageExactnessBoundary` として読む。
status は candidate、
missing evidence block、unmeasured coverage block、formal promotion guardrail block、
supplied assumption、out-of-scope を区別する。

`air-from-archmap` はこの対応を AIR `claims[].requiredAssumptions` にも残す。したがって
`theorem-check` は ArchMap-derived AIR だけを入力にした場合でも、どの
`ArchMapPreservationPackage` field の候補かを report できる。ただし `theorem-check` pass は
Lean proof term、semantic preservation proof、または package field discharge ではない。

特に `measurementBoundary = measuredZero` と semantic coverage gap は別の前提である。
unmeasured semantic diagram universe を measured zero として扱う report は、formal promotion
candidate として block する。

ArchMap は SFT computation result を theorem precondition として持たない。ArchMap に保持してよいのは
source-level candidate、たとえば operation / state / state transition / event / workflow /
test oracle / runtime observation の候補と source refs である。field、force、attractor、basin、
ForecastCone、ConsequenceEnvelope、calibration boundary は FieldSig-computed SFT artifact 側の
責務であり、ArchMap checklist では proof relation や計算結果として読まない。

## Artifact-to-AAT-supported SFT boundary reading

ArchMap / ArchSig artifact から AAT-supported SFT Grand Theorem surface へ接続する場合も、
artifact は theorem proof ではなく theorem precondition / boundary evidence として読む。

```text
artifact-to-boundary input :=
  ArchMap preservation package
  + ArchSig report estimate boundary
  + AAT/SFT interface boundary
  + finite exact SFT model boundary
  + selected source / horizon boundary
  + explicit non-conclusions
```

Lean では、`Formal/Arch/Evolution/SFTArtifactBoundaryBridge.lean` の
`AATSelectedArchitectureSlice.ofArchMapPreservationPackage` が ArchMap 側を selected AAT
slice として読み、`ArchSigDerivedSFTReportBoundary` が ArchSig 側を SFT report / forecast
boundary として読む。`AATSupportedSFTBoundary.ofArchMapAndArchSigBoundaries` は、それらを
`AATSupportedSFTBoundary` へ接続する。

この接続で discharge されるのは、selected slice boundary、report / theorem-status boundary、
finite exact model boundary、non-conclusion preservation である。extractor completeness、
calibrated forecast correctness、operational governance effectiveness、global AI safety は
missing / non-conclusion のまま残す。
