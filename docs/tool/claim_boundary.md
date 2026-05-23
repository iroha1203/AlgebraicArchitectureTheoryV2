# Claim Boundary

Claim boundary は、tool output を「何を主張してよいか」に変換するための境界である。

## ClaimLevel

```text
formal
tooling
empirical
hypothesis
```

`formal` は theorem package と precondition discharge に接続する claim である。
`tooling` は extractor、validator、report による measured claim である。
`empirical` は dataset や case study による claim である。
`hypothesis` は検証前の研究仮説である。

## ClaimClassification

```text
proved
measured
assumed
empirical
unmeasured
outOfScope
```

`proved` と `measured` を混同しない。`assumed` は policy adoption や analysis boundary の
明示に使う。`unmeasured` は zero ではない。

## MeasurementBoundary

```text
measuredZero
measuredNonzero
unmeasured
unavailable
private
notComparable
outOfScope
```

`notComparable` は schema version、projection rule、measurement unit、coverage boundary が
揃わない場合に使う。

## Claim schema

```text
ArchitectureClaim :=
  subjectRef
  + predicate
  + claimLevel
  + claimClassification
  + measurementBoundary
  + theoremRefs
  + evidenceRefs
  + requiredAssumptions
  + coverageAssumptions
  + exactnessAssumptions
  + missingPreconditions
  + nonConclusions
```

## Formal claim promotion guardrail

tooling artifact から formal claim へ昇格するには、少なくとも次が必要である。

```text
theorem ref exists
required assumptions discharged
coverage assumptions discharged
exactness assumptions discharged
measurement boundary compatible
non-conclusions preserved
```

これらが揃わない場合、claim は measured claim または blocked formal claim として扱う。

## ArchMap formal bridge

ArchMap tooling artifact と Lean formal bridge は別物として読む。

```text
archmap-v0 / validation report
  -> theorem precondition candidate
  -> optional Lean ArchMapModel
  -> explicit ArchMapPreservationPackage
  -> bounded AATStructurePreserved
```

`archmap-v0` は selected source universe、mapping item、coverage boundary、missing evidence、
non-conclusions を保持する tooling artifact である。Lean の `ArchMapModel` は、その情報を
抽象化して selected AAT architecture universe へ写す model であり、JSON validation pass から
自動生成または自動証明される theorem witness ではない。

`ArchMapPreservationPackage` に昇格するには、object / relation preservation、semantic diagram
preservation、nonfillability witness preservation、law / policy boundary preservation、flatness
precondition preservation、coverage / exactness / non-conclusion が Lean 側で明示される必要がある。
tooling confidence、validation success、AIR projection success はこれらの field を discharge しない。

## AAT-supported SFT bridge guardrail

ArchMap / ArchSig artifact を AAT-supported SFT boundary へ渡す場合、claim level は次のように保つ。

```text
ArchMap preservation package -> selected AAT slice boundary
ArchSig report boundary -> SFT report / forecast boundary
selected finite exact model -> theorem package precondition
artifact validation success -> tooling evidence only
```

`AATSupportedSFTBoundary.ofArchMapAndArchSigBoundaries` は、これらの境界を一つの
AAT-supported SFT boundary record に束ねるための Lean constructor である。constructor の存在は、
JSON extractor completeness、forecast calibration、runtime schedule safety、operational governance
effectiveness、global AI safety を formal claim に昇格しない。

## Report reading rule

Report consumer は、次を同時に読む。

```text
claim
evidence
measurement boundary
missing preconditions
non-conclusions
```

summary text や score だけで pass / fail を判断しない。
