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
