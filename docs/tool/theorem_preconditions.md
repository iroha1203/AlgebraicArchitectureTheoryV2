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

特に `measurementBoundary = measuredZero` と semantic coverage gap は別の前提である。
unmeasured semantic diagram universe を measured zero として扱う report は、formal promotion
candidate として block する。
