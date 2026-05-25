# AIR: Architecture Intermediate Representation

AIR は、extractor、policy、runtime evidence、semantic evidence、manual annotation、
generated-change provenance を統合する中間表現である。

AIR は `ArchitectureCore` そのものではない。AIR は、tool が観測・保持できる証拠と claim を
束ね、後段 report や theorem precondition check が読める形にする artifact である。

## Schema role

```text
aat-air-v0 :=
  architecture identity
  + revision
  + feature metadata
  + artifacts
  + evidence
  + components
  + relations
  + policies
  + semantic diagrams
  + architecture paths
  + homotopy generators
  + nonfillability witnesses
  + signature axes
  + coverage
  + claims
  + operation trace
  + extension summary
```

## Identity and provenance

AIR は、artifact の出所と参照可能性を持つ。

```text
architectureId
revision.before
revision.after
feature.source
artifacts[]
evidence[]
```

`feature.source = ai_session` の場合は、provider、model、prompt ref、generated patch、
human review boundary を保持する。これは生成物を formal claim に昇格するためではなく、
provenance と review boundary を失わないためである。

## Components and relations

component は lifecycle と evidence refs を持つ。

```text
components[]:
  id
  kind
  lifecycle
  owner?
  evidenceRefs[]
```

relation は layer、方向、kind、lifecycle、protection、extraction rule、evidence refs を持つ。

```text
relations[]:
  id
  layer
  from?
  to?
  kind
  lifecycle
  protectedBy?
  extractionRule?
  evidenceRefs[]
```

`from` / `to` が欠ける relation は、未解決または外部境界を示すために保持できる。

## Policies and laws

AIR の policy は、law universe を実用 artifact として参照する。

```text
policies:
  laws[]
  boundaries[]
  allowedEdges[]
  forbiddenEdges[]
  abstractionRules[]
  protectionRules[]
```

policy adoption は measured claim ではなく assumed claim として始まることがある。
policy rule の測定結果は、別の claim と evidence に分ける。

## Semantic path and homotopy layer

semantic layer は、path、diagram、filler claim、nonfillability witness を扱う。

```text
semanticDiagrams[]
architecturePaths[]
homotopyGenerators[]
nonfillabilityWitnesses[]
```

semantic diagram がないことは semantic flatness ではない。diagram universe が空なら、
semantic axis は unmeasured または outOfScope として扱う。

## Coverage

coverage は layer ごとに measurement boundary を持つ。

```text
coverage.layers[]:
  layer
  measurementBoundary
  universeRefs[]
  measuredAxes[]
  unmeasuredAxes[]
  projectionRule?
  extractionScope[]
  exactnessAssumptions[]
  unsupportedConstructs[]
```

coverage は claim の前提であり、report の補足情報ではない。

## Claims

AIR claim は、subject、predicate、claim level、claim classification、measurement boundary、
theorem refs、evidence refs、assumptions、non-conclusions を持つ。

```text
claims[]:
  claimId
  subjectRef
  predicate
  claimLevel
  claimClassification
  measurementBoundary
  theoremRefs[]
  evidenceRefs[]
  requiredAssumptions[]
  coverageAssumptions[]
  exactnessAssumptions[]
  missingPreconditions[]
  nonConclusions[]
```

formal claim は theorem ref だけでは成立しない。theorem preconditions が満たされていることを
別途確認する。

## Extension fields

Feature extension に関する summary は、split claim と interaction claim を分ける。

```text
extension:
  embeddingClaimRef?
  featureViewClaimRef?
  interactionClaimRefs[]
  splitClaimRef?
  splitStatus
```

`splitStatus = split` は、selected universe と claim boundary に相対化される。
runtime / semantic / lifting evidence を static split と混同しない。

## ArchMap projection

`air-from-archmap` は supplied JSON の `archmap-v0` を AIR へ投影する。対応は次の通り。

| ArchMap | AIR |
| --- | --- |
| source artifact refs | `artifacts[]`, `evidence[]` |
| object mapping | `components[]` |
| relation mapping | `relations[]` |
| semantic diagram / commutation claim | `semanticDiagrams[]`, `architecturePaths[]`, `claims[]` |
| nonfillability witness | `nonfillabilityWitnesses[]`, obstruction claim |
| missing evidence / conflict | `claims[].missingPreconditions`, coverage gap / review cue |
| non-conclusions | `claims[].nonConclusions` |

projection は loss-aware である。runtime trace 不足、private / unavailable context、policy disagreement、
semantic-runtime disagreement は measured zero や resolved claim に変換しない。
