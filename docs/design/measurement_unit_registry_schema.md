# Measurement unit registry v0 schema

Lean status: empirical hypothesis / tooling validation.

`measurement-unit-registry-v0` は、monorepo / multi-service 環境で runtime / semantic
evidence を読む前に、どの測定 universe を選んだかを固定する tooling registry である。
repository root、service root、deployment unit、runtime evidence source、semantic
workflow source を別々の boundary として記録し、AIR coverage / Feature Extension Report
へ trace する。

この registry は Lean theorem ではない。measurement unit を選んだことから、global
architecture completeness、Lean `ComponentUniverse` completeness、runtime / semantic
completeness、architecture lawfulness は結論しない。

## Schema

```text
MeasurementUnitRegistryV0
  schemaVersion: "measurement-unit-registry-v0"
  registryId: String
  scope: String
  units: List MeasurementUnitV0
  evidenceAdapters: List MeasurementEvidenceAdapterBoundaryV0
  explicitAssumptions: List String
  nonConclusions: List String
```

```text
MeasurementUnitV0
  unitId: String
  unitKind: "repository-root" | "service-root" | "deployment-unit"
  repositoryRoot: String
  serviceRoot: String | null
  deploymentUnit: String | null
  componentIdKind: String
  selectedComponentRefs: List String
  runtimeEvidenceSources: List MeasurementEvidenceSourceV0
  semanticWorkflowSources: List MeasurementEvidenceSourceV0
  coverageAssumptions: List String
  unsupportedConstructs: List String
  outputArtifacts: List String
  nonConclusions: List String
```

```text
MeasurementEvidenceSourceV0
  sourceId: String
  sourceKind: "runtime-trace" | "service-mesh" | "log" | "semantic-workflow" | "contract-test" | "manual-diagram"
  ownerUnitRef: String
  path: String
  privacyBoundary: String
  coverageAssumptions: List String
  unsupportedConstructs: List String
```

```text
MeasurementEvidenceAdapterBoundaryV0
  adapterId: String
  adapterKind: "runtime-evidence-adapter" | "semantic-evidence-adapter"
  measurementUnitRefs: List String
  measuredLayers: List "runtime" | "semantic"
  evidenceKinds: List String
  projectionRule: String
  coverageAssumptions: List String
  exactnessAssumptions: List String
  unsupportedConstructs: List String
  outputArtifacts: List String
  theoremBridgePreconditions: List String
  nonConclusions: List String
```

## Boundary semantics

`repositoryRoot` は checkout と artifact path の基準である。これは service ownership や
deployment topology ではない。

`serviceRoot` は source ownership / service boundary の候補を表す。service root が同じでも、
deployment unit や runtime trace source が一致するとは限らない。

`deploymentUnit` は runtime packaging / deploy target の候補を表す。deployment unit は
selected runtime evidence の単位であり、service 全体の挙動や semantic workflow 全体の
完全性を主張しない。

`runtimeEvidenceSources` と `semanticWorkflowSources` は、source id、owner unit、path、
privacy boundary、coverage assumptions、unsupported constructs を持つ。private data、
missing telemetry、redacted logs、unmapped workflow nodes は measured-zero evidence へ
丸めない。

`evidenceAdapters` は runtime / semantic evidence adapter がどの measurement unit を読んだか、
どの layer / evidence kind / projection rule へ写したか、coverage / exactness assumptions と
unsupported constructs を AIR coverage / Feature Extension Report へ trace するための
boundary である。

## CLI

```bash
archsig measurement-units --input measurement_units.json
```

出力 schema:

```text
measurement-unit-registry-validation-report-v0
```

Canonical fixture は `tools/archsig/tests/fixtures/minimal/measurement_units.json` で固定する。
validation は unit id、unit kind、repository root / service root / deployment unit、
runtime / semantic evidence source、adapter の measurement unit refs、coverage / exactness
assumptions、unsupported constructs、output artifacts、non-conclusion boundary を検査する。

## AIR / Feature Extension Report trace

- runtime adapter は `measurementUnitRefs` と `projectionRule` を AIR runtime coverage layer
  の `universeRefs` / `projectionRule` に対応させる。
- semantic adapter は workflow / diagram / contract-test evidence の source boundary を
  semantic coverage gap と theorem precondition boundary へ trace する。
- `unsupportedConstructs` は Feature Extension Report の coverage gap に残す。未対応 source
  や private / missing evidence は measured-zero ではない。
- theorem bridge は `theoremBridgePreconditions` が claim 側で明示され、Theorem Precondition
  Checker が不足を返さない場合にだけ formal claim の候補になる。

## Non-conclusions

- measurement unit registry は Lean theorem ではない。
- selected measurement unit は global architecture completeness を結論しない。
- selected measurement unit は Lean `ComponentUniverse` completeness を結論しない。
- runtime / semantic adapter coverage gap は measured-zero evidence ではない。
- private / missing evidence source は明示的に供給されるまで unmeasured のままである。
