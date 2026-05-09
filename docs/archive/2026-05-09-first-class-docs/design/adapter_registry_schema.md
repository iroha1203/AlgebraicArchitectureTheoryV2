# Adapter registry v0 schema

Lean status: empirical hypothesis / tooling validation.

`adapter-registry-v0` は、non-Lean extractor、framework-specific adapter、
runtime / semantic evidence adapter が AIR と Feature Extension Report へ渡す
evidence boundary を記録する tooling registry である。
registry は adapter が何を測ったか、何を測っていないか、どの projection rule と
coverage assumption の下で読めるかを固定する。

この registry は Lean theorem ではない。entry が存在することから、extractor
completeness、Lean `ComponentUniverse` completeness、architecture lawfulness、
formal theorem claim は結論しない。

## Schema

```text
AdapterRegistryV0
  schemaVersion: "adapter-registry-v0"
  registryId: String
  scope: String
  adapters: List AdapterRegistryEntryV0
  explicitAssumptions: List String
  nonConclusions: List String
```

```text
AdapterRegistryEntryV0
  adapterId: String
  adapterKind: "language-extractor" | "framework-adapter" | "runtime-evidence-adapter" | "semantic-evidence-adapter" | "policy-adapter"
  sourceLanguage: String | null
  frameworks: List String
  componentKinds: List String
  relationKinds: List String
  evidenceKinds: List String
  projectionRule: String
  measuredLayers: List "static" | "framework" | "runtime" | "semantic" | "policy"
  measuredAxes: List String
  coverageAssumptions: List String
  exactnessAssumptions: List String
  unsupportedConstructs: List String
  requiredInputs: List String
  outputArtifacts: List String
  theoremBridgePreconditions: List String
  nonConclusions: List String
```

`adapterId` と `projectionRule` は stable id として扱う。AIR relation の
`extractionRule`、AIR coverage の `projectionRule`、Feature Extension Report の
coverage gap は、この id を trace できる必要がある。

## Entry boundary

`adapterKind` は adapter の責務境界を表す。

- `language-extractor`: source file から static component / relation evidence を作る。
- `framework-adapter`: framework convention を bounded relation evidence に写す。
- `runtime-evidence-adapter`: trace、log、service mesh、runtime edge JSON などを runtime relation evidence に写す。
- `semantic-evidence-adapter`: workflow、contract test、diagram evidence などを semantic evidence に写す。
- `policy-adapter`: policy template や organization policy selector を tooling evidence に写す。

`coverageAssumptions` は「対象 universe のどこまでを見たか」を記録する。
`exactnessAssumptions` は「input から AIR relation / evidence への写像が何を保存するか」を
記録する。どちらかが空の場合、その adapter entry は formal claim promotion の根拠に
使わない。

`unsupportedConstructs` は measured-zero evidence ではない。adapter が明示的に扱えない
syntax、framework convention、runtime metadata、private data、semantic workflow を
文字列 taxonomy として残す。

## Canonical Python entry

Python pilot は次の registry entry として読む。

```json
{
  "adapterId": "python-import-graph-v0",
  "adapterKind": "language-extractor",
  "sourceLanguage": "python",
  "frameworks": [],
  "componentKinds": ["python-module", "external-dependency"],
  "relationKinds": ["import"],
  "evidenceKinds": ["python_import"],
  "projectionRule": "python-import-graph-v0",
  "measuredLayers": ["static"],
  "measuredAxes": ["hasCycle", "sccMaxSize", "maxDepth", "fanoutRisk"],
  "coverageAssumptions": [
    "package roots enumerate the measured Python module universe",
    "source roots enumerate the scanned Python files"
  ],
  "exactnessAssumptions": [
    "Python ast import/from nodes are projected to static import edges",
    "relative imports are resolved relative to the package root policy"
  ],
  "unsupportedConstructs": [
    "dynamic-import",
    "plugin-loading",
    "framework-convention",
    "generated-code",
    "notebook"
  ],
  "requiredInputs": ["repository root", "source root", "package root"],
  "outputArtifacts": ["archsig-sig0-v0", "aat-air-v0"],
  "theoremBridgePreconditions": [
    "explicit Lean ComponentUniverse bridge precondition",
    "AIR component and relation identifiers match the Lean theorem parameters"
  ],
  "nonConclusions": [
    "Python runtime semantics are not fully captured",
    "extractor completeness is not concluded",
    "Lean ComponentUniverse completeness is not concluded",
    "architecture lawfulness is not concluded"
  ]
}
```

Theorem Precondition Checker は、この entry だけでは `FORMAL_PROVED` へ昇格しない。
formal claim へ読むには `theoremBridgePreconditions` を claim 側で明示し、coverage /
exactness / selected universe がすべて足りている必要がある。

## Canonical framework adapter fixture

Issue #599 の FastAPI fixture は次の registry entry として読む。

```json
{
  "adapterId": "fastapi-route-adapter-fixture-v0",
  "adapterKind": "framework-adapter",
  "sourceLanguage": "python",
  "frameworks": ["fastapi"],
  "componentKinds": ["python-module"],
  "relationKinds": ["http_route_handler"],
  "evidenceKinds": ["framework_route"],
  "projectionRule": "fastapi-route-adapter-fixture-v0",
  "measuredLayers": ["framework"],
  "measuredAxes": ["frameworkRouteBinding"],
  "coverageAssumptions": [
    "fixture adapter inspects FastAPI APIRouter decorator calls in src/app/web.py"
  ],
  "exactnessAssumptions": [
    "fastapi-route-adapter-fixture-v0 maps observed APIRouter method decorators to route handler relations"
  ],
  "unsupportedConstructs": [
    "fastapi-dependency-injection",
    "fastapi-middleware",
    "fastapi-runtime-routing"
  ],
  "requiredInputs": ["archsig-sig0-v0", "framework-adapter-evidence-v0"],
  "outputArtifacts": ["aat-air-v0", "feature-extension-report-v0"],
  "theoremBridgePreconditions": [
    "explicit Lean ComponentUniverse bridge precondition",
    "framework route evidence is selected by the theorem package"
  ],
  "nonConclusions": [
    "FastAPI runtime semantics are not fully captured",
    "framework adapter output is not a Lean ComponentUniverse completeness proof",
    "unmeasured FastAPI conventions are not measured-zero evidence"
  ]
}
```

`framework-adapter-evidence-v0` の fixture は route relation を AIR の
`layer = "framework"` として追加する。Feature Extension Report は同じ layer の
coverage gap へ unsupported constructs を trace する。route relation が測定されても、
dependency injection、middleware、runtime routing は未対応 boundary として残る。

## Future adapter constraints

Issue #599, #594, #596, #600 の後続 adapter / policy / plugin / measurement-unit work は、
少なくとも次を満たす。

- AIR relation の `extractionRule` と registry `projectionRule` が対応する。
- evidence kind は registry `evidenceKinds` に現れる。
- measured layer / axis と unsupported construct は Feature Extension Report に trace できる。
- runtime / semantic adapter は `measurement-unit-registry-v0` の `measurementUnitRefs` と
  repository root / service root / deployment unit 境界を trace できる。
- adapter-specific confidence は formal theorem claim の代替ではない。
- private / missing / unparsed data は measured-zero に丸めない。
- registry validation は tooling validation であり、Lean proof obligation の discharge ではない。

## Non-conclusions

- adapter registry は extractor completeness を証明しない。
- adapter registry は Lean `ComponentUniverse` completeness を証明しない。
- adapter registry は architecture lawfulness を証明しない。
- adapter registry は runtime / semantic flatness を証明しない。
- adapter registry は organization policy pass や plugin output を formal theorem claim に昇格しない。
