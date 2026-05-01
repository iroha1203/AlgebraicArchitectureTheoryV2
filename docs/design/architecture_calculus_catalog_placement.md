# Architecture Calculus catalog placement

Lean status: `design` / `future proof obligation`.

この文書は Issue [#359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/359)
の設計決定である。数学設計書第3章の operation catalog を、Lean の public API 上で
どの層に置くかを固定する。ここでの配置は proof obligation の切り分けであり、
operation tag だけから保存性、改善、runtime / semantic completeness、global flatness
preservation を主張しない。

この文書の `既存 Lean API` 欄は、API の配置先を示す。`proved` status の分類は
`docs/proof_obligations.md` と `docs/lean_theorem_index.md` で管理し、schema /
accessor theorem / bounded bridge / substantive theorem を区別する。配置表に名前が
載ることは、無条件の operation law や global flatness preservation の証明を意味しない。

## 配置原則

- finite `ArchGraph` 上で辺関係として意味が閉じる operation だけを concrete graph
  kernel に置く。
- contract、observation、projection、LSP に依存する operation は、graph 変換ではなく
  contract / observation theorem package として扱う。
- runtime path、protection policy、migration protocol に依存する operation は、
  runtime / semantic package として扱い、telemetry completeness は前提に分離する。
- selected obstruction measure を減らす主張は、`Repair` / `RepairSynthesis` の selected
  obstruction universe と admissible rule 前提に相対化する。
- constraint から候補を作る operation は synthesis package に置き、solver failure と
  valid no-solution certificate を分ける。

## Catalog placement

| Operation | 主配置 | 既存 Lean API | 将来扱う proof obligation |
| --- | --- | --- | --- |
| `compose` | concrete graph kernel + interface compatibility law | `ArchGraph.compose`, `FiniteArchGraph.compose`, `ConcreteGraphOperation.compose` | 同一 component 型上の edge union を越える interface-mediated composition、bounded associativity、coverage / exactness 前提。 |
| `refine` | semantic / contract package | `ArchitectureOperationKind.refine`, `OperationProofObligation.refine` | abstract component を subarchitecture へ展開する refinement soundness、external observation equivalence。 |
| `abstract` | projection / observation package | `InterfaceProjection`, `ProjectionSound`, `ObservationFactorsThrough`, `OperationProofObligation.abstract` | region を interface へ射影する abstraction soundness、coverage と exactness に相対化した quotient / observation bridge。 |
| `replace` | concrete graph kernel + local contract package | `ArchGraph.replace`, `FiniteArchGraph.replace`, `ConcreteGraphOperation.replace`, `LocalReplacementContract` | edge equivalence または local replacement contract に相対化した preservation / observational equivalence。 |
| `split` | feature extension / split package | `FeatureExtension`, `SelectedStaticSplitExtension`, `StaticSplitFailureCoverage`, `OperationProofObligation.split` | static split evidence と runtime / semantic split preservation を別前提として束ねる theorem package。 |
| `merge` | contract / observation package | `ArchitectureOperationKind.merge`, `OperationProofObligation.merge`, `MergedBoundaryContract`, `mergeExternalContractPreservationLaw` | merged boundary が外部 contract を保つための observation equivalence と projection exactness。 |
| `isolate` | runtime / semantic localization package | `ArchitectureOperationKind.isolate`, `OperationProofObligation.isolate`, `RuntimePathLocalizedWithin`, `isolateRuntimeLocalizationLaw` | dangerous dependency、runtime path、semantic drift を selected boundary / region に相対化する localization theorem。runtime telemetry completeness は主張しない。 |
| `protect` | concrete graph identity kernel + runtime policy package | `FiniteArchGraph.protect`, `ConcreteGraphOperation.protect`, `RuntimeProtectionContract`, `protectRuntimeProtectionLaw` | timeout、fallback、queue、bulkhead、circuit breaker など policy-aware runtime protection を selected runtime universe に相対化する bounded theorem。global protection idempotence は主張しない。 |
| `migrate` | runtime / semantic package | `ArchitectureOperationKind.migrate`, `OperationProofObligation.migrate`, `StagedMigrationPath`, `MigrationCompatibilityWindow`, `MigrationObserved`, `migrateObservationEquivalenceLaw` | staged migration path、compatibility window、old / new architecture observation equivalence を bounded package として扱う。runtime telemetry completeness、semantic completeness、global flatness preservation は主張しない。 |
| `reverse` | concrete graph kernel | `ArchGraph.reverse`, `FiniteArchGraph.reverse`, `ConcreteGraphOperation.reverse` | reverse involution entrypoint と、blast radius / upstream impact 診断への接続。 |
| `contract` | contract / observation package | `LocalReplacementContract`, `ObservationFactorsThrough`, `ExplicitContractSound`, `contractExplicitizationLaw`, `OperationProofObligation.contract` | implicit dependency / semantic expectation を explicit contract へ写す soundness と non-completeness 境界。 |
| `repair` | repair package | `SelectedObstructionUniverse`, `AdmissibleRepairRule`, `FiniteRepairPackage`, `OperationProofObligation.repair` | selected obstruction universe と admissible rule 前提に相対化した monotonicity / finite clearing。 |
| `synthesize` | synthesis package | `SynthesisConstraintSystem`, `SynthesisSoundnessPackage`, `NoSolutionCertificate`, `OperationProofObligation.synthesize` | produced candidate soundness と valid no-solution certificate soundness。solver completeness は主張しない。 |

## Concrete kernel に置かないもの

`refine`, `abstract`, `split`, `merge`, `isolate`, `migrate`, `contract`,
`synthesize` は、operation tag と proof-obligation constructor を持つが、現時点では
uniform な finite graph transform として定義しない。これらは、interface compatibility、
coverage、exactness、observation equivalence、runtime policy、semantic diagram、
constraint validity のいずれかを必要とするため、専用 theorem package 側で扱う。

## Synthesis との接続

`synthesize` は `RepairSynthesis.lean` の synthesis package と接続する。候補を返す場合は
`SynthesisSoundnessPackage.candidate_satisfies` によって selected constraint system への
soundness を読む。解なしを主張する場合は、solver が失敗した事実ではなく、
`NoSolutionCertificate.sound_of_valid` の valid certificate 前提を使う。

## Non-conclusions

この配置表は次を主張しない。

- catalog 全 operation に対する uniform graph transform の存在。
- operation tag からの preservation、reflection、improvement、localization、
  translation、transfer、assumption discharge。
- runtime telemetry completeness、semantic diagram completeness、extractor completeness。
- global flatness preservation、全 operation law の無条件成立、solver completeness。
