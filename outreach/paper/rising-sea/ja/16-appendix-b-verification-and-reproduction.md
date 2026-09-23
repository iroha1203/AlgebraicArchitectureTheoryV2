# 付録B リポジトリとLeanのビルド

証明ソースは、[AlgebraicArchitectureTheoryV2リポジトリ](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2)で公開している。

Gitとelanをインストールした環境で、次を実行して本体（`Formal`）をビルドする。
`lean-toolchain`で指定されたLeanと、`lake-manifest.json`で固定された依存ライブラリを用いる。

```sh
git clone https://github.com/iroha1203/AlgebraicArchitectureTheoryV2.git
cd AlgebraicArchitectureTheoryV2
git checkout --detach 719f81f47d410701fd82c2bc88613cc140c59377
lake exe cache get
lake build +Formal.AG
```

続いて、`research/lean`で次を実行する。
以下の対象と自動的にビルドされる依存モジュールに、付録Aが固定版`719f81f47d41`で参照するResearch側の証明ソースが含まれる。

```sh
cd research/lean
lake build \
  ResearchLean.AG.AtomFoundation.RefinementSupply \
  ResearchLean.AG.CanonicalResolution.NegativeWitness \
  ResearchLean.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness \
  ResearchLean.AG.ComparisonInformationLoss.PresentationTransport \
  ResearchLean.AG.DiagnosticConservativity.ObstructionExactness \
  ResearchLean.AG.DiagnosticConservativity.OrbitExactness \
  ResearchLean.AG.DoctrineFiberProduct.ConfigurationDescent \
  ResearchLean.AG.DoctrineFiberProduct.IndexedRawFamilyClassification \
  ResearchLean.AG.DoctrineFiberProduct.InternalNormalizationSplitNoGo \
  ResearchLean.AG.FiniteDecoderRepresentability.CountableSyntaxObstruction \
  ResearchLean.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction \
  ResearchLean.AG.ObstructionDiagnosticBridge.SelectedFiniteObstructionExamples \
  ResearchLean.AG.RealizationComparisonIdempotents.MaximalSubgroupoid \
  ResearchLean.AG.RealizationReconstruction.CSAATProtocolAdapterSquares \
  ResearchLean.AG.RealizationReconstruction.CSAATRestrictionKernelFiberTransport \
  ResearchLean.AG.RealizationReconstruction.FixedFLensGroupConnection \
  ResearchLean.AG.RealizationReconstruction.FixedFProtocolGroupConnection \
  ResearchLean.AG.StructuralCover.GeneratedH1Vanishing \
  ResearchLean.AG.UniformInvariance.AtlasPositioning \
  ResearchLean.AG.UniformInvariance.ConditionCAllAFiring \
  ResearchLean.AG.UniformInvariance.GLocalV1T3T6Uniformity
```

一般の輸送・lens・基底変換・比較群については、同じ`research/lean`ディレクトリで次を実行する。
この版に固定した付録Aの宣言は、以下の対象とその依存モジュールにすべて含まれる。

```sh
git checkout --detach 7e68ec6e77ef0249ede6a4c875715cfaf1cb3ee6
lake build \
  ResearchLean.AG.ComparisonInformation.F37GeneralComparison \
  ResearchLean.AG.CrossStageCoherence.ArbitraryStrongLiftPseudofunctor \
  ResearchLean.AG.CrossStageCoherence.CompositeQualification \
  ResearchLean.AG.DoctrineFiberProduct.ArbitrarySemanticCleavageCoherence \
  ResearchLean.AG.FullGeometryNormalization.\
SemanticDerivedCanonicalComparisonIdentification \
  ResearchLean.AG.FullGeometryNormalization.SemanticDerivedDiagnosticEndpointBridge \
  ResearchLean.AG.FullGeometryNormalization.\
SemanticDerivedSelectorGlobalBottomReflection \
  ResearchLean.AG.FullGeometryNormalization.SemanticExactBarBetaKaroubiProjection \
  ResearchLean.AG.LocalSemanticReconstruction.\
SemanticGeneratedComparisonReconstruction \
  ResearchLean.AG.RealizationReconstruction.FixedFSemidirectProduct \
  ResearchLean.AG.RealizationReconstruction.GeneralRelativeLensComparison \
  ResearchLean.AG.TransportCoherence.ArbitraryObstruction
```
