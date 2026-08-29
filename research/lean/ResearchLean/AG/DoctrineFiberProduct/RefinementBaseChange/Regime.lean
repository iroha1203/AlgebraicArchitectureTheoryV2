import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.RealizedSupport
import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor

/-!
# Support transfer and refinement base-change regimes

Pulled support is transported covariantly along the exact first projection.
This is the G-101/G-109 route; no contravariant G-112 reindexing is used.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation
open CrossStageCoherence

/-- Base and pulled refinement cleavages at one compatible source. -/
structure RefinementBCRegimeAt {U : AtomCarrier.{u}}
    (C : RefinementBCConfiguration U) (p : C.CompatibleSource) where
  /-- Cleavage for the repointed base refinement. -/
  baseCleavage : RefinementCartesianCleavage (C.baseRefinementAt p)
  /-- Cleavage for the generated pulled refinement. -/
  pulledCleavage : RefinementCartesianCleavage (C.pulledRefinementAt p)

/-- A refinement base-change regime at every compatible source. -/
def RefinementBCRegime {U : AtomCarrier.{u}}
    (C : RefinementBCConfiguration U) :=
  ∀ p : C.CompatibleSource, RefinementBCRegimeAt C p

/-- A raw configuration is active when some compatible target point has a package. -/
def Active {U : AtomCarrier.{u}} (C : RefinementBCConfiguration U) : Prop :=
  Nonempty (Sigma fun p : C.CompatibleSource => CoreFiber (C.targetPointAt p))

/-- Active support together with an available configuration-wide regime. -/
def ActiveRegimeAvailable {U : AtomCarrier.{u}}
    (C : RefinementBCConfiguration U) : Prop :=
  Active C ∧ Nonempty (RefinementBCRegime C)

/-- Exact first projection transports every pulled target package to base support. -/
theorem pulledSupportTransfer
    {U : AtomCarrier.{u}} (C : RefinementBCConfiguration U)
    (p : C.CompatibleSource) :
    Nonempty (CoreFiber (C.pullbackTargetAt p)) →
      Nonempty (CoreFiber (C.targetPointAt p)) := by
  rintro ⟨package⟩
  exact ⟨coreFiberTransportObj
    (C.pointedConfigurationAt p).pullbackFst package⟩

/-- The base condition propagates to the generated pulled refinement. -/
theorem pulledRealizedReflection
    {U : AtomCarrier.{u}} (C : RefinementBCConfiguration U)
    (p : C.CompatibleSource)
    (condition : RealizedLocusExtractionReflecting (C.baseRefinementAt p)) :
    RealizedLocusExtractionReflecting (C.pulledRefinementAt p) := by
  intro hpulled atom htarget
  have hbaseSupport := pulledSupportTransfer C p hpulled
  have hbaseExtracts :
      (C.targetPointAt p).doctrine.extracts
        (C.targetPointAt p).source
        ((C.baseRefinementAt p).doctrineHom.atomMap atom) := by
    have projected :=
      ((C.pointedConfigurationAt p).pullbackFst.doctrineHom.extraction_iff
        (C.pullbackTargetAt p).source
        ((C.pulledRefinementAt p).doctrineHom.atomMap atom)).mpr htarget
    simpa [RefinementBCConfiguration.pullbackTargetAt,
      RefinementBCConfiguration.pointedConfigurationAt,
      RefinementBCConfiguration.baseRefinementAt,
      RefinementBCConfiguration.pulledRefinementAt,
      LegacyRefinementBCConfiguration.pullbackFst] using projected
  have hsource := condition hbaseSupport atom hbaseExtracts
  simpa [RefinementBCConfiguration.pullbackSourceAt,
    RefinementBCConfiguration.pointedConfigurationAt,
    LegacyRefinementBCConfiguration.pulled,
    LegacyRefinementBCConfiguration.pulledDoctrine,
    LegacyRefinementBCConfiguration.pulledSource] using hsource

/-- The configuration condition produces both local cleavages. -/
noncomputable def refinementBCRegimeOfCondition
    {U : AtomCarrier.{u}} (C : RefinementBCConfiguration U)
    (condition : ConfigurationRealizedLocusExtractionReflecting C) :
    RefinementBCRegime C := fun p => {
  baseCleavage := refinementCleavageOfRealizedReflection
    (C.baseRefinementAt p) (condition p)
  pulledCleavage := refinementCleavageOfRealizedReflection
    (C.pulledRefinementAt p) (pulledRealizedReflection C p (condition p))
}

/-- A regime recovers the fixed condition from its base cleavages. -/
theorem configurationConditionOfRegime
    {U : AtomCarrier.{u}} (C : RefinementBCConfiguration U)
    (regime : RefinementBCRegime C) :
    ConfigurationRealizedLocusExtractionReflecting C := by
  intro p
  exact realizedReflectionOfRefinementCleavage
    (C.baseRefinementAt p) (regime p).baseCleavage

/-- Global support-stratified classification for a raw configuration. -/
theorem refinementBCRegime_iff_configurationCondition
    {U : AtomCarrier.{u}} (C : RefinementBCConfiguration U) :
    Nonempty (RefinementBCRegime C) ↔
      ConfigurationRealizedLocusExtractionReflecting C := by
  constructor
  · rintro ⟨regime⟩
    exact configurationConditionOfRegime C regime
  · intro condition
    exact ⟨refinementBCRegimeOfCondition C condition⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
