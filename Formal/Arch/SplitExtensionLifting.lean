import Formal.Arch.FeatureExtension

namespace Formal.Arch

universe u v w q r

/--
Observation-relative section law for the selected feature quotient.

This is intentionally weaker than strict equality `q ∘ s = id`: the section is
judged only by the selected feature observation universe.
-/
def FeatureSectionLaw
    (X : FeatureExtension Core Feature Extended FeatureView)
    (featureObservation : Observation Feature FeatureView)
    (featureSection : Feature -> Extended) : Prop :=
  ∀ f : Feature,
    X.featureView.observe (featureSection f) = featureObservation.observe f

/--
Observation-relative core retraction law for the embedded core.

The retraction is not required to recover implementation identity in `Extended`;
it only has to agree with the selected core observation on embedded core
components.
-/
def ObservationalCoreRetraction
    (X : FeatureExtension Core Feature Extended FeatureView)
    (coreObservation : Observation Core CoreView)
    (retraction : Extended -> Core) : Prop :=
  ∀ c : Core,
    coreObservation.observe (retraction (X.coreEmbedding c)) =
      coreObservation.observe c

/--
Selected split-extension lifting data.

The fields record the section and retraction laws used by the bounded lifting
theorem. They do not claim a strict fibration, a unique decomposition of every
extended component, or semantic/runtime flatness.
-/
structure SplitExtensionLiftingData (Core : Type u) (Feature : Type v)
    (Extended : Type w) (FeatureView : Type q) (CoreView : Type r) where
  extension : FeatureExtension Core Feature Extended FeatureView
  featureObservation : Observation Feature FeatureView
  coreObservation : Observation Core CoreView
  featureSection : Feature -> Extended
  coreRetraction : Extended -> Core
  featureSectionLaw :
    FeatureSectionLaw extension featureObservation featureSection
  observationalCoreRetraction :
    ObservationalCoreRetraction extension coreObservation coreRetraction
  interfaceFactorization :
    extension.interactionFactorsThroughDeclaredInterfaces
  preservesRequiredInvariants :
    extension.preservesRequiredInvariants

namespace SplitExtensionLiftingData

variable {Core : Type u} {Feature : Type v} {Extended : Type w}
  {FeatureView : Type q} {CoreView : Type r}

/-- The feature section observes as the selected feature observation. -/
theorem featureSection_observes
    (e : SplitExtensionLiftingData Core Feature Extended FeatureView CoreView)
    (f : Feature) :
    e.extension.featureView.observe (e.featureSection f) =
      e.featureObservation.observe f :=
  e.featureSectionLaw f

/-- The core retraction preserves the selected observation on embedded core. -/
theorem coreRetraction_observes_coreEmbedding
    (e : SplitExtensionLiftingData Core Feature Extended FeatureView CoreView)
    (c : Core) :
    e.coreObservation.observe (e.coreRetraction (e.extension.coreEmbedding c)) =
      e.coreObservation.observe c :=
  e.observationalCoreRetraction c

end SplitExtensionLiftingData

/-- A selected feature step between feature states. -/
structure SelectedFeatureStep (Feature : Type v) where
  source : Feature
  target : Feature

/-- A selected lifted step inside the extended architecture. -/
structure LiftedExtensionStep (Extended : Type w) where
  source : Extended
  target : Extended

/-- A selected feature step preserves the supplied feature invariant. -/
def LawfulFeatureStep (featureInvariant : Feature -> Prop)
    (step : SelectedFeatureStep Feature) : Prop :=
  featureInvariant step.source -> featureInvariant step.target

/-- The canonical lifted endpoint pair induced by the feature section. -/
def CanonicalLiftedFeatureStep
    (e : SplitExtensionLiftingData Core Feature Extended FeatureView CoreView)
    (step : SelectedFeatureStep Feature) : LiftedExtensionStep Extended :=
  { source := e.featureSection step.source
    target := e.featureSection step.target }

/--
The lifted step realizes the selected feature step through the section and is an
edge of the extended static architecture.
-/
def LiftsFeatureStep
    (e : SplitExtensionLiftingData Core Feature Extended FeatureView CoreView)
    (featureStep : SelectedFeatureStep Feature)
    (liftedStep : LiftedExtensionStep Extended) : Prop :=
  liftedStep.source = e.featureSection featureStep.source ∧
  liftedStep.target = e.featureSection featureStep.target ∧
  e.extension.extended.edge liftedStep.source liftedStep.target

/--
The lifted step preserves the selected core invariant after applying the
observational core retraction.
-/
def PreservesCoreInvariants
    (e : SplitExtensionLiftingData Core Feature Extended FeatureView CoreView)
    (coreInvariant : Core -> Prop)
    (liftedStep : LiftedExtensionStep Extended) : Prop :=
  coreInvariant (e.coreRetraction liftedStep.source) ->
    coreInvariant (e.coreRetraction liftedStep.target)

/--
Compatibility assumptions for a selected feature step.

This is deliberately local to the selected step: it records the required
extended edge, the already-declared interface factorization, coverage, and the
core-invariant preservation needed by the bounded lifting theorem.
-/
structure CompatibleWithInterface
    (e : SplitExtensionLiftingData Core Feature Extended FeatureView CoreView)
    (coreInvariant : Core -> Prop)
    (featureStep : SelectedFeatureStep Feature) : Prop where
  liftedEdge :
    e.extension.extended.edge
      (e.featureSection featureStep.source)
      (e.featureSection featureStep.target)
  interfaceFactorization :
    e.extension.interactionFactorsThroughDeclaredInterfaces
  coverageAssumptions :
    e.extension.coverageAssumptions
  coreInvariantPreserved :
    coreInvariant (e.coreRetraction (e.featureSection featureStep.source)) ->
      coreInvariant (e.coreRetraction (e.featureSection featureStep.target))

/--
Selected split-extension lifting theorem.

Given split-extension lifting data, a lawful selected feature step, and local
interface compatibility for that step, the canonical section-induced extended
step lifts the feature step and preserves the selected core invariant.
-/
theorem SplitExtensionLifting
    (e : SplitExtensionLiftingData Core Feature Extended FeatureView CoreView)
    {featureInvariant : Feature -> Prop} {coreInvariant : Core -> Prop}
    (featureStep : SelectedFeatureStep Feature)
    (_hLawfulFeatureStep : LawfulFeatureStep featureInvariant featureStep)
    (hCompatible : CompatibleWithInterface e coreInvariant featureStep) :
    ∃ liftedStep : LiftedExtensionStep Extended,
      LiftsFeatureStep e featureStep liftedStep ∧
        PreservesCoreInvariants e coreInvariant liftedStep := by
  refine ⟨CanonicalLiftedFeatureStep e featureStep, ?_, ?_⟩
  · exact ⟨rfl, rfl, hCompatible.liftedEdge⟩
  · intro hCore
    exact hCompatible.coreInvariantPreserved hCore

end Formal.Arch
