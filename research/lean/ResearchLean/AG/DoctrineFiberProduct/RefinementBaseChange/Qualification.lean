import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Regime

/-!
# Qualification of realized-support reflection

Composition does not assume support at its intermediate point.  The outer
condition authors the intermediate package, which is then consumed by the inner
condition.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-- Identity pointed refinements satisfy realized-support reflection. -/
theorem realizedReflection_id {U : AtomCarrier.{u}} (X : ExtractionInstance U) :
    RealizedLocusExtractionReflecting (PointedRefinementHom.id X) := by
  intro _ atom extracted
  exact extracted

/-- Every exact pointed morphism lies in the realized-support class. -/
theorem realizedReflection_ofExact {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (f : X ⟶ Y) :
    RealizedLocusExtractionReflecting (PointedRefinementHom.ofExact f) := by
  intro _ atom extracted
  exact (f.doctrineHom.extraction_iff X.source atom).mpr (by
    simpa [f.source_eq] using extracted)

/-- Either leg of a pointed refinement isomorphism reflects realized extraction. -/
theorem realizedReflection_ofIsoHom {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (e : PointedRefinementIso X Y) :
    RealizedLocusExtractionReflecting e.hom := by
  intro _support atom extracted
  have reflected := e.inv.doctrineHom.extraction_forward
    Y.source (e.hom.doctrineHom.atomMap atom) extracted
  have hsource := e.inv.source_eq
  have hmaps := congrArg
    (fun f => f.doctrineHom.atomMap atom) e.hom_inv_id
  have hmaps' : e.inv.doctrineHom.atomMap
      (e.hom.doctrineHom.atomMap atom) = atom := by
    simpa [PointedRefinementHom.comp, refinementHomComp,
      PointedRefinementHom.id, refinementHomId] using hmaps
  rw [hsource, hmaps'] at reflected
  exact reflected

/-- Realized reflection is unchanged when an isomorphism is read backwards. -/
theorem realizedReflection_ofIsoInv {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (e : PointedRefinementIso X Y) :
    RealizedLocusExtractionReflecting e.inv := by
  intro _support atom extracted
  have reflected := e.hom.doctrineHom.extraction_forward
    X.source (e.inv.doctrineHom.atomMap atom) extracted
  have hsource := e.hom.source_eq
  have hmaps := congrArg
    (fun f => f.doctrineHom.atomMap atom) e.inv_hom_id
  have hmaps' : e.hom.doctrineHom.atomMap
      (e.inv.doctrineHom.atomMap atom) = atom := by
    simpa [PointedRefinementHom.comp, refinementHomComp,
      PointedRefinementHom.id, refinementHomId] using hmaps
  rw [hsource, hmaps'] at reflected
  exact reflected

/-- The authored lift supplies an actual package at the refinement source. -/
noncomputable def sourceSupportOfRealizedReflection
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (target : CoreFiber Y) : CoreFiber X := by
  let lift := refinementLiftOfRealizedReflection r condition target
  letI := lift.isStronglyCartesian
  exact ⟨lift.domain,
    congrArg PointedRefinementObject.pointed
      (CategoryTheory.IsHomLift.domain_eq
        (refinementPackageProjection U) r lift.hom)⟩

/-- Realized-support reflection is closed under pointed refinement composition. -/
theorem realizedReflection_comp
    {U : AtomCarrier.{u}} {X₀ X₁ X₂ : ExtractionInstance U}
    (inner : PointedRefinementHom X₀ X₁)
    (outer : PointedRefinementHom X₁ X₂)
    (hinner : RealizedLocusExtractionReflecting inner)
    (houter : RealizedLocusExtractionReflecting outer) :
    RealizedLocusExtractionReflecting (inner.comp outer) := by
  intro htarget atom extracted
  rcases htarget with ⟨target⟩
  let intermediate := sourceSupportOfRealizedReflection outer houter target
  have hmiddle : X₁.doctrine.extracts X₁.source
      (inner.doctrineHom.atomMap atom) := by
    apply houter ⟨target⟩ (inner.doctrineHom.atomMap atom)
    exact extracted
  exact hinner ⟨intermediate⟩ atom hmiddle

/-- Raw configurations whose refinement lies in the exact comparison image. -/
def RefinementExactComparisonImage {U : AtomCarrier.{u}}
    (C : RefinementBCConfiguration U) : Prop :=
  ∃ exact : ExactDoctrineHom C.sOnePrime C.sOne,
    exactToRefinement exact = C.refinement

/-- The derived configuration predicate holds throughout the exact image. -/
theorem configurationRealizedReflection_of_exactImage
    {U : AtomCarrier.{u}} (C : RefinementBCConfiguration U)
    (image : RefinementExactComparisonImage C) :
    ConfigurationRealizedLocusExtractionReflecting C := by
  rcases image with ⟨exact, hexact⟩
  intro p
  let pointedExact : C.sourcePointAt p ⟶ C.targetPointAt p := {
    doctrineHom := exact
    source_eq := by
      have hsource := congrArg RefinementDoctrineHom.sourceMap hexact
      exact congrFun hsource p.sourcePrime
  }
  have hpointed : PointedRefinementHom.ofExact pointedExact =
      C.baseRefinementAt p := by
    apply PointedRefinementHom.ext
    exact hexact
  rw [← hpointed]
  exact realizedReflection_ofExact pointedExact

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
