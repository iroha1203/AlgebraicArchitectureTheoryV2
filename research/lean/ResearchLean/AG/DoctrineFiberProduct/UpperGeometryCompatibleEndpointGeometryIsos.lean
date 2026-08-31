import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationStrongCartesian

/-!
# Complete endpoint comparison isomorphisms

The canonical-authored normalization and the generated route geometry are
strongly Cartesian lifts over the same literal lax route base.  Cartesian
uniqueness therefore produces their complete geometry comparison isomorphism
over the identity lower package map.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- Complete base-route endpoint comparison from the canonical-authored
normalization to the generated route geometry. -/
noncomputable def canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (⟨input.canonicalAuthoredBaseRouteGeometryAt i⟩ :
      RefinementGeometryCategory.{u, v} U) ≅
      ⟨input.generatedBaseRouteGeometryAt i⟩ := by
  let generated := input.generatedBaseRouteLegAt i
  let canonical := input.canonicalAuthoredBaseRouteGeometryHomAt i
  letI : (refinementGeometryProjection U).IsStronglyCartesian generated.base
      generated := input.generatedBaseRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian canonical.base
      canonical := input.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian i
  have base_fac : canonical.base =
      (Iso.refl (⟨(input.generatedBaseRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U)).hom ≫ generated.base := by
    simp [generated, canonical]
  exact CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := refinementGeometryProjection U)
    (g := Iso.refl (⟨(input.generatedBaseRouteGeometryAt i).core⟩ :
      RefinementPackageTotalCategory U))
    (f := generated.base) (f' := canonical.base) base_fac generated canonical

/-- The base endpoint comparison hom factors the generated route leg as the
canonical-authored direct leg. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
        input.generatedBaseRouteLegAt i =
      input.canonicalAuthoredBaseRouteGeometryHomAt i := by
  let generated := input.generatedBaseRouteLegAt i
  let canonical := input.canonicalAuthoredBaseRouteGeometryHomAt i
  letI : (refinementGeometryProjection U).IsStronglyCartesian generated.base
      generated := input.generatedBaseRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian canonical.base
      canonical := input.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian i
  have base_fac : canonical.base =
      (Iso.refl (⟨(input.generatedBaseRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U)).hom ≫ generated.base := by
    simp [generated, canonical]
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    generated.base generated base_fac canonical

/-- The inverse base endpoint comparison factors the canonical-authored leg
as the generated route leg. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
        input.canonicalAuthoredBaseRouteGeometryHomAt i =
      input.generatedBaseRouteLegAt i := by
  rw [← input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_fac i]
  simp

/-- Complete pulled-route endpoint comparison from its independently
normalized canonical-authored endpoint to the generated pulled geometry. -/
noncomputable def canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (⟨input.canonicalAuthoredPulledRouteGeometryAt i⟩ :
      RefinementGeometryCategory.{u, v} U) ≅
      ⟨input.generatedPulledRouteGeometryAt i⟩ := by
  let generated := input.generatedPulledRouteLegAt i
  let canonical := input.canonicalAuthoredPulledRouteGeometryHomAt i
  letI : (refinementGeometryProjection U).IsStronglyCartesian generated.base
      generated := input.generatedPulledRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian canonical.base
      canonical :=
    input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian i
  have base_fac : canonical.base =
      (Iso.refl (⟨(input.generatedPulledRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U)).hom ≫ generated.base := by
    simp [generated, canonical]
  exact CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := refinementGeometryProjection U)
    (g := Iso.refl (⟨(input.generatedPulledRouteGeometryAt i).core⟩ :
      RefinementPackageTotalCategory U))
    (f := generated.base) (f' := canonical.base) base_fac generated canonical

/-- The pulled endpoint comparison hom factors the generated route leg as the
canonical-authored direct leg. -/
theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom ≫
        input.generatedPulledRouteLegAt i =
      input.canonicalAuthoredPulledRouteGeometryHomAt i := by
  let generated := input.generatedPulledRouteLegAt i
  let canonical := input.canonicalAuthoredPulledRouteGeometryHomAt i
  letI : (refinementGeometryProjection U).IsStronglyCartesian generated.base
      generated := input.generatedPulledRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian canonical.base
      canonical :=
    input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian i
  have base_fac : canonical.base =
      (Iso.refl (⟨(input.generatedPulledRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U)).hom ≫ generated.base := by
    simp [generated, canonical]
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    generated.base generated base_fac canonical

/-- The inverse pulled endpoint comparison factors the canonical-authored leg
as the generated pulled route leg. -/
theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv ≫
        input.canonicalAuthoredPulledRouteGeometryHomAt i =
      input.generatedPulledRouteLegAt i := by
  rw [← input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_fac i]
  simp

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
