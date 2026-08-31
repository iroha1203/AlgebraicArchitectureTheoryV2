import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointComparatorConjugation

/-!
# Exact endpoint comparison isomorphisms

The compatible endpoint comparisons are first constructed in the refinement
geometry category.  This module reflects their complete hom and inverse along
the faithful exact embedding, producing isomorphisms in the actual total
geometry category.  Their lower maps and coefficient maps remain literal
identities, and the existing edge naturality and comparator conjugation laws
are reflected to exact complete-geometry equations.

Implementation notes: the two exact arrows are constructed separately from
the already proved refinement hom and inverse.  Packaging those arrows into an
`Iso` preserves the proof provenance of both directions; using `asIso` on one
direction would hide the independently proved inverse and its coefficient law.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-! ## Exact base-route endpoint comparison -/

/-- Exact identity core map from the canonical-authored base endpoint to the
generated base endpoint.  The endpoint core theorem supplies the required
type transport. -/
noncomputable def canonicalAuthoredBaseToGeneratedRouteExactCoreHomAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    PackageTotalHom (input.canonicalAuthoredBaseRouteGeometryAt i).core
      (input.generatedBaseRouteGeometryAt i).core := by
  simpa only [input.canonicalAuthoredBaseRouteGeometryAt_core] using
    PackageTotalHom.id (input.generatedBaseRouteGeometryAt i).core

/-- Exact identity core map returning from the generated base endpoint to the
canonical-authored base endpoint. -/
noncomputable def canonicalAuthoredBaseToGeneratedRouteExactCoreInvAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    PackageTotalHom (input.generatedBaseRouteGeometryAt i).core
      (input.canonicalAuthoredBaseRouteGeometryAt i).core := by
  simpa only [input.canonicalAuthoredBaseRouteGeometryAt_core] using
    PackageTotalHom.id (input.generatedBaseRouteGeometryAt i).core

/-- The exact base core hom becomes the categorical identity after refinement
embedding. -/
theorem canonicalAuthoredBaseToGeneratedRouteExactCoreHomAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (exactPackageToRefinement U).map
        (input.canonicalAuthoredBaseToGeneratedRouteExactCoreHomAt i) =
      𝟙 (⟨(input.canonicalAuthoredBaseRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) := by
  simp only [canonicalAuthoredBaseToGeneratedRouteExactCoreHomAt,
    input.canonicalAuthoredBaseRouteGeometryAt_core]
  change (exactPackageToRefinement U).map
      (𝟙 ((input.generatedBaseRouteGeometryAt i).core :
        PackageTotalCategory U)) = 𝟙 _
  exact (exactPackageToRefinement U).map_id _

/-- The exact base core inverse becomes the categorical identity after
refinement embedding. -/
theorem canonicalAuthoredBaseToGeneratedRouteExactCoreInvAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (exactPackageToRefinement U).map
        (input.canonicalAuthoredBaseToGeneratedRouteExactCoreInvAt i) =
      𝟙 (⟨(input.generatedBaseRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) := by
  simp only [canonicalAuthoredBaseToGeneratedRouteExactCoreInvAt,
    input.canonicalAuthoredBaseRouteGeometryAt_core]
  change (exactPackageToRefinement U).map
      (𝟙 ((input.generatedBaseRouteGeometryAt i).core :
        PackageTotalCategory U)) = 𝟙 _
  exact (exactPackageToRefinement U).map_id _

/-- Exact complete-geometry hom underlying the base endpoint comparison. -/
noncomputable def canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryTotalHom (input.canonicalAuthoredBaseRouteGeometryAt i)
      (input.generatedBaseRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.canonicalAuthoredBaseToGeneratedRouteExactCoreHomAt i)
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom
    (by
      rw [input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_base]
      exact
        (input.canonicalAuthoredBaseToGeneratedRouteExactCoreHomAt_toRefinement i).symm)

/-- Exact complete-geometry inverse underlying the base endpoint comparison. -/
noncomputable def canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryTotalHom (input.generatedBaseRouteGeometryAt i)
      (input.canonicalAuthoredBaseRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.canonicalAuthoredBaseToGeneratedRouteExactCoreInvAt i)
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv
    (by
      rw [input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_base]
      exact
        (input.canonicalAuthoredBaseToGeneratedRouteExactCoreInvAt_toRefinement i).symm)

/-- Re-embedding the exact base comparison hom recovers the original complete
refinement comparison. -/
theorem canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i) =
      (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- Re-embedding the exact base comparison inverse recovers the original
complete refinement inverse. -/
theorem canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i) =
      (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The exact base comparison hom and the independently exactified inverse
form an isomorphism in the total geometry category. -/
noncomputable def canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.canonicalAuthoredBaseRouteGeometryAt i ≅
      input.generatedBaseRouteGeometryAt i where
  hom := input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i
  inv := input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i
  hom_inv_id := by
    apply (exactGeometryToRefinementGeometry U).map_injective
    change (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i ≫
          input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i) =
      (exactGeometryToRefinementGeometry U).map (𝟙 _)
    rw [Functor.map_comp,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_toRefinement]
    simpa only [Functor.map_id] using
      input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_inv i
  inv_hom_id := by
    apply (exactGeometryToRefinementGeometry U).map_injective
    change (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i ≫
          input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i) =
      (exactGeometryToRefinementGeometry U).map (𝟙 _)
    rw [Functor.map_comp,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_toRefinement,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement]
    simpa only [Functor.map_id] using
      input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_hom i

/-- The hom of the exact base endpoint isomorphism is the independently
exactified comparison hom. -/
@[simp] theorem canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i).hom =
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i := rfl

/-- The inverse of the exact base endpoint isomorphism is the independently
exactified comparison inverse. -/
@[simp] theorem canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i).inv =
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i := rfl

/-- The exact base comparison hom lies over the identity exact package map. -/
@[simp] theorem canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i).base =
      input.canonicalAuthoredBaseToGeneratedRouteExactCoreHomAt i := rfl

/-- The exact base comparison inverse lies over the identity exact package
map. -/
@[simp] theorem canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i).base =
      input.canonicalAuthoredBaseToGeneratedRouteExactCoreInvAt i := rfl

/-- The exact base comparison hom fixes the authored coefficient ring. -/
theorem canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
      i).geometry.coefficientHom = RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement i)
  change
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
      i).geometry.coefficientHom =
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
          i).hom.geometry.coefficientHom at h
  exact h.trans
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_coefficient_id i)

/-- The exact base comparison inverse fixes the authored coefficient ring. -/
theorem canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
      i).geometry.coefficientHom = RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_toRefinement i)
  change
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
      i).geometry.coefficientHom =
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
          i).inv.geometry.coefficientHom at h
  exact h.trans
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_coefficient_id i)

/-! ## Exact pulled-route endpoint comparison -/

/-- Exact identity core map from the canonical-authored pulled endpoint to the
generated pulled endpoint. -/
noncomputable def canonicalAuthoredPulledToGeneratedRouteExactCoreHomAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    PackageTotalHom (input.canonicalAuthoredPulledRouteGeometryAt i).core
      (input.generatedPulledRouteGeometryAt i).core := by
  simpa only [input.canonicalAuthoredPulledRouteGeometryAt_core] using
    PackageTotalHom.id (input.generatedPulledRouteGeometryAt i).core

/-- Exact identity core map returning from the generated pulled endpoint to
the canonical-authored pulled endpoint. -/
noncomputable def canonicalAuthoredPulledToGeneratedRouteExactCoreInvAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    PackageTotalHom (input.generatedPulledRouteGeometryAt i).core
      (input.canonicalAuthoredPulledRouteGeometryAt i).core := by
  simpa only [input.canonicalAuthoredPulledRouteGeometryAt_core] using
    PackageTotalHom.id (input.generatedPulledRouteGeometryAt i).core

/-- The exact pulled core hom becomes the categorical identity after
refinement embedding. -/
theorem canonicalAuthoredPulledToGeneratedRouteExactCoreHomAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (exactPackageToRefinement U).map
        (input.canonicalAuthoredPulledToGeneratedRouteExactCoreHomAt i) =
      𝟙 (⟨(input.canonicalAuthoredPulledRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) := by
  simp only [canonicalAuthoredPulledToGeneratedRouteExactCoreHomAt,
    input.canonicalAuthoredPulledRouteGeometryAt_core]
  change (exactPackageToRefinement U).map
      (𝟙 ((input.generatedPulledRouteGeometryAt i).core :
        PackageTotalCategory U)) = 𝟙 _
  exact (exactPackageToRefinement U).map_id _

/-- The exact pulled core inverse becomes the categorical identity after
refinement embedding. -/
theorem canonicalAuthoredPulledToGeneratedRouteExactCoreInvAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (exactPackageToRefinement U).map
        (input.canonicalAuthoredPulledToGeneratedRouteExactCoreInvAt i) =
      𝟙 (⟨(input.generatedPulledRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) := by
  simp only [canonicalAuthoredPulledToGeneratedRouteExactCoreInvAt,
    input.canonicalAuthoredPulledRouteGeometryAt_core]
  change (exactPackageToRefinement U).map
      (𝟙 ((input.generatedPulledRouteGeometryAt i).core :
        PackageTotalCategory U)) = 𝟙 _
  exact (exactPackageToRefinement U).map_id _

/-- Exact complete-geometry hom underlying the pulled endpoint comparison. -/
noncomputable def canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryTotalHom (input.canonicalAuthoredPulledRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.canonicalAuthoredPulledToGeneratedRouteExactCoreHomAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom
    (by
      rw [input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_base]
      exact
        (input.canonicalAuthoredPulledToGeneratedRouteExactCoreHomAt_toRefinement i).symm)

/-- Exact complete-geometry inverse underlying the pulled endpoint
comparison. -/
noncomputable def canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryTotalHom (input.generatedPulledRouteGeometryAt i)
      (input.canonicalAuthoredPulledRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.canonicalAuthoredPulledToGeneratedRouteExactCoreInvAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv
    (by
      rw [input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_base]
      exact
        (input.canonicalAuthoredPulledToGeneratedRouteExactCoreInvAt_toRefinement i).symm)

/-- Re-embedding the exact pulled comparison hom recovers the original
complete refinement comparison. -/
theorem canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i) =
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- Re-embedding the exact pulled comparison inverse recovers the original
complete refinement inverse. -/
theorem canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i) =
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The exact pulled comparison hom and the independently exactified inverse
form an isomorphism in the total geometry category. -/
noncomputable def canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.canonicalAuthoredPulledRouteGeometryAt i ≅
      input.generatedPulledRouteGeometryAt i where
  hom := input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i
  inv := input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i
  hom_inv_id := by
    apply (exactGeometryToRefinementGeometry U).map_injective
    change (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i ≫
          input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i) =
      (exactGeometryToRefinementGeometry U).map (𝟙 _)
    rw [Functor.map_comp,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_toRefinement,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_toRefinement]
    simpa only [Functor.map_id] using
      input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_inv i
  inv_hom_id := by
    apply (exactGeometryToRefinementGeometry U).map_injective
    change (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i ≫
          input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i) =
      (exactGeometryToRefinementGeometry U).map (𝟙 _)
    rw [Functor.map_comp,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_toRefinement,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_toRefinement]
    simpa only [Functor.map_id] using
      input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_hom i

/-- The hom of the exact pulled endpoint isomorphism is the independently
exactified comparison hom. -/
@[simp] theorem canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i).hom =
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i := rfl

/-- The inverse of the exact pulled endpoint isomorphism is the independently
exactified comparison inverse. -/
@[simp] theorem canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i).inv =
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i := rfl

/-- The exact pulled comparison hom lies over the identity exact package map. -/
@[simp] theorem canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i).base =
      input.canonicalAuthoredPulledToGeneratedRouteExactCoreHomAt i := rfl

/-- The exact pulled comparison inverse lies over the identity exact package
map. -/
@[simp] theorem canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i).base =
      input.canonicalAuthoredPulledToGeneratedRouteExactCoreInvAt i := rfl

/-- The exact pulled comparison hom fixes the authored coefficient ring. -/
theorem canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
      i).geometry.coefficientHom = RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_toRefinement i)
  change
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
      i).geometry.coefficientHom =
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
          i).hom.geometry.coefficientHom at h
  exact h.trans
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_coefficient_id i)

/-- The exact pulled comparison inverse fixes the authored coefficient ring. -/
theorem canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
      i).geometry.coefficientHom = RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_toRefinement i)
  change
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
      i).geometry.coefficientHom =
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
          i).inv.geometry.coefficientHom at h
  exact h.trans
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_coefficient_id i)

/-! ## Exact presentation naturality -/

/-- Exact base endpoint comparisons are natural on every canonical-authored
presentation edge. -/
theorem canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt j) =
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i).comp
        (input.generatedBaseRouteGeometryEdge edge) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change (exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseRouteGeometryEdge edge ≫
        input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt j) =
    (exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i ≫
        input.generatedBaseRouteGeometryEdge edge)
  rw [Functor.map_comp, Functor.map_comp,
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement,
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement]
  exact input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_naturality edge

/-- Exact pulled endpoint comparisons are natural on every independently
generated canonical-authored presentation edge. -/
theorem canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredPulledRouteGeometryEdge edge).comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt j) =
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i).comp
        (input.generatedPulledRouteGeometryEdge edge) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change (exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredPulledRouteGeometryEdge edge ≫
        input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt j) =
    (exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i ≫
        input.generatedPulledRouteGeometryEdge edge)
  rw [Functor.map_comp, Functor.map_comp,
    input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_toRefinement,
    input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_toRefinement]
  exact input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_naturality edge

/-! ## Exact comparator conjugation -/

/-- Exact base endpoint comparison conjugates the literal canonical-authored
comparator to the generated comparator. -/
theorem canonicalAuthoredBaseRouteComparator_exact_conjugation
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (input.canonicalAuthoredBaseRouteComparator cell).comp
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
          (P.twoTarget cell)) =
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
        (P.twoTarget cell)).comp
          (CompositeFiberAut.hom
            (input.generatedBaseRouteComparator cell)) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change (exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseRouteComparator cell ≫
        input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
          (P.twoTarget cell)) =
    (exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
          (P.twoTarget cell) ≫
        CompositeFiberAut.hom (input.generatedBaseRouteComparator cell))
  rw [Functor.map_comp, Functor.map_comp,
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement]
  exact input.canonicalAuthoredBaseRouteComparator_conjugation cell

/-- The exact inverse base endpoint comparison returns the generated
comparator to the literal canonical-authored comparator. -/
theorem canonicalAuthoredBaseRouteComparator_exact_conjugation_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (input.generatedBaseRouteComparator cell)).comp
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
          (P.twoTarget cell)) =
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
        (P.twoTarget cell)).comp
          (input.canonicalAuthoredBaseRouteComparator cell) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change (exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom (input.generatedBaseRouteComparator cell) ≫
        input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
          (P.twoTarget cell)) =
    (exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
          (P.twoTarget cell) ≫
        input.canonicalAuthoredBaseRouteComparator cell)
  rw [Functor.map_comp, Functor.map_comp,
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_toRefinement]
  exact input.canonicalAuthoredBaseRouteComparator_conjugation_inv cell

/-- Exact pulled endpoint comparison conjugates its independently generated
canonical-authored comparator to the generated pulled comparator. -/
theorem canonicalAuthoredPulledRouteComparator_exact_conjugation
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (input.canonicalAuthoredPulledRouteComparator cell).comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
          (P.twoTarget cell)) =
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
        (P.twoTarget cell)).comp
          (CompositeFiberAut.hom
            (input.generatedPulledRouteComparator cell)) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change (exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredPulledRouteComparator cell ≫
        input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
          (P.twoTarget cell)) =
    (exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
          (P.twoTarget cell) ≫
        CompositeFiberAut.hom (input.generatedPulledRouteComparator cell))
  rw [Functor.map_comp, Functor.map_comp,
    input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_toRefinement]
  exact input.canonicalAuthoredPulledRouteComparator_conjugation cell

/-- The exact inverse pulled endpoint comparison returns the generated
comparator to the literal canonical-authored comparator. -/
theorem canonicalAuthoredPulledRouteComparator_exact_conjugation_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (input.generatedPulledRouteComparator cell)).comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
          (P.twoTarget cell)) =
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
        (P.twoTarget cell)).comp
          (input.canonicalAuthoredPulledRouteComparator cell) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change (exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom (input.generatedPulledRouteComparator cell) ≫
        input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
          (P.twoTarget cell)) =
    (exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
          (P.twoTarget cell) ≫
        input.canonicalAuthoredPulledRouteComparator cell)
  rw [Functor.map_comp, Functor.map_comp,
    input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_toRefinement]
  exact input.canonicalAuthoredPulledRouteComparator_conjugation_inv cell

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
