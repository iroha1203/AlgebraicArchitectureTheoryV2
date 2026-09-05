import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF8

/-!
# Pasted source and endpoint actions along dependent source-change chains

The selected complete-source comparison and the two independently generated
endpoint comparisons can be pasted link by link along a dependent C1s chain.
This module proves that the selected comparison agrees with structural
composition, while the endpoint pastings equal the comparisons freshly
generated from the chain composite.  The source-pair and endpoint-pair actions
are also composed link by link, with explicit nil and cons laws, and identified
with the actions induced by the pasted comparisons.

Implementation notes: C1s uses two deliberately separate constructions.  The
three `pasted*IsoAt` definitions record geometric pasting, while the two
`recursive*PairMulEquivAt` definitions record the typed composition of the
actual action of every link.  The comparison theorems identify them.  Defining
only one conjugation by the final pasted isomorphism was rejected because it
would hide the finite-chain unitality and composition laws required by G-118.
No pasted comparison or coherence equality is accepted as an input field.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace CompositeFiberAut

/-- Conjugation by a reflexive complete-geometry isomorphism is the identity
multiplicative equivalence. -/
theorem conjugationMulEquiv_refl
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    conjugationMulEquiv (Iso.refl G) = MulEquiv.refl _ := by
  apply MulEquiv.ext
  intro automorphism
  apply Subtype.ext
  apply Iso.ext
  change ((𝟙 G : G ⟶ G) ≫ CompositeFiberAut.hom automorphism) ≫ 𝟙 G =
    CompositeFiberAut.hom automorphism
  rw [Category.id_comp, Category.comp_id]

/-- Conjugation by a composite complete-geometry isomorphism is typed
composition of the two conjugation equivalences. -/
theorem conjugationMulEquiv_trans
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : G ≅ H) (second : H ≅ K) :
    (conjugationMulEquiv first).trans (conjugationMulEquiv second) =
      conjugationMulEquiv (first ≪≫ second) := by
  apply MulEquiv.ext
  intro automorphism
  apply Subtype.ext
  apply Iso.ext
  change
    (second.inv ≫ ((first.inv ≫ CompositeFiberAut.hom automorphism) ≫
      first.hom)) ≫ second.hom =
      ((second.inv ≫ first.inv) ≫ CompositeFiberAut.hom automorphism) ≫
        (first.hom ≫ second.hom)
  simp only [Category.assoc]

end CompositeFiberAut

namespace UpperGeometryCompatibleSourcePresentationChange.Chain

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- G-118 C1s construction API: linkwise paste of the selected complete-source
comparisons supplied by the permitted source-change data. -/
noncomputable def pastedSourceGeometryIsoAt
    {input : UpperGeometryCompatibleProblemInputData ctx P k} :
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input) →
    (i : P.Vertex) →
    (chain.composite.changedInput.sourceGeometry i).package ≅
      (input.sourceGeometry i).package
  | .nil initial, i => Iso.refl (initial.sourceGeometry i).package
  | .cons head tail, i =>
      tail.pastedSourceGeometryIsoAt i ≪≫ head.geometryIso i

/-- G-118 C1s main construction: linkwise paste of base-route endpoint
comparisons independently generated from each changed input. -/
noncomputable def pastedBaseRouteExactGeometryIsoAt
    {input : UpperGeometryCompatibleProblemInputData ctx P k} :
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input) →
    (i : P.Vertex) →
    chain.composite.changedInput.generatedBaseRouteGeometryAt i ≅
      input.generatedBaseRouteGeometryAt i
  | .nil initial, i => Iso.refl (initial.generatedBaseRouteGeometryAt i)
  | .cons head tail, i =>
      tail.pastedBaseRouteExactGeometryIsoAt i ≪≫
        head.generatedBaseRouteExactGeometryIsoAt i

/-- G-118 C1s main construction: linkwise paste of pulled-route endpoint
comparisons independently generated from each changed input. -/
noncomputable def pastedPulledRouteExactGeometryIsoAt
    {input : UpperGeometryCompatibleProblemInputData ctx P k} :
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input) →
    (i : P.Vertex) →
    chain.composite.changedInput.generatedPulledRouteGeometryAt i ≅
      input.generatedPulledRouteGeometryAt i
  | .nil initial, i => Iso.refl (initial.generatedPulledRouteGeometryAt i)
  | .cons head tail, i =>
      tail.pastedPulledRouteExactGeometryIsoAt i ≪≫
        head.generatedPulledRouteExactGeometryIsoAt i

/-- C1s coherence API: the selected source comparison structurally assembled
by the chain composite equals the linkwise pasted selected comparison. -/
theorem composite_geometryIso_eq_pastedSourceGeometryIsoAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.composite.geometryIso i = chain.pastedSourceGeometryIsoAt i := by
  induction chain with
  | nil initial => simp [pastedSourceGeometryIsoAt, composite, identity]
  | cons head tail inductionHypothesis =>
      simp only [composite, pastedSourceGeometryIsoAt, comp]
      rw [inductionHypothesis]

/-- C1s main coherence theorem: the base comparison independently generated
from the chain composite equals the linkwise pasted generated comparison. -/
theorem composite_generatedBaseRouteExactGeometryIsoAt_eq_pasted
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.composite.generatedBaseRouteExactGeometryIsoAt i =
      chain.pastedBaseRouteExactGeometryIsoAt i := by
  induction chain with
  | nil initial =>
      simpa [composite, pastedBaseRouteExactGeometryIsoAt] using
        generatedBaseRouteExactGeometryIsoAt_identity initial i
  | cons head tail inductionHypothesis =>
      simp only [composite, pastedBaseRouteExactGeometryIsoAt]
      rw [generatedBaseRouteExactGeometryIsoAt_comp, inductionHypothesis]

/-- C1s main coherence theorem: the pulled comparison independently generated
from the chain composite equals the linkwise pasted generated comparison. -/
theorem composite_generatedPulledRouteExactGeometryIsoAt_eq_pasted
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.composite.generatedPulledRouteExactGeometryIsoAt i =
      chain.pastedPulledRouteExactGeometryIsoAt i := by
  induction chain with
  | nil initial =>
      simpa [composite, pastedPulledRouteExactGeometryIsoAt] using
        generatedPulledRouteExactGeometryIsoAt_identity initial i
  | cons head tail inductionHypothesis =>
      simp only [composite, pastedPulledRouteExactGeometryIsoAt]
      rw [generatedPulledRouteExactGeometryIsoAt_comp, inductionHypothesis]

/-! ## Linkwise pair actions -/

/-- G-118 C1s action construction: compose the permitted selected-source action
of every link through the dependent intermediate automorphism groups. -/
noncomputable def recursiveSourcePairMulEquivAt
    {input : UpperGeometryCompatibleProblemInputData ctx P k} :
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input) →
    (i : P.Vertex) →
    (CompositeFiberAut (chain.composite.changedInput.sourceGeometry i).package ×
        CompositeFiberAut
          (chain.composite.changedInput.sourceGeometry i).package) ≃*
      (CompositeFiberAut (input.sourceGeometry i).package ×
        CompositeFiberAut (input.sourceGeometry i).package)
  | .nil initial, _ => MulEquiv.refl _
  | .cons head tail, i =>
      (tail.recursiveSourcePairMulEquivAt i).trans
        (head.generatedSourcePairMulEquivAt i)

/-- G-118 C1s action construction: compose the independently generated
endpoint action of every link through the dependent intermediate groups. -/
noncomputable def recursiveEndpointPairMulEquivAt
    {input : UpperGeometryCompatibleProblemInputData ctx P k} :
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input) →
    (i : P.Vertex) →
    (CompositeFiberAut
          (chain.composite.changedInput.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut
          (chain.composite.changedInput.generatedPulledRouteGeometryAt i)) ≃*
      (CompositeFiberAut (input.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut (input.generatedPulledRouteGeometryAt i))
  | .nil initial, _ => MulEquiv.refl _
  | .cons head tail, i =>
      (tail.recursiveEndpointPairMulEquivAt i).trans
        (head.generatedEndpointPairMulEquivAt i)

/-- C1s unitality API: the recursively composed selected-source action of the
empty chain is the identity. -/
@[simp] theorem recursiveSourcePairMulEquivAt_nil
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    recursiveSourcePairMulEquivAt
        (UpperGeometryCompatibleSourcePresentationChange.Chain.nil input) i =
      MulEquiv.refl _ := by
  rfl

/-- C1s composition API: the selected-source action of a cons chain is the
typed tail action followed by the head-link action. -/
@[simp] theorem recursiveSourcePairMulEquivAt_cons
    (head : UpperGeometryCompatibleSourcePresentationChange input)
    (tail : UpperGeometryCompatibleSourcePresentationChange.Chain
      head.changedInput)
    (i : P.Vertex) :
    recursiveSourcePairMulEquivAt
        (UpperGeometryCompatibleSourcePresentationChange.Chain.cons head tail) i =
      (tail.recursiveSourcePairMulEquivAt i).trans
        (head.generatedSourcePairMulEquivAt i) := by
  rfl

/-- C1s unitality API: the recursively composed generated-endpoint action of
the empty chain is the identity. -/
@[simp] theorem recursiveEndpointPairMulEquivAt_nil
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    recursiveEndpointPairMulEquivAt
        (UpperGeometryCompatibleSourcePresentationChange.Chain.nil input) i =
      MulEquiv.refl _ := by
  rfl

/-- C1s composition API: the generated-endpoint action of a cons chain is the
typed tail action followed by the head-link generated action. -/
@[simp] theorem recursiveEndpointPairMulEquivAt_cons
    (head : UpperGeometryCompatibleSourcePresentationChange input)
    (tail : UpperGeometryCompatibleSourcePresentationChange.Chain
      head.changedInput)
    (i : P.Vertex) :
    recursiveEndpointPairMulEquivAt
        (UpperGeometryCompatibleSourcePresentationChange.Chain.cons head tail) i =
      (tail.recursiveEndpointPairMulEquivAt i).trans
        (head.generatedEndpointPairMulEquivAt i) := by
  rfl

/-- C1s comparison API: source-pair conjugation induced directly by the pasted
selected source comparison of a dependent chain. -/
noncomputable def pastedSourcePairMulEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    (CompositeFiberAut (chain.composite.changedInput.sourceGeometry i).package ×
        CompositeFiberAut
          (chain.composite.changedInput.sourceGeometry i).package) ≃*
      (CompositeFiberAut (input.sourceGeometry i).package ×
        CompositeFiberAut (input.sourceGeometry i).package) :=
  MulEquiv.prodCongr
    (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedSourceGeometryIsoAt i))
    (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedSourceGeometryIsoAt i))

/-- C1s comparison API: endpoint-pair conjugation induced directly by the two
independently generated and pasted endpoint comparisons. -/
noncomputable def pastedEndpointPairMulEquivAt
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    (CompositeFiberAut
          (chain.composite.changedInput.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut
          (chain.composite.changedInput.generatedPulledRouteGeometryAt i)) ≃*
      (CompositeFiberAut (input.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut (input.generatedPulledRouteGeometryAt i)) :=
  MulEquiv.prodCongr
    (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedBaseRouteExactGeometryIsoAt i))
    (CompositeFiberAut.conjugationMulEquiv
      (chain.pastedPulledRouteExactGeometryIsoAt i))

/-- C1s main coherence theorem: the pasted selected-source action equals the
typed recursive composition of the actual action of every link. -/
theorem pastedSourcePairMulEquivAt_eq_recursive
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.pastedSourcePairMulEquivAt i =
      chain.recursiveSourcePairMulEquivAt i := by
  induction chain with
  | nil initial =>
      simp only [pastedSourcePairMulEquivAt, pastedSourceGeometryIsoAt,
        recursiveSourcePairMulEquivAt, composite, identity, changedInput]
      rw [CompositeFiberAut.conjugationMulEquiv_refl]
      rfl
  | cons head tail inductionHypothesis =>
      rw [recursiveSourcePairMulEquivAt_cons, ← inductionHypothesis]
      simp only [pastedSourcePairMulEquivAt, pastedSourceGeometryIsoAt,
        generatedSourcePairMulEquivAt]
      rw [← CompositeFiberAut.conjugationMulEquiv_trans]
      rfl

/-- C1s main coherence theorem: the pasted generated-endpoint action equals the
typed recursive composition of the actual generated action of every link. -/
theorem pastedEndpointPairMulEquivAt_eq_recursive
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.pastedEndpointPairMulEquivAt i =
      chain.recursiveEndpointPairMulEquivAt i := by
  induction chain with
  | nil initial =>
      rw [pastedEndpointPairMulEquivAt,
        pastedBaseRouteExactGeometryIsoAt,
        pastedPulledRouteExactGeometryIsoAt,
        recursiveEndpointPairMulEquivAt]
      simp only [composite]
      have h := identity_changedInput initial
      cases h
      change
        MulEquiv.prodCongr
            (CompositeFiberAut.conjugationMulEquiv
              (Iso.refl (initial.generatedBaseRouteGeometryAt i)))
            (CompositeFiberAut.conjugationMulEquiv
              (Iso.refl (initial.generatedPulledRouteGeometryAt i))) =
          MulEquiv.refl
            (CompositeFiberAut (initial.generatedBaseRouteGeometryAt i) ×
              CompositeFiberAut (initial.generatedPulledRouteGeometryAt i))
      rw [CompositeFiberAut.conjugationMulEquiv_refl,
        CompositeFiberAut.conjugationMulEquiv_refl]
      rfl
  | cons head tail inductionHypothesis =>
      rw [recursiveEndpointPairMulEquivAt_cons, ← inductionHypothesis]
      simp only [pastedEndpointPairMulEquivAt,
        pastedBaseRouteExactGeometryIsoAt,
        pastedPulledRouteExactGeometryIsoAt,
        generatedEndpointPairMulEquivAt]
      rw [← CompositeFiberAut.conjugationMulEquiv_trans,
        ← CompositeFiberAut.conjugationMulEquiv_trans]
      rfl

/-- The source-pair action generated by the composite change is exactly the
action induced by the pasted source comparison. -/
theorem composite_generatedSourcePairMulEquivAt_eq_pasted
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.composite.generatedSourcePairMulEquivAt i =
      chain.pastedSourcePairMulEquivAt i := by
  rw [generatedSourcePairMulEquivAt, pastedSourcePairMulEquivAt,
    chain.composite_geometryIso_eq_pastedSourceGeometryIsoAt]

/-- The endpoint-pair action generated by the composite change is exactly the
action induced by the pasted generated endpoint comparisons. -/
theorem composite_generatedEndpointPairMulEquivAt_eq_pasted
    (chain : UpperGeometryCompatibleSourcePresentationChange.Chain input)
    (i : P.Vertex) :
    chain.composite.generatedEndpointPairMulEquivAt i =
      chain.pastedEndpointPairMulEquivAt i := by
  rw [generatedEndpointPairMulEquivAt, pastedEndpointPairMulEquivAt,
    chain.composite_generatedBaseRouteExactGeometryIsoAt_eq_pasted,
    chain.composite_generatedPulledRouteExactGeometryIsoAt_eq_pasted]

end UpperGeometryCompatibleSourcePresentationChange.Chain
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
