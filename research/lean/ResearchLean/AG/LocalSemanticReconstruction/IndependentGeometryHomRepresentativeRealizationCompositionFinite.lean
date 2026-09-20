import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointCompositionFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRealizationCompositionRows
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomAlgebraicCompositionFinite
import Formal.Util.AssertStandardAxioms

/-!
# Finite fragments for directed realization composition

Every representative support, axis, or observable point is determined by
one context point and two value points in the original common declaration.
The fragment theorem uses the actual quotient fragments, so auxiliary
invariant witnesses do not become extra local observations.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}}

namespace RepresentativeRealization

variable {A B C : ArchitectureObject U}

/-- Each composed directed realization point depends on at most three original common query cells. -/
theorem composeRealization_finite_support
    (s : IndependentContextPrimitive.Table A) (t : IndependentContextPrimitive.Table B)
    (h : Table.{u, v} U .representative) (hp : PointLaws s t h)
    (hctx : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h W V = true)
    (k : Table.{u, v} U .representative) (a : RealizationQuery A C .representative) :
    ∃ (D E : Finset (Query.{u, v} U .representative)), D.card + E.card ≤ 3 ∧
      ∀ (h' : Table.{u, v} U .representative) (hp' : PointLaws s t h')
        (hctx' : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h' W V = true)
        (k' : Table.{u, v} U .representative),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        composeRealization s t h hp hctx k a = composeRealization s t h' hp' hctx' k' a := by
  cases a with
  | representativeSupport W Z x z =>
    obtain ⟨D, E, hcard, hs⟩ := IndependentFixedIndexedPointGraph.compose_lifted_finite_support
      (fun W V => Query.atObjects A B (.context .forward W V))
      (fun W V x y => Query.atObjects A B (.realization (.representativeSupport W V x y)))
      (fun V Z y z => Query.atObjects B C (.realization (.representativeSupport V Z y z)))
      h k hctx hp.supportRows W Z x z
    refine ⟨D, E, hcard, ?_⟩
    intro h' hp' hctx' k' hD hE
    exact hs h' k' hctx' hp'.supportRows hD hE
  | representativeAxis W Z x z =>
    obtain ⟨D, E, hcard, hs⟩ := IndependentFixedIndexedPointGraph.compose_lifted_finite_support
      (fun W V => Query.atObjects A B (.context .forward W V))
      (fun W V x y => Query.atObjects A B (.realization (.representativeAxis W V x y)))
      (fun V Z y z => Query.atObjects B C (.realization (.representativeAxis V Z y z)))
      h k hctx hp.axisRows W Z x z
    refine ⟨D, E, hcard, ?_⟩
    intro h' hp' hctx' k' hD hE
    exact hs h' k' hctx' hp'.axisRows hD hE
  | representativeObservable W Z x z =>
    obtain ⟨D, E, hcard, hs⟩ := IndependentFixedIndexedPointGraph.compose_lifted_finite_support
      (fun W V => Query.atObjects A B (.context .forward W V))
      (fun W V x y => Query.atObjects A B (.realization (.representativeObservable W V x y)))
      (fun V Z y z => Query.atObjects B C (.realization (.representativeObservable V Z y z)))
      h k hctx hp.observableRows W Z x z
    refine ⟨D, E, hcard, ?_⟩
    intro h' hp' hctx' k' hD hE
    exact hs h' k' hctx' hp'.observableRows hD hE

end RepresentativeRealization

namespace Composition

variable (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .representative)
variable (ep : GeometryComponents.RepresentativePoints s t p)

/-- The directed realization composite is fixed by two actual finite quotient fragments totaling at most three cells. -/
theorem representativeRealization_finite_fragment
    (a : RealizationQuery (assemble s).core.object (assemble r).core.object .representative) :
    ∃ (D E : Finset (Query.{u, v} U .representative)), D.card + E.card ≤ 3 ∧
      ∀ (p' : InvariantWitness.Local.{u, v}
          (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)
        (hp' : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p').table)
        (q' : InvariantWitness.Local.{u, v}
          (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .representative)
        (ep' : GeometryComponents.RepresentativePoints s t p'),
        InvariantWitness.fragment _ _ p D = InvariantWitness.fragment _ _ p' D →
        InvariantWitness.fragment _ _ q E = InvariantWitness.fragment _ _ q' E →
        representativeRealizationRows s t r p hp q ep a = representativeRealizationRows s t r p' hp' q' ep' a := by
  obtain ⟨D, E, hcard, hs⟩ := RepresentativeRealization.composeRealization_finite_support
    s.1.val.2.1.val t.1.val.2.1.val (PackageAssembly.retained s.1 t.1 p).table ep
    hp.contextRows.forward (PackageAssembly.retained t.1 r.1 q).table a
  refine ⟨D, E, hcard, ?_⟩
  intro p' hp' q' ep' hD hE
  exact hs (PackageAssembly.retained s.1 t.1 p').table ep' hp'.contextRows.forward
    (PackageAssembly.retained t.1 r.1 q').table
    ((InvariantWitness.fragment_eq_iff_points _ _ p p' D).1 hD)
    ((InvariantWitness.fragment_eq_iff_points _ _ q q' E).1 hE)

end Composition

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRealization
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
