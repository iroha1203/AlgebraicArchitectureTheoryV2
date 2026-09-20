import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseAgainstCompositionFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoreRawComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomAlgebraicCompositionFinite
import Formal.Util.AssertStandardAxioms

/-!
# Common finite fragments determining raw coordinate and relation composition

Each raw coordinate or relation output uses two backward context points and
at most two value points from the original common Hom declaration. The same
supports determine the output on the actual local quotient's finite fragments.
The result concerns these two roles; dependent local-data support is separate.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

noncomputable section

universe u v

open Site IndependentGeometryTableAssembly

namespace ExplicitRaw

variable {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}
variable (s : IndependentRawCandidate.Table.{u, v} A) (t : IndependentRawCandidate.Table.{u, v} B)
variable (r : IndependentRawCandidate.Table.{u, v} C)
variable (h : Table.{u, v} U .explicit) (hp : PointLaws s t h) (k : Table.{u, v} U .explicit)
variable (hq : ∀ Z : ArchCtx C, ∃! V : ArchCtx B, contextPoints k V Z = true) (kp : PointLaws t r k)

/-- Any coordinate-composition output is determined by at most four original common query values. -/
theorem composeCoordinate_finite_support
    (a : IndependentIndexedInverseGraph.Query.{u + 1, u + 1, u, u} (ArchCtx A) (ArchCtx C)) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)), D.card + E.card ≤ 4 ∧
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws s t h')
        (k' : Table.{u, v} U .explicit) (hq' : ∀ Z : ArchCtx C, ∃! V : ArchCtx B, contextPoints k' V Z = true)
        (kp' : PointLaws t r k'),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        composeCoordinate s t r h hp k hq kp a = composeCoordinate s t r h' hp' k' hq' kp' a := by
  obtain ⟨D, E, hcard, hs⟩ := IndependentIndexedInverseGraph.composeAgainst_lifted_finite_support
    (fun WV => Query.atObjects A B (.context .backward WV.1 WV.2))
    (fun VZ => Query.atObjects B C (.context .backward VZ.1 VZ.2))
    (fun | .edge W V (.forward a) => Query.atObjects A B (.raw (.coordinate .forward W V a))
         | .edge W V (.backward a) => Query.atObjects A B (.raw (.coordinate .backward W V (InverseRows.reverse a))))
    (fun | .edge V Z (.forward a) => Query.atObjects B C (.raw (.coordinate .forward V Z a))
         | .edge V Z (.backward a) => Query.atObjects B C (.raw (.coordinate .backward V Z (InverseRows.reverse a))))
    (coordinateTable (A := A) (B := B)) (coordinateTable (A := B) (B := C))
    (by intro h a; cases a with | edge W V a => cases a <;> rfl)
    (by intro h a; cases a with | edge V Z a => cases a <;> rfl)
    (IndependentRawCandidate.coord s) (IndependentRawCandidate.coord t) (IndependentRawCandidate.coord r)
    h k (coordinateTable_isLawful s t h hp) hq (coordinateTable_isLawful t r k kp) a
  refine ⟨D, E, hcard, ?_⟩
  intro h' hp' k' hq' kp' hD hE
  exact hs h' k' (coordinateTable_isLawful s t h' hp') hq' (coordinateTable_isLawful t r k' kp') hD hE

/-- Any relation-generator composition output is determined by at most four original common query values. -/
theorem composeRelation_finite_support
    (a : IndependentIndexedInverseGraph.Query.{u + 1, u + 1, u, u} (ArchCtx A) (ArchCtx C)) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)), D.card + E.card ≤ 4 ∧
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws s t h')
        (k' : Table.{u, v} U .explicit) (hq' : ∀ Z : ArchCtx C, ∃! V : ArchCtx B, contextPoints k' V Z = true)
        (kp' : PointLaws t r k'),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        composeRelation s t r h hp k hq kp a = composeRelation s t r h' hp' k' hq' kp' a := by
  obtain ⟨D, E, hcard, hs⟩ := IndependentIndexedInverseGraph.composeAgainst_lifted_finite_support
    (fun WV => Query.atObjects A B (.context .backward WV.1 WV.2))
    (fun VZ => Query.atObjects B C (.context .backward VZ.1 VZ.2))
    (fun | .edge W V (.forward a) => Query.atObjects A B (.raw (.relation .forward W V a))
         | .edge W V (.backward a) => Query.atObjects A B (.raw (.relation .backward W V (InverseRows.reverse a))))
    (fun | .edge V Z (.forward a) => Query.atObjects B C (.raw (.relation .forward V Z a))
         | .edge V Z (.backward a) => Query.atObjects B C (.raw (.relation .backward V Z (InverseRows.reverse a))))
    (relationTable (A := A) (B := B)) (relationTable (A := B) (B := C))
    (by intro h a; cases a with | edge W V a => cases a <;> rfl)
    (by intro h a; cases a with | edge V Z a => cases a <;> rfl)
    (IndependentRawCandidate.rel s) (IndependentRawCandidate.rel t) (IndependentRawCandidate.rel r)
    h k (relationTable_isLawful s t h hp) hq (relationTable_isLawful t r k kp) a
  refine ⟨D, E, hcard, ?_⟩
  intro h' hp' k' hq' kp' hD hE
  exact hs h' k' (relationTable_isLawful s t h' hp') hq' (relationTable_isLawful t r k' kp') hD hE

end ExplicitRaw

namespace Composition

variable {U : AtomCarrier.{u}} (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)
variable (rp : GeometryComponents.ExplicitRawPoints s t p) (rq : GeometryComponents.ExplicitRawPoints t r q)

/-- At most four cells in the actual quotient fragments determine each primitive raw-coordinate composition output. -/
theorem rawCoordinate_finite_fragment
    (a : IndependentIndexedInverseGraph.Query.{u + 1, u + 1, u, u}
      (ArchCtx (assemble s).core.object) (ArchCtx (assemble r).core.object)) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)), D.card + E.card ≤ 4 ∧
      ∀ (p' : InvariantWitness.Local.{u, v}
          (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
        (q' : InvariantWitness.Local.{u, v}
          (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
        (hq' : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q').table)
        (rp' : GeometryComponents.ExplicitRawPoints s t p') (rq' : GeometryComponents.ExplicitRawPoints t r q'),
        InvariantWitness.fragment _ _ p D = InvariantWitness.fragment _ _ p' D →
        InvariantWitness.fragment _ _ q E = InvariantWitness.fragment _ _ q' E →
        ExplicitRaw.composeCoordinate s.2.2.2.val t.2.2.2.val r.2.2.2.val
          (PackageAssembly.retained s.1 t.1 p).table rp (PackageAssembly.retained t.1 r.1 q).table hq.contextRows.backward rq a =
        ExplicitRaw.composeCoordinate s.2.2.2.val t.2.2.2.val r.2.2.2.val
          (PackageAssembly.retained s.1 t.1 p').table rp' (PackageAssembly.retained t.1 r.1 q').table hq'.contextRows.backward rq' a := by
  obtain ⟨D, E, hcard, hs⟩ := ExplicitRaw.composeCoordinate_finite_support s.2.2.2.val t.2.2.2.val r.2.2.2.val
    (PackageAssembly.retained s.1 t.1 p).table rp (PackageAssembly.retained t.1 r.1 q).table hq.contextRows.backward rq a
  refine ⟨D, E, hcard, ?_⟩
  intro p' q' hq' rp' rq' hD hE
  exact hs _ rp' _ hq'.contextRows.backward rq'
    ((InvariantWitness.fragment_eq_iff_points _ _ p p' D).1 hD)
    ((InvariantWitness.fragment_eq_iff_points _ _ q q' E).1 hE)

/-- At most four cells in the actual quotient fragments determine each raw relation-generator composition output. -/
theorem rawRelation_finite_fragment
    (a : IndependentIndexedInverseGraph.Query.{u + 1, u + 1, u, u}
      (ArchCtx (assemble s).core.object) (ArchCtx (assemble r).core.object)) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)), D.card + E.card ≤ 4 ∧
      ∀ (p' : InvariantWitness.Local.{u, v}
          (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
        (q' : InvariantWitness.Local.{u, v}
          (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
        (hq' : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q').table)
        (rp' : GeometryComponents.ExplicitRawPoints s t p') (rq' : GeometryComponents.ExplicitRawPoints t r q'),
        InvariantWitness.fragment _ _ p D = InvariantWitness.fragment _ _ p' D →
        InvariantWitness.fragment _ _ q E = InvariantWitness.fragment _ _ q' E →
        ExplicitRaw.composeRelation s.2.2.2.val t.2.2.2.val r.2.2.2.val
          (PackageAssembly.retained s.1 t.1 p).table rp (PackageAssembly.retained t.1 r.1 q).table hq.contextRows.backward rq a =
        ExplicitRaw.composeRelation s.2.2.2.val t.2.2.2.val r.2.2.2.val
          (PackageAssembly.retained s.1 t.1 p').table rp' (PackageAssembly.retained t.1 r.1 q').table hq'.contextRows.backward rq' a := by
  obtain ⟨D, E, hcard, hs⟩ := ExplicitRaw.composeRelation_finite_support s.2.2.2.val t.2.2.2.val r.2.2.2.val
    (PackageAssembly.retained s.1 t.1 p).table rp (PackageAssembly.retained t.1 r.1 q).table hq.contextRows.backward rq a
  refine ⟨D, E, hcard, ?_⟩
  intro p' q' hq' rp' rq' hD hE
  exact hs _ rp' _ hq'.contextRows.backward rq'
    ((InvariantWitness.fragment_eq_iff_points _ _ p p' D).1 hD)
    ((InvariantWitness.fragment_eq_iff_points _ _ q q' E).1 hE)

end Composition

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
