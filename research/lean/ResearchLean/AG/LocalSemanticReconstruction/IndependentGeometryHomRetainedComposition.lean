import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomInvariantComposition
import Formal.Util.AssertStandardAxioms

/-!
# Retaining a directly composed common Hom table

The composed table is supplied by its primitive point construction. Only its
object and invariant-index rows are used here, in their direct composition
form. All original finite query tables survive unchanged. Auxiliary invariant
rows and erasure are constructed after this retained family.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode} {I J K : InvariantFamily U}
variable (p : Retained.{u, v} I J mode) (q : Retained.{u, v} J K mode)
variable (h : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
variable (ho : ∀ A C, h (.object A C) = q.table (.object (p.objectMap A) C))
variable (hi : invariant h = IndependentCarrierGraph.compose I.Index J.Index K.Index
  (invariant p.table) p.indexRows (invariant q.table))

/-- Retain the primitive composite as coherent finite tables with its directed object and invariant-index laws. -/
def composeRetained : Retained.{u, v} I K mode where
  family := TagChange.read h
  objectRows := by
    intro A
    obtain ⟨C, hC, hu⟩ := q.objectRows (p.objectMap A)
    refine ⟨C, (ho A C).trans hC, ?_⟩
    intro D hD
    exact hu D ((ho A D).symm.trans hD)
  indexRows := by
    change IndependentCarrierGraph.IsLawful I.Index K.Index (invariant h)
    rw [hi]
    exact IndependentCarrierGraph.compose_isLawful I.Index J.Index K.Index
      (invariant p.table) p.indexRows (invariant q.table) q.indexRows

/-- Every original query is retained exactly, before choosing any auxiliary invariant row. -/
theorem composeRetained_table : (composeRetained p q h ho hi).table = h :=
  TagChange.assemble_read h

include hi in
/-- A composite invariant-index point is the second point at the first primitive index image. -/
theorem composite_index_point (i : I.Index) (k : K.Index) :
    h (.invariant (.edge I.Index K.Index i k)) =
      q.table (.invariant (.edge J.Index K.Index (p.indexMap i) k)) :=
  (congrFun hi (.edge I.Index K.Index i k)).trans
    (IndependentCarrierGraph.compose_edge I.Index J.Index K.Index
      (invariant p.table) p.indexRows (invariant q.table) i k)

include ho in
/-- Each true composite object point factors through one true primitive object point of each input. -/
theorem composite_object_factor (A C : ArchitectureObject U) (hAC : h (.object A C) = true) :
    ∃ B, p.table (.object A B) = true ∧ q.table (.object B C) = true :=
  ⟨p.objectMap A, (p.object_point_iff A _).2 rfl, (ho A C).symm.trans hAC⟩

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness
