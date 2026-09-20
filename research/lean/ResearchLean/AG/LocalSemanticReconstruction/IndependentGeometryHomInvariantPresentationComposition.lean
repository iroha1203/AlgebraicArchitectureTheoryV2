import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRetainedComposition
import Formal.Util.AssertStandardAxioms

/-!
# Coherent auxiliary presentations of primitive Hom composition

An active composite invariant row follows the first index point and composes
the two original auxiliary rows. Predicate rows and inactive candidates remain
false. Object factorization proves the evaluation rules before any auxiliary
choices are erased. No native transport existence is used to define these rows.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- A predicate at either end forces every composed auxiliary value point to be inactive. -/
theorem composeRow_inactive (S M T : Invariant U)
    (h k : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (w z : IndependentInverseGraph.Table.{u, u}) (hw : RowLaw S M h w) (hz : RowLaw M T k z)
    (hn : isFunction S = false ∨ isFunction T = false) (a : IndependentInverseGraph.Query.{u, u}) :
    composeRow S M T h k w z hw hz a = false := by
  cases S <;> cases M <;> cases T
  all_goals first | exact False.elim hw | exact False.elim hz | exact rfl | simp [isFunction] at hn

variable {I J K : InvariantFamily U}
variable (p : Presentation.{u, v} I J mode) (q : Presentation.{u, v} J K mode)

/-- Compose one active auxiliary row through the first primitive invariant-index image. -/
def compositeAuxRow (i : I.Index) (k : K.Index) : IndependentInverseGraph.Table.{u, u} := by
  classical
  exact if hjk : q.retained.table (.invariant (.edge J.Index K.Index (p.retained.indexMap i) k)) = true then
    composeRow (I.invariant i) (J.invariant (p.retained.indexMap i)) (K.invariant k)
      p.retained.table q.retained.table
      (row (TagChange.assemble p.auxiliary) I.Index J.Index i (p.retained.indexMap i))
      (row (TagChange.assemble q.auxiliary) J.Index K.Index (p.retained.indexMap i) k)
      (p.rows i _ ((p.retained.index_point_iff i _).2 rfl)) (q.rows _ k hjk)
  else fun _ => false

/-- A true second index point exposes exactly the two composed primitive auxiliary rows. -/
theorem compositeAuxRow_active (i : I.Index) (k : K.Index)
    (hjk : q.retained.table (.invariant (.edge J.Index K.Index (p.retained.indexMap i) k)) = true) :
    compositeAuxRow p q i k =
      composeRow (I.invariant i) (J.invariant (p.retained.indexMap i)) (K.invariant k)
        p.retained.table q.retained.table
        (row (TagChange.assemble p.auxiliary) I.Index J.Index i (p.retained.indexMap i))
        (row (TagChange.assemble q.auxiliary) J.Index K.Index (p.retained.indexMap i) k)
        (p.rows i _ ((p.retained.index_point_iff i _).2 rfl)) (q.rows _ k hjk) := by
  classical
  simp only [compositeAuxRow, dif_pos hjk]

/-- Inactive composite index points and predicate endpoints contribute no auxiliary observations. -/
theorem compositeAuxRow_inactive (i : I.Index) (k : K.Index) (a : IndependentInverseGraph.Query.{u, u})
    (hn : q.retained.table (.invariant (.edge J.Index K.Index (p.retained.indexMap i) k)) = false ∨
      isFunction (I.invariant i) = false ∨ isFunction (K.invariant k) = false) :
    compositeAuxRow p q i k a = false := by
  classical
  by_cases hjk : q.retained.table (.invariant (.edge J.Index K.Index (p.retained.indexMap i) k)) = true
  · rw [compositeAuxRow_active p q i k hjk]
    rcases hn with hf | hn
    · exact False.elim (Bool.noConfusion (hjk.symm.trans hf))
    · exact composeRow_inactive _ _ _ _ _ _ _ _ _ hn a
  · simp only [compositeAuxRow, dif_neg hjk]

/-- Original candidate-index queries read the primitive composite row, with all other carriers false. -/
def composeAux : Table.{u} := by
  classical
  intro a
  cases a with
  | row M N i k a =>
    exact if hM : M = I.Index then if hN : N = K.Index then
      compositeAuxRow p q (hM ▸ i) (hN ▸ k) a else false else false

/-- Selected original index carriers expose exactly the corresponding primitive composite row. -/
theorem composeAux_row (i : I.Index) (k : K.Index) :
    row (composeAux p q) I.Index K.Index i k = compositeAuxRow p q i k := by
  classical
  funext a
  simp [row, composeAux]

/-- Every candidate query with an incorrect invariant-index carrier remains false. -/
theorem composeAux_wrong_indices (M N : Type u) (i : M) (k : N)
    (a : IndependentInverseGraph.Query.{u, u}) (hn : M ≠ I.Index ∨ N ≠ K.Index) :
    composeAux p q (.row M N i k a) = false := by
  classical
  rcases hn with hM | hN
  · simp only [composeAux, dif_neg hM]
  · by_cases hM : M = I.Index <;> simp only [composeAux, hM, hN, ↓reduceDIte]

variable (h : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
variable (ho : ∀ A C, h (.object A C) = q.retained.table (.object (p.retained.objectMap A) C))
variable (hi : invariant h = IndependentCarrierGraph.compose I.Index J.Index K.Index
  (invariant p.retained.table) p.retained.indexRows (invariant q.retained.table))

/-- The directly composed auxiliary table satisfies every original candidate and predicate inactivity rule. -/
theorem composeAux_typed : IsAuxTyped I K (composeRetained p.retained q.retained h ho hi) (composeAux p q) := by
  constructor
  · exact composeAux_wrong_indices p q
  · intro i k a hn
    change h (.invariant (.edge I.Index K.Index i k)) = false ∨
      isFunction (I.invariant i) = false ∨ isFunction (K.invariant k) = false at hn
    have hn' : q.retained.table (.invariant (.edge J.Index K.Index (p.retained.indexMap i) k)) = false ∨
        isFunction (I.invariant i) = false ∨ isFunction (K.invariant k) = false := by
      rcases hn with hf | hn
      · exact Or.inl ((composite_index_point p.retained q.retained h hi i k).symm.trans hf)
      · exact Or.inr hn
    exact (congrFun (composeAux_row p q i k) a).trans (compositeAuxRow_inactive p q i k a hn')

/-- Compose coherent presentations by primitive object, invariant-index, and auxiliary value points. -/
def composePresentation : Presentation.{u, v} I K mode where
  retained := composeRetained p.retained q.retained h ho hi
  auxiliary := TagChange.read (composeAux p q)
  auxiliaryTyped := composeAux_typed p q h ho hi
  rows := by
    intro i k hik
    have hjk := (composite_index_point p.retained q.retained h hi i k).symm.trans hik
    change RowLaw (I.invariant i) (K.invariant k) h (row (composeAux p q) I.Index K.Index i k)
    rw [composeAux_row p q i k, compositeAuxRow_active p q i k hjk]
    exact composeRow_law _ _ _ _ _ h _ _
      (p.rows i _ ((p.retained.index_point_iff i _).2 rfl)) (q.rows _ k hjk)
      (composite_object_factor p.retained q.retained h ho)

/-- Coherent composition preserves the entire supplied primitive point table before witness erasure. -/
theorem composePresentation_table : (composePresentation p q h ho hi).retained.table = h :=
  composeRetained_table p.retained q.retained h ho hi

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness
