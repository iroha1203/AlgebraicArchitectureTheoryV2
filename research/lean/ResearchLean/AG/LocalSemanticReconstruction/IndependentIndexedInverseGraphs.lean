import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedCarrierGraphs
import ResearchLean.AG.LocalSemanticReconstruction.IndependentInverseGraphReadings
import Formal.Util.AssertStandardAxioms

/-!
# Dependent equivalences on candidate index and carrier pairs

A total-functional index graph activates one target index for each source.
Each active fiber consists of two candidate-carrier point graphs and their
pointwise inverse rule. No bijectivity of the index map is assumed. The query
precedes the selected index map and fiber carriers, and inactive responses
are uniquely false.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraph

noncomputable section

universe u v w z

variable (I : Type u) (J : Type v)

/-- Candidate index pairs with one direction-tagged candidate carrier point query. -/
inductive Query where
  /-- One forward or backward fiber point, before the active indices and carriers are selected. -/
  | edge (i : I) (j : J) (q : IndependentInverseGraph.Query.{w, z})

/-- Every local value is a single Boolean. -/
abbrev Table := Query.{u, v, w, z} I J → Bool

variable {I J}

/-- The two candidate-carrier directions at one candidate index pair. -/
def row (t : Table.{u, v, w, z} I J) (i : I) (j : J) : IndependentInverseGraph.Table.{w, z} :=
  fun q => t (.edge i j q)

/-- Index inactivity and the original primitive inverse point conditions. -/
structure IsLawful (p : I → J → Bool) (S : I → Type w) (T : J → Type z)
    (t : Table.{u, v, w, z} I J) : Prop where
  /-- Both direction-tagged point graphs vanish at inactive index pairs. -/
  inactive : ∀ i j, p i j = false → ∀ q, t (.edge i j q) = false
  /-- Active rows have unique outputs in both directions and the pointwise inverse condition. -/
  active : ∀ i j, p i j = true → IndependentInverseGraph.IsLawful (S i) (T j) (row t i j)

variable (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
variable (S : I → Type w) (T : J → Type z)

/-- Assemble the native dependent equivalences using only active primitive inverse rows. -/
def assemble (t : Table.{u, v, w, z} I J) (h : IsLawful p S T t) :
    ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i) :=
  fun i => IndependentInverseGraph.assemble _ _ (row t i (IndependentIndexedCarrierGraph.index p hp i))
    (h.active i _ ((IndependentIndexedCarrierGraph.active_iff p hp i _).2 rfl))

/-- Read all native fiber equivalences, keeping inactive index rows false. -/
def read (f : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i)) : Table.{u, v, w, z} I J := by
  classical
  intro q
  cases q with
  | edge i j q => exact (if hj : j = IndependentIndexedCarrierGraph.index p hp i then
      IndependentInverseGraph.read (S i) (T j) (hj.symm ▸ f i) q else false)

/-- Reading the active index row recovers both native fiber point graphs. -/
theorem row_read (f : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i)) (i : I) :
    row (read p hp S T f) i (IndependentIndexedCarrierGraph.index p hp i) =
      IndependentInverseGraph.read (S i) (T (IndependentIndexedCarrierGraph.index p hp i)) (f i) := by
  classical
  funext q
  simp [row, read]

/-- Native dependent equivalences supply active inverse laws and forced inactive values. -/
theorem read_isLawful (f : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i)) :
    IsLawful p S T (read p hp S T f) := by
  classical
  constructor
  · intro i j hij q
    have hj : j ≠ IndependentIndexedCarrierGraph.index p hp i := by
      intro he
      exact Bool.noConfusion (hij.symm.trans ((IndependentIndexedCarrierGraph.active_iff p hp i j).2 he))
    simp [read, hj]
  · intro i j hij
    have hj := (IndependentIndexedCarrierGraph.active_iff p hp i j).1 hij
    subst j
    rw [row_read]
    exact IndependentInverseGraph.read_isLawful _ _ (f i)

/-- The native dependent equivalence is recovered on every fiber, including both inverse functions. -/
theorem assemble_read (f : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i)) :
    assemble p hp S T (read p hp S T f) (read_isLawful p hp S T f) = f := by
  funext i
  have hc : (⟨row (read p hp S T f) i (IndependentIndexedCarrierGraph.index p hp i),
      (read_isLawful p hp S T f).active i _
        ((IndependentIndexedCarrierGraph.active_iff p hp i _).2 rfl)⟩ :
      {t // IndependentInverseGraph.IsLawful (S i) (T (IndependentIndexedCarrierGraph.index p hp i)) t}) =
      ⟨IndependentInverseGraph.read _ _ (f i), IndependentInverseGraph.read_isLawful _ _ (f i)⟩ :=
    Subtype.ext (row_read p hp S T f i)
  exact (congrArg
    (IndependentInverseGraph.readingEquiv (S i) (T (IndependentIndexedCarrierGraph.index p hp i))).symm hc).trans
      (IndependentInverseGraph.assemble_read _ _ (f i))

/-- Re-reading restores every active/inactive index and carrier row exactly. -/
theorem read_assemble (t : Table.{u, v, w, z} I J) (h : IsLawful p S T t) :
    read p hp S T (assemble p hp S T t h) = t := by
  classical
  funext q
  cases q with
  | edge i j q =>
    by_cases hj : j = IndependentIndexedCarrierGraph.index p hp i
    · subst j
      have hr := congrFun (IndependentInverseGraph.read_assemble (S i)
        (T (IndependentIndexedCarrierGraph.index p hp i))
        (row t i (IndependentIndexedCarrierGraph.index p hp i))
        (h.active i _ ((IndependentIndexedCarrierGraph.active_iff p hp i _).2 rfl))) q
      simpa only [read, dif_pos rfl, assemble, row] using hr
    · have hij : p i j = false := by
        cases he : p i j with
        | false => rfl
        | true => exact False.elim (hj ((IndependentIndexedCarrierGraph.active_iff p hp i j).1 he))
      simp [read, hj, h.inactive i j hij q]

/-- All dependent native equivalences correspond exactly to the independent inverse point tables. -/
def readingEquiv : (∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i)) ≃
    {t : Table.{u, v, w, z} I J // IsLawful p S T t} where
  toFun f := ⟨read p hp S T f, read_isLawful p hp S T f⟩
  invFun t := assemble p hp S T t.val t.property
  left_inv := assemble_read p hp S T
  right_inv t := Subtype.ext (read_assemble p hp S T t.val t.property)

end

end AAT.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraph
