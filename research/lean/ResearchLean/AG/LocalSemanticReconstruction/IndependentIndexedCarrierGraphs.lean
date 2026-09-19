import ResearchLean.AG.LocalSemanticReconstruction.IndependentCarrierGraphReadings
import Formal.Util.AssertStandardAxioms

/-!
# Dependent point graphs at candidate index pairs

The query is fixed before the index function and the source/target fibers are
selected. An independent total-functional index graph activates exactly one
target-index row. Each active row is a candidate-carrier graph; every inactive
row is false. Assembly and re-reading are inverse on every row, including
inactive index pairs and inactive carrier pairs.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentIndexedCarrierGraph

noncomputable section

universe u v w z

variable (I : Type u) (J : Type v)

/-- Candidate index pairs and candidate point carriers precede the selected dependent map. -/
inductive Query where
  /-- One input/output point edge in a candidate index pair. -/
  | edge (i : I) (j : J) (q : IndependentCarrierGraph.Query.{w, z})

/-- All local responses are individual point-pair Booleans. -/
abbrev Table := Query.{u, v, w, z} I J → Bool

variable {I J}

/-- Select one candidate index pair's raw carrier-graph cells. -/
def row (t : Table.{u, v, w, z} I J) (i : I) (j : J) : IndependentCarrierGraph.Table.{w, z} :=
  fun q => t (.edge i j q)

/-- Index activation and candidate-carrier totality are independent local conditions. -/
structure IsLawful (p : I → J → Bool) (S : I → Type w) (T : J → Type z)
    (t : Table.{u, v, w, z} I J) : Prop where
  /-- Inactive index pairs have only false responses. -/
  inactive : ∀ i j, p i j = false → ∀ q, t (.edge i j q) = false
  /-- A true index pair has exactly its declared candidate carrier graph. -/
  active : ∀ i j, p i j = true → IndependentCarrierGraph.IsLawful (S i) (T j) (row t i j)

variable (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
variable (S : I → Type w) (T : J → Type z)

/-- Build the independent index map from exact-one primitive rows. -/
def indexGraph : PrimitiveFunctionGraph.GraphCode I J := ⟨⟨p⟩, ⟨hp⟩⟩

/-- The native target index is an output of the primitive index graph. -/
def index (i : I) : J := (indexGraph p hp).assemble i

/-- A candidate index flag is true precisely at the derived image index. -/
theorem active_iff (i : I) (j : J) : p i j = true ↔ j = index p hp i := by
  exact ((indexGraph p hp).edge_eq_true_iff_target_eq i j).trans eq_comm

/-- Assemble each directed dependent map using the active primitive carrier row. -/
def assemble (t : Table.{u, v, w, z} I J) (h : IsLawful p S T t) : ∀ i, S i → T (index p hp i) :=
  fun i => IndependentCarrierGraph.assemble _ _ (row t i (index p hp i))
    (h.active i _ ((active_iff p hp i _).2 rfl))

/-- Read the dependent point function on its active index row and normalize all other rows to false. -/
def read (f : ∀ i, S i → T (index p hp i)) : Table.{u, v, w, z} I J := by
  classical
  intro q
  cases q with
  | edge i j q => exact (if hj : j = index p hp i then
      IndependentCarrierGraph.read (S i) (T j) (fun x => hj.symm ▸ f i x) q else false)

/-- Reading at the actual selected index recovers its full candidate-carrier point table. -/
theorem row_read (f : ∀ i, S i → T (index p hp i)) (i : I) :
    row (read p hp S T f) i (index p hp i) = IndependentCarrierGraph.read (S i) (T (index p hp i)) (f i) := by
  classical
  funext q
  simp [row, read]

/-- Every dependent directed function satisfies index inactivity and active point totality. -/
theorem read_isLawful (f : ∀ i, S i → T (index p hp i)) : IsLawful p S T (read p hp S T f) := by
  classical
  constructor
  · intro i j hij q
    have hj : j ≠ index p hp i := by
      intro he
      exact Bool.noConfusion (hij.symm.trans ((active_iff p hp i j).2 he))
    simp [read, hj]
  · intro i j hij
    have hj := (active_iff p hp i j).1 hij
    subst j
    rw [row_read]
    exact IndependentCarrierGraph.read_isLawful _ _ (f i)

/-- Assembly of every native dependent function is exact. -/
theorem assemble_read (f : ∀ i, S i → T (index p hp i)) :
    assemble p hp S T (read p hp S T f) (read_isLawful p hp S T f) = f := by
  funext i
  dsimp only [assemble]
  have h := row_read p hp S T f i
  have hc : (⟨row (read p hp S T f) i (index p hp i),
      (read_isLawful p hp S T f).active i _ ((active_iff p hp i _).2 rfl)⟩ :
      {t // IndependentCarrierGraph.IsLawful (S i) (T (index p hp i)) t}) =
      ⟨IndependentCarrierGraph.read _ _ (f i), IndependentCarrierGraph.read_isLawful _ _ (f i)⟩ :=
    Subtype.ext h
  exact (congrArg (IndependentCarrierGraph.functionEquiv (S i) (T (index p hp i))).symm hc).trans
    (IndependentCarrierGraph.assemble_read _ _ (f i))

/-- Re-reading recovers active rows and all forced false rows without extra index choices. -/
theorem read_assemble (t : Table.{u, v, w, z} I J) (h : IsLawful p S T t) :
    read p hp S T (assemble p hp S T t h) = t := by
  classical
  funext q
  cases q with
  | edge i j q =>
    by_cases hj : j = index p hp i
    · subst j
      have hr := congrFun (IndependentCarrierGraph.read_assemble (S i) (T (index p hp i))
        (row t i (index p hp i)) (h.active i _ ((active_iff p hp i _).2 rfl))) q
      simpa only [read, dif_pos rfl, assemble, row] using hr
    · have hij : p i j = false := by
        cases he : p i j with
        | false => rfl
        | true => exact False.elim (hj ((active_iff p hp i j).1 he))
      simp [read, hj, h.inactive i j hij q]

/-- All dependent directed maps have exact presentations on the predeclared common index/carrier query. -/
def readingEquiv : (∀ i, S i → T (index p hp i)) ≃
    {t : Table.{u, v, w, z} I J // IsLawful p S T t} where
  toFun f := ⟨read p hp S T f, read_isLawful p hp S T f⟩
  invFun t := assemble p hp S T t.val t.property
  left_inv := assemble_read p hp S T
  right_inv t := Subtype.ext (read_assemble p hp S T t.val t.property)

/-- One nonfalse response at an inactive index pair is rejected. -/
theorem inactive_nonfalse_rejected (t : Table.{u, v, w, z} I J) (i : I) (j : J)
    (q : IndependentCarrierGraph.Query.{w, z}) (hi : p i j = false) (hq : t (.edge i j q) = true) :
    ¬ IsLawful p S T t := fun h => Bool.noConfusion ((h.inactive i j hi q).symm.trans hq)

end

end AAT.AG.LocalSemanticReconstruction.IndependentIndexedCarrierGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentIndexedCarrierGraph
