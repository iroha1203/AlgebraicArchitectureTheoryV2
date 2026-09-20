import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraphs
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRingCarrierGraphs
import Formal.Util.AssertStandardAxioms

/-!
# Dependent observable ring equivalences from primitive point rows

The index map remains a directed graph. Its active fibers carry inverse
carrier graphs and the four forward ring-preservation point clauses. The
native dependent ring-equivalence family is assembled from these rows and
is recovered in both directions, including inactive candidate responses.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentIndexedRingGraph

noncomputable section

universe u v w z

variable {I : Type u} {J : Type v}
variable (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
variable (S : I → Type w) (T : J → Type z)
variable [∀ i, CommRing (S i)] [∀ j, CommRing (T j)]

/-- The two inverse graph directions and primitive ring equations at every true index pair. -/
structure IsLawful (t : IndependentIndexedInverseGraph.Table.{u, v, w, z} I J) : Prop where
  /-- Index inactivity, candidate-carrier typing, row totality, and pointwise inverse equations. -/
  graphs : IndependentIndexedInverseGraph.IsLawful p S T t
  /-- Active pairs preserve only the original zero/one/add/mul ring points. -/
  ring : ∀ i j, p i j = true →
    IndependentRingCarrierGraph.Preserves
      (IndependentRingPrimitive.read (inferInstance : CommRing (S i)))
      (IndependentRingPrimitive.read (inferInstance : CommRing (T j)))
      (IndependentInverseGraph.forward (IndependentIndexedInverseGraph.row t i j))

/-- Assemble every native observable fiber equivalence from its active inverse graph and ring point laws. -/
def assemble (t : IndependentIndexedInverseGraph.Table.{u, v, w, z} I J) (h : IsLawful p S T t) :
    ∀ i, S i ≃+* T (IndependentIndexedCarrierGraph.index p hp i) :=
  fun i => IndependentRingCarrierGraph.assembleEquiv
    (IndependentIndexedInverseGraph.row t i (IndependentIndexedCarrierGraph.index p hp i))
    ⟨h.graphs.active i _ ((IndependentIndexedCarrierGraph.active_iff p hp i _).2 rfl),
      h.ring i _ ((IndependentIndexedCarrierGraph.active_iff p hp i _).2 rfl)⟩

/-- Read a native dependent ring equivalence through both candidate carrier point directions. -/
def read (f : ∀ i, S i ≃+* T (IndependentIndexedCarrierGraph.index p hp i)) :
    IndependentIndexedInverseGraph.Table.{u, v, w, z} I J :=
  IndependentIndexedInverseGraph.read p hp S T (fun i => (f i).toEquiv)

/-- Every native ring-equivalence family supplies all independent primitive row and ring conditions. -/
theorem read_isLawful (f : ∀ i, S i ≃+* T (IndependentIndexedCarrierGraph.index p hp i)) :
    IsLawful p S T (read p hp S T f) := by
  constructor
  · exact IndependentIndexedInverseGraph.read_isLawful p hp S T (fun i => (f i).toEquiv)
  · intro i j hij
    have hj := (IndependentIndexedCarrierGraph.active_iff p hp i j).1 hij
    subst j
    change IndependentRingCarrierGraph.Preserves _ _ (IndependentInverseGraph.forward
      (IndependentIndexedInverseGraph.row
        (IndependentIndexedInverseGraph.read p hp S T (fun i => (f i).toEquiv)) i _))
    rw [IndependentIndexedInverseGraph.row_read]
    exact (IndependentRingCarrierGraph.readEquiv_isLawful (f i)).2

/-- Every native dependent ring-equivalence field survives assembly of its primitive point readings. -/
theorem assemble_read (f : ∀ i, S i ≃+* T (IndependentIndexedCarrierGraph.index p hp i)) :
    assemble p hp S T (read p hp S T f) (read_isLawful p hp S T f) = f := by
  funext i
  apply RingEquiv.ext
  intro x
  have he := congrFun (IndependentIndexedInverseGraph.assemble_read p hp S T (fun i => (f i).toEquiv)) i
  exact congrArg (fun e : S i ≃ T (IndependentIndexedCarrierGraph.index p hp i) => e x) he

/-- Re-reading restores every active/inactive point in the two candidate carrier directions. -/
theorem read_assemble (t : IndependentIndexedInverseGraph.Table.{u, v, w, z} I J)
    (h : IsLawful p S T t) : read p hp S T (assemble p hp S T t h) = t :=
  IndependentIndexedInverseGraph.read_assemble p hp S T t h.graphs

/-- All native dependent ring equivalences correspond exactly to the lawful primitive candidate rows. -/
def readingEquiv : (∀ i, S i ≃+* T (IndependentIndexedCarrierGraph.index p hp i)) ≃
    {t : IndependentIndexedInverseGraph.Table.{u, v, w, z} I J // IsLawful p S T t} where
  toFun f := ⟨read p hp S T f, read_isLawful p hp S T f⟩
  invFun t := assemble p hp S T t.val t.property
  left_inv := assemble_read p hp S T
  right_inv t := Subtype.ext (read_assemble p hp S T t.val t.property)

end

end AAT.AG.LocalSemanticReconstruction.IndependentIndexedRingGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentIndexedRingGraph
