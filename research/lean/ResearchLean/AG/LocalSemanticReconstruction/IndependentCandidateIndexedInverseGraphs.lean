import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraphs
import Formal.Util.AssertStandardAxioms

/-!
# Dependent inverse graphs before selecting the outer index carriers

Signature coordinates and nested raw rows need candidate outer carriers as
well as candidate fiber carriers. This declaration keeps both in each query.
The selected outer carriers only enter activation laws. The indexed inverse
assembler handles active rows, while all other outer rows are forced false.
Both inverses recover these inactive cells as well as every native fiber map.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentCandidateIndexedInverseGraph

noncomputable section

universe u v w z

/-- Two candidate index carriers, an index pair, and one candidate inverse-fiber query. -/
inductive Query where
  /-- Every outer and inner type reference precedes the choice of a realization. -/
  | edge (I : Type u) (J : Type v) (i : I) (j : J) (q : IndependentInverseGraph.Query.{w, z})

/-- All outer and inner graph responses remain Boolean points. -/
abbrev Table := Query.{u, v, w, z} → Bool

/-- Restrict to one explicitly selected pair of outer index carriers. -/
def project (t : Table.{u, v, w, z}) (I : Type u) (J : Type v) :
    IndependentIndexedInverseGraph.Table.{u, v, w, z} I J
  | .edge i j q => t (.edge I J i j q)

variable (I : Type u) (J : Type v) (p : I → J → Bool)
variable (S : I → Type w) (T : J → Type z)

/-- Outer carrier activation and the existing pointwise dependent inverse laws. -/
structure IsLawful (t : Table.{u, v, w, z}) : Prop where
  /-- Incorrect outer carrier references cannot carry active inverse points. -/
  inactive : ∀ (K : Type u) (L : Type v) (k : K) (l : L) q,
    (K ≠ I ∨ L ≠ J) → t (.edge K L k l q) = false
  /-- The selected outer carriers obey all indexed activation and inverse rules. -/
  selected : IndependentIndexedInverseGraph.IsLawful p S T (project t I J)

variable (hp : ∀ i, ∃! j, p i j = true)

/-- Construct every dependent native equivalence from the selected primitive rows. -/
def assemble (t : Table.{u, v, w, z}) (ht : IsLawful I J p S T t) :
    ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i) :=
  IndependentIndexedInverseGraph.assemble p hp S T (project t I J) ht.selected

/-- Reading native fiber equivalences activates only the selected outer carrier references. -/
def read (f : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i)) : Table.{u, v, w, z} := by
  classical
  intro q
  cases q with
  | edge K L k l q => exact if hK : K = I then
      if hL : L = J then
        IndependentIndexedInverseGraph.read p hp S T f (.edge (hK ▸ k) (hL ▸ l) q)
      else false
    else false

/-- At the selected outer carriers the new reading is exactly the indexed inverse reading. -/
theorem project_read (f : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i)) :
    project (read I J p S T hp f) I J = IndependentIndexedInverseGraph.read p hp S T f := by
  classical
  funext q
  cases q with
  | edge i j q => simp [project, read]

/-- Every native fiber family satisfies exact outer activation and all indexed inverse laws. -/
theorem read_isLawful (f : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i)) :
    IsLawful I J p S T (read I J p S T hp f) := by
  classical
  constructor
  · intro K L k l q h
    rcases h with hK | hL
    · simp [read, hK]
    · by_cases hK : K = I <;> simp [read, hK, hL]
  · rw [project_read]
    exact IndependentIndexedInverseGraph.read_isLawful p hp S T f

/-- Native reconstruction restores every fiber equivalence, including its inverse function. -/
theorem assemble_read (f : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i)) :
    assemble I J p S T hp (read I J p S T hp f) (read_isLawful I J p S T hp f) = f := by
  have he : (⟨project (read I J p S T hp f) I J, (read_isLawful I J p S T hp f).selected⟩ :
      {t // IndependentIndexedInverseGraph.IsLawful p S T t}) =
      ⟨IndependentIndexedInverseGraph.read p hp S T f,
        IndependentIndexedInverseGraph.read_isLawful p hp S T f⟩ :=
    Subtype.ext (project_read I J p S T hp f)
  exact (congrArg (IndependentIndexedInverseGraph.readingEquiv p hp S T).symm he).trans
    (IndependentIndexedInverseGraph.assemble_read p hp S T f)

/-- Reading after assembly restores every outer and inner candidate point, including all inactive rows. -/
theorem read_assemble (t : Table.{u, v, w, z}) (ht : IsLawful I J p S T t) :
    read I J p S T hp (assemble I J p S T hp t ht) = t := by
  classical
  funext q
  cases q with
  | edge K L k l q =>
    by_cases hK : K = I
    · subst K
      by_cases hL : L = J
      · subst L
        have he := congrFun (IndependentIndexedInverseGraph.read_assemble p hp S T
          (project t I J) ht.selected) (.edge k l q)
        simpa only [read, dif_pos rfl, assemble, project] using he
      · simp [read, hL, ht.inactive I L k l q (Or.inr hL)]
    · simp [read, hK, ht.inactive K L k l q (Or.inl hK)]

/-- Native indexed equivalences and fully candidate-indexed inverse tables have both exact inverses. -/
def readingEquiv : (∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i)) ≃
    {t : Table.{u, v, w, z} // IsLawful I J p S T t} where
  toFun f := ⟨read I J p S T hp f, read_isLawful I J p S T hp f⟩
  invFun t := assemble I J p S T hp t.val t.property
  left_inv := assemble_read I J p S T hp
  right_inv t := Subtype.ext (read_assemble I J p S T hp t.val t.property)

end

end AAT.AG.LocalSemanticReconstruction.IndependentCandidateIndexedInverseGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentCandidateIndexedInverseGraph
