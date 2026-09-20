import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedCarrierComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentCandidateIndexedInverseGraphs
import ResearchLean.AG.LocalSemanticReconstruction.IndependentInverseGraphComposition
import Formal.Util.AssertStandardAxioms

/-!
# Primitive composition of dependent inverse rows

Implementation notes: the first index graph chooses the middle index. A true
second index flag then activates the ordinary forward/backward point
composition; false flags normalize the entire row to false. No inverse of
an index map is required. Both fiber directions remain primitive points.
Candidate outer carriers are normalized independently of fiber composition.
-/

namespace AAT.AG.LocalSemanticReconstruction

noncomputable section

universe u v w x y z

namespace IndependentIndexedInverseGraph

variable {I : Type u} {J : Type v} {K : Type w}
variable (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
variable (S : I → Type x) (M : J → Type y) (T : K → Type z)
variable (h : Table.{u, v, x, y} I J) (hh : IsLawful p S M h)
variable (q : J → K → Bool) (k : Table.{v, w, y, z} J K) (hk : IsLawful q M T k)

/-- Compose active inverse fibers using the primitive middle index; inactive second indices give false. -/
def composeRows : Table.{u, w, x, z} I K := by
  classical
  intro a
  cases a with
  | edge i l a =>
    let j := IndependentIndexedCarrierGraph.index p hp i
    exact if hl : q j l = true then
      IndependentInverseGraph.compose (S i) (M j) (T l) (row h i j)
        (hh.active i j ((IndependentIndexedCarrierGraph.active_iff p hp i j).2 rfl))
        (row k j l) (hk.active j l hl) a
      else false

/-- At a true composite index pair, the whole row is the two primitive fiber graphs in the original direction order. -/
theorem row_composeRows (i : I) (l : K) (hl : q (IndependentIndexedCarrierGraph.index p hp i) l = true) :
    row (composeRows p hp S M T h hh q k hk) i l =
      IndependentInverseGraph.compose (S i) (M (IndependentIndexedCarrierGraph.index p hp i)) (T l)
        (row h i (IndependentIndexedCarrierGraph.index p hp i))
        (hh.active i _ ((IndependentIndexedCarrierGraph.active_iff p hp i _).2 rfl))
        (row k (IndependentIndexedCarrierGraph.index p hp i) l) (hk.active _ l hl) := by
  funext a
  simp only [row, composeRows, hl, dif_pos]

/-- Primitive dependent composition preserves index inactivity and both fiber inverse equations. -/
theorem composeRows_isLawful : IsLawful (IndependentIndexedCarrierGraph.composeIndex p hp q) S T
    (composeRows p hp S M T h hh q k hk) := by
  constructor
  · intro i l hil a
    have he : q (IndependentIndexedCarrierGraph.index p hp i) l = false := hil
    simp only [composeRows, he, Bool.false_eq_true, ↓reduceDIte]
  · intro i l hil
    change IndependentInverseGraph.IsLawful _ _ (row _ i l)
    rw [row_composeRows p hp S M T h hh q k hk i l hil]
    exact IndependentInverseGraph.compose_isLawful _ _ _ _ _ _ _

/-- The reconstructed fiber at any true index pair is its original primitive inverse-row assembly. -/
theorem assemble_at_pair_heq (i : I) (j : J) (hij : p i j = true) : HEq
    (assemble p hp S M h hh i)
    (IndependentInverseGraph.assemble (S i) (M j) (row h i j) (hh.active i j hij)) := by
  have he := (IndependentIndexedCarrierGraph.active_iff p hp i j).1 hij
  subst j
  rfl

variable (hq : ∀ j, ∃! l, q j l = true)

/-- Assembly of direct primitive inverse composition is the successive pair of native fiber equivalences. -/
theorem assemble_composeRows_heq : HEq
    (assemble (IndependentIndexedCarrierGraph.composeIndex p hp q)
      (IndependentIndexedCarrierGraph.composeIndex_total p hp q hq) S T
      (composeRows p hp S M T h hh q k hk) (composeRows_isLawful p hp S M T h hh q k hk))
    (fun i => (assemble p hp S M h hh i).trans
      (assemble q hq M T k hk (IndependentIndexedCarrierGraph.index p hp i))) := by
  apply Function.hfunext rfl
  intro i i' hii'
  cases hii'
  let j := IndependentIndexedCarrierGraph.index p hp i
  let l := IndependentIndexedCarrierGraph.index q hq j
  have hl : q j l = true := (IndependentIndexedCarrierGraph.active_iff q hq j l).2 rfl
  refine (assemble_at_pair_heq (IndependentIndexedCarrierGraph.composeIndex p hp q)
    (IndependentIndexedCarrierGraph.composeIndex_total p hp q hq) S T
    (composeRows p hp S M T h hh q k hk) (composeRows_isLawful p hp S M T h hh q k hk) i l hl).trans ?_
  have he : (⟨row (composeRows p hp S M T h hh q k hk) i l,
      (composeRows_isLawful p hp S M T h hh q k hk).active i l hl⟩ :
      {a // IndependentInverseGraph.IsLawful (S i) (T l) a}) =
      ⟨IndependentInverseGraph.compose (S i) (M j) (T l) (row h i j)
        (hh.active i j ((IndependentIndexedCarrierGraph.active_iff p hp i j).2 rfl))
        (row k j l) (hk.active j l hl), IndependentInverseGraph.compose_isLawful _ _ _ _ _ _ _⟩ :=
    Subtype.ext (row_composeRows p hp S M T h hh q k hk i l hl)
  exact heq_of_eq ((congrArg (IndependentInverseGraph.readingEquiv (S i) (T l)).symm he).trans
    (IndependentInverseGraph.assemble_compose _ _ _ _ _ _ _))

/-- Equal primitive index graphs and heterogeneously equal fiber families have identical complete inverse readings. -/
theorem read_eq_of_heq {L : Type w} (p q : I → L → Bool)
    (hp : ∀ i, ∃! l, p i l = true) (hq : ∀ i, ∃! l, q i l = true) (he : p = q)
    (S : I → Type x) (T : L → Type z)
    (f : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i))
    (g : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index q hq i)) (hf : HEq f g) :
    read p hp S T f = read q hq S T g := by
  cases he
  cases hf
  rfl

end IndependentIndexedInverseGraph

namespace IndependentCandidateIndexedInverseGraph

/-- Place a primitive indexed table at its declared outer carriers and force all other outer candidates to false. -/
def extend (I : Type u) (J : Type v) (h : IndependentIndexedInverseGraph.Table.{u, v, w, z} I J) : Table.{u, v, w, z} := by
  classical
  intro a
  cases a with
  | edge K L k l a => exact if hK : K = I then
      if hL : L = J then h (.edge (hK ▸ k) (hL ▸ l) a) else false
    else false

/-- Selecting the declared outer carriers restores the original primitive indexed table. -/
theorem project_extend (I : Type u) (J : Type v) (h : IndependentIndexedInverseGraph.Table.{u, v, w, z} I J) :
    project (extend I J h) I J = h := by
  classical
  funext a
  cases a
  simp [project, extend]

/-- Extending the indexed inverse reader is exactly the existing complete candidate reader. -/
theorem extend_read (I : Type u) (J : Type v) (p : I → J → Bool)
    (hp : ∀ i, ∃! j, p i j = true) (S : I → Type w) (T : J → Type z)
    (f : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i)) :
    extend I J (IndependentIndexedInverseGraph.read p hp S T f) = read I J p S T hp f := rfl

end IndependentCandidateIndexedInverseGraph

end

end AAT.AG.LocalSemanticReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraph
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentCandidateIndexedInverseGraph
