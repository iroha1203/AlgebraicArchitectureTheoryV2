import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedCarrierGraphs
import Mathlib.Logic.Function.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Point composition of dependent candidate-carrier graphs

Implementation notes: an exact-one primitive index row supplies one middle
index, and an exact-one value row supplies one middle value. The second table
is then queried at that point. No completed Hom is an input or intermediate
value. This construction is used for the common operation-family composition.
-/

namespace AAT.AG.LocalSemanticReconstruction

noncomputable section

universe u v w x y z

/-- A false second table gives a false composite at every candidate carrier pair. -/
theorem IndependentCarrierGraph.compose_false (A : Type u) (B : Type v) (C : Type w)
    (h : IndependentCarrierGraph.Table.{u, v}) (hh : IndependentCarrierGraph.IsLawful A B h) :
    IndependentCarrierGraph.compose A B C h hh (fun _ => false) = fun _ => false := by
  classical
  funext q
  cases q
  simp only [IndependentCarrierGraph.compose, dite_eq_ite, ite_self]

namespace IndependentIndexedCarrierGraph

variable {I : Type u} {J : Type v} {K : Type w}

/-- Compose index flags by one true first-row target followed by one second-table lookup. -/
def composeIndex (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true) (q : J → K → Bool) : I → K → Bool :=
  fun i k => q (index p hp i) k

/-- Every composite index row has exactly one output because its selected second row does. -/
theorem composeIndex_total (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
    (q : J → K → Bool) (hq : ∀ j, ∃! k, q j k = true) :
    ∀ i, ∃! k, composeIndex p hp q i k = true := fun i => hq (index p hp i)

/-- The composite index is the successive pair of primitive row targets. -/
theorem index_composeIndex (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
    (q : J → K → Bool) (hq : ∀ j, ∃! k, q j k = true) (i : I) :
    index (composeIndex p hp q) (composeIndex_total p hp q hq) i = index q hq (index p hp i) :=
  ((indexGraph q hq).target_eq_of_edge ((indexGraph (composeIndex p hp q)
    (composeIndex_total p hp q hq)).edge_target i)).symm

/-- Composite index flags are exactly relational composition of the two original primitive graphs. -/
theorem composeIndex_iff (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
    (q : J → K → Bool) (i : I) (k : K) :
    composeIndex p hp q i k = true ↔ ∃ j, p i j = true ∧ q j k = true := by
  constructor
  · intro h
    exact ⟨index p hp i, (indexGraph p hp).edge_target i, h⟩
  · rintro ⟨j, hj, hq⟩
    have he := (indexGraph p hp).target_eq_of_edge hj
    change q (index p hp i) k = true
    exact (congrArg (fun j => q j k) he).trans hq

/-- Two index cells determine a composition value on any other exact-one first graph. -/
theorem composeIndex_point_support (p p' : I → J → Bool)
    (hp : ∀ i, ∃! j, p i j = true) (hp' : ∀ i, ∃! j, p' i j = true)
    (q q' : J → K → Bool) (i : I) (k : K)
    (h1 : p i (index p hp i) = p' i (index p hp i))
    (h2 : q (index p hp i) k = q' (index p hp i) k) :
    composeIndex p hp q i k = composeIndex p' hp' q' i k := by
  have he := (indexGraph p' hp').target_eq_of_edge (h1.symm.trans ((indexGraph p hp).edge_target i))
  change q (index p hp i) k = q' (index p' hp' i) k
  exact h2.trans (congrArg (fun j => q' j k) he).symm

/-- Assembly at any true index pair is the corresponding primitive carrier-row function. -/
theorem assemble_at_pair_heq (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
    (S : I → Type x) (T : J → Type y) (h : Table.{u, v, x, y} I J) (hh : IsLawful p S T h)
    (i : I) (j : J) (hij : p i j = true) :
    HEq (assemble p hp S T h hh i) (IndependentCarrierGraph.assemble (S i) (T j) (row h i j) (hh.active i j hij)) := by
  have he := (active_iff p hp i j).1 hij
  subst j
  rfl

variable (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
variable (S : I → Type x) (M : J → Type y) (T : K → Type z)
variable (h : Table.{u, v, x, y} I J) (hh : IsLawful p S M h)
variable (k : Table.{v, w, y, z} J K)

/-- Compose dependent value rows by the first primitive index and first primitive value, then query the second row. -/
def composeRows : Table.{u, w, x, z} I K
  | .edge i l q => IndependentCarrierGraph.compose (S i) (M (index p hp i)) (T l)
      (row h i (index p hp i)) (hh.active i _ ((active_iff p hp i _).2 rfl)) (row k (index p hp i) l) q

/-- An active carrier-pair output is the second graph at the first row's unique primitive value. -/
theorem composeRows_edge (i : I) (l : K) (a : S i) (b : T l) :
    composeRows p hp S M T h hh k (.edge i l (.edge (S i) (T l) a b)) =
      k (.edge (index p hp i) l (.edge (M (index p hp i)) (T l) (assemble p hp S M h hh i a) b)) :=
  IndependentCarrierGraph.compose_edge _ _ _ _ _ _ a b

variable (q : J → K → Bool) (hq : ∀ j, ∃! l, q j l = true) (hk : IsLawful q M T k)

include hk in
/-- Direct dependent point composition preserves all candidate inactivity and active exact-one value laws. -/
theorem composeRows_isLawful : IsLawful (composeIndex p hp q) S T (composeRows p hp S M T h hh k) := by
  constructor
  · intro i l hil r
    have hz : row k (index p hp i) l = fun _ => false := funext (hk.inactive _ _ hil)
    change IndependentCarrierGraph.compose (S i) (M (index p hp i)) (T l)
      (row h i (index p hp i)) (hh.active i _ ((active_iff p hp i _).2 rfl)) (row k (index p hp i) l) r = false
    rw [hz]
    exact congrFun (IndependentCarrierGraph.compose_false _ _ _ _ _) r
  · intro i l hil
    exact IndependentCarrierGraph.compose_isLawful _ _ _ _
      (hh.active i _ ((active_iff p hp i _).2 rfl)) _ (hk.active _ _ hil)

/-- Assembly of the composed primitive rows is the successive native dependent function, up to the proved index identification. -/
theorem assemble_composeRows_heq : HEq
    (assemble (composeIndex p hp q) (composeIndex_total p hp q hq) S T
      (composeRows p hp S M T h hh k) (composeRows_isLawful p hp S M T h hh k q hk))
    (fun i a => assemble q hq M T k hk (index p hp i) (assemble p hp S M h hh i a)) := by
  apply Function.hfunext rfl
  intro i j hij
  cases hij
  have ht : composeIndex p hp q i (index q hq (index p hp i)) = true :=
    (indexGraph q hq).edge_target (index p hp i)
  exact (assemble_at_pair_heq (composeIndex p hp q) (composeIndex_total p hp q hq) S T
    (composeRows p hp S M T h hh k) (composeRows_isLawful p hp S M T h hh k q hk) i _ ht).trans
      (heq_of_eq (IndependentCarrierGraph.assemble_compose _ _ _ _
        (hh.active i _ ((active_iff p hp i _).2 rfl)) _
        (hk.active _ _ ((active_iff q hq _ _).2 rfl))))

end IndependentIndexedCarrierGraph

end

end AAT.AG.LocalSemanticReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentCarrierGraph
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentIndexedCarrierGraph
