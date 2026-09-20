import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointComposition
import Formal.Util.AssertStandardAxioms

/-!
# Three-query support for fixed dependent point composition

One first index point fixes the middle context, and one first value point
fixes the middle value. The remaining second value point then determines the
answer, even for inactive final context candidates. The support is expressed
directly in the original query types so it can be used by common Hom fragments.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

noncomputable section

universe u v w x y z u₁ u₂

variable {I : Type u} {J : Type v} {K : Type w}
variable {S : I → Type x} {M : J → Type y} {T : K → Type z}
variable {X : Type u₁} {Y : Type u₂}

/-- At most three original query cells determine a composed dependent value point. -/
theorem compose_lifted_finite_support
    (indexQuery : I → J → X) (leftQuery : ∀ i j, S i → M j → X)
    (rightQuery : ∀ j l, M j → T l → Y) (h : X → Bool) (k : Y → Bool)
    (hp : ∀ i, ∃! j, h (indexQuery i j) = true)
    (hh : IsLawful S M (fun i j => h (indexQuery i j)) (fun i j x y => h (leftQuery i j x y)))
    (i : I) (l : K) (x : S i) (z : T l) :
    ∃ (D : Finset X) (E : Finset Y), D.card + E.card ≤ 3 ∧
      ∀ (h' : X → Bool) (k' : Y → Bool)
        (hp' : ∀ i, ∃! j, h' (indexQuery i j) = true)
        (hh' : IsLawful S M (fun i j => h' (indexQuery i j)) (fun i j x y => h' (leftQuery i j x y))),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        compose (fun i j => h (indexQuery i j)) hp (fun i j x y => h (leftQuery i j x y)) hh
          (fun j l y z => k (rightQuery j l y z)) i l x z =
        compose (fun i j => h' (indexQuery i j)) hp' (fun i j x y => h' (leftQuery i j x y)) hh'
          (fun j l y z => k' (rightQuery j l y z)) i l x z := by
  classical
  let j := IndependentIndexedCarrierGraph.index (fun i j => h (indexQuery i j)) hp i
  have hij : h (indexQuery i j) = true := (IndependentIndexedCarrierGraph.active_iff _ hp i j).2 rfl
  let row := graph (fun i j x y => h (leftQuery i j x y)) hh i j hij
  let y := row.assemble x
  have hxy : h (leftQuery i j x y) = true := row.edge_target x
  refine ⟨{indexQuery i j, leftQuery i j x y}, {rightQuery j l y z}, ?_, ?_⟩
  · have hd := Finset.card_insert_le (indexQuery i j) ({leftQuery i j x y} : Finset X)
    simpa only [Finset.card_singleton] using Nat.add_le_add_right hd 1
  · intro h' k' hp' hh' hD hE
    have hij' : h' (indexQuery i j) = true := (hD _ (by simp)).symm.trans hij
    have hxy' : h' (leftQuery i j x y) = true := (hD _ (by simp)).symm.trans hxy
    have hy : (graph (fun i j x y => h' (leftQuery i j x y)) hh' i j hij').assemble x = y :=
      (graph (fun i j x y => h' (leftQuery i j x y)) hh' i j hij').target_eq_of_edge hxy'
    rw [compose_at_pair _ hp _ hh _ i j l hij x z, compose_at_pair _ hp' _ hh' _ i j l hij' x z, hy]
    exact hE (rightQuery j l y z) (by simp)

end

end AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph
