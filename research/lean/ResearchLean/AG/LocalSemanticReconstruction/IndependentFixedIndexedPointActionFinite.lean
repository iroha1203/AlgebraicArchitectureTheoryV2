import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointAction

/-!
# Finite support for actual actions of dependent inverse graphs

Two index flags, one backward-selected value, and one forward action value
determine an actual action point. Inverse laws let the backward-selected value
be fixed by a forward graph cell, so the support uses only original table cells.

Implementation notes: the support is stated against the original lifted query
tables. Retaining a completed action would make finiteness immediate but would
not establish finite dependence of the primitive declaration.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

noncomputable section

universe u v w z u₁

variable {I : Type u} {J : Type v} {S : I → Type w} {T : J → Type z}

/-- At most four lifted primitive cells determine one actual action point. -/
theorem action_lifted_finite_support {X : Type u₁}
    (indexQuery : I → J → X)
    (forwardQuery backwardQuery : ∀ i j, S i → T j → X)
    (h : X → Bool)
    (hl : InverseLaws
      (fun i j => h (indexQuery i j))
      (fun i j x y => h (forwardQuery i j x y))
      (fun i j x y => h (backwardQuery i j x y)))
    (i i' : I) (j j' : J) (a : S i → S i') (y : T j) (z : T j') :
    ∃ D : Finset X, D.card ≤ 4 ∧
      ∀ (h' : X → Bool)
        (hl' : InverseLaws
          (fun i j => h' (indexQuery i j))
          (fun i j x y => h' (forwardQuery i j x y))
          (fun i j x y => h' (backwardQuery i j x y))),
        (∀ q ∈ D, h q = h' q) →
        action (fun i j => h (indexQuery i j))
            (fun i j x y => h (forwardQuery i j x y))
            (fun i j x y => h (backwardQuery i j x y)) hl i i' j j' a y z =
          action (fun i j => h' (indexQuery i j))
            (fun i j x y => h' (forwardQuery i j x y))
            (fun i j x y => h' (backwardQuery i j x y)) hl' i i' j j' a y z := by
  classical
  by_cases hij : h (indexQuery i j) = true
  · by_cases hij' : h (indexQuery i' j') = true
    · let x := (backwardGraph
        (fun i j x y => h (forwardQuery i j x y))
        (fun i j x y => h (backwardQuery i j x y)) hl i j hij).assemble y
      have hr : h (backwardQuery i j x y) = true :=
        (backwardGraph
          (fun i j x y => h (forwardQuery i j x y))
          (fun i j x y => h (backwardQuery i j x y)) hl i j hij).edge_target y
      have hf : h (forwardQuery i j x y) = true :=
        (hl.inverse i j x y).trans hr
      refine ⟨{indexQuery i j, indexQuery i' j', forwardQuery i j x y,
        forwardQuery i' j' (a x) z}, ?_, ?_⟩
      · calc
          Finset.card {indexQuery i j, indexQuery i' j', forwardQuery i j x y,
              forwardQuery i' j' (a x) z} ≤
              Finset.card {indexQuery i' j', forwardQuery i j x y,
                forwardQuery i' j' (a x) z} + 1 := Finset.card_insert_le _ _
          _ ≤ (Finset.card {forwardQuery i j x y,
                forwardQuery i' j' (a x) z} + 1) + 1 :=
            Nat.add_le_add_right (Finset.card_insert_le _ _) 1
          _ ≤ ((Finset.card {forwardQuery i' j' (a x) z} + 1) + 1) + 1 :=
            Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
          _ = 4 := by simp
      · intro h' hl' hD
        have h0 : h' (indexQuery i j) = true :=
          (hD _ (by simp)).symm.trans hij
        have h1 : h' (indexQuery i' j') = true :=
          (hD _ (by simp)).symm.trans hij'
        have hxy : h' (forwardQuery i j x y) = true :=
          (hD _ (by simp)).symm.trans hf
        have hr' : h' (backwardQuery i j x y) = true :=
          (hl'.inverse i j x y).symm.trans hxy
        have hx : (backwardGraph
            (fun i j x y => h' (forwardQuery i j x y))
            (fun i j x y => h' (backwardQuery i j x y)) hl' i j h0).assemble y = x :=
          (backwardGraph
            (fun i j x y => h' (forwardQuery i j x y))
            (fun i j x y => h' (backwardQuery i j x y)) hl' i j h0).target_eq_of_edge hr'
        rw [action_active _ _ _ _ i i' j j' a y z hij hij',
          action_active _ _ _ _ i i' j j' a y z h0 h1, hx]
        change h (forwardQuery i' j' (a x) z) = h' (forwardQuery i' j' (a x) z)
        exact hD _ (by simp)
    · have hij0 : h (indexQuery i' j') = false := Bool.eq_false_iff.mpr hij'
      refine ⟨{indexQuery i j, indexQuery i' j'}, ?_, ?_⟩
      · calc
          Finset.card {indexQuery i j, indexQuery i' j'} ≤
              Finset.card {indexQuery i' j'} + 1 := Finset.card_insert_le _ _
          _ = 2 := by simp
          _ ≤ 4 := by omega
      intro h' hl' hD
      have h0 : h' (indexQuery i j) = true :=
        (hD _ (by simp)).symm.trans hij
      have h1 : h' (indexQuery i' j') = false :=
        (hD _ (by simp)).symm.trans hij0
      exact (action_inactive _ _ _ _ i i' j j' a y z (Or.inr hij0)).trans
        (action_inactive _ _ _ _ i i' j j' a y z (Or.inr h1)).symm
  · have hij0 : h (indexQuery i j) = false := Bool.eq_false_iff.mpr hij
    refine ⟨{indexQuery i j}, by simp, ?_⟩
    intro h' hl' hD
    have h0 : h' (indexQuery i j) = false :=
      (hD _ (by simp)).symm.trans hij0
    exact (action_inactive _ _ _ _ i i' j j' a y z (Or.inl hij0)).trans
      (action_inactive _ _ _ _ i i' j j' a y z (Or.inl h0)).symm

end

end AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraph
