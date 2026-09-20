import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseAgainstComposition
import Formal.Util.AssertStandardAxioms

/-!
# Finite support of inverse-fiber composition against backward indices

The second backward index point fixes the middle index; the first index flag
determines activation. At a true pair, at most two primitive inverse-fiber
points determine each composed value. The statement retains arbitrary index
and value carriers and all inactive candidate queries.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraph

noncomputable section

universe u v w x y z u₁ u₂

variable {I : Type u} {J : Type v} {K : Type w}
variable (p : I → J → Bool) (S : I → Type x) (M : J → Type y) (T : K → Type z)
variable (h : Table.{u, v, x, y} I J) (hh : IsLawful p S M h)
variable (q : J → K → Bool) (hq : ∀ l, ∃! j, q j l = true)
variable (k : Table.{v, w, y, z} J K) (hk : IsLawful q M T k)

/-- Two backward index cells and at most two value cells determine each composed inverse-fiber point. -/
theorem composeAgainst_finite_support (a : Query.{u, w, x, z} I K) :
    ∃ (D : Finset (I × J)) (E : Finset (J × K))
      (F : Finset (Query.{u, v, x, y} I J)) (G : Finset (Query.{v, w, y, z} J K)),
      D.card ≤ 1 ∧ E.card ≤ 1 ∧ F.card + G.card ≤ 2 ∧
      ∀ (p' : I → J → Bool) (h' : Table.{u, v, x, y} I J) (hh' : IsLawful p' S M h')
        (q' : J → K → Bool) (hq' : ∀ l, ∃! j, q' j l = true)
        (k' : Table.{v, w, y, z} J K) (hk' : IsLawful q' M T k'),
        (∀ a ∈ D, p a.1 a.2 = p' a.1 a.2) → (∀ a ∈ E, q a.1 a.2 = q' a.1 a.2) →
        (∀ a ∈ F, h a = h' a) → (∀ a ∈ G, k a = k' a) →
        composeAgainst p S M T h hh q hq k hk a = composeAgainst p' S M T h' hh' q' hq' k' hk' a := by
  classical
  cases a with
  | edge i l a =>
    let j := IndependentIndexedCarrierGraph.index (fun l j => q j l) hq l
    have hjl : q j l = true := (IndependentIndexedCarrierGraph.active_iff _ hq l j).2 rfl
    by_cases hij : p i j = true
    · obtain ⟨F, G, hcard, hs⟩ := IndependentInverseGraph.compose_finite_support (S i) (M j) (T l)
        (row h i j) (hh.active i j hij) (row k j l) (hk.active j l hjl) a
      refine ⟨{(i, j)}, {(j, l)}, F.image (Query.edge i j), G.image (Query.edge j l), by simp, by simp, ?_, ?_⟩
      · exact (Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans hcard
      · intro p' h' hh' q' hq' k' hk' hD hE hF hG
        have hij' : p' i j = true := (hD (i, j) (by simp)).symm.trans hij
        have hjl' : q' j l = true := (hE (j, l) (by simp)).symm.trans hjl
        have hv := hs (row h' i j) (hh'.active i j hij') (row k' j l) (hk'.active j l hjl')
          (fun a ha => hF (.edge i j a) (Finset.mem_image_of_mem _ ha))
          (fun a ha => hG (.edge j l a) (Finset.mem_image_of_mem _ ha))
        exact (congrFun (composeAgainst_at_pair p S M T h hh q hq k hk i j l hjl hij) a).trans
          (hv.trans (congrFun (composeAgainst_at_pair p' S M T h' hh' q' hq' k' hk' i j l hjl' hij') a).symm)
    · have hij0 : p i j = false := Bool.eq_false_iff.mpr hij
      refine ⟨{(i, j)}, {(j, l)}, ∅, ∅, by simp, by simp, by simp, ?_⟩
      intro p' h' hh' q' hq' k' hk' hD hE _ _
      have hij' : p' i j = false := (hD (i, j) (by simp)).symm.trans hij0
      have hjl' : q' j l = true := (hE (j, l) (by simp)).symm.trans hjl
      exact (congrFun (composeAgainst_false_at_pair p S M T h hh q hq k hk i j l hjl hij0) a).trans
        (congrFun (composeAgainst_false_at_pair p' S M T h' hh' q' hq' k' hk' i j l hjl' hij') a).symm

/-- Embedding the two index and two value supports into original query types gives at most four cells. -/
theorem composeAgainst_lifted_finite_support {X : Type u₁} {Y : Type u₂}
    (leftIndex : I × J → X) (rightIndex : J × K → Y)
    (leftRow : Query.{u, v, x, y} I J → X) (rightRow : Query.{v, w, y, z} J K → Y)
    (leftTable : (X → Bool) → Table.{u, v, x, y} I J) (rightTable : (Y → Bool) → Table.{v, w, y, z} J K)
    (leftPoint : ∀ h a, leftTable h a = h (leftRow a)) (rightPoint : ∀ k a, rightTable k a = k (rightRow a))
    (S : I → Type x) (M : J → Type y) (T : K → Type z) (h : X → Bool) (k : Y → Bool)
    (hh : IsLawful (fun i j => h (leftIndex (i, j))) S M (leftTable h))
    (hq : ∀ l, ∃! j, k (rightIndex (j, l)) = true)
    (hk : IsLawful (fun j l => k (rightIndex (j, l))) M T (rightTable k))
    (a : Query.{u, w, x, z} I K) :
    ∃ (D : Finset X) (E : Finset Y), D.card + E.card ≤ 4 ∧
      ∀ (h' : X → Bool) (k' : Y → Bool)
        (hh' : IsLawful (fun i j => h' (leftIndex (i, j))) S M (leftTable h'))
        (hq' : ∀ l, ∃! j, k' (rightIndex (j, l)) = true)
        (hk' : IsLawful (fun j l => k' (rightIndex (j, l))) M T (rightTable k')),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        composeAgainst (fun i j => h (leftIndex (i, j))) S M T (leftTable h) hh
          (fun j l => k (rightIndex (j, l))) hq (rightTable k) hk a =
        composeAgainst (fun i j => h' (leftIndex (i, j))) S M T (leftTable h') hh'
          (fun j l => k' (rightIndex (j, l))) hq' (rightTable k') hk' a := by
  classical
  obtain ⟨D, E, F, G, hD, hE, hFG, hs⟩ := composeAgainst_finite_support
    (fun i j => h (leftIndex (i, j))) S M T (leftTable h) hh
    (fun j l => k (rightIndex (j, l))) hq (rightTable k) hk a
  refine ⟨D.image leftIndex ∪ F.image leftRow, E.image rightIndex ∪ G.image rightRow, ?_, ?_⟩
  · have hd := Finset.card_image_le (s := D) (f := leftIndex)
    have he := Finset.card_image_le (s := E) (f := rightIndex)
    have hf := Finset.card_image_le (s := F) (f := leftRow)
    have hg := Finset.card_image_le (s := G) (f := rightRow)
    have hl := Finset.card_union_le (D.image leftIndex) (F.image leftRow)
    have hr := Finset.card_union_le (E.image rightIndex) (G.image rightRow)
    omega
  · intro h' k' hh' hq' hk' hL hR
    apply hs (fun i j => h' (leftIndex (i, j))) (leftTable h') hh'
      (fun j l => k' (rightIndex (j, l))) hq' (rightTable k') hk'
    · intro a ha
      exact hL (leftIndex a) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
    · intro a ha
      exact hR (rightIndex a) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
    · intro a ha
      exact (leftPoint h a).trans ((hL (leftRow a) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))).trans (leftPoint h' a).symm)
    · intro a ha
      exact (rightPoint k a).trans ((hR (rightRow a) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))).trans (rightPoint k' a).symm)

end

end AAT.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraph
