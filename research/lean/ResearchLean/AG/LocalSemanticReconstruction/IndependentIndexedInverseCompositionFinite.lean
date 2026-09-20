import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseComposition
import Formal.Util.AssertStandardAxioms

/-!
# Finite point support of dependent inverse composition

Forward fiber composition reads one point in each graph. Backward composition
reads them in the opposite order. A dependent row additionally reads one
first-index point and the second-index activation flag. The selected supports
therefore remain finite even when index and value carriers are infinite.
-/

namespace AAT.AG.LocalSemanticReconstruction

noncomputable section

universe u v w x y z u₁ u₂

namespace IndependentInverseGraph

/-- Each inverse-composition output uses at most two primitive point cells, including inactive carrier candidates. -/
theorem compose_finite_support (A : Type u) (B : Type v) (C : Type w)
    (h : Table.{u, v}) (hh : IsLawful A B h) (k : Table.{v, w}) (hk : IsLawful B C k) (a : Query.{u, w}) :
    ∃ (D : Finset Query.{u, v}) (E : Finset Query.{v, w}), D.card + E.card ≤ 2 ∧
      ∀ (h' : Table.{u, v}) (hh' : IsLawful A B h') (k' : Table.{v, w}) (hk' : IsLawful B C k'),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        compose A B C h hh k hk a = compose A B C h' hh' k' hk' a := by
  classical
  cases a with
  | forward a =>
    obtain ⟨D, E, hcard, hs⟩ := IndependentCarrierGraph.compose_finite_support A B C (forward h) hh.forward (forward k) a
    refine ⟨D.image Query.forward, E.image Query.forward, ?_, ?_⟩
    · exact (Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans hcard
    · intro h' hh' k' hk' hD hE
      exact hs (forward h') hh'.forward (forward k')
        (fun a ha => hD (.forward a) (Finset.mem_image_of_mem _ ha))
        (fun a ha => hE (.forward a) (Finset.mem_image_of_mem _ ha))
  | backward a =>
    obtain ⟨D, E, hcard, hs⟩ := IndependentCarrierGraph.compose_finite_support C B A (backward k) hk.backward (backward h) a
    refine ⟨E.image Query.backward, D.image Query.backward, ?_, ?_⟩
    · have hd := Finset.card_image_le (s := D) (f := Query.backward)
      have he := Finset.card_image_le (s := E) (f := Query.backward)
      omega
    · intro h' hh' k' hk' hD hE
      exact hs (backward k') hk'.backward (backward h')
        (fun a ha => hE (.backward a) (Finset.mem_image_of_mem _ ha))
        (fun a ha => hD (.backward a) (Finset.mem_image_of_mem _ ha))

end IndependentInverseGraph

namespace IndependentIndexedInverseGraph

variable {I : Type u} {J : Type v} {K : Type w}
variable (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
variable (S : I → Type x) (M : J → Type y) (T : K → Type z)
variable (h : Table.{u, v, x, y} I J) (hh : IsLawful p S M h)
variable (q : J → K → Bool) (k : Table.{v, w, y, z} J K) (hk : IsLawful q M T k)

/-- Any true first index pair and true second pair expose the same primitive fiber composition. -/
theorem composeRows_at_pair (i : I) (j : J) (l : K) (hij : p i j = true) (hjl : q j l = true)
    (a : IndependentInverseGraph.Query.{x, z}) :
    composeRows p hp S M T h hh q k hk (.edge i l a) =
      IndependentInverseGraph.compose (S i) (M j) (T l) (row h i j) (hh.active i j hij) (row k j l) (hk.active j l hjl) a := by
  have he := (IndependentIndexedCarrierGraph.active_iff p hp i j).1 hij
  subst j
  exact congrFun (row_composeRows p hp S M T h hh q k hk i l hjl) a

/-- A false second index flag forces all composed fiber points to false at a true first index pair. -/
theorem composeRows_false_at_pair (i : I) (j : J) (l : K) (hij : p i j = true) (hjl : q j l = false)
    (a : IndependentInverseGraph.Query.{x, z}) : composeRows p hp S M T h hh q k hk (.edge i l a) = false := by
  have he := (IndependentIndexedCarrierGraph.active_iff p hp i j).1 hij
  subst j
  simp only [composeRows, hjl, Bool.false_eq_true, ↓reduceDIte]

/-- Two index cells and at most two fiber cells determine any direct dependent inverse-composition output. -/
theorem composeRows_finite_support (a : Query.{u, w, x, z} I K) :
    ∃ (D : Finset (I × J)) (E : Finset (J × K))
      (F : Finset (Query.{u, v, x, y} I J)) (G : Finset (Query.{v, w, y, z} J K)),
      D.card ≤ 1 ∧ E.card ≤ 1 ∧ F.card + G.card ≤ 2 ∧
      ∀ (p' : I → J → Bool) (hp' : ∀ i, ∃! j, p' i j = true)
        (h' : Table.{u, v, x, y} I J) (hh' : IsLawful p' S M h')
        (q' : J → K → Bool) (k' : Table.{v, w, y, z} J K) (hk' : IsLawful q' M T k'),
        (∀ a ∈ D, p a.1 a.2 = p' a.1 a.2) → (∀ a ∈ E, q a.1 a.2 = q' a.1 a.2) →
        (∀ a ∈ F, h a = h' a) → (∀ a ∈ G, k a = k' a) →
        composeRows p hp S M T h hh q k hk a = composeRows p' hp' S M T h' hh' q' k' hk' a := by
  classical
  cases a with
  | edge i l a =>
    let j := IndependentIndexedCarrierGraph.index p hp i
    have hij : p i j = true := (IndependentIndexedCarrierGraph.active_iff p hp i j).2 rfl
    by_cases hjl : q j l = true
    · obtain ⟨F, G, hcard, hs⟩ := IndependentInverseGraph.compose_finite_support (S i) (M j) (T l)
        (row h i j) (hh.active i j hij) (row k j l) (hk.active j l hjl) a
      refine ⟨{(i, j)}, {(j, l)}, F.image (Query.edge i j), G.image (Query.edge j l), by simp, by simp, ?_, ?_⟩
      · exact (Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans hcard
      · intro p' hp' h' hh' q' k' hk' hD hE hF hG
        have hij' : p' i j = true := (hD (i, j) (by simp)).symm.trans hij
        have hjl' : q' j l = true := (hE (j, l) (by simp)).symm.trans hjl
        have hv := hs (row h' i j) (hh'.active i j hij') (row k' j l) (hk'.active j l hjl')
          (fun a ha => hF (.edge i j a) (Finset.mem_image_of_mem _ ha))
          (fun a ha => hG (.edge j l a) (Finset.mem_image_of_mem _ ha))
        exact (composeRows_at_pair p hp S M T h hh q k hk i j l hij hjl a).trans
          (hv.trans (composeRows_at_pair p' hp' S M T h' hh' q' k' hk' i j l hij' hjl' a).symm)
    · have hjl0 : q j l = false := by
        cases he : q j l with
        | false => rfl
        | true => exact False.elim (hjl he)
      refine ⟨{(i, j)}, {(j, l)}, ∅, ∅, by simp, by simp, by simp, ?_⟩
      intro p' hp' h' hh' q' k' hk' hD hE _ _
      have hij' : p' i j = true := (hD (i, j) (by simp)).symm.trans hij
      have hjl' : q' j l = false := (hE (j, l) (by simp)).symm.trans hjl0
      exact (composeRows_false_at_pair p hp S M T h hh q k hk i j l hij hjl0 a).trans
        (composeRows_false_at_pair p' hp' S M T h' hh' q' k' hk' i j l hij' hjl' a).symm


/-- Embedding the two index and two value supports into original query types gives at most four input cells. -/
theorem composeRows_lifted_finite_support {X : Type u₁} {Y : Type u₂}
    (leftIndex : I × J → X) (rightIndex : J × K → Y)
    (leftRow : Query.{u, v, x, y} I J → X) (rightRow : Query.{v, w, y, z} J K → Y)
    (leftTable : (X → Bool) → Table.{u, v, x, y} I J) (rightTable : (Y → Bool) → Table.{v, w, y, z} J K)
    (leftPoint : ∀ h a, leftTable h a = h (leftRow a)) (rightPoint : ∀ k a, rightTable k a = k (rightRow a))
    (S : I → Type x) (M : J → Type y) (T : K → Type z) (h : X → Bool) (k : Y → Bool)
    (hp : ∀ i, ∃! j, h (leftIndex (i, j)) = true)
    (hh : IsLawful (fun i j => h (leftIndex (i, j))) S M (leftTable h))
    (hk : IsLawful (fun j l => k (rightIndex (j, l))) M T (rightTable k))
    (a : Query.{u, w, x, z} I K) :
    ∃ (D : Finset X) (E : Finset Y), D.card + E.card ≤ 4 ∧
      ∀ (h' : X → Bool) (k' : Y → Bool)
        (hp' : ∀ i, ∃! j, h' (leftIndex (i, j)) = true)
        (hh' : IsLawful (fun i j => h' (leftIndex (i, j))) S M (leftTable h'))
        (hk' : IsLawful (fun j l => k' (rightIndex (j, l))) M T (rightTable k')),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        composeRows (fun i j => h (leftIndex (i, j))) hp S M T (leftTable h) hh
          (fun j l => k (rightIndex (j, l))) (rightTable k) hk a =
        composeRows (fun i j => h' (leftIndex (i, j))) hp' S M T (leftTable h') hh'
          (fun j l => k' (rightIndex (j, l))) (rightTable k') hk' a := by
  classical
  obtain ⟨D, E, F, G, hD, hE, hFG, hs⟩ := composeRows_finite_support
    (fun i j => h (leftIndex (i, j))) hp S M T (leftTable h) hh
    (fun j l => k (rightIndex (j, l))) (rightTable k) hk a
  refine ⟨D.image leftIndex ∪ F.image leftRow, E.image rightIndex ∪ G.image rightRow, ?_, ?_⟩
  · have hd := Finset.card_image_le (s := D) (f := leftIndex)
    have he := Finset.card_image_le (s := E) (f := rightIndex)
    have hf := Finset.card_image_le (s := F) (f := leftRow)
    have hg := Finset.card_image_le (s := G) (f := rightRow)
    have hl := Finset.card_union_le (D.image leftIndex) (F.image leftRow)
    have hr := Finset.card_union_le (E.image rightIndex) (G.image rightRow)
    omega
  · intro h' k' hp' hh' hk' hL hR
    apply hs (fun i j => h' (leftIndex (i, j))) hp' (leftTable h') hh'
      (fun j l => k' (rightIndex (j, l))) (rightTable k') hk'
    · intro a ha
      exact hL (leftIndex a) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
    · intro a ha
      exact hR (rightIndex a) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
    · intro a ha
      exact (leftPoint h a).trans ((hL (leftRow a) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))).trans (leftPoint h' a).symm)
    · intro a ha
      exact (rightPoint k a).trans ((hR (rightRow a) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))).trans (rightPoint k' a).symm)

end IndependentIndexedInverseGraph

namespace IndependentCandidateIndexedInverseGraph

/-- Candidate extension forces a false value whenever either outer carrier differs from the declared one. -/
theorem extend_inactive (I : Type u) (J : Type v) (h : IndependentIndexedInverseGraph.Table.{u, v, w, z} I J)
    (K : Type u) (L : Type v) (k : K) (l : L) (a : IndependentInverseGraph.Query.{w, z})
    (hn : K ≠ I ∨ L ≠ J) : extend I J h (.edge K L k l a) = false := by
  classical
  rcases hn with hK | hL
  · simp [extend, hK]
  · by_cases hK : K = I <;> simp [extend, hK, hL]

end IndependentCandidateIndexedInverseGraph

end

end AAT.AG.LocalSemanticReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentInverseGraph
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentIndexedInverseGraph
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentCandidateIndexedInverseGraph
