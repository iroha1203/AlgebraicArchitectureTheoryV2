import ResearchLean.AG.RelativeRepairComposition.SubdivisionPrivatePartition
import ResearchLean.AG.RelativeRepairComposition.SubdivisionCoefficientMaps

/-!
# Complete public original names and candidate masks after subdivision

## Implementation notes

Public names are the full complement of private names among nonfixed edges of
each region. They include every shared and candidate edge, not only candidates.
The independently defined new complement is first compared through edgeOrigin.
When the chosen edge is private in one member, no public member can contain its
name, so the resulting public name equivalence retains every complete name.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open TransportCoherence
universe uG uI
variable (K : FiniteTransportPresentation.{uG}) (chosen : EdgeName (K := K))
variable {I : Type uI} (U : I → ClosedRegion K) (P : ClosedRegion K)
variable (candidates : Set (EdgeName (K := K)))

/-- Every nonfixed original edge outside the private variables is a public name. -/
def publicEdges (i : I) : Set (EdgeName (K := K)) :=
  {e | e ∈ (U i).edges ∧ e ∉ P.edges ∧ e ∉ ClosedRegion.privateAlwaysEdges U P candidates i}

/-- All independently generated new public names read their original public membership. -/
theorem expanded_public_edges (hc : chosen ∉ candidates) (i : I) :
    publicEdges (presentation K chosen)
      (fun j => expandedRegion K chosen (U j)) (expandedRegion K chosen P)
      (oldEdgeSet K chosen candidates) i = expandedEdgeSet K chosen (publicEdges K U P candidates i) := by
  unfold publicEdges
  rw [expanded_private_edges K chosen U P candidates hc]
  rfl

/-- A chosen edge private in one member is public in no member. -/
theorem chosen_not_public (i : I)
    (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I) :
    chosen ∉ publicEdges K U P candidates j := by
  intro h
  have hj : j = i := by
    by_contra hji
    exact chosen_outside_other K chosen U P candidates i j hi hji h.1
  subst j
  exact h.2.2 hi

/-- The full new public complement has no first or second factor when the chosen edge is private. -/
theorem public_origin_ne_chosen (i : I)
    (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I)
    (a : publicEdges (presentation K chosen) (fun l => expandedRegion K chosen (U l))
      (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j) :
    edgeOrigin K chosen a.1 ≠ chosen := by
  have hc := hi.2.2.1
  have ha : edgeOrigin K chosen a.1 ∈ publicEdges K U P candidates j :=
    (congrArg (fun s : Set (EdgeName (K := presentation K chosen)) => a.1 ∈ s)
      (expanded_public_edges K chosen U P candidates hc j)).mp a.2
  intro h
  exact chosen_not_public K chosen U P candidates i hi j (h ▸ ha)

/-- Every region's entire new public complement is equivalent to its entire old public complement. -/
noncomputable def publicNameEquiv (i : I)
    (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I) :
    publicEdges (presentation K chosen) (fun l => expandedRegion K chosen (U l))
      (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j ≃
      publicEdges K U P candidates j where
  toFun a := ⟨edgeOrigin K chosen a.1,by
    exact (congrArg (fun s : Set (EdgeName (K := presentation K chosen)) => a.1 ∈ s)
      (expanded_public_edges K chosen U P candidates hi.2.2.1 j)).mp a.2⟩
  invFun e := ⟨oldEdgeName K chosen e.1 (fun h =>
      chosen_not_public K chosen U P candidates i hi j (h ▸ e.2)),by
    rw [expanded_public_edges K chosen U P candidates hi.2.2.1]
    exact e.2⟩
  left_inv a := by
    apply Subtype.ext
    exact ((edgeOrigin_eq_old K chosen a.1 _
      (public_origin_ne_chosen K chosen U P candidates i hi j a)).mp rfl).symm
  right_inv e := by apply Subtype.ext; rfl

/-- The forward map reads exactly the same complete original name. -/
theorem publicNameEquiv_value (i : I)
    (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I)
    (a : publicEdges (presentation K chosen) (fun l => expandedRegion K chosen (U l))
      (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j) :
    (publicNameEquiv K chosen U P candidates i hi j a).1 = edgeOrigin K chosen a.1 := rfl

/-- The inverse restores the exact retained name at its original endpoints. -/
theorem publicNameEquiv_inverse_value (i : I)
    (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I)
    (e : publicEdges K U P candidates j) :
    ((publicNameEquiv K chosen U P candidates i hi j).symm e).1 =
      oldEdgeName K chosen e.1 (fun h => chosen_not_public K chosen U P candidates i hi j (h ▸ e.2)) := rfl

/-- All candidate permission sets retain the same forbidden complete names. -/
theorem retained_forbidden_mask (hc : chosen ∉ candidates)
    (S : Set (EdgeName (K := K))) (a : EdgeName (K := presentation K chosen)) :
    a ∈ oldEdgeSet K chosen (candidates \ S) ↔ edgeOrigin K chosen a ∈ candidates \ S := by
  rw [← expanded_set_avoiding K chosen (candidates \ S) (fun h => hc h.1)]
  exact Iff.rfl

/-- The whole public name comparison preserves every forbidden candidate mask simultaneously. -/
theorem public_forbidden_mask (i : I)
    (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I)
    (S : Set (EdgeName (K := K)))
    (a : publicEdges (presentation K chosen) (fun l => expandedRegion K chosen (U l))
      (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j) :
    a.1 ∈ oldEdgeSet K chosen (candidates \ S) ↔
      (publicNameEquiv K chosen U P candidates i hi j a).1 ∈ candidates \ S :=
  retained_forbidden_mask K chosen candidates hi.2.2.1 S a.1


namespace PublicKernels
open CategoryTheory TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uE uB uD vE vB vD
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (F : Factorization T chosen)
variable (i : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I)

/-- Every retained public name keeps the entire actual target projection kernel. -/
noncomputable def coefficientEquiv (e : publicEdges K U P candidates j) :
    (originalTower T chosen F).toTower.localCoefficients.A
      ((publicNameEquiv K chosen U P candidates i hi j).symm e).1.2.1 ≃+
      T.toTower.localCoefficients.A e.1.2.1 := AddEquiv.refl _

/-- No public full-kernel value is changed by the coefficient comparison. -/
theorem coefficientEquiv_value (e : publicEdges K U P candidates j)
    (x : (originalTower T chosen F).toTower.localCoefficients.A
      ((publicNameEquiv K chosen U P candidates i hi j).symm e).1.2.1) :
    coefficientEquiv K chosen U P candidates T F i hi j e x = x := rfl

/-- Complete new public coefficient families and complete old families have both inverse compositions. -/
noncomputable def familyEquiv :
    (∀ a : publicEdges (presentation K chosen) (fun l => expandedRegion K chosen (U l))
      (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j,
      (originalTower T chosen F).toTower.localCoefficients.A a.1.2.1) ≃
    (∀ e : publicEdges K U P candidates j, T.toTower.localCoefficients.A e.1.2.1) :=
  (Equiv.piCongrLeft' (fun a => (originalTower T chosen F).toTower.localCoefficients.A a.1.2.1)
    (publicNameEquiv K chosen U P candidates i hi j)).trans
      (Equiv.piCongrRight (fun e => (coefficientEquiv K chosen U P candidates T F i hi j e).toEquiv))

/-- The forward full-family comparison reads the exact actual retained public value. -/
theorem familyEquiv_value
    (x : ∀ a : publicEdges (presentation K chosen) (fun l => expandedRegion K chosen (U l))
      (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) j,
      (originalTower T chosen F).toTower.localCoefficients.A a.1.2.1)
    (e : publicEdges K U P candidates j) :
    familyEquiv K chosen U P candidates T F i hi j x e =
      x ((publicNameEquiv K chosen U P candidates i hi j).symm e) := rfl

/-- The inverse restores each whole actual public coefficient with the original value. -/
theorem familyEquiv_inverse_value
    (x : ∀ e : publicEdges K U P candidates j, T.toTower.localCoefficients.A e.1.2.1)
    (e : publicEdges K U P candidates j) :
    (familyEquiv K chosen U P candidates T F i hi j).symm x
      ((publicNameEquiv K chosen U P candidates i hi j).symm e) = x e := by
  exact congrArg (fun y => y e) ((familyEquiv K chosen U P candidates T F i hi j).apply_symm_apply x)

end PublicKernels

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
