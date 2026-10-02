import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedExternal

/-!
# Full original actual external morphisms of independently generated strict objects

## Implementation notes

Both maps read the original actual arrows restored from the independent native
generated groupoid. Their full inverse correspondence retains every external
morphism and every shared original label; identities and compositions use the
same native functor before any quotient or object existence test.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [∀ j, DecidablePred (· ∈ (U j).vertices)]
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (owner : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates owner)
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k)
  (x : T.toTower.localCoefficients.A s),
  T.toTower.localCoefficients.edge e (a • x) = a • T.toTower.localCoefficients.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)
local notation "Mo" => T.toTower.localCoefficients
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Bn" => FiniteBases.expandedBases T chosen factor bases
local notation "Un" => (fun j => expandedRegion K chosen (U j))
local notation "Pn" => expandedRegion K chosen P
local notation "Cn" => oldEdgeSet K chosen candidates
local notation "en" => FiniteEnumerations.edgeEnumeration K chosen ee
local notation "Aw" => Additive (Kernel p q factor.middle)


variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (ei : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (allowed : Set (EdgeName (K := K)))
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed
local notation "values" => (fun j => -CoverEquation.defect Mo P (ActualEquation.defectFamily T P hfixed) (U j))



universe uX vX
variable (W : ClosedRegion K) (hw : chosen ∉ W.edges)
local notation "N" => GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values (candidates \ allowed)
local notation "O" => GeneratedStrictObjects.OldObjects T bases U P candidates hlinear ek ee ef values (candidates \ allowed)
local notation "C" => GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values
local notation "EN" => GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed
local notation "EO" => GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc allowed

local notation "Ln" => StrictSupportedCover.Labels Mn Pn Un Cn (oldEdgeSet K chosen allowed)
local notation "G" => ActionCategory (Multiplicative Ln) N
local notation "A" => RepairGroupoid T P.vertices fixed
local notation "Enew" => GeneratedActualNative.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed

/-- Restore the entire original actual new arrow, then collapse it with all original old labels. -/
noncomputable def collapseActualFunctor : G ⥤ A :=
  (Enew).inverse ⋙ collapseFunctor T chosen factor P.vertices fixed
    (GeneratedActualComparison.chosen_not_fixed chosen U P candidates owner hi allowed)

/-- The native actual collapse functor reads exactly the independently compared old generated object. -/
theorem collapseActual_object (x : G) :
    ((collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).obj x).back =
      (EO).symm ((C) x.back).1 := by
  apply (EO).injective
  rw [Equiv.apply_symm_apply]
  have h := GeneratedActualComparison.comparison_old_actual T chosen factor bases U P candidates owner hi hlinear ek ee ef
    hfixed ei hc allowed ((EN).symm x.back)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Every native generated arrow between arbitrary objects corresponds bijectively to its original old actual arrow. -/
noncomputable def homEquiv (x y : G) :
    (x ⟶ y) ≃
      ((collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).obj x ⟶
       (collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).obj y) :=
  ((Enew).fullyFaithfulInverse.homEquiv).trans
    (collapseHomEquiv T chosen factor P.vertices fixed
      (GeneratedActualComparison.chosen_not_fixed chosen U P candidates owner hi allowed)
      ((Enew).inverse.obj x) ((Enew).inverse.obj y))

/-- Full arrow comparison is the same native actual restoration and collapse functor. -/
theorem homEquiv_value {x y : G} (f : x ⟶ y) :
    homEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed x y f =
      (collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).map f := rfl

/-- The new shared label is read directly from the independently restored full actual new arrow. -/
noncomputable def newSharedLabel {x y : G} (f : x ⟶ y) (v : W.vertices) : (Mo).A v.1 :=
  (((Enew).inverse.map f).1.toAdd).1 (.inl v.1)

/-- Native comparison retains each full shared actual vertex label literally. -/
theorem mapped_shared_label {x y : G} (f : x ⟶ y) (v : W.vertices) :
    (((collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).map f).1.toAdd).1 v.1 =
      newSharedLabel T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W f v := rfl

section ExternalCategory
variable {X : Type uX} [Category.{vX} X]
variable (externalLabel : ∀ {x y : X}, (x ⟶ y) → ∀ v : W.vertices, (Mo).A v.1)

set_option maxHeartbeats 8000000 in
/-- All independent external compatible arrows have full inverse comparisons, retaining the entire external morphism. -/
noncomputable def externalHomEquiv
    (externalLabel : ∀ {x y : X}, (x ⟶ y) → ∀ v : W.vertices, (Mo).A v.1) (x y : G) (a b : X) :
    {f : (x ⟶ y) × (a ⟶ b) // ∀ v : W.vertices,
      newSharedLabel T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W f.1 v = externalLabel f.2 v} ≃
    {f : ((collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).obj x ⟶
      (collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).obj y) × (a ⟶ b) //
      ∀ v : W.vertices, (f.1.1.toAdd).1 v.1 = externalLabel f.2 v} where
  toFun f := ⟨(homEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed x y f.1.1,f.1.2),by
    intro v
    rw [homEquiv_value,mapped_shared_label]
    exact f.2 v⟩
  invFun f := ⟨((homEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed x y).symm f.1.1,f.1.2),by
    intro v
    have h := mapped_shared_label T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W
      ((homEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed x y).symm f.1.1) v
    rw [← homEquiv_value,Equiv.apply_symm_apply] at h
    exact h.symm.trans (f.2 v)⟩
  left_inv f := by
    apply Subtype.ext
    exact Prod.ext ((homEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed x y).symm_apply_apply f.1.1) rfl
  right_inv f := by
    apply Subtype.ext
    exact Prod.ext ((homEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed x y).apply_symm_apply f.1.1) rfl

/-- Full comparison leaves every external compatible morphism literally unchanged. -/
theorem external_arrow_value
    (externalLabel : ∀ {x y : X}, (x ⟶ y) → ∀ v : W.vertices, (Mo).A v.1) (x y : G) (a b : X)
    (f : {f : (x ⟶ y) × (a ⟶ b) // ∀ v : W.vertices,
      newSharedLabel T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W f.1 v = externalLabel f.2 v}) :
    (externalHomEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W externalLabel x y a b f).1.2 = f.1.2 := rfl

/-- Complete generated comparison preserves native composition and the entire external composite. -/
theorem external_composition {x y z : G} {a b c : X}
    (f : x ⟶ y) (g : y ⟶ z) (r : a ⟶ b) (s : b ⟶ c) :
    ((collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).map (f ≫ g),r ≫ s) =
    ((collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).map f ≫
      (collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).map g,r ≫ s) :=
  Prod.ext ((collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).map_comp f g) rfl

/-- Complete generated comparison preserves native identity and every external identity. -/
theorem external_identity (x : G) (a : X) :
    ((collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).map (𝟙 x),𝟙 a) =
    (𝟙 ((collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).obj x),𝟙 a) :=
  Prod.ext ((collapseActualFunctor T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).map_id x) rfl
end ExternalCategory

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedExternalArrows
