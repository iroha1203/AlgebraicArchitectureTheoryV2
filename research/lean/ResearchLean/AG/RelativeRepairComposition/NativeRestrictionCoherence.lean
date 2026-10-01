import ResearchLean.AG.RelativeRepairComposition.NativeDescent

/-!
# Original-label coherence of actual restriction

The identity and composition comparisons retain every original physical edge
choice and use identity vertex labels. Their naturality is checked on full raw
labels, without replacing actual repairs or arrows by their isomorphism classes.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uC vC uH uX
section IdentityComparison
variable {C : Type uC} [Category.{vC} C] {H : Type uH} [Group H]
variable {X : Type uX} [MulAction H X]
/-- A full group-action equation generates the actual labeled isomorphism in both directions. -/
def actionLabelIso {x y : ActionCategory H X} (g : H) (h : g • x.back = y.back) : x ≅ y where
  hom := ⟨g,h⟩
  inv := ⟨g⁻¹,by
    change g⁻¹ • y.back = x.back
    rw [← h, inv_smul_smul]⟩
  hom_inv_id := Subtype.ext (inv_mul_cancel g)
  inv_hom_id := Subtype.ext (mul_inv_cancel g)

/-- The forward isomorphism keeps exactly the specified original label. -/
theorem action_label_iso_label {x y : ActionCategory H X} (g : H) (h : g • x.back = y.back) :
    (actionLabelIso g h).hom.1 = g := rfl

/-- The reverse isomorphism keeps the complete inverse original label. -/
theorem action_label_iso_inverse_label {x y : ActionCategory H X} (g : H) (h : g • x.back = y.back) :
    (actionLabelIso g h).inv.1 = g⁻¹ := rfl

variable (F G : C ⥤ ActionCategory H X)
variable (ho : ∀ x, (F.obj x).back = (G.obj x).back)
variable (hm : ∀ {x y} (f : x ⟶ y), (F.map f).1 = (G.map f).1)

/-- Equality of actual objects gives an isomorphism with the full identity label. -/
def identityLabelIso (x : C) : F.obj x ≅ G.obj x where
  hom := ⟨1,by
    change (1 : H) • (F.obj x).back = (G.obj x).back
    rw [one_smul]; exact ho x⟩
  inv := ⟨1,by
    change (1 : H) • (G.obj x).back = (F.obj x).back
    rw [one_smul]; exact (ho x).symm⟩
  hom_inv_id := Subtype.ext (one_mul 1)
  inv_hom_id := Subtype.ext (one_mul 1)

/-- Full original object and arrow equalities generate the whole natural comparison. -/
def identityLabelComparison : F ≅ G :=
  NatIso.ofComponents (identityLabelIso F G ho) (by
    intro x y f
    apply Subtype.ext
    change (1 : H) * (F.map f).1 = (G.map f).1 * 1
    rw [one_mul, mul_one, hm f])

/-- Every component carries the whole original identity label. -/
theorem identity_comparison_label (x : C) :
    ((identityLabelComparison F G ho hm).hom.app x).1 = (1 : H) := rfl
end IdentityComparison

universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace NativeDescent
variable (T : OriginalTowerPresentation K p q) (P : ClosedRegion K)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))

/-- Two successive native restrictions preserve precisely the same full actual repair. -/
theorem restriction_comp_obj {U V W : ClosedRegion K}
    (i : ClosedRegion.Inclusion V U) (j : ClosedRegion.Inclusion W V)
    (R : LocalGroupoid T P U) :
    ((restrictionFunctor T P hfixed i ⋙ restrictionFunctor T P hfixed j).obj R).back =
      ((restrictionFunctor T P hfixed (j.trans i)).obj R).back := by
  apply Subtype.ext
  apply Solution.ext
  intro a b e
  simp only [Functor.comp_obj, restriction_obj_choice]

/-- Composed restrictions keep the full original gauge label at every vertex. -/
theorem restriction_comp_map {U V W : ClosedRegion K}
    (i : ClosedRegion.Inclusion V U) (j : ClosedRegion.Inclusion W V)
    {R Q : LocalGroupoid T P U} (f : R ⟶ Q) :
    ((restrictionFunctor T P hfixed i ⋙ restrictionFunctor T P hfixed j).map f).1 =
      ((restrictionFunctor T P hfixed (j.trans i)).map f).1 := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext; funext v
  rfl

/-- Identity restriction keeps the complete actual repair, including every edge choice. -/
theorem restriction_id_obj (U : ClosedRegion K) (R : LocalGroupoid T P U) :
    ((restrictionFunctor T P hfixed (ClosedRegion.Inclusion.refl U)).obj R).back = R.back := by
  apply Subtype.ext
  apply Solution.ext
  intro a b e
  rw [restriction_obj_choice]
  rfl

/-- Identity restriction retains the entire original vertex label. -/
theorem restriction_id_map (U : ClosedRegion K) {R Q : LocalGroupoid T P U} (f : R ⟶ Q) :
    ((restrictionFunctor T P hfixed (ClosedRegion.Inclusion.refl U)).map f).1 = f.1 := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext; funext v
  rfl

set_option maxHeartbeats 1000000 in
/-- The full identity-labeled natural comparison of two successive restrictions. -/
noncomputable def restrictionComposition {U V W : ClosedRegion K}
    (i : ClosedRegion.Inclusion V U) (j : ClosedRegion.Inclusion W V) :
    restrictionFunctor T P hfixed i ⋙ restrictionFunctor T P hfixed j ≅
      restrictionFunctor T P hfixed (j.trans i) :=
  identityLabelComparison _ _ (restriction_comp_obj T P hfixed i j)
    (restriction_comp_map T P hfixed i j)

set_option maxHeartbeats 1000000 in
/-- The full identity-labeled comparison of identity restriction. -/
noncomputable def restrictionIdentity (U : ClosedRegion K) :
    restrictionFunctor T P hfixed (ClosedRegion.Inclusion.refl U) ≅ 𝟭 (LocalGroupoid T P U) :=
  identityLabelComparison _ _ (restriction_id_obj T P hfixed U) (restriction_id_map T P hfixed U)

/-- Every composition comparison retains the complete identity gauge on its final region. -/
theorem restriction_composition_label {U V W : ClosedRegion K}
    (i : ClosedRegion.Inclusion V U) (j : ClosedRegion.Inclusion W V) (R : LocalGroupoid T P U) :
    ((restrictionComposition T P hfixed i j).hom.app R).1 =
      (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower W T)
        (ClosedRegion.nativeIntersection W P).vertices (ClosedRegion.nativeIntersection W P).edges)) := rfl

/-- Every identity comparison retains the complete identity gauge. -/
theorem restriction_identity_label (U : ClosedRegion K) (R : LocalGroupoid T P U) :
    ((restrictionIdentity T P hfixed U).hom.app R).1 =
      (1 : Multiplicative (supportedC0 (ClosedRegion.restrictTower U T)
        (ClosedRegion.nativeIntersection U P).vertices (ClosedRegion.nativeIntersection U P).edges)) := rfl
end NativeDescent
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
