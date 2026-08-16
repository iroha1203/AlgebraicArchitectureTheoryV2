import ResearchLean.AG.CrossStageCoherence.TowerCompatibility
import ResearchLean.AG.TransportCoherence.FinitePresentation
import Mathlib.Algebra.Exact

/-!
# Cross-stage fiber automorphism groups

This module fixes the three groups used by the G-109 obstruction formula.
`CompositeFiberAut` consists of geometry automorphisms lying over identity only
after both projections, while `InnerFiberAut` imposes identity already at the
core-package stage.  Projection therefore gives a potentially nonconstant
homomorphism to the G-106 core-fiber group, with the inner group as its kernel.

The final section constructs the composite canonical comparator directly from
the two local strong-cocartesian certificates and proves that projection sends
it to the G-106 canonical core comparator.

## Implementation notes

`C_G` is realized as the automorphisms vertical only after the composite
projection and `H_G` as the kernel of the actual pushforward.  An abstract
pre-supplied extension was rejected because it would sever the groups and the
canonical comparator from the geometry-to-core tower.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 2000000

/-- Geometry automorphisms that are vertical for the composite projection. -/
def compositeFiberAutSubgroup {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) : Subgroup (Aut G) where
  carrier automorphism :=
    automorphism.hom.base.base = 𝟙 (packagePoint G.core)
  one_mem' := by rfl
  mul_mem' := by
    intro left right hleft hright
    change (right.hom.comp left.hom).base.base = 𝟙 (packagePoint G.core)
    change right.hom.base.base.comp left.hom.base.base =
      𝟙 (packagePoint G.core)
    rw [hright, hleft]
    exact (@Category.id_comp
      (ExtractionInstance U) (ExtInstHom.extractionInstanceCategory U)
      (packagePoint G.core) (packagePoint G.core)
      (𝟙 (packagePoint G.core)))
  inv_mem' := by
    intro automorphism homBase
    have mappedIso : (crossStageProjection.{u, v} U).mapIso automorphism =
        Iso.refl (packagePoint G.core) := by
      apply Iso.ext
      exact homBase
    have invBase := congrArg
      (fun iso : Aut (packagePoint G.core) => iso.inv) mappedIso
    simpa using invBase

/-- The composite-fiber group `C_G`. -/
abbrev CompositeFiberAut {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) := compositeFiberAutSubgroup G

namespace CompositeFiberAut

/-- Forward geometry morphism represented by a composite-fiber automorphism. -/
def hom {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    (automorphism : CompositeFiberAut G) : GeometryTotalHom G G :=
  automorphism.1.hom

/-- Inverse geometry morphism represented by a composite-fiber automorphism. -/
def inv {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    (automorphism : CompositeFiberAut G) : GeometryTotalHom G G :=
  automorphism.1.inv

/-- A composite-fiber automorphism lies over the pointed identity. -/
theorem hom_base_base_eq {U : AtomCarrier.{u}}
    {G : GeometryPackage.{u, v} U} (automorphism : CompositeFiberAut G) :
    (hom automorphism).base.base = 𝟙 (packagePoint G.core) :=
  automorphism.2

/-- The inverse also lies over the pointed identity. -/
theorem inv_base_base_eq {U : AtomCarrier.{u}}
    {G : GeometryPackage.{u, v} U} (automorphism : CompositeFiberAut G) :
    (inv automorphism).base.base = 𝟙 (packagePoint G.core) := by
  exact (compositeFiberAutSubgroup G).inv_mem automorphism.2

/-- Composite-fiber automorphisms are determined after a common strong lift. -/
theorem ext_of_strong_fac {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (lift : GeometryTotalHom G H)
    [(crossStageProjection.{u, v} U).IsStronglyCocartesian
      lift.base.base lift]
    (left right : CompositeFiberAut H)
    (fac : lift.comp (hom left) = lift.comp (hom right)) : left = right := by
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 (packagePoint H.core)) left.1.hom := by
    rw [← hom_base_base_eq]
    change (crossStageProjection.{u, v} U).IsHomLift
      ((crossStageProjection.{u, v} U).map (hom left)) (hom left)
    infer_instance
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 (packagePoint H.core)) right.1.hom := by
    rw [← hom_base_base_eq]
    change (crossStageProjection.{u, v} U).IsHomLift
      ((crossStageProjection.{u, v} U).map (hom right)) (hom right)
    infer_instance
  apply Subtype.ext
  apply Iso.ext
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (crossStageProjection.{u, v} U) lift.base.base lift
    (𝟙 (packagePoint H.core))
  exact fac

end CompositeFiberAut

/-- The subgroup of `C_G` already vertical at the geometry-to-core stage. -/
def innerFiberAutSubgroup {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) : Subgroup (CompositeFiberAut G) where
  carrier automorphism := automorphism.1.hom.base = 𝟙 G.core
  one_mem' := by rfl
  mul_mem' := by
    intro left right hleft hright
    change (right.1.hom.comp left.1.hom).base = 𝟙 G.core
    change right.1.hom.base.comp left.1.hom.base = 𝟙 G.core
    rw [hright, hleft]
    exact (@Category.id_comp
      (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
      G.core G.core (𝟙 G.core))
  inv_mem' := by
    intro automorphism homBase
    have mappedIso : (geometryProjection U).mapIso automorphism.1 =
        Iso.refl G.core := by
      apply Iso.ext
      exact homBase
    have invBase := congrArg (fun iso : Aut G.core => iso.inv) mappedIso
    simpa using invBase

/-- The strict inner group `H_G`. -/
abbrev InnerFiberAut {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) := innerFiberAutSubgroup G

/-- The lower group `B_G`, inherited from G-106. -/
abbrev CoreStageFiberAut {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) := PackageFiberAut G.core

/-- Projection of composite-fiber automorphisms to the G-106 core group. -/
noncomputable def compositeFiberPushforward {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    CompositeFiberAut G →* CoreStageFiberAut G where
  toFun automorphism :=
    ⟨(geometryProjection U).mapIso automorphism.1, automorphism.2⟩
  map_one' := by
    apply Subtype.ext
    apply Iso.ext
    rfl
  map_mul' left right := by
    apply Subtype.ext
    apply Iso.ext
    rfl

/-- On forward morphisms, pushforward is exactly the geometry projection. -/
@[simp] theorem compositeFiberPushforward_hom {U : AtomCarrier.{u}}
    {G : GeometryPackage.{u, v} U} (automorphism : CompositeFiberAut G) :
    PackageFiberAut.hom (compositeFiberPushforward G automorphism) =
      (CompositeFiberAut.hom automorphism).base :=
  rfl

/-- Pushforward is identity exactly for core-vertical geometry automorphisms. -/
theorem compositeFiberPushforward_eq_one_iff {U : AtomCarrier.{u}}
    {G : GeometryPackage.{u, v} U} (automorphism : CompositeFiberAut G) :
    compositeFiberPushforward G automorphism = 1 ↔
      automorphism.1.hom.base = 𝟙 G.core := by
  constructor
  · intro equality
    have homEquality := congrArg
      (fun element : CoreStageFiberAut G => PackageFiberAut.hom element)
      equality
    simpa using homEquality
  · intro homBase
    apply Subtype.ext
    apply Iso.ext
    exact homBase

/-- The authored strict subgroup is precisely the kernel of pushforward. -/
theorem innerFiberAutSubgroup_eq_ker {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    innerFiberAutSubgroup G = (compositeFiberPushforward G).ker := by
  ext automorphism
  change automorphism.1.hom.base = 𝟙 G.core ↔
    compositeFiberPushforward G automorphism = 1
  exact (compositeFiberPushforward_eq_one_iff automorphism).symm

/-- Inclusion of the strict inner group into the composite-fiber group. -/
def innerFiberInclusion {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    InnerFiberAut G →* CompositeFiberAut G :=
  (innerFiberAutSubgroup G).subtype

/-- The terminal map in the canonical group extension, restricted to its image. -/
noncomputable def compositeFiberImageMap {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    CompositeFiberAut G →* (compositeFiberPushforward G).range :=
  (compositeFiberPushforward G).rangeRestrict

/-- The first arrow of the group extension is injective. -/
theorem innerFiberInclusion_injective {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    Function.Injective (innerFiberInclusion G) :=
  Subtype.val_injective

/-- The image-restricted pushforward is surjective. -/
theorem compositeFiberImageMap_surjective {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    Function.Surjective (compositeFiberImageMap G) :=
  MonoidHom.rangeRestrict_surjective _

/-- Exactness at `C_G`: the image of `H_G` is the pushforward kernel. -/
theorem inner_to_composite_to_image_exact {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    Function.MulExact (innerFiberInclusion G) (compositeFiberImageMap G) := by
  intro automorphism
  constructor
  · intro imageIdentity
    have pushedIdentity : compositeFiberPushforward G automorphism = 1 := by
      exact congrArg Subtype.val imageIdentity
    exact ⟨⟨automorphism,
      (compositeFiberPushforward_eq_one_iff automorphism).1 pushedIdentity⟩,
      rfl⟩
  · rintro ⟨inner, rfl⟩
    apply Subtype.ext
    exact (compositeFiberPushforward_eq_one_iff inner.1).2 inner.2

/-- The canonical short group extension `1 → H_G → C_G → p(C_G) → 1`. -/
theorem compositeFiber_group_extension {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    Function.Injective (innerFiberInclusion G) ∧
      Function.MulExact (innerFiberInclusion G) (compositeFiberImageMap G) ∧
      Function.Surjective (compositeFiberImageMap G) :=
  ⟨innerFiberInclusion_injective G,
    inner_to_composite_to_image_exact G,
    compositeFiberImageMap_surjective G⟩

/-! ## Composite strong lifts and canonical comparisons -/

/-- Two local certificates generate the composite strong certificate. -/
theorem geometryHom_isCompositeStronglyCocartesian
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (φ : GeometryTotalHom G H)
    [(geometryProjection U).IsStronglyCocartesian φ.base φ]
    [(packageProjection U).IsStronglyCocartesian φ.base.base φ.base] :
    (crossStageProjection.{u, v} U).IsStronglyCocartesian
      φ.base.base φ := by
  letI : (geometryProjection U).IsStronglyCocartesian
      ((geometryProjection U).map φ) φ := by
    simpa only [geometryProjection_map] using inferInstanceAs
      ((geometryProjection U).IsStronglyCocartesian φ.base φ)
  letI : (packageProjection U).IsStronglyCocartesian
      ((packageProjection U).map ((geometryProjection U).map φ))
      ((geometryProjection U).map φ) := by
    simpa only [geometryProjection_map, packageProjection_map] using
      inferInstanceAs
        ((packageProjection U).IsStronglyCocartesian φ.base.base φ.base)
  exact stronglyCocartesian_comp_projection
    (geometryProjection U) (packageProjection U) φ

/-- Canonical `C_G` comparison of two composite strong lifts. -/
noncomputable def canonicalCompositeFiberComparator
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (left right : GeometryTotalHom G H)
    (baseEq : left.base.base = right.base.base)
    [(geometryProjection U).IsStronglyCocartesian left.base left]
    [(geometryProjection U).IsStronglyCocartesian right.base right]
    [(packageProjection U).IsStronglyCocartesian left.base.base left.base]
    [(packageProjection U).IsStronglyCocartesian right.base.base right.base] :
    CompositeFiberAut H := by
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      left.base.base left := geometryHom_isCompositeStronglyCocartesian left
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      right.base.base right := geometryHom_isCompositeStronglyCocartesian right
  have rightBase : right.base.base =
      left.base.base ≫ (Iso.refl (packagePoint H.core)).hom := by
    simpa using baseEq.symm
  let comparison : H ≅ H :=
    CategoryTheory.Functor.IsStronglyCocartesian.codomainIsoOfBaseIso
      (p := crossStageProjection.{u, v} U)
      (f := left.base.base) (f' := right.base.base)
      (g := Iso.refl (packagePoint H.core)) rightBase left right
  have homLift : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 (packagePoint H.core)) comparison.hom := by
    change (crossStageProjection.{u, v} U).IsHomLift
      (Iso.refl (packagePoint H.core)).hom
      (CategoryTheory.Functor.IsStronglyCocartesian.map
        (crossStageProjection.{u, v} U) left.base.base left
        rightBase right)
    infer_instance
  have homBase : comparison.hom.base.base = 𝟙 (packagePoint H.core) :=
    (CategoryTheory.IsHomLift.eq_of_isHomLift
      (crossStageProjection.{u, v} U) _ comparison.hom).symm
  exact ⟨comparison, homBase⟩

/-- The composite canonical comparator satisfies its defining factorization. -/
@[simp] theorem canonicalCompositeFiberComparator_fac
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (left right : GeometryTotalHom G H)
    (baseEq : left.base.base = right.base.base)
    [(geometryProjection U).IsStronglyCocartesian left.base left]
    [(geometryProjection U).IsStronglyCocartesian right.base right]
    [(packageProjection U).IsStronglyCocartesian left.base.base left.base]
    [(packageProjection U).IsStronglyCocartesian right.base.base right.base] :
    left.comp (CompositeFiberAut.hom
        (canonicalCompositeFiberComparator left right baseEq)) = right := by
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      left.base.base left := geometryHom_isCompositeStronglyCocartesian left
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      right.base.base right := geometryHom_isCompositeStronglyCocartesian right
  have rightBase : right.base.base =
      left.base.base ≫ (Iso.refl (packagePoint H.core)).hom := by
    simpa using baseEq.symm
  unfold canonicalCompositeFiberComparator
  dsimp only
  simpa only using CategoryTheory.Functor.IsStronglyCocartesian.fac
    (p := crossStageProjection.{u, v} U)
    (f := left.base.base) (φ := left)
    (g := (Iso.refl (packagePoint H.core)).hom)
    (f' := right.base.base) (hf' := rightBase) (φ' := right)

/-- Projection sends the composite comparator to the G-106 core comparator. -/
theorem compositeFiberPushforward_canonicalComparator
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (left right : GeometryTotalHom G H)
    (baseEq : left.base.base = right.base.base)
    [(geometryProjection U).IsStronglyCocartesian left.base left]
    [(geometryProjection U).IsStronglyCocartesian right.base right]
    [(packageProjection U).IsStronglyCocartesian left.base.base left.base]
    [(packageProjection U).IsStronglyCocartesian right.base.base right.base] :
    compositeFiberPushforward H
        (canonicalCompositeFiberComparator left right baseEq) =
      canonicalFiberComparator left.base right.base baseEq := by
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      left.base.base left := geometryHom_isCompositeStronglyCocartesian left
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      right.base.base right := geometryHom_isCompositeStronglyCocartesian right
  apply PackageFiberAut.ext_of_strong_fac left.base
  calc
    left.base.comp (PackageFiberAut.hom
        (compositeFiberPushforward H
          (canonicalCompositeFiberComparator left right baseEq))) =
      (left.comp (CompositeFiberAut.hom
        (canonicalCompositeFiberComparator left right baseEq))).base := rfl
    _ = right.base := congrArg GeometryTotalHom.base
      (canonicalCompositeFiberComparator_fac left right baseEq)
    _ = left.base.comp (PackageFiberAut.hom
        (canonicalFiberComparator left.base right.base baseEq)) :=
      (canonicalFiberComparator_fac left.base right.base baseEq).symm

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
