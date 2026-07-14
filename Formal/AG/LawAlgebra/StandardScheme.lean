import Formal.AG.LawAlgebra.StructureSheaf
import Mathlib.AlgebraicGeometry.Scheme

namespace AAT.AG
namespace LawAlgebra

universe u v w x

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

/-! ### The canonical section-ring route to affine scheme charts -/

/-- The ringed AAT site obtained from the selected raw restriction system. -/
noncomputable def RawAmbientRestrictionSystem.toRingedSite
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    RingedAATSite S k :=
  RingedAATSite.ofMathlibSheafification raw.toPresheaf

/-- The section ring of the canonical sheafification on a selected context. -/
noncomputable abbrev SheafifiedSectionRing
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) : CommRingCat :=
  (raw.toRingedSite.structureSheaf.val.obj (op W)).right

/-- The coefficient map induced by the structure map of the sheafified Under-object. -/
noncomputable def sheafifiedSectionAlgebraMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    k →+* SheafifiedSectionRing raw W :=
  (raw.toRingedSite.structureSheaf.val.obj (op W)).hom.hom.comp
    ULift.ringEquiv.symm.toRingHom

namespace SheafifiedSectionRing

/-- The canonical `k`-algebra structure on a sheafified section ring. -/
noncomputable instance instAlgebra
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    Algebra k (SheafifiedSectionRing raw W) :=
  (sheafifiedSectionAlgebraMap raw W).toAlgebra

end SheafifiedSectionRing

/-- Restriction of sheafified sections along a selected context morphism. -/
noncomputable def sheafifiedRestriction
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    SheafifiedSectionRing raw V ⟶ SheafifiedSectionRing raw W :=
  (raw.toRingedSite.structureSheaf.val.map f.op).right

/-- Restriction as a morphism of the canonical `k`-algebra structures. -/
noncomputable def sheafifiedRestrictionAlgHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    SheafifiedSectionRing raw V →ₐ[k] SheafifiedSectionRing raw W where
  __ := (sheafifiedRestriction raw f).hom
  commutes' a := by
    change
      (raw.toRingedSite.structureSheaf.val.map f.op).right
          ((raw.toRingedSite.structureSheaf.val.obj (op V)).hom
            (ULift.up a)) =
        (raw.toRingedSite.structureSheaf.val.obj (op W)).hom (ULift.up a)
    simpa only [Functor.const_obj_obj, Functor.id_obj, CommRingCat.comp_apply] using
      congrArg (fun q => q.hom (ULift.up a))
        (raw.toRingedSite.structureSheaf.val.map f.op).w.symm

/-- The canonical sheafification unit as a morphism of `k`-algebras. -/
noncomputable def sheafificationUnitAlgHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    raw.rawAlgebra W →ₐ[k] SheafifiedSectionRing raw W where
  __ := (raw.toRingedSite.canonical.app (op W)).right.hom
  commutes' a := by
    change
      (raw.toRingedSite.canonical.app (op W)).right
          ((raw.toPresheaf.obj (op W)).hom (ULift.up a)) =
        (raw.toRingedSite.structureSheaf.val.obj (op W)).hom (ULift.up a)
    simpa only [Functor.const_obj_obj, Functor.id_obj, CommRingCat.comp_apply] using
      congrArg (fun q => q.hom (ULift.up a))
        (raw.toRingedSite.canonical.app (op W)).w.symm

/-- The affine chart attached to the sheafified section ring of a context. -/
noncomputable abbrev architectureChartSpec
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Scheme.Spec.obj
    (op (SheafifiedSectionRing raw W))

/-- The affine Scheme transition induced by sheafified restriction. -/
noncomputable def architectureChartRestriction
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    architectureChartSpec raw W ⟶ architectureChartSpec raw V :=
  AlgebraicGeometry.Scheme.Spec.map (sheafifiedRestriction raw f).op

@[simp] theorem RawAmbientRestrictionSystem.toRingedSite_raw
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    (raw.toRingedSite).raw = raw.toPresheaf :=
  rfl

theorem SheafifiedSectionRing_eq_structureSheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    SheafifiedSectionRing raw W =
      (raw.toRingedSite.structureSheaf.val.obj (op W)).right :=
  rfl

@[simp] theorem SheafifiedSectionRing_algebraMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    algebraMap k (SheafifiedSectionRing raw W) =
      sheafifiedSectionAlgebraMap raw W :=
  rfl

theorem sheafifiedRestriction_eq_structureSheafMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    sheafifiedRestriction raw f =
      (raw.toRingedSite.structureSheaf.val.map f.op).right :=
  rfl

theorem sheafifiedRestrictionAlgHom_toRingHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    (sheafifiedRestrictionAlgHom raw f).toRingHom =
      (sheafifiedRestriction raw f).hom :=
  rfl

theorem sheafificationUnitAlgHom_toRingHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (sheafificationUnitAlgHom raw W).toRingHom =
      (raw.toRingedSite.canonical.app (op W)).right.hom :=
  rfl

theorem architectureChartSpec_eq_Spec
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    architectureChartSpec raw W =
      AlgebraicGeometry.Scheme.Spec.obj
        (op (SheafifiedSectionRing raw W)) :=
  rfl

theorem architectureChartRestriction_eq_SpecMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    architectureChartRestriction raw f =
      AlgebraicGeometry.Scheme.Spec.map
        (sheafifiedRestriction raw f).op :=
  rfl

@[simp] theorem sheafifiedRestriction_id
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    sheafifiedRestriction raw (𝟙 W) = 𝟙 (SheafifiedSectionRing raw W) := by
  change
    (raw.toRingedSite.structureSheaf.val.map (𝟙 (op W))).right =
      (𝟙 (raw.toRingedSite.structureSheaf.val.obj (op W)) :
        raw.toRingedSite.structureSheaf.val.obj (op W) ⟶
          raw.toRingedSite.structureSheaf.val.obj (op W)).right
  exact congrArg (fun q => q.right)
    (raw.toRingedSite.structureSheaf.val.map_id (op W))

@[simp] theorem sheafifiedRestriction_comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V Z : S.category} (f : W ⟶ V) (g : V ⟶ Z) :
    sheafifiedRestriction raw (f ≫ g) =
      sheafifiedRestriction raw g ≫ sheafifiedRestriction raw f := by
  simp [sheafifiedRestriction]

@[simp] theorem architectureChartRestriction_id
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    architectureChartRestriction raw (𝟙 W) = 𝟙 (architectureChartSpec raw W) := by
  simp [architectureChartRestriction]

@[simp] theorem architectureChartRestriction_comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V Z : S.category} (f : W ⟶ V) (g : V ⟶ Z) :
    architectureChartRestriction raw (f ≫ g) =
      architectureChartRestriction raw f ≫ architectureChartRestriction raw g := by
  simp [architectureChartRestriction]

/-- The selected-context functor of affine Scheme charts. -/
noncomputable def architectureChartFunctor
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    S.category ⥤ AlgebraicGeometry.Scheme where
  obj W := architectureChartSpec raw W
  map f := architectureChartRestriction raw f
  map_id W := architectureChartRestriction_id raw W
  map_comp f g := architectureChartRestriction_comp raw f g

@[simp] theorem architectureChartFunctor_obj
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (architectureChartFunctor raw).obj W = architectureChartSpec raw W :=
  rfl

@[simp] theorem architectureChartFunctor_map
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    (architectureChartFunctor raw).map f =
      architectureChartRestriction raw f :=
  rfl

/-- A context isomorphism induces the corresponding affine Scheme isomorphism. -/
noncomputable def architectureChartIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (e : W ≅ V) :
    architectureChartSpec raw W ≅ architectureChartSpec raw V :=
  (architectureChartFunctor raw).mapIso e

@[simp] theorem architectureChartIso_hom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (e : W ≅ V) :
    (architectureChartIso raw e).hom =
      architectureChartRestriction raw e.hom :=
  rfl

@[simp] theorem architectureChartIso_inv
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (e : W ≅ V) :
    (architectureChartIso raw e).inv =
      architectureChartRestriction raw e.inv :=
  rfl

theorem architectureChartRestriction_appTop
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    (architectureChartRestriction raw f).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw W)).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw V)).hom ≫
        sheafifiedRestriction raw f := by
  exact AlgebraicGeometry.Scheme.ΓSpecIso_naturality
    (sheafifiedRestriction raw f)

end
end LawAlgebra
end AAT.AG
