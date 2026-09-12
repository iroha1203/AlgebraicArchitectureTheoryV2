import ResearchLean.AG.GeometryTransport.Categories
import ResearchLean.AG.RealizationComparisonIdempotents.NormalizationCategory

/-!
# Canonical normalization of a complete geometry

This module begins G-122(A) by lifting the reviewed canonical normalization of
the underlying AAT core package to the complete geometry category.

## Implementation notes

The normalization changes only the selected architecture object.  Its Atom,
equation, context, coefficient, and local realization indices are identities.
Consequently the geometry comparison data are the identity comparisons; the
nontrivial object-normalization laws come from
`CanonicalObjectNormalizationAdmissible` through the existing core morphism.
-/

open CategoryTheory
open CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

open AtomFoundation
open GeometryTransport
open DoctrineFiberProduct
open RealizationComparisonIdempotents

universe u v

/-- Compare dependent geometry homs after a separately proved equality of
their core indices. -/
private theorem geometryReadHom_heq_of_base_eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {f g : PackageTotalHom G.core H.core}
    (F : GeomReadHom G H f) (T : GeomReadHom G H g)
    (hbase : f = g)
    (hcoefficient : F.coefficientHom = T.coefficientHom)
    (hsupport : HEq F.supportComp T.supportComp)
    (haxis : HEq F.axisComp T.axisComp)
    (hobservable : HEq F.observableComp T.observableComp) : HEq F T := by
  cases hbase
  exact heq_of_eq (GeomReadHom.ext hcoefficient hsupport haxis hobservable)

/-- G-122(A): the geometry data carried by canonical object normalization.

The admissibility premise is the named direction hypothesis in the fixed
G-122 target.  All geometry fields are constructed here from identity index
maps; no completed geometry morphism is accepted as input.
-/
noncomputable def canonicalGeometryNormalizationReadHom
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    GeomReadHom G G (canonicalObjectNormalizationTotal G.core admissible) where
  coverage := by
    constructor <;> intros <;> assumption
  overlap := by
    constructor
    intro base left right
    exact Iso.refl _
  coefficientHom := RingHom.id G.Coefficient
  raw_eq := by
    unfold rawTransport
    rw [LawAlgebra.RawAmbientRestrictionSystem.baseChange_id]
    apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- G-122(A): canonical object normalization as a complete geometry
endomorphism. -/
noncomputable def canonicalGeometryNormalization
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) : G ⟶ G where
  base := canonicalObjectNormalizationTotal G.core admissible
  geometry := canonicalGeometryNormalizationReadHom G admissible

/-- Normalization rule: the core component is the existing canonical object
normalization. -/
@[simp]
theorem canonicalGeometryNormalization_base
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    (canonicalGeometryNormalization G admissible).base =
      canonicalObjectNormalizationTotal G.core admissible :=
  rfl

/-- Normalization rule: canonical geometry normalization fixes the coefficient
ring. -/
@[simp]
theorem canonicalGeometryNormalization_coefficientHom
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    (canonicalGeometryNormalization G admissible).geometry.coefficientHom =
      RingHom.id G.Coefficient :=
  rfl

/-- Normalization rule: local Support realizations are retained identically. -/
@[simp]
theorem canonicalGeometryNormalization_supportComp
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (W : G.site.category) (support : W.ctx.Support) :
    (canonicalGeometryNormalization G admissible).geometry.supportComp W support =
      support :=
  rfl

/-- Normalization rule: local Axis realizations are retained identically. -/
@[simp]
theorem canonicalGeometryNormalization_axisComp
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (W : G.site.category) (axis : W.ctx.Axis) :
    (canonicalGeometryNormalization G admissible).geometry.axisComp W axis = axis :=
  rfl

/-- Normalization rule: local Observable realizations are retained
identically. -/
@[simp]
theorem canonicalGeometryNormalization_observableComp
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (W : G.site.category) (observable : W.ctx.Observable) :
    (canonicalGeometryNormalization G admissible).geometry.observableComp W observable =
      observable :=
  rfl

/-- G-122(A): the lifted normalization is idempotent as an equality of complete
geometry morphisms, not merely after forgetting to the core. -/
theorem canonicalGeometryNormalization_idem
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    canonicalGeometryNormalization G admissible ≫
        canonicalGeometryNormalization G admissible =
      canonicalGeometryNormalization G admissible := by
  have hbase :
      (canonicalGeometryNormalization G admissible ≫
          canonicalGeometryNormalization G admissible).base =
        (canonicalGeometryNormalization G admissible).base :=
    canonicalObjectNormalizationTotal_comp G.core admissible
  apply GeometryTotalHom.ext hbase
  apply geometryReadHom_heq_of_base_eq _ _ hbase <;> rfl

/-- G-122(A): forgetting complete geometry recovers the reviewed G-116 core
normalization exactly. -/
@[simp]
theorem geometryProjection_canonicalGeometryNormalization
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    (geometryProjection U).map (canonicalGeometryNormalization G admissible) =
      canonicalObjectNormalizationTotal G.core admissible :=
  rfl

/-- G-122(A): the composite projection to the pointed doctrine is the
identity. -/
@[simp]
theorem packageProjection_geometryProjection_canonicalGeometryNormalization
    {U : AtomCarrier.{u}} (G : GeomReadCategory.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    (packageProjection U).map
        ((geometryProjection U).map
          (canonicalGeometryNormalization G admissible)) =
      𝟙 (packagePoint G.core) :=
  rfl

/-! ## The admissible complete-geometry category -/

/-- Admissibility of a complete geometry is exactly admissibility of its
underlying core package. -/
abbrev canonicalGeometryNormalizationAdmissibleProperty
    (U : AtomCarrier.{u}) : ObjectProperty (GeomReadCategory.{u, v} U) :=
  fun G => CanonicalObjectNormalizationAdmissible G.core

/-- G-122(A)'s full subcategory `C_geom` of complete geometries with
admissible cores. -/
abbrev CanonicalNormalizationAdmissibleGeometry
    (U : AtomCarrier.{u}) :=
  (canonicalGeometryNormalizationAdmissibleProperty.{u, v} U).FullSubcategory

/-- The complete normalization endomorphism inside `C_geom`. -/
noncomputable def canonicalAdmissibleGeometryNormalization
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) : G ⟶ G :=
  ObjectProperty.homMk (canonicalGeometryNormalization G.obj G.property)

/-- Normalization rule: the admissible-subcategory morphism retains the
complete normalization constructed above. -/
@[simp]
theorem canonicalAdmissibleGeometryNormalization_hom
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    (canonicalAdmissibleGeometryNormalization G).hom =
      canonicalGeometryNormalization G.obj G.property :=
  rfl

/-- G-122(A)'s one-sided absorption law in complete geometry.  In the target's
ordinary composition notation this is `n_H f n_G = f n_G`. -/
theorem canonicalAdmissibleGeometryNormalization_absorption
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (f : G ⟶ H) :
    canonicalAdmissibleGeometryNormalization G ≫ f ≫
        canonicalAdmissibleGeometryNormalization H =
      canonicalAdmissibleGeometryNormalization G ≫ f := by
  let Gcore : CanonicalNormalizationAdmissiblePackage U :=
    ⟨G.obj.core, G.property⟩
  let Hcore : CanonicalNormalizationAdmissiblePackage U :=
    ⟨H.obj.core, H.property⟩
  let fcore : Gcore ⟶ Hcore := ObjectProperty.homMk f.hom.base
  have hcore := canonicalPackageNormalization_absorption fcore
  have hbase :
      (canonicalAdmissibleGeometryNormalization G ≫ f ≫
          canonicalAdmissibleGeometryNormalization H).hom.base =
        (canonicalAdmissibleGeometryNormalization G ≫ f).hom.base := by
    exact congrArg (fun h => h.hom) hcore
  apply ObjectProperty.hom_ext
  apply GeometryTotalHom.ext hbase
  apply geometryReadHom_heq_of_base_eq _ _ hbase <;> rfl

/-- The normalization endomorphism remains idempotent inside the admissible
full subcategory. -/
theorem canonicalAdmissibleGeometryNormalization_idem
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    canonicalAdmissibleGeometryNormalization G ≫
        canonicalAdmissibleGeometryNormalization G =
      canonicalAdmissibleGeometryNormalization G := by
  apply ObjectProperty.hom_ext
  exact canonicalGeometryNormalization_idem G.obj G.property

/-! ## The normalized complete-geometry category and functor -/

/-- An object of the normalized complete-geometry category retains its
admissible geometry as a label. -/
structure NormalizedGeometryObject (U : AtomCarrier.{u}) where
  /-- The underlying admissible complete geometry. -/
  obj : CanonicalNormalizationAdmissibleGeometry.{u, v} U

@[ext]
theorem normalizedGeometryObject_ext
    {U : AtomCarrier.{u}} {G H : NormalizedGeometryObject.{u, v} U}
    (h : G.obj = H.obj) : G = H := by
  cases G
  cases H
  cases h
  rfl

/-- The Karoubi object `(G,n_G)` associated with an admissible complete
geometry. -/
noncomputable def normalizedGeometryKaroubiObject
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    Karoubi (CanonicalNormalizationAdmissibleGeometry.{u, v} U) where
  X := G
  p := canonicalAdmissibleGeometryNormalization G
  idem := canonicalAdmissibleGeometryNormalization_idem G

/-- G-122(A)'s category whose arrows are all complete-geometry sandwich
morphisms. -/
noncomputable instance normalizedGeometryCategory (U : AtomCarrier.{u}) :
    Category (NormalizedGeometryObject.{u, v} U) where
  Hom G H := normalizedGeometryKaroubiObject G.obj ⟶
    normalizedGeometryKaroubiObject H.obj
  id G := 𝟙 (normalizedGeometryKaroubiObject G.obj)
  comp f g := f ≫ g
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

/-- Normalization rule: the identity of a labelled normalized geometry is its
canonical idempotent. -/
@[simp]
theorem normalizedGeometryCategory_id_f
    {U : AtomCarrier.{u}} (G : NormalizedGeometryObject.{u, v} U) :
    (𝟙 G : G ⟶ G).f = canonicalAdmissibleGeometryNormalization G.obj :=
  rfl

/-- Normalization rule: normalized-geometry composition retains the composite
of the underlying sandwich arrows. -/
@[simp]
theorem normalizedGeometryCategory_comp_f
    {U : AtomCarrier.{u}}
    {G H K : NormalizedGeometryObject.{u, v} U}
    (f : G ⟶ H) (g : H ⟶ K) : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/-- Every normalized complete-geometry arrow is exactly a two-endpoint
sandwich arrow. -/
theorem normalizedGeometryHom_sandwich
    {U : AtomCarrier.{u}}
    {G H : NormalizedGeometryObject.{u, v} U} (f : G ⟶ H) :
    canonicalAdmissibleGeometryNormalization G.obj ≫ f.f ≫
        canonicalAdmissibleGeometryNormalization H.obj = f.f :=
  f.comm

/-- The identity-on-sandwich-arrows embedding into the Karoubi completion. -/
noncomputable def normalizedGeometryKaroubiFunctor (U : AtomCarrier.{u}) :
    NormalizedGeometryObject.{u, v} U ⥤
      Karoubi (CanonicalNormalizationAdmissibleGeometry.{u, v} U) where
  obj G := normalizedGeometryKaroubiObject G.obj
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The Karoubi comparison is faithful because it retains every sandwich
arrow. -/
instance normalizedGeometryKaroubiFunctor_faithful (U : AtomCarrier.{u}) :
    (normalizedGeometryKaroubiFunctor.{u, v} U).Faithful where
  map_injective h := h

/-- The Karoubi comparison is full because its source Hom is the same
sandwich Hom. -/
instance normalizedGeometryKaroubiFunctor_full (U : AtomCarrier.{u}) :
    (normalizedGeometryKaroubiFunctor.{u, v} U).Full where
  map_surjective f := ⟨f, rfl⟩

/-- G-122(A)'s canonical normalization functor `N_geom`.  It preserves the
geometry label and maps `f` to `f n_G` in ordinary composition notation. -/
noncomputable def geometryNormalizationFunctor (U : AtomCarrier.{u}) :
    CanonicalNormalizationAdmissibleGeometry.{u, v} U ⥤
      NormalizedGeometryObject.{u, v} U where
  obj G := ⟨G⟩
  map := fun {G _} f =>
    { f := canonicalAdmissibleGeometryNormalization G ≫ f
      comm := by
        change canonicalAdmissibleGeometryNormalization G ≫
            (canonicalAdmissibleGeometryNormalization G ≫ f) ≫
              canonicalAdmissibleGeometryNormalization _ =
          canonicalAdmissibleGeometryNormalization G ≫ f
        rw [← Category.assoc]
        rw [← Category.assoc
          (canonicalAdmissibleGeometryNormalization G)
          (canonicalAdmissibleGeometryNormalization G) f,
          canonicalAdmissibleGeometryNormalization_idem]
        exact canonicalAdmissibleGeometryNormalization_absorption f }
  map_id G := by
    apply Karoubi.Hom.ext
    exact Category.comp_id _
  map_comp f g := by
    apply Karoubi.Hom.ext
    change canonicalAdmissibleGeometryNormalization _ ≫ (f ≫ g) =
      (canonicalAdmissibleGeometryNormalization _ ≫ f) ≫
        (canonicalAdmissibleGeometryNormalization _ ≫ g)
    simpa only [Category.assoc] using congrArg
      (fun h => h ≫ g)
      (canonicalAdmissibleGeometryNormalization_absorption f).symm

/-- Normalization rule: `N_geom` preserves the complete-geometry label. -/
@[simp]
theorem geometryNormalizationFunctor_obj_obj
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    ((geometryNormalizationFunctor.{u, v} U).obj G).obj = G :=
  rfl

/-- Normalization rule: the underlying arrow of `N_geom(f)` is source
normalization followed by `f`. -/
@[simp]
theorem geometryNormalizationFunctor_map_f
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (f : G ⟶ H) :
    ((geometryNormalizationFunctor.{u, v} U).map f).f =
      canonicalAdmissibleGeometryNormalization G ≫ f :=
  rfl

/-- G-122(A): every sandwich arrow has its own underlying complete-geometry
arrow as a preimage, so `N_geom` is full. -/
instance geometryNormalizationFunctor_full (U : AtomCarrier.{u}) :
    (geometryNormalizationFunctor.{u, v} U).Full where
  map_surjective f := by
    refine ⟨f.f, ?_⟩
    apply Karoubi.Hom.ext
    exact Karoubi.p_comp f

/-- Normalization preserves the complete coefficient morphism of every input
arrow. -/
@[simp]
theorem geometryNormalizationFunctor_map_coefficientHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (f : G ⟶ H) :
    (((geometryNormalizationFunctor.{u, v} U).map f).f.hom.geometry.coefficientHom) =
      f.hom.geometry.coefficientHom :=
  rfl

/-- Normalization also preserves the pointed-doctrine morphism carried by an
input arrow. -/
@[simp]
theorem geometryNormalizationFunctor_map_packageBase
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (f : G ⟶ H) :
    (((geometryNormalizationFunctor.{u, v} U).map f).f.hom.base).base =
      f.hom.base.base :=
  rfl

/-! ## Compatibility with the accepted core normalization -/

/-- Forget complete geometry while retaining the inherited core
admissibility. -/
noncomputable def admissibleGeometryCoreFunctor (U : AtomCarrier.{u}) :
    CanonicalNormalizationAdmissibleGeometry.{u, v} U ⥤
      CanonicalNormalizationAdmissiblePackage U where
  obj G := ⟨G.obj.core, G.property⟩
  map f := ObjectProperty.homMk f.hom.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forget normalized complete geometry to G-119's normalized core-package
category. -/
noncomputable def normalizedGeometryCoreFunctor (U : AtomCarrier.{u}) :
    NormalizedGeometryObject.{u, v} U ⥤ NormalizedPackageObject U where
  obj G := ⟨(admissibleGeometryCoreFunctor.{u, v} U).obj G.obj⟩
  map f :=
    { f := (admissibleGeometryCoreFunctor.{u, v} U).map f.f
      comm := by
        apply ObjectProperty.hom_ext
        exact congrArg (fun h => h.hom.base) f.comm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- G-122(A): the object part of complete normalization agrees exactly with
G-119's core normalization after forgetting geometry. -/
@[simp]
theorem normalizedGeometryCoreFunctor_geometryNormalizationFunctor_obj
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    (normalizedGeometryCoreFunctor.{u, v} U).obj
        ((geometryNormalizationFunctor.{u, v} U).obj G) =
      (packageNormalizationFunctor U).obj
        ((admissibleGeometryCoreFunctor.{u, v} U).obj G) :=
  rfl

/-- G-122(A): the arrow part of complete normalization commutes with G-119's
core normalization, including the complete underlying package morphism. -/
@[simp]
theorem normalizedGeometryCoreFunctor_geometryNormalizationFunctor_map
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (f : G ⟶ H) :
    (normalizedGeometryCoreFunctor.{u, v} U).map
        ((geometryNormalizationFunctor.{u, v} U).map f) =
      (packageNormalizationFunctor U).map
        ((admissibleGeometryCoreFunctor.{u, v} U).map f) :=
  rfl

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
