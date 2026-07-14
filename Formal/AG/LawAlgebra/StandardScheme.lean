import Formal.AG.LawAlgebra.StructureSheaf
import Mathlib.AlgebraicGeometry.Scheme

namespace AAT.AG
namespace LawAlgebra

universe u v w x

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

/-!
### The canonical section-ring route to affine scheme charts

This module keeps every chart on the single sheafification selected by `raw`.
Section rings are the right objects of the resulting Under-valued structure
sheaf, and the `k`-algebra maps are obtained by composing their structure maps
with the canonical equivalence from `k` to `ULift k`.  Restrictions and the
sheafification unit retain the underlying maps of the actual Under-morphisms,
so their algebra compatibility is discharged by `Under.w` rather than by a
separately supplied equation.

Affine charts use Mathlib `Scheme.Spec` directly.  Consequently transition
functoriality comes from the structure-sheaf functor and `Spec`, while the
global-section comparison is Mathlib's `Scheme.ΓSpecIso_naturality`.  This
choice rules out storing independently selected rings, restrictions, affine
objects, or compatibility witnesses in the standard chart route.
-/

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

/-- The selected ringed site retains exactly the raw algebra presheaf. -/
@[simp] theorem RawAmbientRestrictionSystem.toRingedSite_raw
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    (raw.toRingedSite).raw = raw.toPresheaf :=
  rfl

/-- A sheafified section ring is the right object of the structure sheaf. -/
theorem SheafifiedSectionRing_eq_structureSheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    SheafifiedSectionRing raw W =
      (raw.toRingedSite.structureSheaf.val.obj (op W)).right :=
  rfl

/-- The section-ring algebra map is the canonical Under-object structure map. -/
@[simp] theorem SheafifiedSectionRing_algebraMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    algebraMap k (SheafifiedSectionRing raw W) =
      sheafifiedSectionAlgebraMap raw W :=
  rfl

/-- Sheafified restriction is the underlying structure-sheaf map. -/
theorem sheafifiedRestriction_eq_structureSheafMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    sheafifiedRestriction raw f =
      (raw.toRingedSite.structureSheaf.val.map f.op).right :=
  rfl

/-- The algebra-hom restriction retains the canonical underlying ring hom. -/
theorem sheafifiedRestrictionAlgHom_toRingHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (f : W ⟶ V) :
    (sheafifiedRestrictionAlgHom raw f).toRingHom =
      (sheafifiedRestriction raw f).hom :=
  rfl

/-- The algebra-hom unit retains the canonical sheafification component. -/
theorem sheafificationUnitAlgHom_toRingHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (sheafificationUnitAlgHom raw W).toRingHom =
      (raw.toRingedSite.canonical.app (op W)).right.hom :=
  rfl

/-- An architecture chart is definitionally the Mathlib spectrum of its section ring. -/
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

/-- A chart transition is the spectrum map of the same sheafified restriction. -/
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

/-- Restriction along an identity context morphism is the identity ring morphism. -/
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

/-- Sheafified restrictions compose contravariantly with context morphisms. -/
@[simp] theorem sheafifiedRestriction_comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V Z : S.category} (f : W ⟶ V) (g : V ⟶ Z) :
    sheafifiedRestriction raw (f ≫ g) =
      sheafifiedRestriction raw g ≫ sheafifiedRestriction raw f := by
  simp [sheafifiedRestriction]

/-- The chart transition attached to an identity is the identity Scheme morphism. -/
@[simp] theorem architectureChartRestriction_id
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    architectureChartRestriction raw (𝟙 W) = 𝟙 (architectureChartSpec raw W) := by
  simp [architectureChartRestriction]

/-- Architecture chart transitions compose covariantly in the context category. -/
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

/-- The chart functor sends a context to its canonical affine chart. -/
@[simp] theorem architectureChartFunctor_obj
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (architectureChartFunctor raw).obj W = architectureChartSpec raw W :=
  rfl

/-- The chart functor sends a context morphism to its canonical transition. -/
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

/-- The forward map of a chart isomorphism is the induced chart transition. -/
@[simp] theorem architectureChartIso_hom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (e : W ≅ V) :
    (architectureChartIso raw e).hom =
      architectureChartRestriction raw e.hom :=
  rfl

/-- The inverse map of a chart isomorphism is the transition along the inverse context map. -/
@[simp] theorem architectureChartIso_inv
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W V : S.category} (e : W ≅ V) :
    (architectureChartIso raw e).inv =
      architectureChartRestriction raw e.inv :=
  rfl

/-- Global sections of a chart transition recover the originating restriction via `ΓSpecIso`. -/
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

/-!
### Global reading decoration

A reading decoration records only the selected context and the actual map from
its canonical sheafified section ring to global sections.  Coordinate data,
law-universe provenance, and the architecture signature remain projections of
the same `raw` and `S`; they are not stored again.  Pullback and preservation
use `Scheme.Hom.appTop`, so no independent open-wise reading or compatibility
slot is introduced here.  Law-generated ideals are constructed by the later
closed-equational layer rather than being provisional fields of this structure.
-/

/-- The global reading component on a Scheme. -/
structure AATReadingDecoration
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : AlgebraicGeometry.Scheme) where
  /-- The selected context from which the global reading is interpreted. -/
  context : S.category
  /-- The actual ring map from canonical sections to Scheme global sections. -/
  interpretation :
    SheafifiedSectionRing raw context ⟶ Γ(X, ⊤)

namespace AATReadingDecoration

/-- The typed coordinates of a decoration's selected context. -/
def coordinateFamily
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    CoordinateFamily D.context.ctx :=
  raw.coordFamily D.context

/-- The selected law universe read from the ambient AAT site. -/
def lawUniverse
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (_D : AATReadingDecoration raw X) : LawUniverse U :=
  S.lawUniverse

/-- The architecture signature read from the ambient AAT site. -/
def signature
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (_D : AATReadingDecoration raw X) : ArchitectureSignature U :=
  S.signature

/-- The coefficient reading obtained from the canonical section-algebra map. -/
noncomputable def coefficientMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    k →+* Γ(X, ⊤) :=
  D.interpretation.hom.comp
    (sheafifiedSectionAlgebraMap raw D.context)

/-- The global section represented by a selected typed coordinate. -/
noncomputable def coordinateSection
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X)
    (c : D.coordinateFamily raw |>.CoordX) : Γ(X, ⊤) :=
  D.interpretation
    ((raw.toRingedSite.canonical.app (op D.context)).right
      ((raw.relationFamily D.context).quotientMap (MvPolynomial.X c)))

/-- Pull a reading decoration back along a Scheme morphism using global sections. -/
noncomputable def pullback
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    AATReadingDecoration raw X where
  context := D.context
  interpretation := D.interpretation ≫ f.appTop

/-- Actual preservation of a reading along a Scheme morphism. -/
def Preserves
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y : AlgebraicGeometry.Scheme}
    (D_X : AATReadingDecoration raw X) (f : X ⟶ Y)
    (D_Y : AATReadingDecoration raw Y) : Prop :=
  ∃ h : D_X.context ⟶ D_Y.context,
    sheafifiedRestriction raw h ≫ D_X.interpretation =
      D_Y.interpretation ≫ f.appTop

/-- Decorations agree when their context and interpretation agree. -/
@[ext] theorem ext
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D E : AATReadingDecoration raw X)
    (hcontext : D.context = E.context)
    (hinterpretation : HEq D.interpretation E.interpretation) : D = E := by
  cases D
  cases E
  cases hcontext
  cases hinterpretation
  rfl

/-- The coordinate-family projection is the selected raw coordinate family. -/
@[simp] theorem coordinateFamily_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.coordinateFamily raw = raw.coordFamily D.context :=
  rfl

/-- The law-universe projection is the selected site's law universe. -/
@[simp] theorem lawUniverse_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.lawUniverse raw = S.lawUniverse :=
  rfl

/-- The signature projection is the selected site's architecture signature. -/
@[simp] theorem signature_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.signature raw = S.signature :=
  rfl

/-- The coefficient map is the canonical section-algebra map followed by interpretation. -/
@[simp] theorem coefficientMap_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.coefficientMap raw =
      D.interpretation.hom.comp
        (sheafifiedSectionAlgebraMap raw D.context) :=
  rfl

/-- Coordinate sections expose the variable, quotient, unit, and interpretation route. -/
@[simp] theorem coordinateSection_apply
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X)
    (c : D.coordinateFamily raw |>.CoordX) :
    D.coordinateSection raw c =
      D.interpretation
        ((raw.toRingedSite.canonical.app (op D.context)).right
          ((raw.relationFamily D.context).quotientMap (MvPolynomial.X c))) :=
  rfl

/-- Pullback retains the selected context. -/
@[simp] theorem pullback_context
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    (D.pullback raw f).context = D.context :=
  rfl

/-- Pullback interpretation is composition with the Scheme map on global sections. -/
@[simp] theorem pullback_interpretation
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    (D.pullback raw f).interpretation = D.interpretation ≫ f.appTop :=
  rfl

/-- Pullback transports coefficient readings by the map on global sections. -/
@[simp] theorem pullback_coefficientMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    (D.pullback raw f).coefficientMap raw =
      f.appTop.hom.comp (D.coefficientMap raw) := by
  rfl

/-- Pullback along an identity Scheme morphism fixes a decoration. -/
@[simp] theorem pullback_id
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.pullback raw (𝟙 X) = D := by
  apply AATReadingDecoration.ext raw
  · rfl
  · simp [pullback]

/-- Pullback respects composition of Scheme morphisms. -/
@[simp] theorem pullback_comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y Z : AlgebraicGeometry.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (D : AATReadingDecoration raw Z) :
    D.pullback raw (f ≫ g) =
      (D.pullback raw g).pullback raw f := by
  apply AATReadingDecoration.ext raw
  · rfl
  · simp [pullback, Category.assoc]

/-- Coordinate sections pull back through the Scheme map on global sections. -/
@[simp] theorem coordinateSection_pullback
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y)
    (c : D.coordinateFamily raw |>.CoordX) :
    (D.pullback raw f).coordinateSection raw c =
      f.appTop (D.coordinateSection raw c) :=
  rfl

/-- Every reading decoration is preserved by the identity Scheme morphism. -/
theorem preserves_id
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.Preserves raw (𝟙 X) D := by
  refine ⟨𝟙 D.context, ?_⟩
  simp

/-- Preservation composes along context and Scheme morphisms. -/
theorem preserves_comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y Z : AlgebraicGeometry.Scheme}
    {D_X : AATReadingDecoration raw X}
    {D_Y : AATReadingDecoration raw Y}
    {D_Z : AATReadingDecoration raw Z}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : D_X.Preserves raw f D_Y)
    (hg : D_Y.Preserves raw g D_Z) :
    D_X.Preserves raw (f ≫ g) D_Z := by
  rcases hf with ⟨hXY, hf⟩
  rcases hg with ⟨hYZ, hg⟩
  refine ⟨hXY ≫ hYZ, ?_⟩
  rw [sheafifiedRestriction_comp, Category.assoc, hf]
  rw [← Category.assoc, hg, Category.assoc, AlgebraicGeometry.Scheme.Hom.comp_appTop]

/-- Preservation forces the same reading of coefficients on source and target. -/
theorem Preserves.coefficientMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y : AlgebraicGeometry.Scheme}
    {D_X : AATReadingDecoration raw X}
    {D_Y : AATReadingDecoration raw Y}
    {f : X ⟶ Y}
    (hf : D_X.Preserves raw f D_Y) :
    D_X.coefficientMap raw =
      f.appTop.hom.comp (D_Y.coefficientMap raw) := by
  rcases hf with ⟨h, hf⟩
  ext a
  have hcoeff :
      sheafifiedRestriction raw h
          ((sheafifiedSectionAlgebraMap raw D_Y.context) a) =
        (sheafifiedSectionAlgebraMap raw D_X.context) a := by
    change
      (sheafifiedRestrictionAlgHom raw h)
          (algebraMap k (SheafifiedSectionRing raw D_Y.context) a) =
        algebraMap k (SheafifiedSectionRing raw D_X.context) a
    exact (sheafifiedRestrictionAlgHom raw h).commutes a
  change
    D_X.interpretation
        ((sheafifiedSectionAlgebraMap raw D_X.context) a) =
      f.appTop
        (D_Y.interpretation
          ((sheafifiedSectionAlgebraMap raw D_Y.context) a))
  rw [← hcoeff]
  exact congrArg
    (fun q => q ((sheafifiedSectionAlgebraMap raw D_Y.context) a)) hf

/-- The canonical reading decoration of a selected affine chart. -/
noncomputable def ofContext
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    AATReadingDecoration raw (architectureChartSpec raw W) where
  context := W
  interpretation :=
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing raw W)).inv

/-- The canonical affine reading uses the selected context. -/
@[simp] theorem ofContext_context
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (AATReadingDecoration.ofContext raw W).context = W :=
  rfl

/-- The canonical affine interpretation is the inverse global-section isomorphism. -/
@[simp] theorem ofContext_interpretation
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (AATReadingDecoration.ofContext raw W).interpretation =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing raw W)).inv :=
  rfl

end AATReadingDecoration

end
end LawAlgebra
end AAT.AG
