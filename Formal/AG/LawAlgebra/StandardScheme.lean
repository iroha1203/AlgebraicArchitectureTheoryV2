import Formal.AG.LawAlgebra.StructureSheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
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

/--
The architectural equation system read from the ambient AAT site. The
decoration receiver fixes the same `raw` and site for dot notation.
-/
def equationSystem
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (_D : AATReadingDecoration raw X) :
    ArchitecturalEquationSystem S.contextPreorder :=
  S.equationSystem

/--
The architecture signature read from the ambient AAT site.  The decoration receiver fixes the
same `raw` and site for dot notation; the returned signature is intentionally site-level data.
-/
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

/-- The equation-system projection is the selected site's equation system. -/
@[simp] theorem equationSystem_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.equationSystem raw = S.equationSystem :=
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

/-!
### Actual affine charts

An architecture affine chart stores only a selected context, its actual morphism into the
decoration context, and the Scheme map from the canonical Spec of the selected sheafified
section ring.  Chart validity remains a separate proposition consisting of Mathlib open
immersion data and the actual interpretation equation.
-/

/-- A selected affine chart whose domain is the canonical Spec of a sheafified section ring. -/
structure ArchitectureAffineChart
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X) where
  /-- The local context selecting the chart's section ring. -/
  context : S.category
  /-- The actual context morphism into the decoration's selected context. -/
  contextHom : context ⟶ D.context
  /-- The actual Scheme morphism from the canonical affine domain. -/
  map : architectureChartSpec raw context ⟶ X

/-- Actual validity of a selected architecture affine chart. -/
structure IsArchitectureAffineChart
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) : Prop where
  /-- The actual chart map is an open immersion. -/
  isOpenImmersion : AlgebraicGeometry.IsOpenImmersion C.map
  /-- Context restriction agrees with global interpretation along the chart map. -/
  interpretation_compatible :
    sheafifiedRestriction raw C.contextHom =
      D.interpretation ≫ C.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw C.context)).hom

namespace ArchitectureAffineChart

/-- The chart domain, definitionally the Spec of its canonical sheafified section ring. -/
def domain
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) : AlgebraicGeometry.Scheme :=
  architectureChartSpec raw C.context

/-- The locally ringed space underlying the canonical affine chart domain. -/
def domainLocallyRingedSpace
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) : LocallyRingedSpace :=
  C.domain.toLocallyRingedSpace

/-- Every canonical chart domain is affine. -/
theorem domain_isAffine
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) :
    AlgebraicGeometry.IsAffine C.domain := by
  change AlgebraicGeometry.IsAffine
    (AlgebraicGeometry.Spec (SheafifiedSectionRing raw C.context))
  infer_instance

/-- The chart domain unfolds to the canonical Spec selected by its context. -/
@[simp] theorem domain_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) :
    C.domain = architectureChartSpec raw C.context :=
  rfl

/-- The open image of a valid affine chart. -/
def image
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D)
    (hC : IsArchitectureAffineChart raw C) : X.Opens := by
  letI : AlgebraicGeometry.IsOpenImmersion C.map := hC.isOpenImmersion
  exact C.map.opensRange

/-- The identity chart on a selected context. -/
noncomputable def identity
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    ArchitectureAffineChart raw
      (architectureChartSpec raw W)
      (AATReadingDecoration.ofContext raw W) where
  context := W
  contextHom := 𝟙 W
  map := 𝟙 (architectureChartSpec raw W)

/-- The identity chart retains its selected context. -/
@[simp] theorem identity_context
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (ArchitectureAffineChart.identity raw W).context = W :=
  rfl

/-- The identity chart uses the identity context morphism. -/
@[simp] theorem identity_contextHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (ArchitectureAffineChart.identity raw W).contextHom = 𝟙 W :=
  rfl

/-- The identity chart uses the identity Scheme morphism. -/
@[simp] theorem identity_map
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (ArchitectureAffineChart.identity raw W).map =
      𝟙 (architectureChartSpec raw W) :=
  rfl

/-- The identity chart satisfies actual open-immersion and interpretation compatibility. -/
theorem identity_isArchitectureAffineChart
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    IsArchitectureAffineChart raw (ArchitectureAffineChart.identity raw W) := by
  constructor
  · change AlgebraicGeometry.IsOpenImmersion
      (𝟙 (architectureChartSpec raw W))
    infer_instance
  · simp

/-- A valid chart preserves the canonical local decoration along its actual map. -/
theorem localDecoration_preserves
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D)
    (hC : IsArchitectureAffineChart raw C) :
    (AATReadingDecoration.ofContext raw C.context).Preserves raw C.map D := by
  refine ⟨C.contextHom, ?_⟩
  rw [hC.interpretation_compatible]
  simp

end ArchitectureAffineChart

/-- A selected family of canonical affine charts on a Scheme. -/
structure ArchitectureAffineAtlas
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X) where
  /-- Index type of selected charts. -/
  Index : Type u
  /-- The selected actual affine chart at an index. -/
  chart : Index → ArchitectureAffineChart raw X D

/-- Actual validity and pointwise coverage of an architecture affine atlas. -/
structure IsArchitectureAffineAtlas
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D) : Prop where
  /-- Every selected chart satisfies actual affine-chart validity. -/
  chart_valid : ∀ i, IsArchitectureAffineChart raw (atlas.chart i)
  /-- Every point of the Scheme lies in the image of a selected chart. -/
  covers : ∀ x : X, ∃ i y, (atlas.chart i).map y = x

namespace ArchitectureAffineAtlas

/-- The Mathlib affine open cover induced by a valid architecture affine atlas. -/
noncomputable def toAffineOpenCover
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas) : X.AffineOpenCover where
  I₀ := atlas.Index
  X i := SheafifiedSectionRing raw (atlas.chart i).context
  f i := (atlas.chart i).map
  idx x := (h.covers x).choose
  covers x := by
    change x ∈ Set.range (atlas.chart ((h.covers x).choose)).map
    exact ⟨(h.covers x).choose_spec.choose,
      (h.covers x).choose_spec.choose_spec⟩
  map_prop i := (h.chart_valid i).isOpenImmersion

/-- The component ring of the induced affine open cover is the canonical section ring. -/
@[simp] theorem toAffineOpenCover_X
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas)
    (i : atlas.Index) :
    (atlas.toAffineOpenCover raw h).X i =
      SheafifiedSectionRing raw (atlas.chart i).context :=
  rfl

/-- The component map of the induced affine open cover is the selected chart map. -/
@[simp] theorem toAffineOpenCover_f
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas)
    (i : atlas.Index) :
    (atlas.toAffineOpenCover raw h).f i = (atlas.chart i).map :=
  rfl

/-- The open ranges of a valid architecture affine atlas cover the Scheme. -/
theorem jointlyCovers
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas) :
    ⨆ i, ((atlas.toAffineOpenCover raw h).f i).opensRange = ⊤ := by
  exact (atlas.toAffineOpenCover raw h).openCover.iSup_opensRange

/-- The selected pair-overlap context generated by the site's overlap operation. -/
noncomputable def pairContext
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) : S.category :=
  Site.ContextCategoryObject.of S.contextPreorder
    (S.overlap.overlap D.context.ctx
      (atlas.chart i).context.ctx (atlas.chart j).context.ctx)

/-- The selected pair context maps to its left chart context. -/
noncomputable def pairToLeft
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairContext raw i j ⟶ (atlas.chart i).context :=
  homOfLE (S.overlap.left
    (leOfHom (atlas.chart i).contextHom)
    (leOfHom (atlas.chart j).contextHom))

/-- The selected pair context maps to its right chart context. -/
noncomputable def pairToRight
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairContext raw i j ⟶ (atlas.chart j).context :=
  homOfLE (S.overlap.right
    (leOfHom (atlas.chart i).contextHom)
    (leOfHom (atlas.chart j).contextHom))

/-- The selected pair context maps to the reading's base context. -/
noncomputable def pairToBase
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairContext raw i j ⟶ D.context :=
  homOfLE (S.overlap.base
    (leOfHom (atlas.chart i).contextHom)
    (leOfHom (atlas.chart j).contextHom))

/-- A chart context maps to its selected self-overlap context. -/
noncomputable def selfToPair
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    (atlas.chart i).context ⟶ atlas.pairContext raw i i :=
  homOfLE (S.overlap.lift
    (leOfHom (atlas.chart i).contextHom)
    (leOfHom (atlas.chart i).contextHom)
    (S.contextPreorder.refl _)
    (S.contextPreorder.refl _))

/-- The selected self-overlap context is isomorphic to its chart context. -/
noncomputable def selfPairContextIso
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    atlas.pairContext raw i i ≅ (atlas.chart i).context where
  hom := atlas.pairToLeft raw i i
  inv := atlas.selfToPair raw i
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- The selected triple context generated from two adjacent pair contexts. -/
noncomputable def tripleContext
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) : S.category :=
  Site.ContextCategoryObject.of S.contextPreorder
    (S.overlap.overlap D.context.ctx
      (atlas.pairContext raw i j).ctx
      (atlas.pairContext raw j l).ctx)

/-- The selected triple context maps to the first pair context. -/
noncomputable def tripleToFirstPair
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ atlas.pairContext raw i j :=
  homOfLE (S.overlap.left
    (leOfHom (atlas.pairToBase raw i j))
    (leOfHom (atlas.pairToBase raw j l)))

/-- The selected triple context maps to the second pair context. -/
noncomputable def tripleToSecondPair
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ atlas.pairContext raw j l :=
  homOfLE (S.overlap.right
    (leOfHom (atlas.pairToBase raw i j))
    (leOfHom (atlas.pairToBase raw j l)))

/-- The selected triple context maps to the left chart context. -/
noncomputable def tripleToLeft
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ (atlas.chart i).context :=
  atlas.tripleToFirstPair raw i j l ≫ atlas.pairToLeft raw i j

/-- The selected triple context maps to the middle chart context. -/
noncomputable def tripleToMiddle
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ (atlas.chart j).context :=
  atlas.tripleToFirstPair raw i j l ≫ atlas.pairToRight raw i j

/-- The selected triple context maps to the right chart context. -/
noncomputable def tripleToRight
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ (atlas.chart l).context :=
  atlas.tripleToSecondPair raw i j l ≫ atlas.pairToRight raw j l

/-- SD3 API lemma exposing the pair context selected by `S.overlap`; all data comes from the
atlas charts and the fixed site overlap operation. -/
@[simp] theorem pairContext_ctx
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    (atlas.pairContext raw i j).ctx =
      S.overlap.overlap D.context.ctx
        (atlas.chart i).context.ctx (atlas.chart j).context.ctx :=
  rfl

/-- SD3 API lemma exposing the adjacent-pair triple context selected by `S.overlap`; it adds no
context or compatibility premise. -/
@[simp] theorem tripleContext_ctx
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    (atlas.tripleContext raw i j l).ctx =
      S.overlap.overlap D.context.ctx
        (atlas.pairContext raw i j).ctx
        (atlas.pairContext raw j l).ctx :=
  rfl

/-- SD3 API lemma identifying the pair-to-base map through the left chart; thin-context
uniqueness compares maps already generated by `S.overlap`. -/
@[simp] theorem pairToBase_eq_left
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairToBase raw i j =
      atlas.pairToLeft raw i j ≫ (atlas.chart i).contextHom :=
  Subsingleton.elim _ _

/-- SD3 API lemma identifying the pair-to-base map through the right chart; thin-context
uniqueness compares maps already generated by `S.overlap`. -/
theorem pairToBase_eq_right
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairToBase raw i j =
      atlas.pairToRight raw i j ≫ (atlas.chart j).contextHom :=
  Subsingleton.elim _ _

/-- SD3 API lemma exposing the forward map of the self-overlap isomorphism; it is the selected
left projection generated by `S.overlap.left`. -/
@[simp] theorem selfPairContextIso_hom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    (atlas.selfPairContextIso raw i).hom = atlas.pairToLeft raw i i :=
  rfl

/-- SD3 API lemma exposing the inverse map of the self-overlap isomorphism; it is generated by
`S.overlap.lift` from the chart's identity comparisons. -/
@[simp] theorem selfPairContextIso_inv
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    (atlas.selfPairContextIso raw i).inv = atlas.selfToPair raw i :=
  rfl

/-- SD3 API lemma fixing the left triple restriction as the first-pair route generated by the
selected overlap maps. -/
@[simp] theorem tripleToLeft_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToLeft raw i j l =
      atlas.tripleToFirstPair raw i j l ≫ atlas.pairToLeft raw i j :=
  rfl

/-- SD3 API lemma fixing the simp normal form of the middle triple restriction as the first-pair
route; no coherence premise is supplied. -/
@[simp] theorem tripleToMiddle_eq_first
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToMiddle raw i j l =
      atlas.tripleToFirstPair raw i j l ≫ atlas.pairToRight raw i j :=
  rfl

/-- SD3 API lemma identifying the middle triple restriction with the second-pair route;
thin-context uniqueness compares the two already constructed routes. -/
theorem tripleToMiddle_eq_second
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToMiddle raw i j l =
      atlas.tripleToSecondPair raw i j l ≫ atlas.pairToLeft raw j l :=
  Subsingleton.elim _ _

/-- SD3 API lemma fixing the right triple restriction as the second-pair route generated by the
selected overlap maps. -/
@[simp] theorem tripleToRight_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToRight raw i j l =
      atlas.tripleToSecondPair raw i j l ≫ atlas.pairToRight raw j l :=
  rfl

/-- The actual Scheme overlap is the Mathlib pullback of the two chart maps. -/
noncomputable abbrev actualOverlap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) : AlgebraicGeometry.Scheme :=
  pullback (atlas.chart i).map (atlas.chart j).map

/-- The actual overlap maps to the underlying Scheme through the left chart. -/
noncomputable def actualOverlapToUnderlying
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.actualOverlap raw i j ⟶ X :=
  pullback.fst (atlas.chart i).map (atlas.chart j).map ≫
    (atlas.chart i).map

/-- The actual triple overlap is the iterated Mathlib pullback. -/
noncomputable abbrev actualTripleOverlap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) : AlgebraicGeometry.Scheme :=
  pullback (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map

/-- The actual triple overlap maps to the left chart domain. -/
noncomputable def actualTripleToLeft
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l ⟶
      architectureChartSpec raw (atlas.chart i).context :=
  pullback.fst (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map ≫
    pullback.fst (atlas.chart i).map (atlas.chart j).map

/-- The actual triple overlap maps to the middle chart domain. -/
noncomputable def actualTripleToMiddle
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l ⟶
      architectureChartSpec raw (atlas.chart j).context :=
  pullback.fst (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map ≫
    pullback.snd (atlas.chart i).map (atlas.chart j).map

/-- The actual triple overlap maps to the right chart domain. -/
noncomputable def actualTripleToRight
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l ⟶
      architectureChartSpec raw (atlas.chart l).context :=
  pullback.snd (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map

/-- SD3 characterization theorem stating that the actual pair overlap is the Mathlib pullback
of the two selected chart maps. -/
theorem actualOverlap_eq_pullback
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.actualOverlap raw i j =
      pullback (atlas.chart i).map (atlas.chart j).map :=
  rfl

/-- SD3 characterization theorem stating that the actual triple overlap is the iterated
Mathlib pullback of the pair-overlap map and the third chart map. -/
theorem actualTripleOverlap_eq_pullback
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l =
      pullback (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map :=
  rfl

/-- SD3 API lemma exposing the left projection route from the actual overlap to the underlying
Scheme; it unfolds only the canonical Mathlib pullback construction. -/
theorem actualOverlapToUnderlying_eq_left
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.actualOverlapToUnderlying raw i j =
      pullback.fst (atlas.chart i).map (atlas.chart j).map ≫
        (atlas.chart i).map :=
  rfl

/-- SD3 API lemma exposing the two Mathlib pullback projections defining the actual
triple-to-left map. -/
theorem actualTripleToLeft_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToLeft raw i j l =
      pullback.fst (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map ≫
        pullback.fst (atlas.chart i).map (atlas.chart j).map :=
  rfl

/-- SD3 API lemma exposing the outer-left and inner-right Mathlib pullback projections defining
the actual triple-to-middle map. -/
theorem actualTripleToMiddle_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToMiddle raw i j l =
      pullback.fst (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map ≫
        pullback.snd (atlas.chart i).map (atlas.chart j).map :=
  rfl

/-- SD3 API lemma exposing the outer right Mathlib pullback projection defining the actual
triple-to-right map. -/
theorem actualTripleToRight_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToRight raw i j l =
      pullback.snd (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map :=
  rfl

end ArchitectureAffineAtlas

/-- Comparison data between selected pair contexts and actual Scheme pullbacks. -/
structure ArchitectureOverlapPresentation
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D) where
  /-- The selected pair-context Spec is isomorphic to the actual pullback. -/
  comparison : ∀ i j,
    architectureChartSpec raw (atlas.pairContext raw i j) ≅
      atlas.actualOverlap raw i j

/-- Actual compatibility of overlap comparisons with both pullback projections. -/
structure IsArchitectureOverlapPresentation
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (P : ArchitectureOverlapPresentation raw atlas) : Prop where
  /-- The comparison's first projection is the selected left restriction. -/
  comparison_fst : ∀ i j,
    (P.comparison i j).hom ≫
        pullback.fst (atlas.chart i).map (atlas.chart j).map =
      architectureChartRestriction raw (atlas.pairToLeft raw i j)
  /-- The comparison's second projection is the selected right restriction. -/
  comparison_snd : ∀ i j,
    (P.comparison i j).hom ≫
        pullback.snd (atlas.chart i).map (atlas.chart j).map =
      architectureChartRestriction raw (atlas.pairToRight raw i j)

namespace ArchitectureAffineAtlas

/-- The left projection of an overlap in a valid atlas is an open immersion.

The fixed atlas-level API accepts the complete validity package.  Pullback stability for this
projection is local to the selected right chart, so the proof intentionally reads
`h.chart_valid j`; atlas coverage remains part of the validity package used by atlas-level
constructions such as `toAffineOpenCover` rather than this projection calculation. -/
theorem overlap_left_isOpenImmersion
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (h : IsArchitectureAffineAtlas raw atlas)
    (i j : atlas.Index) :
    AlgebraicGeometry.IsOpenImmersion
      (pullback.fst (atlas.chart i).map (atlas.chart j).map) := by
  exact MorphismProperty.pullback_fst
    (P := @AlgebraicGeometry.IsOpenImmersion) _ _
    (h.chart_valid j).isOpenImmersion

/-- The right projection of an overlap in a valid atlas is an open immersion.

The fixed atlas-level API accepts the complete validity package.  Pullback stability for this
projection is local to the selected left chart, so the proof intentionally reads
`h.chart_valid i`; atlas coverage remains part of the validity package used by atlas-level
constructions such as `toAffineOpenCover` rather than this projection calculation. -/
theorem overlap_right_isOpenImmersion
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (h : IsArchitectureAffineAtlas raw atlas)
    (i j : atlas.Index) :
    AlgebraicGeometry.IsOpenImmersion
      (pullback.snd (atlas.chart i).map (atlas.chart j).map) := by
  exact MorphismProperty.pullback_snd
    (P := @AlgebraicGeometry.IsOpenImmersion) _ _
    (h.chart_valid i).isOpenImmersion

/-- SD3 derived theorem giving the right projection route to the underlying Scheme; its only
equational input is Mathlib's pullback condition. -/
theorem actualOverlapToUnderlying_eq_right
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.actualOverlapToUnderlying raw i j =
      pullback.snd (atlas.chart i).map (atlas.chart j).map ≫
        (atlas.chart j).map := by
  exact pullback.condition

/-- SD3 derived theorem making the two presented overlap routes commute; it uses both fixed
presentation equations and Mathlib's pullback condition. -/
theorem overlap_commutes
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (P : ArchitectureOverlapPresentation raw atlas)
    (hP : IsArchitectureOverlapPresentation raw P)
    (i j : atlas.Index) :
    architectureChartRestriction raw (atlas.pairToLeft raw i j) ≫
        (atlas.chart i).map =
      architectureChartRestriction raw (atlas.pairToRight raw i j) ≫
        (atlas.chart j).map := by
  rw [← hP.comparison_fst i j, ← hP.comparison_snd i j]
  simp only [Category.assoc, pullback.condition]

/-- SD3 API theorem showing canonical reading preservation along the selected left overlap map;
the proof is supplied by `ΓSpecIso` naturality for the generated restriction. -/
theorem overlap_toLeft_preserves
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    (AATReadingDecoration.ofContext raw (atlas.pairContext raw i j)).Preserves raw
      (architectureChartRestriction raw (atlas.pairToLeft raw i j))
      (AATReadingDecoration.ofContext raw (atlas.chart i).context) := by
  refine ⟨atlas.pairToLeft raw i j, ?_⟩
  exact AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
    (sheafifiedRestriction raw (atlas.pairToLeft raw i j))

/-- SD3 API theorem showing canonical reading preservation along the selected right overlap map;
the proof is supplied by `ΓSpecIso` naturality for the generated restriction. -/
theorem overlap_toRight_preserves
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    (AATReadingDecoration.ofContext raw (atlas.pairContext raw i j)).Preserves raw
      (architectureChartRestriction raw (atlas.pairToRight raw i j))
      (AATReadingDecoration.ofContext raw (atlas.chart j).context) := by
  refine ⟨atlas.pairToRight raw i j, ?_⟩
  exact AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
    (sheafifiedRestriction raw (atlas.pairToRight raw i j))

/-- SD3 derived theorem equating the two decoration restrictions to the base context;
thin-context uniqueness compares the generated composite context maps. -/
theorem decoration_overlap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    sheafifiedRestriction raw
        (atlas.pairToLeft raw i j ≫ (atlas.chart i).contextHom) =
      sheafifiedRestriction raw
        (atlas.pairToRight raw i j ≫ (atlas.chart j).contextHom) := by
  exact congrArg (sheafifiedRestriction raw) (Subsingleton.elim _ _)

/-- SD3 main coherence theorem for the actual iterated pullback; both equalities are derived from
the inner and outer Mathlib pullback conditions without an added coherence premise. -/
theorem actualTriple_cocycle
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToLeft raw i j l ≫ (atlas.chart i).map =
      atlas.actualTripleToMiddle raw i j l ≫ (atlas.chart j).map ∧
    atlas.actualTripleToMiddle raw i j l ≫ (atlas.chart j).map =
      atlas.actualTripleToRight raw i j l ≫ (atlas.chart l).map := by
  constructor
  · simp only [actualTripleToLeft, actualTripleToMiddle, Category.assoc]
    rw [pullback.condition]
  · simp only [actualTripleToMiddle, actualTripleToRight, Category.assoc]
    rw [← atlas.actualOverlapToUnderlying_eq_right raw i j, pullback.condition]

/-- SD3 main coherence theorem for selected triple-context maps; the two pair-presentation
equations and generated triple routes discharge both equalities. -/
theorem contextTriple_cocycle
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (P : ArchitectureOverlapPresentation raw atlas)
    (hP : IsArchitectureOverlapPresentation raw P)
    (i j l : atlas.Index) :
    architectureChartRestriction raw
          (atlas.tripleToLeft raw i j l) ≫ (atlas.chart i).map =
      architectureChartRestriction raw
          (atlas.tripleToMiddle raw i j l) ≫ (atlas.chart j).map ∧
    architectureChartRestriction raw
          (atlas.tripleToMiddle raw i j l) ≫ (atlas.chart j).map =
      architectureChartRestriction raw
          (atlas.tripleToRight raw i j l) ≫ (atlas.chart l).map := by
  constructor
  · have h := congrArg
      (fun q => architectureChartRestriction raw
        (atlas.tripleToFirstPair raw i j l) ≫ q)
      (atlas.overlap_commutes raw P hP i j)
    simpa [tripleToLeft, tripleToMiddle, Category.assoc] using h
  · rw [atlas.tripleToMiddle_eq_second raw i j l]
    have h := congrArg
      (fun q => architectureChartRestriction raw
        (atlas.tripleToSecondPair raw i j l) ≫ q)
      (atlas.overlap_commutes raw P hP j l)
    simpa [tripleToRight, Category.assoc] using h


end ArchitectureAffineAtlas

/-!
### The reading-decorated standard architecture scheme core

Implementation notes: SD4 realizes Definition 9.3 as an actual Mathlib `Scheme` with
its selected reading decoration, canonical affine-atlas presentation, and overlap comparison
data.  The SD9 ambient inputs are `raw` and `HasSheafify`; `atlasValid` and
`overlapsValid` are generic recognition inputs that later constructors and finite models
produce from primitive data.  SD5 realizes Appendix A.4--A.5: morphisms retain only the
underlying Scheme map and the existing `AATReadingDecoration.Preserves` proof.  Category laws
and the faithful forgetful functor are derived from equality of underlying maps and proof
irrelevance.
-/

/--
SD4's main recognition type for Definition 9.3.  It stores the actual Scheme, reading
decoration, atlas and overlap presentations, with the SD9 recognition inputs
`atlasValid` and `overlapsValid`; `raw` and `HasSheafify` are the ambient SD9 inputs.
-/
structure StandardArchitectureScheme
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] where
  /-- The actual Mathlib Scheme. -/
  underlying : AlgebraicGeometry.Scheme
  /-- The selected reading decoration on the Scheme. -/
  decoration : AATReadingDecoration raw underlying
  /-- The selected canonical affine atlas. -/
  atlas : ArchitectureAffineAtlas raw underlying decoration
  /-- Validity and pointwise coverage of the selected atlas. -/
  atlasValid : IsArchitectureAffineAtlas raw atlas
  /-- Comparison data between context overlaps and actual pullbacks. -/
  overlaps : ArchitectureOverlapPresentation raw atlas
  /-- Compatibility of each comparison with the actual pullback projections. -/
  overlapsValid : IsArchitectureOverlapPresentation raw overlaps

/--
Part III, Definition 5.2B's source functor of architecture-evaluation points.

Implementation notes: a selected representable regime may use one joint point
functor for all contexts.  Keeping the point type opaque permits concrete
representable subfunctors, while the only observable operations exposed from
it are the architecture reading and the `E`-owned evaluations below.  An
independent section map or residual family is deliberately not stored.

The point type is fixed before a representing scheme is selected.  A point
provides its architecture reading and the equation system's observable
evaluation on every context.  Pullback, architecture stability, section
evaluation, and context naturality are verified separately by
`IsEquationArchitecturePointSource`.
-/
structure EquationArchitecturePointSource
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (E : ArchitecturalEquationSystem S.contextPreorder) where
  /-- Architecture-evaluation points on a test scheme. -/
  Point : AlgebraicGeometry.Scheme.{max u v} → Type (max u v)
  /-- Pullback of a point along a test-scheme morphism. -/
  pullback :
    ∀ {T T' : AlgebraicGeometry.Scheme.{max u v}},
      (T' ⟶ T) → Point T → Point T'
  /-- Architecture reading carried by a source point. -/
  architecture :
    ∀ {T : AlgebraicGeometry.Scheme.{max u v}},
      Point T → ArchitectureObject U
  /-- Evaluation of every context-owned observable at a source point. -/
  evaluation :
    ∀ {T : AlgebraicGeometry.Scheme.{max u v}},
      Point T → ∀ W : S.category, E.Observable W →+* Γ(T, ⊤)

/-- Functoriality and context compatibility of architecture-evaluation points. -/
structure IsEquationArchitecturePointSource
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (P : EquationArchitecturePointSource.{u, v} E) : Prop where
  /-- Point pullback preserves identities. -/
  pullback_id :
    ∀ {T : AlgebraicGeometry.Scheme.{max u v}} (p : P.Point T),
      P.pullback (𝟙 T) p = p
  /-- Point pullback preserves composition. -/
  pullback_comp :
    ∀ {T T' T'' : AlgebraicGeometry.Scheme.{max u v}}
      (f : T' ⟶ T) (g : T'' ⟶ T') (p : P.Point T),
      P.pullback (g ≫ f) p = P.pullback g (P.pullback f p)
  /-- Architecture readings are stable under point pullback. -/
  architecture_pullback :
    ∀ {T T' : AlgebraicGeometry.Scheme.{max u v}}
      (f : T' ⟶ T) (p : P.Point T),
      P.architecture (P.pullback f p) = P.architecture p
  /-- Observable evaluation is pulled back through `Scheme.Hom.appTop`. -/
  evaluation_pullback :
    ∀ {T T' : AlgebraicGeometry.Scheme.{max u v}}
      (f : T' ⟶ T) (p : P.Point T) (W : S.category)
      (x : E.Observable W),
      P.evaluation (P.pullback f p) W x =
        f.appTop (P.evaluation p W x)
  /-- Observable restriction is evaluated by the same global section. -/
  evaluation_natural :
    ∀ {T : AlgebraicGeometry.Scheme.{max u v}} (p : P.Point T)
      {source target : S.category} (f : source ⟶ target)
      (x : E.Observable target),
      P.evaluation p source (E.restrict f x) =
        P.evaluation p target x

/--
Selected representable equation-point regime.

Implementation notes: this is the selected-representability input of
Definition 5.2B, not a truth certificate.  It stores only the `E`-indexed
source functor and its representing equivalence.  A presentation containing
caller-supplied section maps, architecture readings, or residual functions was
rejected: the universal observable maps, section reading `A_s`, and regular
residual sections are instead derived from the universal represented point.
-/
structure EquationObservableRealization
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : StandardArchitectureScheme raw)
    (E : ArchitecturalEquationSystem S.contextPreorder) where
  /-- The architecture-evaluation point source defined before representation. -/
  source : EquationArchitecturePointSource.{u, v} E
  /-- The scheme represents the source point functor on every test scheme. -/
  representingEquiv :
    ∀ T : AlgebraicGeometry.Scheme.{max u v},
      (T ⟶ X.underlying) ≃ source.Point T

namespace EquationObservableRealization

/--
The named selected-regime constructor from a source functor and its
representing equivalence.  All scheme sections and residual functions are
derived accessors below.
-/
noncomputable def ofRepresentingEquiv
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : StandardArchitectureScheme raw}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (P : EquationArchitecturePointSource.{u, v} E)
    (e : ∀ T : AlgebraicGeometry.Scheme.{max u v},
      (T ⟶ X.underlying) ≃ P.Point T) :
    EquationObservableRealization raw X E where
  source := P
  representingEquiv := e

/-- The named constructor retains exactly the selected source functor. -/
@[simp] theorem ofRepresentingEquiv_source
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : StandardArchitectureScheme raw}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (P : EquationArchitecturePointSource.{u, v} E)
    (e : ∀ T : AlgebraicGeometry.Scheme.{max u v},
      (T ⟶ X.underlying) ≃ P.Point T) :
    (ofRepresentingEquiv P e :
      EquationObservableRealization raw X E).source = P :=
  rfl

/-- The named constructor retains exactly the representing equivalence. -/
@[simp] theorem ofRepresentingEquiv_representingEquiv
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : StandardArchitectureScheme raw}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (P : EquationArchitecturePointSource.{u, v} E)
    (e : ∀ T : AlgebraicGeometry.Scheme.{max u v},
      (T ⟶ X.underlying) ≃ P.Point T) :
    (ofRepresentingEquiv P e :
      EquationObservableRealization raw X E).representingEquiv = e :=
  rfl

/-- The source point represented by a scheme morphism. -/
noncomputable def pointAt
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : StandardArchitectureScheme raw}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (R : EquationObservableRealization raw X E)
    {T : AlgebraicGeometry.Scheme.{max u v}}
    (s : T ⟶ X.underlying) : R.source.Point T :=
  R.representingEquiv T s

/-- The architecture reading derived from the represented point. -/
noncomputable def architectureAt
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : StandardArchitectureScheme raw}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (R : EquationObservableRealization raw X E)
    {T : AlgebraicGeometry.Scheme.{max u v}}
    (s : T ⟶ X.underlying) : ArchitectureObject U :=
  R.source.architecture (R.pointAt s)

/-- Evaluation derived from the represented point, with no independent map. -/
noncomputable def evaluation
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : StandardArchitectureScheme raw}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (R : EquationObservableRealization raw X E)
    {T : AlgebraicGeometry.Scheme.{max u v}}
    (s : T ⟶ X.underlying) (W : S.category) :
    E.Observable W →+* Γ(T, ⊤) :=
  R.source.evaluation (R.pointAt s) W

/-- The universal section map derived by evaluating the represented identity. -/
noncomputable def sectionMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : StandardArchitectureScheme raw}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (R : EquationObservableRealization raw X E)
    (W : S.category) : E.Observable W →+* Γ(X.underlying, ⊤) :=
  R.evaluation (𝟙 X.underlying) W

/-- The universal residual section is generated from `E.equationResidual`. -/
noncomputable def residualSection
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : StandardArchitectureScheme raw}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (R : EquationObservableRealization raw X E)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    Γ(X.underlying, ⊤) :=
  R.sectionMap W
    (E.equationResidual W (R.architectureAt (𝟙 X.underlying)) i a)

end EquationObservableRealization

/-- Recognition property for a represented architecture-evaluation source. -/
structure IsEquationObservableRealization
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : StandardArchitectureScheme raw}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (R : EquationObservableRealization raw X E) : Prop where
  /-- The represented source is a genuine contravariant point functor. -/
  source_valid : IsEquationArchitecturePointSource R.source
  /-- The representing equivalence commutes with test-scheme pullback. -/
  representingEquiv_natural :
    ∀ {T T' : AlgebraicGeometry.Scheme.{max u v}}
      (s : T ⟶ X.underlying) (f : T' ⟶ T),
      R.pointAt (f ≫ s) = R.source.pullback f (R.pointAt s)

namespace EquationObservableRealization

/--
The named constructor discharges realization validity from source
functoriality and naturality of the representing equivalence.
-/
theorem ofRepresentingEquiv_valid
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X : StandardArchitectureScheme raw}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (P : EquationArchitecturePointSource.{u, v} E)
    (e : ∀ T : AlgebraicGeometry.Scheme.{max u v},
      (T ⟶ X.underlying) ≃ P.Point T)
    (hP : IsEquationArchitecturePointSource P)
    (he :
      ∀ {T T' : AlgebraicGeometry.Scheme.{max u v}}
        (s : T ⟶ X.underlying) (f : T' ⟶ T),
        e T' (f ≫ s) = P.pullback f (e T s)) :
    IsEquationObservableRealization
      (ofRepresentingEquiv P e :
        EquationObservableRealization raw X E) where
  source_valid := hP
  representingEquiv_natural := he

end EquationObservableRealization

namespace StandardArchitectureScheme

/--
SD4 derived accessor for Definition 9.3.  It turns the selected atlas and its
`atlasValid` recognition input into Mathlib's affine cover through
`ArchitectureAffineAtlas.toAffineOpenCover`.
-/
noncomputable def affineOpenCover
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : StandardArchitectureScheme raw) : X.underlying.AffineOpenCover :=
  X.atlas.toAffineOpenCover raw X.atlasValid

/--
SD4 API lemma for the affine-chart clause of Definition 9.3.  The conclusion is discharged
from the `atlasValid.chart_valid` recognition proof supplied by SD9.
-/
theorem chart_isOpenImmersion
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : StandardArchitectureScheme raw) (i : X.atlas.Index) :
    AlgebraicGeometry.IsOpenImmersion (X.atlas.chart i).map :=
  (X.atlasValid.chart_valid i).isOpenImmersion

/--
SD4 API lemma for the covering clause of Definition 9.3.  It uses
`ArchitectureAffineAtlas.jointlyCovers` and the stored `atlasValid` recognition input.
-/
theorem chart_jointlyCovers
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : StandardArchitectureScheme raw) :
    ⨆ i, ((X.affineOpenCover raw).f i).opensRange = ⊤ :=
  X.atlas.jointlyCovers raw X.atlasValid

/--
SD4 normalization lemma connecting Definition 9.3's affine cover to the selected `raw`
section ring.  It is inherited from `ArchitectureAffineAtlas.toAffineOpenCover_X`.
-/
theorem chart_sectionRing
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : StandardArchitectureScheme raw) (i : X.atlas.Index) :
    (X.affineOpenCover raw).X i =
      SheafifiedSectionRing raw (X.atlas.chart i).context :=
  X.atlas.toAffineOpenCover_X raw X.atlasValid i

/--
SD4 overlap accessor for Definition 9.3.  The SD3
`ArchitectureOverlapPresentation.comparison` data identifies the selected context Spec with
the actual Mathlib pullback; its projection equations remain in `overlapsValid`.
-/
noncomputable def overlap_is_actual_pullback
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : StandardArchitectureScheme raw) (i j : X.atlas.Index) :
    architectureChartSpec raw (X.atlas.pairContext raw i j) ≅
      pullback (X.atlas.chart i).map (X.atlas.chart j).map :=
  X.overlaps.comparison i j

/--
SD4 extensionality API for the recognition type.  It compares the four data-bearing fields
and uses proof irrelevance only for the SD9 validity inputs `atlasValid` and
`overlapsValid`.
-/
@[ext] theorem ext
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X Y : StandardArchitectureScheme raw)
    (hunderlying : X.underlying = Y.underlying)
    (hdecoration : HEq X.decoration Y.decoration)
    (hatlas : HEq X.atlas Y.atlas)
    (hoverlaps : HEq X.overlaps Y.overlaps) : X = Y := by
  cases X
  cases Y
  cases hunderlying
  cases hdecoration
  cases hatlas
  cases hoverlaps
  rfl

/--
SD5's main morphism type for Appendix A.4--A.5.  It stores exactly the underlying Scheme map
and the existing `AATReadingDecoration.Preserves` condition; `raw` and `HasSheafify` are
the ambient SD9 inputs.
-/
structure Hom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X Y : StandardArchitectureScheme raw) where
  /-- The underlying morphism of Mathlib Schemes. -/
  base : X.underlying ⟶ Y.underlying
  /-- Preservation of the actual reading equation along the underlying morphism. -/
  preserves : X.decoration.Preserves raw base Y.decoration

namespace Hom

/--
SD5 identity constructor for Appendix A.5.  The required preservation proof is produced by
`AATReadingDecoration.preserves_id` rather than stored as an additional law.
-/
def id
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : StandardArchitectureScheme raw) : Hom X X where
  base := 𝟙 X.underlying
  preserves := X.decoration.preserves_id raw

/--
SD5 composition constructor for Appendix A.5.  It composes underlying Scheme maps and obtains
the preservation proof from `AATReadingDecoration.preserves_comp`.
-/
def comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y Z : StandardArchitectureScheme raw}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  preserves := AATReadingDecoration.preserves_comp raw f.preserves g.preserves

/--
SD5 normalization API for the identity constructor.  It exposes that `Hom.id` uses the
underlying Scheme identity definitionally.
-/
@[simp] theorem id_base
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : StandardArchitectureScheme raw) :
    (id X).base = 𝟙 X.underlying :=
  rfl

/--
SD5 normalization API for composition.  It exposes that `Hom.comp` uses composition of the
underlying Scheme maps definitionally.
-/
@[simp] theorem comp_base
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y Z : StandardArchitectureScheme raw}
    (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).base = f.base ≫ g.base :=
  rfl

/--
SD5 extensionality API for Appendix A.5.  Equality of `base` determines a morphism because
`AATReadingDecoration.Preserves` is a proposition and its proofs are irrelevant.
-/
@[ext] theorem ext
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y : StandardArchitectureScheme raw}
    (f g : Hom X Y) (hbase : f.base = g.base) : f = g := by
  cases f
  cases g
  cases hbase
  rfl

end Hom

/--
SD5 derived category instance for Appendix A.5.  It uses `Hom.id`, `Hom.comp`, and
`Hom.ext`, reducing every category law to the corresponding law for underlying Scheme maps.
-/
instance category
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    Category (StandardArchitectureScheme raw) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext
    simp
  comp_id f := by
    apply Hom.ext
    simp
  assoc f g h := by
    apply Hom.ext
    simp

/--
SD5 derived forgetful functor for Appendix A.5.  It sends the SD4 core to `underlying` and
the SD5 morphism to `base`, using the category instance above.
-/
def forget
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    StandardArchitectureScheme raw ⥤ AlgebraicGeometry.Scheme where
  obj X := X.underlying
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

/--
SD5 faithful-instance target for Appendix A.5.  It connects Mathlib's
`Functor.Faithful.map_injective` to `Hom.ext`, so equality after forgetting determines the
decorated morphism.
-/
instance forget_faithful
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    (forget raw).Faithful where
  map_injective h := Hom.ext _ _ h

/--
SD5 object-normalization API for the forgetful functor.  It records the definitional
connection between `forget.obj` and the SD4 `underlying` field.
-/
@[simp] theorem forget_obj
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : StandardArchitectureScheme raw) :
    (forget raw).obj X = X.underlying :=
  rfl

/--
SD5 morphism-normalization API for the forgetful functor.  It records the definitional
connection between `forget.map` and the SD5 `base` field.
-/
@[simp] theorem forget_map
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {X Y : StandardArchitectureScheme raw}
    (f : X ⟶ Y) :
    (forget raw).map f = f.base :=
  rfl

/-!
### SD6 presentation and single-affine constructors

`ofPresentation` is the recognition constructor for already supplied SD4 data. It does not
serve as completion evidence by itself. The `singleAffine` constructor instead produces
`atlasValid` and `overlapsValid` from the SD2 identity chart, the SD3 self-overlap context
isomorphism, and Mathlib pullback uniqueness. Its only ambient inputs are the SD9 `raw` and
`HasSheafify` parameters.
-/

/--
SD6 recognition constructor for Definition 9.3. It packages the fixed six SD4 fields without
adding a premise or a second presentation layer; callers supply the atlas and overlap validity
used by this generic constructor.
-/
noncomputable def ofPresentation
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X)
    (atlas : ArchitectureAffineAtlas raw X D)
    (hatlas : IsArchitectureAffineAtlas raw atlas)
    (overlaps : ArchitectureOverlapPresentation raw atlas)
    (hoverlaps : IsArchitectureOverlapPresentation raw overlaps) :
    StandardArchitectureScheme raw where
  underlying := X
  decoration := D
  atlas := atlas
  atlasValid := hatlas
  overlaps := overlaps
  overlapsValid := hoverlaps

/--
SD6 normalization API exposing the Definition 9.3 Scheme packaged by `ofPresentation`.
The SD9 ambient inputs are `raw` and `HasSheafify`; validity remains the supplied recognition data.
-/
@[simp] theorem ofPresentation_underlying
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X)
    (atlas : ArchitectureAffineAtlas raw X D)
    (hatlas : IsArchitectureAffineAtlas raw atlas)
    (overlaps : ArchitectureOverlapPresentation raw atlas)
    (hoverlaps : IsArchitectureOverlapPresentation raw overlaps) :
    (ofPresentation raw X D atlas hatlas overlaps hoverlaps).underlying = X :=
  rfl

/--
SD6 normalization API exposing the Definition 9.3 reading decoration packaged by
`ofPresentation`. Its SD9 ambient inputs are `raw` and `HasSheafify`; validity remains supplied.
-/
@[simp] theorem ofPresentation_decoration
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X)
    (atlas : ArchitectureAffineAtlas raw X D)
    (hatlas : IsArchitectureAffineAtlas raw atlas)
    (overlaps : ArchitectureOverlapPresentation raw atlas)
    (hoverlaps : IsArchitectureOverlapPresentation raw overlaps) :
    (ofPresentation raw X D atlas hatlas overlaps hoverlaps).decoration = D :=
  rfl

/--
SD6 normalization API exposing the Definition 9.3 affine atlas packaged by `ofPresentation`.
The SD9 ambient inputs are `raw` and `HasSheafify`; `hatlas` is recognition data used by the core.
-/
@[simp] theorem ofPresentation_atlas
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X)
    (atlas : ArchitectureAffineAtlas raw X D)
    (hatlas : IsArchitectureAffineAtlas raw atlas)
    (overlaps : ArchitectureOverlapPresentation raw atlas)
    (hoverlaps : IsArchitectureOverlapPresentation raw overlaps) :
    (ofPresentation raw X D atlas hatlas overlaps hoverlaps).atlas = atlas :=
  rfl

/--
SD6 normalization API exposing the Definition 9.3 overlap presentation packaged by
`ofPresentation`. The SD9 ambient inputs are `raw` and `HasSheafify`; `hoverlaps` is recognition data.
-/
@[simp] theorem ofPresentation_overlaps
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X)
    (atlas : ArchitectureAffineAtlas raw X D)
    (hatlas : IsArchitectureAffineAtlas raw atlas)
    (overlaps : ArchitectureOverlapPresentation raw atlas)
    (hoverlaps : IsArchitectureOverlapPresentation raw overlaps) :
    (ofPresentation raw X D atlas hatlas overlaps hoverlaps).overlaps = overlaps :=
  rfl

/--
SD6 completion constructor for the single-chart case of Definition 9.3 and Appendix A.5.
It builds the identity chart and pointwise coverage directly. For the self-overlap it sends
`selfPairContextIso` through `architectureChartIso`, proves the square with two identity
chart maps is a pullback, and uses `IsPullback.isoPullback` for the comparison and both
projection equations. No chart-validity, coverage, overlap, or coherence proof is an argument.
-/
noncomputable def singleAffine
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) : StandardArchitectureScheme raw := by
  let atlas :
      ArchitectureAffineAtlas raw
        (architectureChartSpec raw W)
        (AATReadingDecoration.ofContext raw W) := {
    Index := PUnit
    chart _ := ArchitectureAffineChart.identity raw W }
  have hatlas : IsArchitectureAffineAtlas raw atlas := {
    chart_valid _ :=
      ArchitectureAffineChart.identity_isArchitectureAffineChart raw W
    covers x := ⟨PUnit.unit, x, by simp [atlas]⟩ }
  let overlaps : ArchitectureOverlapPresentation raw atlas := {
    comparison i j := by
      cases i
      cases j
      let e :=
        architectureChartIso raw
          (atlas.selfPairContextIso raw PUnit.unit)
      letI : IsIso e.hom := Iso.isIso_hom e
      letI : IsIso (architectureChartRestriction raw
          (atlas.pairToLeft raw PUnit.unit PUnit.unit)) := by
        change IsIso e.hom
        infer_instance
      letI : IsIso (𝟙 (architectureChartSpec raw W)) := IsIso.id _
      let h : IsPullback
          (architectureChartRestriction raw
            (atlas.pairToLeft raw PUnit.unit PUnit.unit))
          (architectureChartRestriction raw
            (atlas.pairToRight raw PUnit.unit PUnit.unit))
          (𝟙 (architectureChartSpec raw W))
          (𝟙 (architectureChartSpec raw W)) :=
        IsPullback.of_horiz_isIso
          ⟨congrArg (architectureChartRestriction raw)
            (Subsingleton.elim _ _)⟩
      exact h.isoPullback }
  have hoverlaps : IsArchitectureOverlapPresentation raw overlaps := {
    comparison_fst i j := by
      cases i
      cases j
      apply IsPullback.isoPullback_hom_fst
    comparison_snd i j := by
      cases i
      cases j
      apply IsPullback.isoPullback_hom_snd }
  exact ofPresentation raw
    (architectureChartSpec raw W)
    (AATReadingDecoration.ofContext raw W)
    atlas hatlas overlaps hoverlaps

/--
SD6 normalization API fixing the Definition 9.3 single-affine Scheme to the selected section-ring
Spec. Its SD9 inputs are `raw`, `HasSheafify`, and `W`; validity is generated by `singleAffine`.
-/
@[simp] theorem singleAffine_underlying
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (singleAffine raw W).underlying = architectureChartSpec raw W :=
  rfl

/--
SD6 normalization API fixing the Definition 9.3 single-affine reading to the canonical decoration
of the same context and `raw`. Its SD9 inputs are `raw`, `HasSheafify`, and `W`; the decoration is
generated by `singleAffine`.
-/
@[simp] theorem singleAffine_decoration
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (singleAffine raw W).decoration =
      AATReadingDecoration.ofContext raw W :=
  rfl

/--
SD6 characterization API for Appendix A.5: the generated `PUnit` atlas has at most one chart
index. Its SD9 inputs are `raw`, `HasSheafify`, and `W`; no index proof is supplied by the caller.
-/
theorem singleAffine_index_subsingleton
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    Subsingleton (singleAffine raw W).atlas.Index := by
  change Subsingleton PUnit
  infer_instance

/--
SD6 constructor API for Appendix A.5 supplying the generated `PUnit.unit` chart index.
Its SD9 inputs are `raw`, `HasSheafify`, and `W`; the inhabitant is constructed internally.
-/
def singleAffineIndex
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) :
    (singleAffine raw W).atlas.Index :=
  PUnit.unit

/--
SD6 characterization API for Appendix A.5: every chart index equals the generated canonical
index. Its SD9 inputs are `raw`, `HasSheafify`, and `W`; uniqueness comes from `PUnit`.
-/
@[simp] theorem singleAffine_index_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category)
    (i : (singleAffine raw W).atlas.Index) :
    i = singleAffineIndex raw W := by
  letI := singleAffine_index_subsingleton raw W
  exact Subsingleton.elim _ _

/--
SD6 normalization API for Definition 9.3 and Appendix A.5 connecting the generated chart to
`ArchitectureAffineChart.identity_map`; the actual Scheme map is the identity. Its SD9 inputs are
`raw`, `HasSheafify`, and `W`, and chart validity is generated by `singleAffine`.
-/
theorem singleAffine_chart_map
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category)
    (i : (singleAffine raw W).atlas.Index) :
    ((singleAffine raw W).atlas.chart i).map =
      𝟙 (architectureChartSpec raw W) := by
  change (ArchitectureAffineChart.identity raw W).map = _
  exact ArchitectureAffineChart.identity_map raw W

end StandardArchitectureScheme

end
end LawAlgebra
end AAT.AG
