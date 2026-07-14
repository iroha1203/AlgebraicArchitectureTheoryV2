import Formal.AG.LawAlgebra.StandardScheme

/-!
Executable statement contracts for the standard architecture scheme core.

This file directly checks the fixed SD0 and SD1 signatures from
`aat_lean_02_standard_architecture_scheme_prd.md` against their implementation
declarations.  It contains elaboration examples only and introduces no new
mathematical declarations.  Later PRD slices extend the same contract surface
with the fixed SD2--SD8 signatures.
-/

noncomputable section

namespace AAT.AG.LawAlgebra

universe u v w x

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable (raw : RawAmbientRestrictionSystem S k)
variable [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]

example : RingedAATSite S k :=
  RawAmbientRestrictionSystem.toRingedSite raw

example (W : S.category) : CommRingCat :=
  SheafifiedSectionRing raw W

example (W : S.category) : k →+* SheafifiedSectionRing raw W :=
  sheafifiedSectionAlgebraMap raw W

example (W : S.category) : Algebra k (SheafifiedSectionRing raw W) :=
  SheafifiedSectionRing.instAlgebra raw W

example {W V : S.category} (f : W ⟶ V) :
    SheafifiedSectionRing raw V ⟶ SheafifiedSectionRing raw W :=
  sheafifiedRestriction raw f

example {W V : S.category} (f : W ⟶ V) :
    SheafifiedSectionRing raw V →ₐ[k] SheafifiedSectionRing raw W :=
  sheafifiedRestrictionAlgHom raw f

example (W : S.category) :
    raw.rawAlgebra W →ₐ[k] SheafifiedSectionRing raw W :=
  sheafificationUnitAlgHom raw W

example (W : S.category) : AlgebraicGeometry.Scheme :=
  architectureChartSpec raw W

example {W V : S.category} (f : W ⟶ V) :
    architectureChartSpec raw W ⟶ architectureChartSpec raw V :=
  architectureChartRestriction raw f

example : (raw.toRingedSite).raw = raw.toPresheaf :=
  RawAmbientRestrictionSystem.toRingedSite_raw raw

example (W : S.category) :
    SheafifiedSectionRing raw W =
      (raw.toRingedSite.structureSheaf.val.obj (op W)).right :=
  SheafifiedSectionRing_eq_structureSheaf raw W

example (W : S.category) :
    algebraMap k (SheafifiedSectionRing raw W) =
      sheafifiedSectionAlgebraMap raw W :=
  SheafifiedSectionRing_algebraMap raw W

example {W V : S.category} (f : W ⟶ V) :
    sheafifiedRestriction raw f =
      (raw.toRingedSite.structureSheaf.val.map f.op).right :=
  sheafifiedRestriction_eq_structureSheafMap raw f

example {W V : S.category} (f : W ⟶ V) :
    (sheafifiedRestrictionAlgHom raw f).toRingHom =
      (sheafifiedRestriction raw f).hom :=
  sheafifiedRestrictionAlgHom_toRingHom raw f

example (W : S.category) :
    (sheafificationUnitAlgHom raw W).toRingHom =
      (raw.toRingedSite.canonical.app (op W)).right.hom :=
  sheafificationUnitAlgHom_toRingHom raw W

example (W : S.category) :
    architectureChartSpec raw W =
      AlgebraicGeometry.Scheme.Spec.obj
        (op (SheafifiedSectionRing raw W)) :=
  architectureChartSpec_eq_Spec raw W

example {W V : S.category} (f : W ⟶ V) :
    architectureChartRestriction raw f =
      AlgebraicGeometry.Scheme.Spec.map
        (sheafifiedRestriction raw f).op :=
  architectureChartRestriction_eq_SpecMap raw f

example (W : S.category) :
    sheafifiedRestriction raw (𝟙 W) = 𝟙 (SheafifiedSectionRing raw W) :=
  sheafifiedRestriction_id raw W

example {W V Z : S.category} (f : W ⟶ V) (g : V ⟶ Z) :
    sheafifiedRestriction raw (f ≫ g) =
      sheafifiedRestriction raw g ≫ sheafifiedRestriction raw f :=
  sheafifiedRestriction_comp raw f g

example (W : S.category) :
    architectureChartRestriction raw (𝟙 W) =
      𝟙 (architectureChartSpec raw W) :=
  architectureChartRestriction_id raw W

example {W V Z : S.category} (f : W ⟶ V) (g : V ⟶ Z) :
    architectureChartRestriction raw (f ≫ g) =
      architectureChartRestriction raw f ≫ architectureChartRestriction raw g :=
  architectureChartRestriction_comp raw f g

example : S.category ⥤ AlgebraicGeometry.Scheme :=
  architectureChartFunctor raw

example (W : S.category) :
    (architectureChartFunctor raw).obj W = architectureChartSpec raw W :=
  architectureChartFunctor_obj raw W

example {W V : S.category} (f : W ⟶ V) :
    (architectureChartFunctor raw).map f = architectureChartRestriction raw f :=
  architectureChartFunctor_map raw f

example {W V : S.category} (e : W ≅ V) :
    architectureChartSpec raw W ≅ architectureChartSpec raw V :=
  architectureChartIso raw e

example {W V : S.category} (e : W ≅ V) :
    (architectureChartIso raw e).hom = architectureChartRestriction raw e.hom :=
  architectureChartIso_hom raw e

example {W V : S.category} (e : W ≅ V) :
    (architectureChartIso raw e).inv = architectureChartRestriction raw e.inv :=
  architectureChartIso_inv raw e

example {W V : S.category} (f : W ⟶ V) :
    (architectureChartRestriction raw f).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw W)).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw V)).hom ≫
        sheafifiedRestriction raw f :=
  architectureChartRestriction_appTop raw f

example (X : AlgebraicGeometry.Scheme) : Type _ :=
  AATReadingDecoration raw X

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    CoordinateFamily D.context.ctx :=
  D.coordinateFamily raw

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) : LawUniverse U :=
  D.lawUniverse raw

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) : ArchitectureSignature U :=
  D.signature raw

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    k →+* Γ(X, ⊤) :=
  D.coefficientMap raw

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X)
    (c : D.coordinateFamily raw |>.CoordX) : Γ(X, ⊤) :=
  D.coordinateSection raw c

example {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    AATReadingDecoration raw X :=
  D.pullback raw f

example {X Y : AlgebraicGeometry.Scheme}
    (D_X : AATReadingDecoration raw X) (f : X ⟶ Y)
    (D_Y : AATReadingDecoration raw Y) : Prop :=
  D_X.Preserves raw f D_Y

example {X : AlgebraicGeometry.Scheme}
    (D E : AATReadingDecoration raw X)
    (hcontext : D.context = E.context)
    (hinterpretation : HEq D.interpretation E.interpretation) : D = E :=
  AATReadingDecoration.ext raw D E hcontext hinterpretation

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.coordinateFamily raw = raw.coordFamily D.context :=
  AATReadingDecoration.coordinateFamily_eq raw D

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.lawUniverse raw = S.lawUniverse :=
  AATReadingDecoration.lawUniverse_eq raw D

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.signature raw = S.signature :=
  AATReadingDecoration.signature_eq raw D

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.coefficientMap raw =
      D.interpretation.hom.comp
        (sheafifiedSectionAlgebraMap raw D.context) :=
  AATReadingDecoration.coefficientMap_eq raw D

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X)
    (c : D.coordinateFamily raw |>.CoordX) :
    D.coordinateSection raw c =
      D.interpretation
        ((raw.toRingedSite.canonical.app (op D.context)).right
          ((raw.relationFamily D.context).quotientMap (MvPolynomial.X c))) :=
  AATReadingDecoration.coordinateSection_apply raw D c

example {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    (D.pullback raw f).context = D.context :=
  AATReadingDecoration.pullback_context raw f D

example {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    (D.pullback raw f).interpretation = D.interpretation ≫ f.appTop :=
  AATReadingDecoration.pullback_interpretation raw f D

example {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y) :
    (D.pullback raw f).coefficientMap raw =
      f.appTop.hom.comp (D.coefficientMap raw) :=
  AATReadingDecoration.pullback_coefficientMap raw f D

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.pullback raw (𝟙 X) = D :=
  AATReadingDecoration.pullback_id raw D

example {X Y Z : AlgebraicGeometry.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (D : AATReadingDecoration raw Z) :
    D.pullback raw (f ≫ g) =
      (D.pullback raw g).pullback raw f :=
  AATReadingDecoration.pullback_comp raw f g D

example {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    (D : AATReadingDecoration raw Y)
    (c : D.coordinateFamily raw |>.CoordX) :
    (D.pullback raw f).coordinateSection raw c =
      f.appTop (D.coordinateSection raw c) :=
  AATReadingDecoration.coordinateSection_pullback raw f D c

example {X : AlgebraicGeometry.Scheme}
    (D : AATReadingDecoration raw X) :
    D.Preserves raw (𝟙 X) D :=
  AATReadingDecoration.preserves_id raw D

example {X Y Z : AlgebraicGeometry.Scheme}
    {D_X : AATReadingDecoration raw X}
    {D_Y : AATReadingDecoration raw Y}
    {D_Z : AATReadingDecoration raw Z}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : D_X.Preserves raw f D_Y)
    (hg : D_Y.Preserves raw g D_Z) :
    D_X.Preserves raw (f ≫ g) D_Z :=
  AATReadingDecoration.preserves_comp raw hf hg

example {X Y : AlgebraicGeometry.Scheme}
    {D_X : AATReadingDecoration raw X}
    {D_Y : AATReadingDecoration raw Y}
    {f : X ⟶ Y}
    (hf : D_X.Preserves raw f D_Y) :
    D_X.coefficientMap raw =
      f.appTop.hom.comp (D_Y.coefficientMap raw) :=
  AATReadingDecoration.Preserves.coefficientMap raw hf

example (W : S.category) :
    AATReadingDecoration raw (architectureChartSpec raw W) :=
  AATReadingDecoration.ofContext raw W

example (W : S.category) :
    (AATReadingDecoration.ofContext raw W).context = W :=
  AATReadingDecoration.ofContext_context raw W

example (W : S.category) :
    (AATReadingDecoration.ofContext raw W).interpretation =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing raw W)).inv :=
  AATReadingDecoration.ofContext_interpretation raw W

end AAT.AG.LawAlgebra
