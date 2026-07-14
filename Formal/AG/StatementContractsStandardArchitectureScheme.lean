import Formal.AG.LawAlgebra.StandardScheme

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

end AAT.AG.LawAlgebra
