import Formal.AG.LawAlgebra.StandardSchemeFiniteExample

/-!
Executable statement contracts for the standard architecture scheme core.

This file directly checks the fixed SD0--SD3 signatures and the SD8 finite
positive and negative witnesses from
`aat_lean_02_standard_architecture_scheme_prd.md` against their implementation
declarations.  It contains elaboration examples only and introduces no new
mathematical declarations.  Later PRD slices extend the same contract surface
with the remaining fixed SD3--SD8 signatures.
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

example (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X) : Type _ :=
  ArchitectureAffineChart raw X D

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) : Prop :=
  IsArchitectureAffineChart raw C

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) : AlgebraicGeometry.Scheme :=
  C.domain

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) : LocallyRingedSpace :=
  C.domainLocallyRingedSpace

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) :
    AlgebraicGeometry.IsAffine C.domain :=
  C.domain_isAffine

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D) :
    C.domain = architectureChartSpec raw C.context :=
  C.domain_eq

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D)
    (hC : IsArchitectureAffineChart raw C) : X.Opens :=
  C.image hC

example (W : S.category) :
    ArchitectureAffineChart raw
      (architectureChartSpec raw W)
      (AATReadingDecoration.ofContext raw W) :=
  ArchitectureAffineChart.identity raw W

example (W : S.category) :
    (ArchitectureAffineChart.identity raw W).context = W :=
  ArchitectureAffineChart.identity_context raw W

example (W : S.category) :
    (ArchitectureAffineChart.identity raw W).contextHom = 𝟙 W :=
  ArchitectureAffineChart.identity_contextHom raw W

example (W : S.category) :
    (ArchitectureAffineChart.identity raw W).map =
      𝟙 (architectureChartSpec raw W) :=
  ArchitectureAffineChart.identity_map raw W

example (W : S.category) :
    IsArchitectureAffineChart raw
      (ArchitectureAffineChart.identity raw W) :=
  ArchitectureAffineChart.identity_isArchitectureAffineChart raw W

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (C : ArchitectureAffineChart raw X D)
    (hC : IsArchitectureAffineChart raw C) :
    (AATReadingDecoration.ofContext raw C.context).Preserves raw C.map D :=
  C.localDecoration_preserves hC

example (X : AlgebraicGeometry.Scheme)
    (D : AATReadingDecoration raw X) : Type _ :=
  ArchitectureAffineAtlas raw X D

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D) : Prop :=
  IsArchitectureAffineAtlas raw atlas

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas) : X.AffineOpenCover :=
  atlas.toAffineOpenCover raw h

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas)
    (i : atlas.Index) :
    (atlas.toAffineOpenCover raw h).X i =
      SheafifiedSectionRing raw (atlas.chart i).context :=
  atlas.toAffineOpenCover_X raw h i

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas)
    (i : atlas.Index) :
    (atlas.toAffineOpenCover raw h).f i = (atlas.chart i).map :=
  atlas.toAffineOpenCover_f raw h i

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (h : IsArchitectureAffineAtlas raw atlas) :
    ⨆ i, ((atlas.toAffineOpenCover raw h).f i).opensRange = ⊤ :=
  atlas.jointlyCovers raw h

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) : S.category :=
  atlas.pairContext raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairContext raw i j ⟶ (atlas.chart i).context :=
  atlas.pairToLeft raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairContext raw i j ⟶ (atlas.chart j).context :=
  atlas.pairToRight raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairContext raw i j ⟶ D.context :=
  atlas.pairToBase raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    (atlas.chart i).context ⟶ atlas.pairContext raw i i :=
  atlas.selfToPair raw i

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    atlas.pairContext raw i i ≅ (atlas.chart i).context :=
  atlas.selfPairContextIso raw i

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) : S.category :=
  atlas.tripleContext raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ atlas.pairContext raw i j :=
  atlas.tripleToFirstPair raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ atlas.pairContext raw j l :=
  atlas.tripleToSecondPair raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ (atlas.chart i).context :=
  atlas.tripleToLeft raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ (atlas.chart j).context :=
  atlas.tripleToMiddle raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleContext raw i j l ⟶ (atlas.chart l).context :=
  atlas.tripleToRight raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    (atlas.pairContext raw i j).ctx =
      S.overlap.overlap D.context.ctx
        (atlas.chart i).context.ctx (atlas.chart j).context.ctx :=
  atlas.pairContext_ctx raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    (atlas.tripleContext raw i j l).ctx =
      S.overlap.overlap D.context.ctx
        (atlas.pairContext raw i j).ctx (atlas.pairContext raw j l).ctx :=
  atlas.tripleContext_ctx raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairToBase raw i j =
      atlas.pairToLeft raw i j ≫ (atlas.chart i).contextHom :=
  atlas.pairToBase_eq_left raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.pairToBase raw i j =
      atlas.pairToRight raw i j ≫ (atlas.chart j).contextHom :=
  atlas.pairToBase_eq_right raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    (atlas.selfPairContextIso raw i).hom = atlas.pairToLeft raw i i :=
  atlas.selfPairContextIso_hom raw i

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i : atlas.Index) :
    (atlas.selfPairContextIso raw i).inv = atlas.selfToPair raw i :=
  atlas.selfPairContextIso_inv raw i

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToLeft raw i j l =
      atlas.tripleToFirstPair raw i j l ≫ atlas.pairToLeft raw i j :=
  atlas.tripleToLeft_eq raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToMiddle raw i j l =
      atlas.tripleToFirstPair raw i j l ≫ atlas.pairToRight raw i j :=
  atlas.tripleToMiddle_eq_first raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToMiddle raw i j l =
      atlas.tripleToSecondPair raw i j l ≫ atlas.pairToLeft raw j l :=
  atlas.tripleToMiddle_eq_second raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.tripleToRight raw i j l =
      atlas.tripleToSecondPair raw i j l ≫ atlas.pairToRight raw j l :=
  atlas.tripleToRight_eq raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) : AlgebraicGeometry.Scheme :=
  atlas.actualOverlap raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) : atlas.actualOverlap raw i j ⟶ X :=
  atlas.actualOverlapToUnderlying raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) : AlgebraicGeometry.Scheme :=
  atlas.actualTripleOverlap raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l ⟶
      architectureChartSpec raw (atlas.chart i).context :=
  atlas.actualTripleToLeft raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l ⟶
      architectureChartSpec raw (atlas.chart j).context :=
  atlas.actualTripleToMiddle raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l ⟶
      architectureChartSpec raw (atlas.chart l).context :=
  atlas.actualTripleToRight raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.actualOverlap raw i j =
      pullback (atlas.chart i).map (atlas.chart j).map :=
  atlas.actualOverlap_eq_pullback raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleOverlap raw i j l =
      pullback (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map :=
  atlas.actualTripleOverlap_eq_pullback raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.actualOverlapToUnderlying raw i j =
      pullback.fst (atlas.chart i).map (atlas.chart j).map ≫
        (atlas.chart i).map :=
  atlas.actualOverlapToUnderlying_eq_left raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToLeft raw i j l =
      pullback.fst (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map ≫
        pullback.fst (atlas.chart i).map (atlas.chart j).map :=
  atlas.actualTripleToLeft_eq raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToMiddle raw i j l =
      pullback.fst (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map ≫
        pullback.snd (atlas.chart i).map (atlas.chart j).map :=
  atlas.actualTripleToMiddle_eq raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToRight raw i j l =
      pullback.snd (atlas.actualOverlapToUnderlying raw i j) (atlas.chart l).map :=
  atlas.actualTripleToRight_eq raw i j l

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D) : Type _ :=
  ArchitectureOverlapPresentation raw atlas

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (P : ArchitectureOverlapPresentation raw atlas) : Prop :=
  IsArchitectureOverlapPresentation raw P

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (h : IsArchitectureAffineAtlas raw atlas)
    (i j : atlas.Index) :
    AlgebraicGeometry.IsOpenImmersion
      (pullback.fst (atlas.chart i).map (atlas.chart j).map) :=
  ArchitectureAffineAtlas.overlap_left_isOpenImmersion raw h i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (h : IsArchitectureAffineAtlas raw atlas)
    (i j : atlas.Index) :
    AlgebraicGeometry.IsOpenImmersion
      (pullback.snd (atlas.chart i).map (atlas.chart j).map) :=
  ArchitectureAffineAtlas.overlap_right_isOpenImmersion raw h i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    atlas.actualOverlapToUnderlying raw i j =
      pullback.snd (atlas.chart i).map (atlas.chart j).map ≫
        (atlas.chart j).map :=
  atlas.actualOverlapToUnderlying_eq_right raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    {atlas : ArchitectureAffineAtlas raw X D}
    (P : ArchitectureOverlapPresentation raw atlas)
    (hP : IsArchitectureOverlapPresentation raw P)
    (i j : atlas.Index) :
    architectureChartRestriction raw (atlas.pairToLeft raw i j) ≫
        (atlas.chart i).map =
      architectureChartRestriction raw (atlas.pairToRight raw i j) ≫
        (atlas.chart j).map :=
  atlas.overlap_commutes raw P hP i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    (AATReadingDecoration.ofContext raw (atlas.pairContext raw i j)).Preserves raw
      (architectureChartRestriction raw (atlas.pairToLeft raw i j))
      (AATReadingDecoration.ofContext raw (atlas.chart i).context) :=
  atlas.overlap_toLeft_preserves raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    (AATReadingDecoration.ofContext raw (atlas.pairContext raw i j)).Preserves raw
      (architectureChartRestriction raw (atlas.pairToRight raw i j))
      (AATReadingDecoration.ofContext raw (atlas.chart j).context) :=
  atlas.overlap_toRight_preserves raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j : atlas.Index) :
    sheafifiedRestriction raw
        (atlas.pairToLeft raw i j ≫ (atlas.chart i).contextHom) =
      sheafifiedRestriction raw
        (atlas.pairToRight raw i j ≫ (atlas.chart j).contextHom) :=
  atlas.decoration_overlap raw i j

example {X : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw X}
    (atlas : ArchitectureAffineAtlas raw X D)
    (i j l : atlas.Index) :
    atlas.actualTripleToLeft raw i j l ≫ (atlas.chart i).map =
      atlas.actualTripleToMiddle raw i j l ≫ (atlas.chart j).map ∧
    atlas.actualTripleToMiddle raw i j l ≫ (atlas.chart j).map =
      atlas.actualTripleToRight raw i j l ≫ (atlas.chart l).map :=
  atlas.actualTriple_cocycle raw i j l

example {X : AlgebraicGeometry.Scheme}
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
          (atlas.tripleToRight raw i j l) ≫ (atlas.chart l).map :=
  atlas.contextTriple_cocycle raw P hP i j l

namespace FiniteExamples.StandardArchitectureScheme

open RingedSite.FiniteModel

example :
    ArchitectureAffineChart rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base) :=
  interpretationBrokenChart

example :
    sheafifiedRestriction rawSystem interpretationBrokenChart.contextHom ≠
      (AATReadingDecoration.ofContext rawSystem base).interpretation ≫
        interpretationBrokenChart.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem
            interpretationBrokenChart.context)).hom :=
  interpretationBrokenChart_equation_ne

example : ¬ IsArchitectureAffineChart rawSystem interpretationBrokenChart :=
  interpretationBrokenChart_not_valid

example : Nontrivial (rawSystem.rawAlgebra base) :=
  rawBaseNontrivial

example :
    Function.Injective
      (rawSystem.toRingedSite.canonical.app (op base)).right :=
  canonicalBaseInjective

example : Nonempty (architectureChartSpec rawSystem base) :=
  baseSpec_nonempty

example :
    ArchitectureAffineAtlas rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base) :=
  identityAtlas

example : IsArchitectureAffineAtlas rawSystem identityAtlas :=
  identityAtlas_valid

example :
    ArchitectureOverlapPresentation rawSystem identityAtlas :=
  identityAtlasPresentation

example :
    IsArchitectureOverlapPresentation rawSystem identityAtlasPresentation :=
  identityAtlasPresentation_valid

example :
    ArchitectureAffineAtlas rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base) :=
  mixedAtlas

example :
    mixedAtlas.pairContext rawSystem false true ≅ RawPresheaf.left :=
  mixedAtlasFalseTruePairIso

example :
    mixedAtlas.pairContext rawSystem true false ≅ RawPresheaf.left :=
  mixedAtlasTrueFalsePairIso

example :
    IsPullback
      (𝟙 (architectureChartSpec rawSystem RawPresheaf.left))
      (𝟙 (architectureChartSpec rawSystem RawPresheaf.left))
      (AlgebraicGeometry.Spec.map
        AAT.AG.LawAlgebra.FiniteExamples.StandardSchemeReading.identitySheafifiedMap)
      (AlgebraicGeometry.Spec.map
        AAT.AG.LawAlgebra.FiniteExamples.StandardSchemeReading.identitySheafifiedMap) :=
  brokenMapSelf_isPullback

example :
    IsPullback
      (AlgebraicGeometry.Spec.map
        AAT.AG.LawAlgebra.FiniteExamples.StandardSchemeReading.identitySheafifiedMap)
      (𝟙 (architectureChartSpec rawSystem RawPresheaf.left))
      (𝟙 (architectureChartSpec rawSystem base))
      (AlgebraicGeometry.Spec.map
        AAT.AG.LawAlgebra.FiniteExamples.StandardSchemeReading.identitySheafifiedMap) :=
  mixedFalseTrue_isPullback

example :
    ArchitectureOverlapPresentation rawSystem mixedAtlas :=
  mixedAtlasPresentation

example :
    ¬ IsArchitectureOverlapPresentation rawSystem mixedAtlasPresentation :=
  mixedAtlasPresentation_not_valid

example :
    ArchitectureAffineAtlas rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base) :=
  uncoveredAtlas

example : ¬ IsArchitectureAffineAtlas rawSystem uncoveredAtlas :=
  uncoveredAtlas_not_valid

end FiniteExamples.StandardArchitectureScheme

end AAT.AG.LawAlgebra
