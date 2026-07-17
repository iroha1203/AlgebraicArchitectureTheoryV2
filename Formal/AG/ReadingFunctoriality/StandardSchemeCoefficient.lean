import Formal.AG.ReadingFunctoriality.Coefficient
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Standard-scheme coefficient base change

This module constructs coefficient change for a standard architecture scheme.  The underlying
scheme is definitionally the actual Mathlib pullback over the coefficient affine.  Its
decoration, affine atlas, coverage proof, and overlap comparisons are derived from the source
scheme and the canonical sheafified-section base-change comparison.

## Implementation notes

The coefficient structure morphism is the `ΓSpec` transpose of the global interpretation.
The changed decoration is obtained from the canonical section-object comparison, and every
changed chart and overlap is reconstructed by pullback universal properties.  Thus the public
API receives no caller-supplied changed scheme, atlas, overlap presentation, or validity
certificate.

Keeping this construction separate from `Coefficient` leaves the scalar-extension foundation
independent of standard-scheme packaging.  An arbitrary comparison morphism or a caller-selected
atlas was rejected because either choice would hide the canonical pullback data that the
characterization theorems expose.
-/

namespace AAT.AG

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

universe u v

noncomputable section

namespace LawAlgebra.StandardArchitectureScheme

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]

private noncomputable def constructedCoefficientStructureMap
    (X : LawAlgebra.StandardArchitectureScheme raw) :
    X.underlying ⟶
      AlgebraicGeometry.Scheme.Spec.obj
        (op (CommRingCat.of (ULift.{max u v, v} k))) := by
  let oldObject :=
    raw.toRingedSite.structureSheaf.val.obj (op X.decoration.context)
  let coefficientToGlobal :
      CommRingCat.of (ULift.{max u v, v} k) ⟶ Γ(X.underlying, ⊤) :=
    oldObject.hom ≫ X.decoration.interpretation
  exact
    (AlgebraicGeometry.ΓSpec.adjunction.homEquiv X.underlying
      (op (CommRingCat.of (ULift.{max u v, v} k))))
      coefficientToGlobal.op

private theorem constructedChartCoefficientSquare
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (i : X.atlas.Index) :
    (X.atlas.chart i).map ≫ constructedCoefficientStructureMap X =
      AlgebraicGeometry.Scheme.Spec.map
        (raw.toRingedSite.structureSheaf.val.obj
          (op (X.atlas.chart i).context)).hom.op := by
  let C := X.atlas.chart i
  let localObject := raw.toRingedSite.structureSheaf.val.obj (op C.context)
  let globalObject :=
    raw.toRingedSite.structureSheaf.val.obj (op X.decoration.context)
  change C.map ≫ constructedCoefficientStructureMap X =
    AlgebraicGeometry.Scheme.Spec.map localObject.hom.op
  change C.map ≫
      (AlgebraicGeometry.ΓSpec.adjunction.homEquiv X.underlying
        (op (CommRingCat.of (ULift.{max u v, v} k))))
        ((globalObject.hom ≫ X.decoration.interpretation).op) =
    AlgebraicGeometry.Scheme.Spec.map localObject.hom.op
  rw [← AlgebraicGeometry.ΓSpec.adjunction.homEquiv_naturality_left]
  apply
    (AlgebraicGeometry.ΓSpec.adjunction.homEquiv
      (LawAlgebra.architectureChartSpec raw C.context)
      (op (CommRingCat.of (ULift.{max u v, v} k)))).symm.injective
  simp only [Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_symm_apply]
  change (C.map.appTop).op ≫ X.decoration.interpretation.op ≫
      globalObject.hom.op =
    (Scheme.Spec.map localObject.hom.op).appTop.op ≫
      (Scheme.ΓSpecIso (CommRingCat.of (ULift.{max u v, v} k))).inv.op
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  calc
    (globalObject.hom ≫ X.decoration.interpretation) ≫ C.map.appTop =
        localObject.hom ≫ (Scheme.ΓSpecIso localObject.right).inv := by
      rw [← cancel_mono (Scheme.ΓSpecIso localObject.right).hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [← (X.atlasValid.chart_valid i).interpretation_compatible]
      have hw :=
        (raw.toRingedSite.structureSheaf.val.map C.contextHom.op).w
      change localObject.hom =
        globalObject.hom ≫ sheafifiedRestriction raw C.contextHom at hw
      exact hw.symm
    _ = _ := Scheme.ΓSpecIso_inv_naturality localObject.hom

variable {k' : Type v} [CommRing k']
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')]

private noncomputable def constructedUnderlying
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k') : Scheme :=
  pullback (constructedCoefficientStructureMap X)
    (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op)

private noncomputable def constructedMap
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k') : constructedUnderlying X f ⟶ X.underlying :=
  pullback.fst _ _

omit [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')] in
private theorem constructedCoefficientSquare
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k') :
    (raw.toRingedSite.structureSheaf.val.obj
          (op X.decoration.context)).hom ≫
        X.decoration.interpretation ≫ (constructedMap X f).appTop =
      CommRingCat.ofHom f.liftedHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ULift.{max u v, v} k'))).inv ≫
        (pullback.snd (constructedCoefficientStructureMap X)
          (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op)).appTop := by
  let oldObject :=
    raw.toRingedSite.structureSheaf.val.obj (op X.decoration.context)
  change oldObject.hom ≫ X.decoration.interpretation ≫
      (pullback.fst (constructedCoefficientStructureMap X)
        (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op)).appTop = _
  have hcoefficient :
      (Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{max u v, v} k))).inv ≫
          (constructedCoefficientStructureMap X).appTop =
        oldObject.hom ≫ X.decoration.interpretation :=
    AlgebraicGeometry.ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (oldObject.hom ≫ X.decoration.interpretation)
  have hp := congrArg (fun q : constructedUnderlying X f ⟶
      Scheme.Spec.obj (op (CommRingCat.of (ULift.{max u v, v} k))) => q.appTop)
    (pullback.condition (f := constructedCoefficientStructureMap X)
      (g := Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op))
  simp only [Scheme.Hom.comp_appTop] at hp
  rw [← Category.assoc, ← hcoefficient]
  rw [Category.assoc, hp]
  have hbase :
      (Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{max u v, v} k))).inv ≫
          (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op).appTop =
        CommRingCat.ofHom f.liftedHom ≫
          (Scheme.ΓSpecIso
            (CommRingCat.of (ULift.{max u v, v} k'))).inv :=
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom f.liftedHom)).symm
  rw [← Category.assoc, hbase]
  simp only [Category.assoc]

private noncomputable def constructedInterpretation
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.SheafifiedSectionRing (raw.baseChange f.hom)
        X.decoration.context ⟶
      Γ(constructedUnderlying X f, ⊤) :=
  (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionObjectBaseChangeIso
      raw f X.decoration.context).inv.right ≫
    pushout.desc
      (X.decoration.interpretation ≫ (constructedMap X f).appTop)
      ((Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{max u v, v} k'))).inv ≫
        (pullback.snd (constructedCoefficientStructureMap X)
          (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op)).appTop)
      (constructedCoefficientSquare X f)

private noncomputable def constructedDecoration
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.AATReadingDecoration (raw.baseChange f.hom)
      (constructedUnderlying X f) where
  context := X.decoration.context
  interpretation := constructedInterpretation X f

private theorem constructedInterpretation_eq
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f X.decoration.context ≫
        constructedInterpretation X f =
      X.decoration.interpretation ≫ (constructedMap X f).appTop := by
  simp [constructedInterpretation,
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap]

private noncomputable def constructedChangedChartToOld
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
        (X.atlas.chart i).context ⟶
      (X.atlas.chart i).domain :=
  (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso
      raw f (X.atlas.chart i).context).hom ≫
    pullback.fst _ _

private noncomputable def constructedChangedChartToTarget
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
        (X.atlas.chart i).context ⟶
      Scheme.Spec.obj (op (CommRingCat.of (ULift.{max u v, v} k'))) :=
  (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso
      raw f (X.atlas.chart i).context).hom ≫
    pullback.snd _ _

private theorem constructedChangedChart_condition
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    constructedChangedChartToOld X f i ≫ (X.atlas.chart i).map ≫
        constructedCoefficientStructureMap X =
      constructedChangedChartToTarget X f i ≫
        Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op := by
  simp only [constructedChartCoefficientSquare]
  simp [constructedChangedChartToOld, constructedChangedChartToTarget,
    Category.assoc, pullback.condition]

private noncomputable def constructedChangedChartMap
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
        (X.atlas.chart i).context ⟶ constructedUnderlying X f :=
  pullback.lift
    (constructedChangedChartToOld X f i ≫ (X.atlas.chart i).map)
    (constructedChangedChartToTarget X f i)
    (constructedChangedChart_condition X f i)

private noncomputable def constructedChangedChart
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    LawAlgebra.ArchitectureAffineChart (raw.baseChange f.hom)
      (constructedUnderlying X f) (constructedDecoration X f) where
  context := (X.atlas.chart i).context
  contextHom := (X.atlas.chart i).contextHom
  map := constructedChangedChartMap X f i

private theorem constructedChangedSpec_isPullback
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    IsPullback
      (constructedChangedChartToOld X f i)
      (constructedChangedChartToTarget X f i)
      (Scheme.Spec.map
        (raw.toRingedSite.structureSheaf.val.obj
          (op (X.atlas.chart i).context)).hom.op)
      (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op) := by
  let e := LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso
    raw f (X.atlas.chart i).context
  refine IsPullback.of_iso_pullback (i := e) ?_ ?_ ?_
  · constructor
    dsimp [constructedChangedChartToOld, constructedChangedChartToTarget]
    rw [Category.assoc, Category.assoc, pullback.condition]
  · rfl
  · rfl

private theorem constructedChangedChart_isPullback
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    IsPullback
      (constructedChangedChartMap X f i)
      (constructedChangedChartToOld X f i)
      (constructedMap X f)
      (X.atlas.chart i).map := by
  let hSpec := constructedChangedSpec_isPullback X f i
  rw [← constructedChartCoefficientSquare X i] at hSpec
  let hBase := IsPullback.of_hasPullback
    (constructedCoefficientStructureMap X)
    (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op)
  let h := (IsPullback.of_bot' hSpec hBase).flip
  convert h using 1
  apply hBase.hom_ext <;> simp [constructedChangedChartMap]

private theorem constructedChangedChart_isOpenImmersion
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    AlgebraicGeometry.IsOpenImmersion (constructedChangedChartMap X f i) := by
  exact MorphismProperty.of_isPullback
    (P := @AlgebraicGeometry.IsOpenImmersion)
    (constructedChangedChart_isPullback X f i).flip
    (X.atlasValid.chart_valid i).isOpenImmersion

private theorem constructedSectionBaseChangeMap_natural
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    {W V : S.category} (g : W ⟶ V) :
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap raw f V ≫
        LawAlgebra.sheafifiedRestriction (raw.baseChange f.hom) g =
      LawAlgebra.sheafifiedRestriction raw g ≫
        LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap raw f W := by
  let comparison :
      raw.toRingedSite.structureSheaf.val ⋙ f.coefficientExtension ≅
        (raw.baseChange f.hom).toRingedSite.structureSheaf.val :=
    (sheafifyComposeIso S.topology f.coefficientExtension raw.toPresheaf).symm ≪≫
      ((CategoryTheory.sheafification S.topology
        (LawAlgebra.AATCommAlgCat.{u, v} k')).mapIso
          (LawAlgebra.RawAmbientRestrictionSystem.baseChangePresheafIso raw f)).symm
  have hnat := congrArg (fun q => q.right)
    (comparison.hom.naturality g.op)
  change ((f.coefficientExtension.map
      (raw.toRingedSite.structureSheaf.val.map g.op)).right ≫
        (comparison.app (op W)).hom.right) =
    (comparison.app (op V)).hom.right ≫
      ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.map g.op).right at hnat
  change pushout.inl _ _ ≫ (comparison.app (op V)).hom.right ≫
      ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.map g.op).right =
    (raw.toRingedSite.structureSheaf.val.map g.op).right ≫
      pushout.inl _ _ ≫ (comparison.app (op W)).hom.right
  rw [← hnat]
  simp only [← Category.assoc]
  rw [cancel_mono (comparison.app (op W)).hom.right]
  simp [FlatCoefficientChange.coefficientExtension]

private theorem constructedChangedChart_appTop_toOld
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    (constructedMap X f).appTop ≫ (constructedChangedChartMap X f i).appTop ≫
        (Scheme.ΓSpecIso
          (LawAlgebra.SheafifiedSectionRing (raw.baseChange f.hom)
            (X.atlas.chart i).context)).hom =
      (X.atlas.chart i).map.appTop ≫
        (Scheme.ΓSpecIso
          (LawAlgebra.SheafifiedSectionRing raw
            (X.atlas.chart i).context)).hom ≫
        LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f (X.atlas.chart i).context := by
  have hMap :
      constructedChangedChartMap X f i ≫ constructedMap X f =
        constructedChangedChartToOld X f i ≫ (X.atlas.chart i).map := by
    simp [constructedChangedChartMap, constructedMap]
  have hTop := congrArg (fun q => q.appTop) hMap
  simp only [Scheme.Hom.comp_appTop] at hTop
  rw [← Category.assoc, hTop]
  simp only [Category.assoc]
  rw [show constructedChangedChartToOld X f i =
      Scheme.Spec.map
        (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f (X.atlas.chart i).context).op from
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso_hom_fst
      raw f (X.atlas.chart i).context]
  simpa only [Category.assoc] using congrArg
    (fun q => (X.atlas.chart i).map.appTop ≫ q)
    (Scheme.ΓSpecIso_naturality
      (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
        raw f (X.atlas.chart i).context))

private theorem constructedChangedChart_appTop_toTarget
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    (Scheme.ΓSpecIso (CommRingCat.of (ULift.{max u v, v} k'))).inv ≫
        (constructedChangedChartToTarget X f i).appTop ≫
        (Scheme.ΓSpecIso
          (LawAlgebra.SheafifiedSectionRing (raw.baseChange f.hom)
            (X.atlas.chart i).context)).hom =
      ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
        (op (X.atlas.chart i).context)).hom := by
  let localObject :=
    (raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
      (op (X.atlas.chart i).context)
  let sourceObject :=
    (Functor.fromPUnit
      (CommRingCat.of (ULift.{max u v, v} k'))).obj localObject.left
  rw [show constructedChangedChartToTarget X f i =
      Scheme.Spec.map
        ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
          (op (X.atlas.chart i).context)).hom.op from
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso_hom_snd
      raw f (X.atlas.chart i).context]
  change (Scheme.ΓSpecIso sourceObject).inv ≫
      (Scheme.Spec.map localObject.hom.op).appTop ≫
        (Scheme.ΓSpecIso localObject.right).hom = localObject.hom
  have h := congrArg
    (fun q => q ≫ (Scheme.ΓSpecIso localObject.right).hom)
    (Scheme.ΓSpecIso_inv_naturality localObject.hom).symm
  simpa [sourceObject, Category.assoc] using h

private theorem constructedChangedChart_interpretationCompatible
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    LawAlgebra.sheafifiedRestriction (raw.baseChange f.hom)
        (X.atlas.chart i).contextHom =
      (constructedDecoration X f).interpretation ≫
        (constructedChangedChartMap X f i).appTop ≫
        (Scheme.ΓSpecIso
          (LawAlgebra.SheafifiedSectionRing (raw.baseChange f.hom)
            (X.atlas.chart i).context)).hom := by
  let globalIso :=
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionObjectBaseChangeIso
      raw f X.decoration.context
  rw [← cancel_epi globalIso.hom.right]
  apply pushout.hom_ext
  · change
      LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f X.decoration.context ≫
        LawAlgebra.sheafifiedRestriction (raw.baseChange f.hom)
          (X.atlas.chart i).contextHom =
      LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f X.decoration.context ≫
        constructedInterpretation X f ≫ (constructedChangedChartMap X f i).appTop ≫
          (Scheme.ΓSpecIso
            (LawAlgebra.SheafifiedSectionRing (raw.baseChange f.hom)
              (X.atlas.chart i).context)).hom
    rw [constructedSectionBaseChangeMap_natural]
    rw [(X.atlasValid.chart_valid i).interpretation_compatible]
    calc
      X.decoration.interpretation ≫
            (X.atlas.chart i).map.appTop ≫
              (Scheme.ΓSpecIso
                (LawAlgebra.SheafifiedSectionRing raw
                  (X.atlas.chart i).context)).hom ≫
                LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
                  raw f (X.atlas.chart i).context =
          X.decoration.interpretation ≫ (constructedMap X f).appTop ≫
            (constructedChangedChartMap X f i).appTop ≫
              (Scheme.ΓSpecIso
                (LawAlgebra.SheafifiedSectionRing (raw.baseChange f.hom)
                  (X.atlas.chart i).context)).hom := by
            simpa only [Category.assoc] using congrArg
              (fun q => X.decoration.interpretation ≫ q)
              (constructedChangedChart_appTop_toOld X f i).symm
      _ = LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
              raw f X.decoration.context ≫
            constructedInterpretation X f ≫ (constructedChangedChartMap X f i).appTop ≫
              (Scheme.ΓSpecIso
                (LawAlgebra.SheafifiedSectionRing (raw.baseChange f.hom)
                  (X.atlas.chart i).context)).hom := by
            simpa only [Category.assoc] using congrArg
              (fun q => q ≫ (constructedChangedChartMap X f i).appTop ≫
                (Scheme.ΓSpecIso
                  (LawAlgebra.SheafifiedSectionRing (raw.baseChange f.hom)
                    (X.atlas.chart i).context)).hom)
              (constructedInterpretation_eq X f).symm
  · simp [globalIso, constructedDecoration, constructedInterpretation, Category.assoc]
    let localObject :=
      (raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
        (op (X.atlas.chart i).context)
    have hLeft :
        pushout.inr
              (raw.toRingedSite.structureSheaf.val.obj
                (op X.decoration.context)).hom
              (CommRingCat.ofHom f.liftedHom) ≫
            globalIso.hom.right ≫
              LawAlgebra.sheafifiedRestriction (raw.baseChange f.hom)
                (X.atlas.chart i).contextHom =
          localObject.hom := by
      have hGlobal := globalIso.hom.w
      have hRestriction :=
        ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.map
          (X.atlas.chart i).contextHom.op).w
      change
        ((Functor.fromPUnit
            (CommRingCat.of (ULift.{max u v, v} k'))).map
              globalIso.hom.left) ≫
              ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
                (op X.decoration.context)).hom =
          pushout.inr
              (raw.toRingedSite.structureSheaf.val.obj
                (op X.decoration.context)).hom
              (CommRingCat.ofHom f.liftedHom) ≫ globalIso.hom.right at hGlobal
      change
        ((Functor.fromPUnit
            (CommRingCat.of (ULift.{max u v, v} k'))).map
              ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.map
                (X.atlas.chart i).contextHom.op).left) ≫ localObject.hom =
          ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
              (op X.decoration.context)).hom ≫
            LawAlgebra.sheafifiedRestriction (raw.baseChange f.hom)
              (X.atlas.chart i).contextHom at hRestriction
      have hGlobal' :
          ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
              (op X.decoration.context)).hom =
            pushout.inr
                (raw.toRingedSite.structureSheaf.val.obj
                  (op X.decoration.context)).hom
                (CommRingCat.ofHom f.liftedHom) ≫ globalIso.hom.right := by
        simpa [Functor.fromPUnit] using hGlobal
      have hRestriction' :
          localObject.hom =
            ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.obj
                (op X.decoration.context)).hom ≫
              LawAlgebra.sheafifiedRestriction (raw.baseChange f.hom)
                (X.atlas.chart i).contextHom := by
        simpa [Functor.fromPUnit] using hRestriction
      rw [← Category.assoc, ← hGlobal']
      exact hRestriction'.symm
    have hTarget :
        (pullback.snd (constructedCoefficientStructureMap X)
              (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op)).appTop ≫
            (constructedChangedChartMap X f i).appTop =
          (constructedChangedChartToTarget X f i).appTop := by
      simpa only [Scheme.Hom.comp_appTop] using congrArg
        (fun q => q.appTop)
        (pullback.lift_snd
          (constructedChangedChartToOld X f i ≫ (X.atlas.chart i).map)
          (constructedChangedChartToTarget X f i)
          (constructedChangedChart_condition X f i))
    have hRight :
        (Scheme.ΓSpecIso
              (CommRingCat.of (ULift.{max u v, v} k'))).inv ≫
            (pullback.snd (constructedCoefficientStructureMap X)
              (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op)).appTop ≫
              (constructedChangedChartMap X f i).appTop ≫
                (Scheme.ΓSpecIso localObject.right).hom =
          localObject.hom := by
      calc
        (Scheme.ΓSpecIso
                (CommRingCat.of (ULift.{max u v, v} k'))).inv ≫
              (pullback.snd (constructedCoefficientStructureMap X)
                (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op)).appTop ≫
                (constructedChangedChartMap X f i).appTop ≫
                  (Scheme.ΓSpecIso localObject.right).hom =
            (Scheme.ΓSpecIso
                (CommRingCat.of (ULift.{max u v, v} k'))).inv ≫
              (constructedChangedChartToTarget X f i).appTop ≫
                (Scheme.ΓSpecIso localObject.right).hom := by
                  simpa only [Category.assoc] using congrArg
                    (fun q =>
                      (Scheme.ΓSpecIso
                          (CommRingCat.of (ULift.{max u v, v} k'))).inv ≫
                        q ≫ (Scheme.ΓSpecIso localObject.right).hom)
                    hTarget
        _ = localObject.hom := constructedChangedChart_appTop_toTarget X f i
    exact hLeft.trans hRight.symm

private theorem constructedChangedChart_valid
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    LawAlgebra.IsArchitectureAffineChart (raw.baseChange f.hom)
      (constructedChangedChart X f i) where
  isOpenImmersion := constructedChangedChart_isOpenImmersion X f i
  interpretation_compatible := constructedChangedChart_interpretationCompatible X f i

private noncomputable def constructedAtlas
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.ArchitectureAffineAtlas (raw.baseChange f.hom)
      (constructedUnderlying X f) (constructedDecoration X f) where
  Index := X.atlas.Index
  chart := constructedChangedChart X f

private theorem constructedAtlas_covers
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    ∀ x : constructedUnderlying X f, ∃ i y, ((constructedAtlas X f).chart i).map y = x := by
  intro x
  obtain ⟨i, y, hy⟩ := X.atlasValid.covers ((constructedMap X f) x)
  obtain ⟨z, hz, -⟩ :=
    AlgebraicGeometry.Scheme.exists_preimage_of_isPullback
      (constructedChangedChart_isPullback X f i) x y hy.symm
  exact ⟨i, z, hz⟩

private theorem constructedAtlas_valid
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.IsArchitectureAffineAtlas (raw.baseChange f.hom)
      (constructedAtlas X f) where
  chart_valid := constructedChangedChart_valid X f
  covers := constructedAtlas_covers X f

private noncomputable def constructedSpecToOld
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    LawAlgebra.architectureChartSpec (raw.baseChange f.hom) W ⟶
      LawAlgebra.architectureChartSpec raw W :=
  (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso
      raw f W).hom ≫ pullback.fst _ _

private noncomputable def constructedSpecToTarget
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    LawAlgebra.architectureChartSpec (raw.baseChange f.hom) W ⟶
      Scheme.Spec.obj (op (CommRingCat.of (ULift.{max u v, v} k'))) :=
  (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso
      raw f W).hom ≫ pullback.snd _ _

private theorem constructedSpecToOld_natural
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    {W V : S.category} (g : W ⟶ V) :
    LawAlgebra.architectureChartRestriction (raw.baseChange f.hom) g ≫
        constructedSpecToOld f V =
      constructedSpecToOld f W ≫ LawAlgebra.architectureChartRestriction raw g := by
  simp only [constructedSpecToOld,
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso_hom_fst,
    LawAlgebra.architectureChartRestriction,
    ← AlgebraicGeometry.Scheme.Spec.map_comp]
  congr 1
  exact congrArg Quiver.Hom.op
    (constructedSectionBaseChangeMap_natural f g)

private theorem constructedSpecToTarget_natural
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    {W V : S.category} (g : W ⟶ V) :
    LawAlgebra.architectureChartRestriction (raw.baseChange f.hom) g ≫
        constructedSpecToTarget f V =
      constructedSpecToTarget f W := by
  simp only [constructedSpecToTarget, LawAlgebra.architectureChartRestriction,
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso_hom_snd,
    ← AlgebraicGeometry.Scheme.Spec.map_comp]
  congr 1
  exact congrArg Quiver.Hom.op
    ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.map g.op).w.symm

private theorem constructedSpecToOld_eq
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    constructedSpecToOld f W =
      Scheme.Spec.map
        (LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f W).op := by
  exact
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso_hom_fst
      raw f W

private theorem constructedSpec_isPullback
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    IsPullback (constructedSpecToOld f W) (constructedSpecToTarget f W)
      (Scheme.Spec.map
        (raw.toRingedSite.structureSheaf.val.obj (op W)).hom.op)
      (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op) := by
  let e := LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso raw f W
  refine IsPullback.of_iso_pullback (i := e) ?_ ?_ ?_
  · constructor
    dsimp [constructedSpecToOld, constructedSpecToTarget]
    rw [Category.assoc, Category.assoc, pullback.condition]
  · rfl
  · rfl

private theorem constructedRestriction_coefficient
    {W V : S.category} (g : W ⟶ V) :
    LawAlgebra.architectureChartRestriction raw g ≫
        Scheme.Spec.map
          (raw.toRingedSite.structureSheaf.val.obj (op V)).hom.op =
      Scheme.Spec.map
        (raw.toRingedSite.structureSheaf.val.obj (op W)).hom.op := by
  change Scheme.Spec.map (LawAlgebra.sheafifiedRestriction raw g).op ≫ _ = _
  rw [← Scheme.Spec.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, unop_op]
  exact (raw.toRingedSite.structureSheaf.val.map g.op).w.symm

private theorem constructedOldOverlap_isPullback
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (i j : X.atlas.Index) :
    IsPullback
      (LawAlgebra.architectureChartRestriction raw
        (X.atlas.pairToLeft raw i j))
      (LawAlgebra.architectureChartRestriction raw
        (X.atlas.pairToRight raw i j))
      (X.atlas.chart i).map
      (X.atlas.chart j).map := by
  refine IsPullback.of_iso_pullback (i := X.overlaps.comparison i j)
    ⟨X.atlas.overlap_commutes raw X.overlaps X.overlapsValid i j⟩ ?_ ?_
  · exact X.overlapsValid.comparison_fst i j
  · exact X.overlapsValid.comparison_snd i j

private noncomputable def constructedChangedPairLeft
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) :=
  LawAlgebra.architectureChartRestriction (raw.baseChange f.hom)
    ((constructedAtlas X f).pairToLeft (raw.baseChange f.hom) i j)

private noncomputable def constructedChangedPairRight
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) :=
  LawAlgebra.architectureChartRestriction (raw.baseChange f.hom)
    ((constructedAtlas X f).pairToRight (raw.baseChange f.hom) i j)

@[simp, reassoc] private theorem constructedChangedPairLeft_toOld
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) :
    constructedChangedPairLeft X f i j ≫ constructedChangedChartToOld X f i =
      constructedSpecToOld f (X.atlas.pairContext raw i j) ≫
        LawAlgebra.architectureChartRestriction raw
          (X.atlas.pairToLeft raw i j) := by
  exact constructedSpecToOld_natural f (X.atlas.pairToLeft raw i j)

@[simp, reassoc] private theorem constructedChangedPairRight_toOld
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) :
    constructedChangedPairRight X f i j ≫ constructedChangedChartToOld X f j =
      constructedSpecToOld f (X.atlas.pairContext raw i j) ≫
        LawAlgebra.architectureChartRestriction raw
          (X.atlas.pairToRight raw i j) := by
  exact constructedSpecToOld_natural f (X.atlas.pairToRight raw i j)

@[simp, reassoc] private theorem constructedChangedPairLeft_toTarget
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) :
    constructedChangedPairLeft X f i j ≫ constructedChangedChartToTarget X f i =
      constructedSpecToTarget f (X.atlas.pairContext raw i j) := by
  exact constructedSpecToTarget_natural f (X.atlas.pairToLeft raw i j)

@[simp, reassoc] private theorem constructedChangedPairRight_toTarget
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) :
    constructedChangedPairRight X f i j ≫ constructedChangedChartToTarget X f j =
      constructedSpecToTarget f (X.atlas.pairContext raw i j) := by
  exact constructedSpecToTarget_natural f (X.atlas.pairToRight raw i j)

private theorem constructedChangedPair_commutes
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) :
    constructedChangedPairLeft X f i j ≫ constructedChangedChartMap X f i =
      constructedChangedPairRight X f i j ≫ constructedChangedChartMap X f j := by
  apply pullback.hom_ext
  · simp only [constructedChangedChartMap, Category.assoc, pullback.lift_fst,
      constructedChangedPairLeft_toOld_assoc, constructedChangedPairRight_toOld_assoc]
    rw [X.atlas.overlap_commutes raw X.overlaps X.overlapsValid i j]
  · simp [constructedChangedChartMap, Category.assoc]

private theorem constructedOldCone_condition
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) {T : Scheme}
    (a : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart i).context)
    (b : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart j).context)
    (w : a ≫ constructedChangedChartMap X f i =
      b ≫ constructedChangedChartMap X f j) :
    (a ≫ constructedChangedChartToOld X f i) ≫ (X.atlas.chart i).map =
      (b ≫ constructedChangedChartToOld X f j) ≫ (X.atlas.chart j).map := by
  have hw := congrArg (fun q => q ≫ constructedMap X f) w
  simpa only [Category.assoc,
    (constructedChangedChart_isPullback X f i).w,
    (constructedChangedChart_isPullback X f j).w] using hw

private noncomputable def constructedOldOverlapLift
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) {T : Scheme}
    (a : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart i).context)
    (b : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart j).context)
    (w : a ≫ constructedChangedChartMap X f i =
      b ≫ constructedChangedChartMap X f j) :
    T ⟶ LawAlgebra.architectureChartSpec raw
      (X.atlas.pairContext raw i j) :=
  (constructedOldOverlap_isPullback X i j).lift
    (a ≫ constructedChangedChartToOld X f i)
    (b ≫ constructedChangedChartToOld X f j)
    (constructedOldCone_condition X f i j a b w)

private theorem constructedPairBaseChange_condition
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) {T : Scheme}
    (a : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart i).context)
    (b : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart j).context)
    (w : a ≫ constructedChangedChartMap X f i =
      b ≫ constructedChangedChartMap X f j) :
    constructedOldOverlapLift X f i j a b w ≫
        Scheme.Spec.map
          (raw.toRingedSite.structureSheaf.val.obj
            (op (X.atlas.pairContext raw i j))).hom.op =
      (a ≫ constructedChangedChartToTarget X f i) ≫
        Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op := by
  rw [← constructedRestriction_coefficient
    (raw := raw) (X.atlas.pairToLeft raw i j)]
  simp only [constructedOldOverlapLift, Category.assoc, IsPullback.lift_fst_assoc]
  simpa only [Category.assoc] using congrArg (fun q => a ≫ q)
    (constructedSpec_isPullback (raw := raw) f
      (X.atlas.chart i).context).w

private noncomputable def constructedChangedOverlapLift
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) {T : Scheme}
    (a : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart i).context)
    (b : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart j).context)
    (w : a ≫ constructedChangedChartMap X f i =
      b ≫ constructedChangedChartMap X f j) :
    T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.pairContext raw i j) :=
  (constructedSpec_isPullback (raw := raw) f (X.atlas.pairContext raw i j)).lift
    (constructedOldOverlapLift X f i j a b w)
    (a ≫ constructedChangedChartToTarget X f i)
    (constructedPairBaseChange_condition X f i j a b w)

private theorem constructedChangedOverlapLift_left
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) {T : Scheme}
    (a : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart i).context)
    (b : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart j).context)
    (w : a ≫ constructedChangedChartMap X f i =
      b ≫ constructedChangedChartMap X f j) :
    constructedChangedOverlapLift X f i j a b w ≫
        constructedChangedPairLeft X f i j = a := by
  apply (constructedSpec_isPullback (raw := raw) f
    (X.atlas.chart i).context).hom_ext
  · change constructedChangedOverlapLift X f i j a b w ≫
        constructedChangedPairLeft X f i j ≫ constructedChangedChartToOld X f i =
      a ≫ constructedChangedChartToOld X f i
    rw [constructedChangedPairLeft_toOld]
    simp only [← Category.assoc, constructedChangedOverlapLift,
      IsPullback.lift_fst, constructedOldOverlapLift]
  · change constructedChangedOverlapLift X f i j a b w ≫
        constructedChangedPairLeft X f i j ≫ constructedChangedChartToTarget X f i =
      a ≫ constructedChangedChartToTarget X f i
    rw [constructedChangedPairLeft_toTarget]
    exact (constructedSpec_isPullback (raw := raw) f
      (X.atlas.pairContext raw i j)).lift_snd _ _ _

private theorem constructedChangedOverlapLift_right
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) {T : Scheme}
    (a : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart i).context)
    (b : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart j).context)
    (w : a ≫ constructedChangedChartMap X f i =
      b ≫ constructedChangedChartMap X f j) :
    constructedChangedOverlapLift X f i j a b w ≫
        constructedChangedPairRight X f i j = b := by
  apply (constructedSpec_isPullback (raw := raw) f
    (X.atlas.chart j).context).hom_ext
  · change constructedChangedOverlapLift X f i j a b w ≫
        constructedChangedPairRight X f i j ≫ constructedChangedChartToOld X f j =
      b ≫ constructedChangedChartToOld X f j
    rw [constructedChangedPairRight_toOld]
    simp only [← Category.assoc, constructedChangedOverlapLift,
      IsPullback.lift_fst, constructedOldOverlapLift]
    exact (constructedOldOverlap_isPullback X i j).lift_snd _ _ _
  · change constructedChangedOverlapLift X f i j a b w ≫
        constructedChangedPairRight X f i j ≫ constructedChangedChartToTarget X f j =
      b ≫ constructedChangedChartToTarget X f j
    rw [constructedChangedPairRight_toTarget]
    rw [constructedChangedOverlapLift]
    simp only [IsPullback.lift_snd]
    have hw := congrArg (fun q => q ≫
      pullback.snd (constructedCoefficientStructureMap X)
        (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op)) w
    simpa only [Category.assoc, constructedChangedChartMap,
      pullback.lift_snd] using hw

private theorem constructedChangedOverlap_uniq
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) {T : Scheme}
    (a : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart i).context)
    (b : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.chart j).context)
    (w : a ≫ constructedChangedChartMap X f i =
      b ≫ constructedChangedChartMap X f j)
    (m : T ⟶ LawAlgebra.architectureChartSpec (raw.baseChange f.hom)
      (X.atlas.pairContext raw i j))
    (hm₁ : m ≫ constructedChangedPairLeft X f i j = a)
    (hm₂ : m ≫ constructedChangedPairRight X f i j = b) :
    m = constructedChangedOverlapLift X f i j a b w := by
  apply (constructedSpec_isPullback (raw := raw) f
    (X.atlas.pairContext raw i j)).hom_ext
  · apply (constructedOldOverlap_isPullback X i j).hom_ext
    · simp only [Category.assoc]
      rw [← constructedChangedPairLeft_toOld X f i j]
      simp only [← Category.assoc, hm₁,
        constructedChangedOverlapLift_left X f i j a b w]
    · simp only [Category.assoc]
      rw [← constructedChangedPairRight_toOld X f i j]
      simp only [← Category.assoc, hm₂,
        constructedChangedOverlapLift_right X f i j a b w]
  · rw [← constructedChangedPairLeft_toTarget X f i j]
    simp only [← Category.assoc, hm₁,
      constructedChangedOverlapLift_left X f i j a b w]

private theorem constructedChangedOverlap_isPullback
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i j : X.atlas.Index) :
    IsPullback
      (constructedChangedPairLeft X f i j)
      (constructedChangedPairRight X f i j)
      (constructedChangedChartMap X f i)
      (constructedChangedChartMap X f j) := by
  apply IsPullback.of_isLimit'
    ⟨constructedChangedPair_commutes X f i j⟩
  refine PullbackCone.IsLimit.mk _
    (fun s => constructedChangedOverlapLift X f i j s.fst s.snd s.condition) ?_ ?_ ?_
  · intro s
    exact constructedChangedOverlapLift_left X f i j s.fst s.snd s.condition
  · intro s
    exact constructedChangedOverlapLift_right X f i j s.fst s.snd s.condition
  · intro s m hm₁ hm₂
    exact constructedChangedOverlap_uniq X f i j s.fst s.snd s.condition m hm₁ hm₂

private noncomputable def constructedOverlaps
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.ArchitectureOverlapPresentation (raw.baseChange f.hom)
      (constructedAtlas X f) where
  comparison i j := (constructedChangedOverlap_isPullback X f i j).isoPullback

private theorem constructedOverlaps_valid
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.IsArchitectureOverlapPresentation (raw.baseChange f.hom)
      (constructedOverlaps X f) where
  comparison_fst i j := by
    exact (constructedChangedOverlap_isPullback X f i j).isoPullback_hom_fst
  comparison_snd i j := by
    exact (constructedChangedOverlap_isPullback X f i j).isoPullback_hom_snd

private noncomputable def constructedStandardScheme
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.StandardArchitectureScheme (raw.baseChange f.hom) where
  underlying := constructedUnderlying X f
  decoration := constructedDecoration X f
  atlas := constructedAtlas X f
  atlasValid := constructedAtlas_valid X f
  overlaps := constructedOverlaps X f
  overlapsValid := constructedOverlaps_valid X f

end LawAlgebra.StandardArchitectureScheme

namespace LawAlgebra.StandardArchitectureScheme

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k k' : Type v}
variable [CommRing k] [CommRing k']
variable (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k')]

/-- The coefficient-affine structure morphism obtained by transposing the global interpretation
through the `ΓSpec` adjunction. -/
noncomputable def coefficientStructureMap
    (X : LawAlgebra.StandardArchitectureScheme raw) :
    X.underlying ⟶ Scheme.Spec.obj
      (op (CommRingCat.of (ULift.{max u v, v} k))) :=
  constructedCoefficientStructureMap X

/-- The canonical coefficient change of a standard architecture scheme.  The required
`HasSheafCompose` instance records preservation of sheaves by the site-dependent scalar-extension
functor; all changed scheme data are constructed from `X`. -/
noncomputable def baseChange
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.StandardArchitectureScheme (raw.baseChange f.hom) :=
  constructedStandardScheme X f

/-- The projection from the coefficient-changed scheme to its source scheme. -/
noncomputable def baseChangeMap
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    (baseChange raw X f).underlying ⟶ X.underlying :=
  constructedMap X f

/-- The canonical identification of the changed underlying scheme with the actual scheme
pullback over the coefficient affine. -/
noncomputable def baseChangeUnderlyingIso
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    (baseChange raw X f).underlying ≅
      pullback (coefficientStructureMap raw X)
        (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op) :=
  Iso.refl _

/-- The scheme projection is the first projection of the defining pullback. -/
theorem baseChangeMap_eq_pullback_fst
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    baseChangeMap raw X f = (baseChangeUnderlyingIso raw X f).hom ≫
      pullback.fst (coefficientStructureMap raw X)
        (Scheme.Spec.map (CommRingCat.ofHom f.liftedHom).op) := by
  simp [baseChangeMap, baseChangeUnderlyingIso, coefficientStructureMap, constructedMap]

/-- The changed reading decoration induced by the canonical map on sheafified sections. -/
noncomputable def baseChangedDecoration
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.AATReadingDecoration (raw.baseChange f.hom)
      (baseChange raw X f).underlying :=
  constructedDecoration X f

/-- Coefficient change preserves the selected reading context. -/
@[simp] theorem baseChangedDecoration_context
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    (baseChangedDecoration raw X f).context = X.decoration.context :=
  rfl

/-- The changed interpretation commutes with the canonical section map and scheme projection. -/
theorem baseChangedDecoration_interpretation
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f X.decoration.context ≫
        (baseChangedDecoration raw X f).interpretation =
      X.decoration.interpretation ≫ (baseChangeMap raw X f).appTop :=
  constructedInterpretation_eq X f

/-- The decoration stored in the changed standard scheme is the canonical changed decoration. -/
@[simp] theorem baseChange_decoration
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    (baseChange raw X f).decoration = baseChangedDecoration raw X f :=
  rfl

/-- The affine atlas reconstructed on the changed scheme by pulling back every source chart. -/
noncomputable def baseChangedAtlas
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.ArchitectureAffineAtlas (raw.baseChange f.hom)
      (baseChange raw X f).underlying (baseChange raw X f).decoration :=
  constructedAtlas X f

/-- The changed atlas uses the same chart index type as the source atlas. -/
@[simp] theorem baseChangedAtlas_Index
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    (baseChangedAtlas raw X f).Index = X.atlas.Index :=
  rfl

/-- The canonical projection from a changed chart to its corresponding source chart. -/
noncomputable def baseChangedChartMap
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    ((baseChangedAtlas raw X f).chart
      (cast (baseChangedAtlas_Index raw X f).symm i)).domain ⟶
      (X.atlas.chart i).domain :=
  constructedChangedChartToOld X f i

/-- Each changed chart forms a pullback square with its source chart and the scheme projection. -/
theorem baseChangedChart_isPullback
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')]
    (i : X.atlas.Index) :
    IsPullback
      ((baseChangedAtlas raw X f).chart
        (cast (baseChangedAtlas_Index raw X f).symm i)).map
      (baseChangedChartMap raw X f i)
      (baseChangeMap raw X f)
      (X.atlas.chart i).map :=
  constructedChangedChart_isPullback X f i

/-- The atlas stored in the changed standard scheme is the reconstructed pullback atlas. -/
theorem baseChange_atlas
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    (baseChange raw X f).atlas = baseChangedAtlas raw X f :=
  rfl

/-- The overlap presentation reconstructed from the source overlaps and changed chart
pullbacks. -/
noncomputable def baseChangedOverlaps
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.ArchitectureOverlapPresentation (raw.baseChange f.hom)
      (baseChangedAtlas raw X f) :=
  constructedOverlaps X f

/-- The reconstructed overlap presentation satisfies the required pullback conditions. -/
theorem baseChangedOverlaps_valid
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    LawAlgebra.IsArchitectureOverlapPresentation (raw.baseChange f.hom)
      (baseChangedOverlaps raw X f) :=
  constructedOverlaps_valid X f

/-- The overlap presentation stored in the changed standard scheme is the reconstructed one. -/
theorem baseChange_overlaps
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{u, v} k ⥤ LawAlgebra.AATCommAlgCat.{u, v} k')] :
    HEq (baseChange raw X f).overlaps (baseChangedOverlaps raw X f) :=
  HEq.rfl

end LawAlgebra.StandardArchitectureScheme
end
end AAT.AG
