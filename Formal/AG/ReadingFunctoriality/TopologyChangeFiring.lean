import Formal.AG.ReadingFunctoriality.FiniteExamples
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-!
# Actual topology-change firing

This module isolates the degree-one Mayer--Vietoris extension calculation used
to compare the independent fine injective-resolution class with the exact
functor map from the coarse topology.
-/

noncomputable section

namespace CategoryTheory

open Category Preadditive Limits

universe u₁ v₁ u₂ v₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable [HasExt.{w₁} C] [HasExt.{w₂} D]
variable [HasDerivedCategory C] [HasDerivedCategory D]
variable {S : ShortComplex C}
variable {T : ShortComplex (CochainComplex C ℤ)}

private noncomputable instance topologyMapHomologicalComplexPreservesFiniteLimits
    (F : Functor C D) [F.Additive] [PreservesFiniteLimits F] :
    PreservesFiniteLimits (F.mapHomologicalComplex (ComplexShape.up ℤ)) :=
  ⟨fun J _ _ => HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun i => by
    change PreservesLimitsOfShape J
      (HomologicalComplex.eval C (ComplexShape.up ℤ) i ⋙ F)
    infer_instance)⟩

private noncomputable instance topologyMapHomologicalComplexPreservesFiniteColimits
    (F : Functor C D) [F.Additive] [PreservesFiniteColimits F] :
    PreservesFiniteColimits (F.mapHomologicalComplex (ComplexShape.up ℤ)) :=
  ⟨fun J _ _ => HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i => by
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval C (ComplexShape.up ℤ) i ⋙ F)
    infer_instance)⟩

private noncomputable def topologyTriangleOfSESMapIso
    (hT : T.ShortExact) (F : Functor C D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.mapTriangle.obj (DerivedCategory.triangleOfSES hT) ≅
      DerivedCategory.triangleOfSES
        (hT.map_of_exact (F.mapHomologicalComplex (ComplexShape.up ℤ))) :=
  F.mapDerivedCategory.mapTriangle.mapIso
      (DerivedCategory.triangleOfSESIso hT) ≪≫
    (Functor.mapTriangleCompIso DerivedCategory.Q
      F.mapDerivedCategory).symm.app _ ≪≫
    (Functor.mapTriangleIso F.mapDerivedCategoryFactors).app _ ≪≫
    (Functor.mapTriangleCompIso
      (F.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q).app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso
      (CochainComplex.mappingCone.mapTriangleIso T.f F) ≪≫
    (DerivedCategory.triangleOfSESIso
      (hT.map_of_exact (F.mapHomologicalComplex (ComplexShape.up ℤ)))).symm

variable {U : ShortComplex (CochainComplex C ℤ)}

private noncomputable def topologyMappingConeIsoOfShortComplexIso
    (e : T ≅ U) :
    CochainComplex.mappingCone T.f ≅ CochainComplex.mappingCone U.f where
  hom := CochainComplex.mappingCone.map T.f U.f
    e.hom.τ₁ e.hom.τ₂ e.hom.comm₁₂.symm
  inv := CochainComplex.mappingCone.map U.f T.f
    e.inv.τ₁ e.inv.τ₂ e.inv.comm₁₂.symm
  hom_inv_id := by
    rw [← CochainComplex.mappingCone.map_comp T.f U.f T.f
      e.hom.τ₁ e.hom.τ₂ e.hom.comm₁₂.symm
      e.inv.τ₁ e.inv.τ₂ e.inv.comm₁₂.symm]
    have h₁ : e.hom.τ₁ ≫ e.inv.τ₁ = 𝟙 T.X₁ :=
      congrArg ShortComplex.Hom.τ₁ e.hom_inv_id
    have h₂ : e.hom.τ₂ ≫ e.inv.τ₂ = 𝟙 T.X₂ :=
      congrArg ShortComplex.Hom.τ₂ e.hom_inv_id
    simpa only [h₁, h₂] using CochainComplex.mappingCone.map_id T.f
  inv_hom_id := by
    rw [← CochainComplex.mappingCone.map_comp U.f T.f U.f
      e.inv.τ₁ e.inv.τ₂ e.inv.comm₁₂.symm
      e.hom.τ₁ e.hom.τ₂ e.hom.comm₁₂.symm]
    have h₁ : e.inv.τ₁ ≫ e.hom.τ₁ = 𝟙 U.X₁ :=
      congrArg ShortComplex.Hom.τ₁ e.inv_hom_id
    have h₂ : e.inv.τ₂ ≫ e.hom.τ₂ = 𝟙 U.X₂ :=
      congrArg ShortComplex.Hom.τ₂ e.inv_hom_id
    simpa only [h₁, h₂] using CochainComplex.mappingCone.map_id U.f

private noncomputable def topologyMappingConeTriangleIsoOfShortComplexIso
    (e : T ≅ U) :
    CochainComplex.mappingCone.triangle T.f ≅
      CochainComplex.mappingCone.triangle U.f := by
  let f := CochainComplex.mappingCone.triangleMap T.f U.f
    e.hom.τ₁ e.hom.τ₂ e.hom.comm₁₂.symm
  letI : IsIso f.hom₁ := by
    change IsIso e.hom.τ₁
    infer_instance
  letI : IsIso f.hom₂ := by
    change IsIso e.hom.τ₂
    infer_instance
  letI : IsIso f.hom₃ := by
    change IsIso (topologyMappingConeIsoOfShortComplexIso e).hom
    infer_instance
  letI : IsIso f :=
    Pretriangulated.Triangle.isIso_of_isIsos f
      inferInstance inferInstance inferInstance
  exact asIso f

private noncomputable def topologyTriangleOfSESNatIso
    (hT : T.ShortExact) (hU : U.ShortExact) (e : T ≅ U) :
    DerivedCategory.triangleOfSES hT ≅ DerivedCategory.triangleOfSES hU :=
  DerivedCategory.triangleOfSESIso hT ≪≫
    DerivedCategory.Q.mapTriangle.mapIso
      (topologyMappingConeTriangleIsoOfShortComplexIso e) ≪≫
    (DerivedCategory.triangleOfSESIso hU).symm

private noncomputable def topologySingleTriangleMapIso
    (hS : S.ShortExact) (F : Functor C D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.mapTriangle.obj hS.singleTriangle ≅
      (hS.map_of_exact F).singleTriangle :=
  F.mapDerivedCategory.mapTriangle.mapIso hS.singleTriangleIso ≪≫
    topologyTriangleOfSESMapIso
      (hS.map_of_exact
        (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) F ≪≫
    topologyTriangleOfSESNatIso
      ((hS.map_of_exact
        (HomologicalComplex.single C (ComplexShape.up ℤ) 0)).map_of_exact
          (F.mapHomologicalComplex (ComplexShape.up ℤ)))
      ((hS.map_of_exact F).map_of_exact
        (HomologicalComplex.single D (ComplexShape.up ℤ) 0))
      (S.mapNatIso (F.mapCochainComplexSingleFunctor 0)) ≪≫
    (hS.map_of_exact F).singleTriangleIso.symm

omit [HasExt C] [HasExt D] in
private lemma topologySingleTriangleMapIso_hom₁
    (hS : S.ShortExact) (F : Functor C D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (topologySingleTriangleMapIso hS F).hom.hom₁ =
      (F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁ := by
  simp [topologySingleTriangleMapIso, topologyTriangleOfSESMapIso,
    topologyTriangleOfSESNatIso,
    topologyMappingConeTriangleIsoOfShortComplexIso,
    ShortComplex.ShortExact.singleTriangleIso,
    DerivedCategory.triangleOfSESIso,
    CochainComplex.mappingCone.mapTriangleIso,
    Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorsPostcompQIso,
    DerivedCategory.singleFunctorIsoCompQ]
  rw [← F.mapDerivedCategory.map_comp_assoc]
  have hC :
      DerivedCategory.Qh.map
          (((HomotopyCategory.singleFunctorsPostcompQuotientIso C).hom.hom 0).app
            S.X₁) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app
          (((CochainComplex.singleFunctors C).functor 0).obj S.X₁) = 𝟙 _ := by
    simpa [DerivedCategory.singleFunctorsPostcompQIso] using
      CategoryTheory.NatTrans.congr_app
        (DerivedCategory.singleFunctorsPostcompQIso_hom_hom C 0) S.X₁
  rw [hC]
  have hD :
      (DerivedCategory.quotientCompQhIso D).inv.app
          (((CochainComplex.singleFunctors D).functor 0).obj (F.obj S.X₁)) ≫
        DerivedCategory.Qh.map
          (((HomotopyCategory.singleFunctorsPostcompQuotientIso D).inv.hom 0).app
            (F.obj S.X₁)) = 𝟙 _ := by
    simpa [DerivedCategory.singleFunctorsPostcompQIso] using
      CategoryTheory.NatTrans.congr_app
        (DerivedCategory.singleFunctorsPostcompQIso_inv_hom D 0) (F.obj S.X₁)
  rw [hD]
  have hMap :
      F.mapDerivedCategory.map
          (𝟙 (DerivedCategory.Qh.obj
            (((HomotopyCategory.singleFunctors C).functor 0).obj S.X₁))) =
        𝟙 (F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
          (((HomotopyCategory.singleFunctors C).functor 0).obj S.X₁))) :=
    F.mapDerivedCategory.map_id _
  rw [hMap]
  change
    (𝟙 _ ≫
      F.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj S.X₁) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.up ℤ) 0).hom.app S.X₁) ≫ 𝟙 _) =
    (𝟙 _ ≫
      F.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj S.X₁) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.up ℤ) 0).hom.app S.X₁) ≫ 𝟙 _)
  rfl

private lemma topologyExtClassMapExactFunctorHomConjugation
    (hS : S.ShortExact) (F : Functor C D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (hS.extClass.mapExactFunctor F).hom =
      (F.mapDerivedCategorySingleFunctor 0).inv.app S.X₃ ≫
        (topologySingleTriangleMapIso hS F).hom.hom₃ ≫
          (hS.map_of_exact F).extClass.hom := by
  rw [Abelian.Ext.mapExactFunctor_hom,
    ShortComplex.ShortExact.extClass_hom,
    ShortComplex.ShortExact.extClass_hom,
    ← topologySingleTriangleMapIso_hom₁ hS F]
  congr 1
  exact (topologySingleTriangleMapIso hS F).hom.comm₃

end CategoryTheory

namespace AAT.AG.ReadingFunctorialityFinite

open CategoryTheory
open Limits
open Opposite

universe u v w

private def topologyTerminalFreeForward
    {C : Type u} [Category.{v} C]
    {X : C} (Y : C) :
    FreeAbelianGroup (Y ⟶ X) →+ ULift.{v} ℤ :=
  FreeAbelianGroup.lift (fun _ => ULift.up 1)

private def topologyTerminalFreeInverse
    {C : Type u} [Category.{v} C]
    {X : C} (hX : IsTerminal X) (Y : C) :
    ULift.{v} ℤ →+ FreeAbelianGroup (Y ⟶ X) where
  toFun z := z.down • FreeAbelianGroup.of (hX.from Y)
  map_zero' := by simp
  map_add' x y := by
    change (x.down + y.down) • FreeAbelianGroup.of (hX.from Y) = _
    rw [add_smul]

private noncomputable def topologyTerminalFreeAddEquiv
    {C : Type u} [Category.{v} C]
    {X : C} (hX : IsTerminal X) (Y : C) :
    FreeAbelianGroup (Y ⟶ X) ≃+ ULift.{v} ℤ where
  toFun := topologyTerminalFreeForward Y
  invFun := topologyTerminalFreeInverse hX Y
  map_add' := (topologyTerminalFreeForward Y).map_add
  right_inv z := by
    rcases z with ⟨z⟩
    apply ULift.ext
    simp [topologyTerminalFreeForward, topologyTerminalFreeInverse]
  left_inv z := by
    let lhs : FreeAbelianGroup (Y ⟶ X) →+
        FreeAbelianGroup (Y ⟶ X) :=
      (topologyTerminalFreeInverse hX Y).comp
        (topologyTerminalFreeForward Y)
    have hlhs : lhs = AddMonoidHom.id _ := by
      apply FreeAbelianGroup.lift_ext
      intro f
      change FreeAbelianGroup.of (hX.from Y) = FreeAbelianGroup.of f
      congr
      exact hX.hom_ext _ _
    exact DFunLike.congr_fun hlhs z

private noncomputable def topologyTerminalFreePresheafIso
    {C : Type u} [Category.{v} C]
    {X : C} (hX : IsTerminal X) :
    yoneda.obj X ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  NatIso.ofComponents
    (fun Y => (topologyTerminalFreeAddEquiv hX Y.unop).toAddCommGrpIso)
    (fun {Y Z} f => by
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro g
      change topologyTerminalFreeForward Z.unop
          (FreeAbelianGroup.map (fun k => f.unop ≫ k)
            (FreeAbelianGroup.of g)) =
        topologyTerminalFreeForward Y.unop (FreeAbelianGroup.of g)
      rw [FreeAbelianGroup.map_of_apply]
      simp [topologyTerminalFreeForward])

private noncomputable def topologyCoarseBaseConstantIso :
    (presheafToSheaf coarseTopology AddCommGrpCat.{1}).obj
        (yoneda.obj topologyBase ⋙ AddCommGrpCat.free) ≅
      (constantSheaf coarseTopology AddCommGrpCat.{1}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  (presheafToSheaf coarseTopology AddCommGrpCat.{1}).mapIso
    (topologyTerminalFreePresheafIso topologyBaseIsTerminal)

private theorem extClass_precomp_ne_zero_of_middle_subsingleton
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    [Subsingleton (Abelian.Ext.{w} S.X₂ Y 0)]
    (x : Abelian.Ext.{w} S.X₁ Y 0) (hx : x ≠ 0) :
    hS.extClass.comp x rfl ≠ 0 := by
  let δ :
      AddCommGrpCat.of (Abelian.Ext.{w} S.X₁ Y 0) ⟶
        AddCommGrpCat.of (Abelian.Ext.{w} S.X₃ Y 1) :=
    AddCommGrpCat.ofHom
      (hS.extClass.precomp Y (rfl : 1 + 0 = 1))
  have hzero :
      (AddCommGrpCat.ofHom
        ((Abelian.Ext.mk₀ S.f).precomp Y (rfl : 0 + 0 = 0)) :
          AddCommGrpCat.of (Abelian.Ext.{w} S.X₂ Y 0) ⟶
            AddCommGrpCat.of (Abelian.Ext.{w} S.X₁ Y 0)) = 0 := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    simp
  letI : Mono δ :=
    (Abelian.Ext.contravariant_sequence_exact₁'
      hS Y 0 1 rfl).mono_g hzero
  intro h
  apply hx
  apply (AddCommGrpCat.mono_iff_injective δ).mp inferInstance
  simpa [δ] using h

private noncomputable def topologyCechToCoarseHOneEquiv :
    (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).AdditiveCechHn 1 ≃+
        topologyCoefficient.coarse.H nonzeroDegree :=
  AddEquiv.ofBijective
    (Cohomology.cechToSheafH topologyCoarseCover
      topologyObstructionSheaf topologyBaseIsTerminal
      topologyCoarseLerayCover nonzeroDegree)
    (Cohomology.cechToSheafH_bijective topologyCoarseCover
      topologyObstructionSheaf topologyBaseIsTerminal
      topologyCoarseLerayCover nonzeroDegree)

private theorem topologySourceHOneClass_ne_zero :
    topologySourceHOneClass ≠ 0 := by
  intro h
  apply topologyCechOneClass_ne_zero
  apply (Cohomology.cechToSheafH_bijective topologyCoarseCover
    topologyObstructionSheaf topologyBaseIsTerminal
    topologyCoarseLerayCover nonzeroDegree).1
  simpa [topologySourceHOneClass] using h

private theorem topologyCoarseHOne_eq_zero_or_eq_source
    (y : topologyCoefficient.coarse.H nonzeroDegree) :
    y = 0 ∨ y = topologySourceHOneClass := by
  let x := topologyCechToCoarseHOneEquiv.symm y
  rcases topologyCechHOne_eq_zero_or_eq_one x with hx | hx
  · left
    dsimp [x] at hx
    rw [← topologyCechToCoarseHOneEquiv.apply_symm_apply y, hx]
    simp
  · right
    dsimp [x] at hx
    rw [← topologyCechToCoarseHOneEquiv.apply_symm_apply y, hx]
    rfl

private noncomputable def topologyFiringOverlapToLeft :
    topologyOverlapObject ⟶ topologyLeftObject :=
  homOfLE topologyStrictDiamond.1

private noncomputable def topologyFiringOverlapToRight :
    topologyOverlapObject ⟶ topologyRightObject :=
  homOfLE topologyStrictDiamond.2.1

private noncomputable def topologyFiringLeftToBase :
    topologyLeftObject ⟶ topologyBase :=
  homOfLE topologyStrictDiamond.2.2.1

private noncomputable def topologyFiringRightToBase :
    topologyRightObject ⟶ topologyBase :=
  homOfLE topologyStrictDiamond.2.2.2.1

/-- The actual pullback square carried by the selected diamond. -/
private noncomputable def topologyDiamondSquare : Square topologySite.category :=
  Square.mk topologyFiringOverlapToLeft topologyFiringOverlapToRight
    topologyFiringLeftToBase topologyFiringRightToBase (Subsingleton.elim _ _)

private theorem topologyDiamondSquare_isPullback :
    topologyDiamondSquare.IsPullback := by
  apply Square.IsPullback.mk
  refine PullbackCone.IsLimit.mk _
    (fun s => homOfLE (Site.productContextFiniteMeet.le_meet
      (leOfHom s.fst) (leOfHom s.snd))) ?_ ?_ ?_
  · intro s
    exact Subsingleton.elim _ _
  · intro s
    exact Subsingleton.elim _ _
  · intro s m hmleft hmright
    exact Subsingleton.elim _ _

private theorem topologyDiamondSieve_eq_coarseCover :
    Sieve.ofTwoArrows topologyDiamondSquare.f₂₄
        topologyDiamondSquare.f₃₄ =
      Sieve.generate topologyCoarseCover.presieve := by
  apply le_antisymm
  · rw [Sieve.generate_le_iff]
    intro Y f hf
    rcases hf with ⟨i⟩
    cases i
    · exact Sieve.le_generate topologyCoarseCover.presieve _
        (Presieve.ofArrows.mk (topologyCoarseCoverIndexEquiv.symm false))
    · exact Sieve.le_generate topologyCoarseCover.presieve _
        (Presieve.ofArrows.mk (topologyCoarseCoverIndexEquiv.symm true))
  · rw [Sieve.generate_le_iff]
    intro Y f hf
    cases hf with
    | mk i =>
        cases i
        · simpa [topologyDiamondSquare] using
            (Sieve.ofArrows_mk
              (Limits.pairFunction topologyDiamondSquare.X₂
                topologyDiamondSquare.X₃)
              (fun k => Limits.WalkingPair.casesOn k
                topologyDiamondSquare.f₂₄ topologyDiamondSquare.f₃₄)
              Limits.WalkingPair.left)
        · simpa [topologyDiamondSquare] using
            (Sieve.ofArrows_mk
              (Limits.pairFunction topologyDiamondSquare.X₂
                topologyDiamondSquare.X₃)
              (fun k => Limits.WalkingPair.casesOn k
                topologyDiamondSquare.f₂₄ topologyDiamondSquare.f₃₄)
              Limits.WalkingPair.right)

/-- The coarse Mayer--Vietoris square attached to the selected diamond. -/
private noncomputable def topologyCoarseMayerVietorisSquare :
    coarseTopology.MayerVietorisSquare := by
  apply GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    topologyDiamondSquare topologyDiamondSquare_isPullback
  rw [topologyDiamondSieve_eq_coarseCover]
  exact topologyCoarseCover_mem_coarseTopology

/-- The same diamond as a Mayer--Vietoris square for the fine topology. -/
private noncomputable def topologyFineMayerVietorisSquare :
    fineTopology.MayerVietorisSquare := by
  apply GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    topologyDiamondSquare topologyDiamondSquare_isPullback
  rw [topologyDiamondSieve_eq_coarseCover]
  exact (show coarseTopology ≤ fineTopology from le_sup_left)
    topologyBase topologyCoarseCover_mem_coarseTopology

private noncomputable def topologySheafificationComparisonIso :
    presheafToSheaf coarseTopology AddCommGrpCat.{1} ⋙
        coarseFineTopologyRefinement.fineSheafification ≅
      presheafToSheaf fineTopology AddCommGrpCat.{1} := by
  let adj₁ := (sheafificationAdjunction coarseTopology
    AddCommGrpCat.{1}).comp
      coarseFineTopologyRefinement.fineSheafificationAdjunction
  let adj₂ := sheafificationAdjunction fineTopology AddCommGrpCat.{1}
  exact adj₁.leftAdjointUniq adj₂

private noncomputable def topologyFreeYonedaIso
    (X : topologySite.category) :
    coarseFineTopologyRefinement.fineSheafification.obj
        ((presheafToSheaf coarseTopology AddCommGrpCat.{1}).obj
          (yoneda.obj X ⋙ AddCommGrpCat.free)) ≅
      (presheafToSheaf fineTopology AddCommGrpCat.{1}).obj
        (yoneda.obj X ⋙ AddCommGrpCat.free) :=
  topologySheafificationComparisonIso.app
    (yoneda.obj X ⋙ AddCommGrpCat.free)

private noncomputable def sheafifiedFreeYonedaHomAddEquiv
    {J : GrothendieckTopology topologySite.category}
    [HasSheafify J AddCommGrpCat.{1}]
    (X : topologySite.category)
    (F : Sheaf J AddCommGrpCat.{1}) :
    (((presheafToSheaf J AddCommGrpCat.{1}).obj
      (yoneda.obj X ⋙ AddCommGrpCat.free) ⟶ F) : Type 1) ≃+
      (F.val.obj (Opposite.op X) : Type 1) := by
  let e₁ := (sheafificationAdjunction J
    AddCommGrpCat.{1}).homAddEquiv
      (yoneda.obj X ⋙ AddCommGrpCat.free) F
  let e₂ := (AddCommGrpCat.adj.whiskerRight
    topologySite.categoryᵒᵖ).homEquiv (yoneda.obj X) F.val
  let e₃ : (yoneda.obj X ⟶ F.val ⋙ forget AddCommGrpCat) ≃
      (F.val ⋙ forget AddCommGrpCat).obj (Opposite.op X) :=
    yonedaEquiv
  exact
    { toFun := fun f => e₃ (e₂ (e₁ f))
      invFun := fun x => e₁.symm (e₂.symm (e₃.symm x))
      left_inv := by
        intro f
        change e₁.symm (e₂.symm (e₃.symm (e₃ (e₂ (e₁ f))))) = f
        rw [e₃.symm_apply_apply, e₂.symm_apply_apply,
          e₁.symm_apply_apply]
      right_inv := by
        intro x
        change e₃ (e₂ (e₁ (e₁.symm (e₂.symm (e₃.symm x))))) = x
        rw [e₁.apply_symm_apply, e₂.apply_symm_apply,
          e₃.apply_symm_apply]
      map_add' := by
        intro f g
        change e₃ (e₂ (e₁ (f + g))) =
          e₃ (e₂ (e₁ f)) + e₃ (e₂ (e₁ g))
        simp only [map_add]
        rfl }

private noncomputable def hPrimeZeroSectionEquiv
    {J : GrothendieckTopology topologySite.category}
    [HasSheafify J AddCommGrpCat.{1}]
    [HasExt.{2} (Sheaf J AddCommGrpCat.{1})]
    (X : topologySite.category)
    (F : Sheaf J AddCommGrpCat.{1}) :
    F.H' 0 X ≃+ (F.val.obj (Opposite.op X) : Type 1) :=
  Abelian.Ext.addEquiv₀.trans (sheafifiedFreeYonedaHomAddEquiv X F)

private noncomputable def topologyFineOverlapSectionOne :
    (topologyCoefficient.fine.val.obj
      (op topologyOverlapObject) : Type 1) := by
  change (topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
    (op topologyOverlapObject) : Type 1)
  exact topologyOverlapCoefficientEquiv.symm 1

private theorem topologyFineOverlapSectionOne_ne_zero :
    topologyFineOverlapSectionOne ≠ 0 := by
  intro h
  have := congrArg topologyOverlapCoefficientEquiv h
  simp [topologyFineOverlapSectionOne] at this

private noncomputable def topologyFineOverlapFreeHomOne :
    (presheafToSheaf fineTopology AddCommGrpCat.{1}).obj
        (yoneda.obj topologyOverlapObject ⋙ AddCommGrpCat.free) ⟶
      topologyCoefficient.fine :=
  (sheafifiedFreeYonedaHomAddEquiv topologyOverlapObject
    topologyCoefficient.fine).symm topologyFineOverlapSectionOne

private theorem topologyFineOverlapFreeHomOne_ne_zero :
    topologyFineOverlapFreeHomOne ≠ 0 := by
  intro h
  apply topologyFineOverlapSectionOne_ne_zero
  rw [← (sheafifiedFreeYonedaHomAddEquiv topologyOverlapObject
    topologyCoefficient.fine).apply_symm_apply
      topologyFineOverlapSectionOne]
  rw [show (sheafifiedFreeYonedaHomAddEquiv topologyOverlapObject
      topologyCoefficient.fine).symm topologyFineOverlapSectionOne =
      topologyFineOverlapFreeHomOne by rfl, h]
  simp

private noncomputable def topologyMappedOverlapHomOne :
    coarseFineTopologyRefinement.fineSheafification.obj
        ((presheafToSheaf coarseTopology AddCommGrpCat.{1}).obj
          (yoneda.obj topologyOverlapObject ⋙ AddCommGrpCat.free)) ⟶
      topologyCoefficient.fine :=
  (topologyFreeYonedaIso topologyOverlapObject).hom ≫
    topologyFineOverlapFreeHomOne

private theorem topologyMappedOverlapHomOne_ne_zero :
    topologyMappedOverlapHomOne ≠ 0 := by
  intro h
  apply topologyFineOverlapFreeHomOne_ne_zero
  rw [← cancel_epi (topologyFreeYonedaIso topologyOverlapObject).hom]
  simpa [topologyMappedOverlapHomOne] using h

private noncomputable def topologyCoarseOverlapHomOne :
    (presheafToSheaf coarseTopology AddCommGrpCat.{1}).obj
        (yoneda.obj topologyOverlapObject ⋙ AddCommGrpCat.free) ⟶
      topologyCoefficient.coarse :=
  coarseFineTopologyRefinement.fineSheafificationAdjunction.homEquiv
    _ _ topologyMappedOverlapHomOne

private theorem topologyFineSheafification_counit_app_eq
    (G : Sheaf fineTopology AddCommGrpCat.{1}) :
    coarseFineTopologyRefinement.fineSheafificationAdjunction.counit.app G =
      (sheafificationAdjunction fineTopology AddCommGrpCat.{1}).counit.app G := by
  simpa [CoverageTopologyRefinement.fineSheafificationAdjunction,
    CoverageTopologyRefinement.coarseRestriction] using
    (Adjunction.map_restrictFullyFaithful_counit_app
      (L := coarseFineTopologyRefinement.fineSheafification)
      (R := coarseFineTopologyRefinement.coarseRestriction)
      (sheafificationAdjunction fineTopology AddCommGrpCat.{1})
      (fullyFaithfulSheafToPresheaf coarseTopology AddCommGrpCat.{1})
      (Functor.FullyFaithful.id _)
      (Iso.refl (sheafToPresheaf coarseTopology AddCommGrpCat.{1} ⋙
        presheafToSheaf fineTopology AddCommGrpCat.{1}))
      (Iso.refl (Functor.id (Sheaf fineTopology AddCommGrpCat.{1}) ⋙
        sheafToPresheaf fineTopology AddCommGrpCat.{1})) G)

set_option maxHeartbeats 2000000 in
private theorem topologyCoarseOverlapHomOne_descends :
    coarseFineTopologyRefinement.fineSheafification.map
        topologyCoarseOverlapHomOne ≫
      (coarseFineTopologyRefinement.commonCoefficientIso
        topologyCoefficient).hom =
      topologyMappedOverlapHomOne := by
  let adj := coarseFineTopologyRefinement.fineSheafificationAdjunction
  let X := (presheafToSheaf coarseTopology AddCommGrpCat.{1}).obj
    (yoneda.obj topologyOverlapObject ⋙ AddCommGrpCat.free)
  let Y := topologyCoefficient.fine
  have hcoeff :
      (coarseFineTopologyRefinement.commonCoefficientIso
        topologyCoefficient).hom = adj.counit.app Y := by
    dsimp [CoverageTopologyRefinement.commonCoefficientIso, adj, Y]
    exact (topologyFineSheafification_counit_app_eq
      topologyCoefficient.fine).symm
  rw [hcoeff]
  rw [← adj.homEquiv_counit X Y topologyCoarseOverlapHomOne]
  exact (adj.homEquiv X Y).symm_apply_apply topologyMappedOverlapHomOne

private theorem topologyCoarseOverlapHomOne_ne_zero :
    topologyCoarseOverlapHomOne ≠ 0 := by
  intro h
  apply topologyMappedOverlapHomOne_ne_zero
  rw [← topologyCoarseOverlapHomOne_descends, h]
  simp

private noncomputable instance topologyCoarseMiddleHomSubsingleton :
    Subsingleton
      (((topologyCoarseMayerVietorisSquare.shortComplex.X₂ ⟶
        topologyCoefficient.coarse) : Type 1)) := by
  letI : Subsingleton
      (topologyCoefficient.coarse.val.obj (op topologyLeftObject) : Type 1) := by
    change Subsingleton
      (topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
        (op topologyLeftObject) : Type 1)
    exact topologyLeftCoefficient_subsingleton
  letI : Subsingleton
      (topologyCoefficient.coarse.val.obj (op topologyRightObject) : Type 1) := by
    change Subsingleton
      (topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
        (op topologyRightObject) : Type 1)
    exact topologyRightCoefficient_subsingleton
  constructor
  intro f g
  apply biprod.hom_ext'
  · apply (sheafifiedFreeYonedaHomAddEquiv topologyLeftObject
      topologyCoefficient.coarse).injective
    exact Subsingleton.elim _ _
  · apply (sheafifiedFreeYonedaHomAddEquiv topologyRightObject
      topologyCoefficient.coarse).injective
    exact Subsingleton.elim _ _

private noncomputable instance topologyCoarseMiddleExtZeroSubsingleton :
    Subsingleton
      (Abelian.Ext.{2} topologyCoarseMayerVietorisSquare.shortComplex.X₂
        topologyCoefficient.coarse 0) :=
  Abelian.Ext.addEquiv₀.toEquiv.subsingleton

private noncomputable def topologyCoarseOverlapExtZeroOne :
    Abelian.Ext.{2} topologyCoarseMayerVietorisSquare.shortComplex.X₁
      topologyCoefficient.coarse 0 :=
  Abelian.Ext.mk₀ topologyCoarseOverlapHomOne

private theorem topologyCoarseOverlapExtZeroOne_ne_zero :
    topologyCoarseOverlapExtZeroOne ≠ 0 := by
  intro h
  apply topologyCoarseOverlapHomOne_ne_zero
  exact (Abelian.Ext.mk₀_eq_zero_iff topologyCoarseOverlapHomOne).mp
    (by simpa [topologyCoarseOverlapExtZeroOne] using h)

private noncomputable def topologyCoarseConnectingClass :
    Abelian.Ext.{2} topologyCoarseMayerVietorisSquare.shortComplex.X₃
      topologyCoefficient.coarse 1 :=
  topologyCoarseMayerVietorisSquare.shortComplex_shortExact.extClass.comp
    topologyCoarseOverlapExtZeroOne rfl

private theorem topologyCoarseConnectingClass_ne_zero :
    topologyCoarseConnectingClass ≠ 0 := by
  exact extClass_precomp_ne_zero_of_middle_subsingleton
    topologyCoarseMayerVietorisSquare.shortComplex_shortExact
    topologyCoefficient.coarse topologyCoarseOverlapExtZeroOne
    topologyCoarseOverlapExtZeroOne_ne_zero

private noncomputable def topologyCoarseMayerVietorisGlobalClass :
    topologyCoefficient.coarse.H nonzeroDegree :=
  (Abelian.Ext.mk₀ topologyCoarseBaseConstantIso.inv).comp
    topologyCoarseConnectingClass rfl

private theorem topologyCoarseMayerVietorisGlobalClass_ne_zero :
    topologyCoarseMayerVietorisGlobalClass ≠ 0 := by
  intro h
  apply topologyCoarseConnectingClass_ne_zero
  have h' := congrArg
    (fun z => (Abelian.Ext.mk₀ topologyCoarseBaseConstantIso.hom).comp z rfl) h
  simpa [topologyCoarseMayerVietorisGlobalClass] using h'

private theorem topologyCoarseMayerVietorisGlobalClass_eq_source :
    topologyCoarseMayerVietorisGlobalClass = topologySourceHOneClass :=
  (topologyCoarseHOne_eq_zero_or_eq_source
    topologyCoarseMayerVietorisGlobalClass).resolve_left
      topologyCoarseMayerVietorisGlobalClass_ne_zero

private noncomputable def topologyMappedCoarseMayerVietorisShortExact :=
  topologyCoarseMayerVietorisSquare.shortComplex_shortExact.map_of_exact
    coarseFineTopologyRefinement.fineSheafification

private noncomputable instance topologyMappedMiddleHomSubsingleton :
    Subsingleton
      (((coarseFineTopologyRefinement.fineSheafification.obj
          topologyCoarseMayerVietorisSquare.shortComplex.X₂ ⟶
        topologyCoefficient.fine) : Type 1)) := by
  let R := coarseFineTopologyRefinement.coarseRestriction
  letI : Subsingleton
      (((topologyCoarseMayerVietorisSquare.shortComplex.X₂ ⟶
        R.obj topologyCoefficient.fine) : Type 1)) := by
    letI : Subsingleton
        ((R.obj topologyCoefficient.fine).val.obj
          (op topologyLeftObject) : Type 1) := by
      change Subsingleton
        (topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
          (op topologyLeftObject) : Type 1)
      exact topologyLeftCoefficient_subsingleton
    letI : Subsingleton
        ((R.obj topologyCoefficient.fine).val.obj
          (op topologyRightObject) : Type 1) := by
      change Subsingleton
        (topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
          (op topologyRightObject) : Type 1)
      exact topologyRightCoefficient_subsingleton
    constructor
    intro f g
    apply biprod.hom_ext'
    · apply (sheafifiedFreeYonedaHomAddEquiv topologyLeftObject
        (R.obj topologyCoefficient.fine)).injective
      exact Subsingleton.elim _ _
    · apply (sheafifiedFreeYonedaHomAddEquiv topologyRightObject
        (R.obj topologyCoefficient.fine)).injective
      exact Subsingleton.elim _ _
  exact (coarseFineTopologyRefinement.fineSheafificationAdjunction.homEquiv
    topologyCoarseMayerVietorisSquare.shortComplex.X₂
    topologyCoefficient.fine).subsingleton

private noncomputable instance topologyMappedMiddleExtZeroSubsingleton :
    Subsingleton
      (Abelian.Ext.{2}
        (coarseFineTopologyRefinement.fineSheafification.obj
          topologyCoarseMayerVietorisSquare.shortComplex.X₂)
        topologyCoefficient.fine 0) :=
  Abelian.Ext.addEquiv₀.toEquiv.subsingleton

private noncomputable def topologyMappedOverlapExtZeroOne :
    Abelian.Ext.{2}
      (coarseFineTopologyRefinement.fineSheafification.obj
        topologyCoarseMayerVietorisSquare.shortComplex.X₁)
      topologyCoefficient.fine 0 :=
  Abelian.Ext.mk₀ topologyMappedOverlapHomOne

private theorem topologyMappedOverlapExtZeroOne_ne_zero :
    topologyMappedOverlapExtZeroOne ≠ 0 := by
  intro h
  apply topologyMappedOverlapHomOne_ne_zero
  exact (Abelian.Ext.mk₀_eq_zero_iff topologyMappedOverlapHomOne).mp
    (by simpa [topologyMappedOverlapExtZeroOne] using h)

private noncomputable def topologyMappedConnectingClass :
    Abelian.Ext.{2}
      (coarseFineTopologyRefinement.fineSheafification.obj
        topologyCoarseMayerVietorisSquare.shortComplex.X₃)
      topologyCoefficient.fine 1 :=
  topologyMappedCoarseMayerVietorisShortExact.extClass.comp
    topologyMappedOverlapExtZeroOne rfl

private theorem topologyMappedConnectingClass_ne_zero :
    topologyMappedConnectingClass ≠ 0 := by
  letI : Subsingleton
      (Abelian.Ext.{2}
        (topologyCoarseMayerVietorisSquare.shortComplex.map
          coarseFineTopologyRefinement.fineSheafification).X₂
        topologyCoefficient.fine 0) := by
    change Subsingleton
      (Abelian.Ext.{2}
        (coarseFineTopologyRefinement.fineSheafification.obj
          topologyCoarseMayerVietorisSquare.shortComplex.X₂)
        topologyCoefficient.fine 0)
    infer_instance
  exact extClass_precomp_ne_zero_of_middle_subsingleton
    topologyMappedCoarseMayerVietorisShortExact topologyCoefficient.fine
    topologyMappedOverlapExtZeroOne topologyMappedOverlapExtZeroOne_ne_zero

private noncomputable instance topologyCoarseHasDerivedCategory :
    HasDerivedCategory.{2}
      (Sheaf topologySite.topology AddCommGrpCat.{1}) :=
  HasDerivedCategory.standard _

private noncomputable instance topologyFineHasDerivedCategory :
    HasDerivedCategory.{2}
      (Sheaf (topologySite.topology ⊔
        topologyAuxPrecoverage.toGrothendieck) AddCommGrpCat.{1}) :=
  HasDerivedCategory.standard _

private noncomputable instance topologyCoarseAliasHasDerivedCategory :
    HasDerivedCategory.{2} (Sheaf coarseTopology AddCommGrpCat.{1}) :=
  HasDerivedCategory.standard _

private noncomputable instance topologyFineAliasHasDerivedCategory :
    HasDerivedCategory.{2} (Sheaf fineTopology AddCommGrpCat.{1}) :=
  HasDerivedCategory.standard _

private noncomputable def topologyMappedConnectingImageClass :
    Abelian.Ext.{2}
      (coarseFineTopologyRefinement.fineSheafification.obj
        topologyCoarseMayerVietorisSquare.shortComplex.X₃)
      topologyCoefficient.fine 1 :=
  (topologyCoarseConnectingClass.mapExactFunctor
      coarseFineTopologyRefinement.fineSheafification).comp
    (Abelian.Ext.mk₀
      (coarseFineTopologyRefinement.commonCoefficientIso
        topologyCoefficient).hom) rfl

private theorem topologyMappedConnectingImageClass_eq :
    topologyMappedConnectingImageClass =
      (topologyCoarseMayerVietorisSquare.shortComplex_shortExact.extClass.mapExactFunctor
        coarseFineTopologyRefinement.fineSheafification).comp
        (Abelian.Ext.mk₀ topologyMappedOverlapHomOne) rfl := by
  letI := HasDerivedCategory.standard
    (Sheaf topologySite.topology AddCommGrpCat.{1})
  letI := HasDerivedCategory.standard
    (Sheaf (topologySite.topology ⊔
      topologyAuxPrecoverage.toGrothendieck) AddCommGrpCat.{1})
  dsimp [topologyMappedConnectingImageClass,
    topologyCoarseConnectingClass, topologyCoarseOverlapExtZeroOne]
  rw [Abelian.Ext.mapExactFunctor_postcomp_mk₀]
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀]
  rw [topologyCoarseOverlapHomOne_descends]

set_option maxRecDepth 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
private theorem topologyMappedConnectingImageClass_hom :
    topologyMappedConnectingImageClass.hom =
      (coarseFineTopologyRefinement.fineSheafification.mapDerivedCategorySingleFunctor
        0).inv.app
            topologyCoarseMayerVietorisSquare.shortComplex.X₃ ≫
        (CategoryTheory.topologySingleTriangleMapIso
          topologyCoarseMayerVietorisSquare.shortComplex_shortExact
          coarseFineTopologyRefinement.fineSheafification).hom.hom₃ ≫
        topologyMappedConnectingClass.hom := by
  letI := HasDerivedCategory.standard
    (Sheaf topologySite.topology AddCommGrpCat.{1})
  letI := HasDerivedCategory.standard
    (Sheaf (topologySite.topology ⊔
      topologyAuxPrecoverage.toGrothendieck) AddCommGrpCat.{1})
  rw [topologyMappedConnectingImageClass_eq]
  simp only [Abelian.Ext.comp_hom]
  rw [CategoryTheory.topologyExtClassMapExactFunctorHomConjugation]
  rw [show topologyMappedConnectingClass =
      topologyMappedCoarseMayerVietorisShortExact.extClass.comp
        (Abelian.Ext.mk₀ topologyMappedOverlapHomOne) rfl by rfl]
  rw [Abelian.Ext.comp_hom]
  simp only [ShiftedHom.comp, Category.assoc]
  rfl

private theorem topologyMappedConnectingImageClass_ne_zero :
    topologyMappedConnectingImageClass ≠ 0 := by
  intro h
  apply topologyMappedConnectingClass_ne_zero
  apply Abelian.Ext.ext
  simp only [Abelian.Ext.zero_hom]
  have hz := congrArg (fun z => z.hom) h
  change topologyMappedConnectingImageClass.hom =
    (0 : Abelian.Ext.{2}
      (coarseFineTopologyRefinement.fineSheafification.obj
        topologyCoarseMayerVietorisSquare.shortComplex.X₃)
      topologyCoefficient.fine 1).hom at hz
  rw [topologyMappedConnectingImageClass_hom] at hz
  simp only [Abelian.Ext.zero_hom] at hz
  apply (cancel_epi
    (CategoryTheory.topologySingleTriangleMapIso
      topologyCoarseMayerVietorisSquare.shortComplex_shortExact
      coarseFineTopologyRefinement.fineSheafification).hom.hom₃).mp
  apply (cancel_epi
    ((coarseFineTopologyRefinement.fineSheafification.mapDerivedCategorySingleFunctor
      0).inv.app
        topologyCoarseMayerVietorisSquare.shortComplex.X₃)).mp
  simpa only [Category.assoc, comp_zero] using hz

private noncomputable def topologyFineConstantToMappedBaseIso :
    (constantSheaf fineTopology AddCommGrpCat.{1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ≅
      coarseFineTopologyRefinement.fineSheafification.obj
        topologyCoarseMayerVietorisSquare.shortComplex.X₃ :=
  (coarseFineTopologyRefinement.constantSheafIso).symm ≪≫
    coarseFineTopologyRefinement.fineSheafification.mapIso
      topologyCoarseBaseConstantIso.symm

private noncomputable def topologyMappedGlobalClass :
    topologyCoefficient.fine.H nonzeroDegree :=
  (Abelian.Ext.mk₀ topologyFineConstantToMappedBaseIso.hom).comp
    topologyMappedConnectingClass rfl

private theorem topologyMappedGlobalClass_ne_zero :
    topologyMappedGlobalClass ≠ 0 := by
  intro h
  apply topologyMappedConnectingClass_ne_zero
  have h' := congrArg
    (fun z => (Abelian.Ext.mk₀ topologyFineConstantToMappedBaseIso.inv).comp z rfl) h
  simpa [topologyMappedGlobalClass] using h'

private noncomputable def topologyMappedImageGlobalClass :
    topologyCoefficient.fine.H nonzeroDegree :=
  (Abelian.Ext.mk₀ topologyFineConstantToMappedBaseIso.hom).comp
    topologyMappedConnectingImageClass rfl

private theorem topologyMappedImageGlobalClass_ne_zero :
    topologyMappedImageGlobalClass ≠ 0 := by
  intro h
  apply topologyMappedConnectingImageClass_ne_zero
  have h' := congrArg
    (fun z => (Abelian.Ext.mk₀ topologyFineConstantToMappedBaseIso.inv).comp z rfl) h
  simpa [topologyMappedImageGlobalClass] using h'

private theorem topologySheafHMap_on_coarseMayerVietorisGlobalClass :
    coarseFineTopologyRefinement.sheafHMap topologyCoefficient
        nonzeroDegree topologyCoarseMayerVietorisGlobalClass =
      topologyMappedImageGlobalClass := by
  change
    ((Abelian.Ext.mk₀ coarseFineTopologyRefinement.constantSheafIso.inv).comp
      (((Abelian.Ext.mk₀ topologyCoarseBaseConstantIso.inv).comp
        topologyCoarseConnectingClass rfl).mapExactFunctor
          coarseFineTopologyRefinement.fineSheafification) rfl).comp
      (Abelian.Ext.mk₀
        (coarseFineTopologyRefinement.commonCoefficientIso
          topologyCoefficient).hom) rfl =
    (Abelian.Ext.mk₀
      (coarseFineTopologyRefinement.constantSheafIso.inv ≫
        coarseFineTopologyRefinement.fineSheafification.map
          topologyCoarseBaseConstantIso.inv)).comp
      ((topologyCoarseConnectingClass.mapExactFunctor
          coarseFineTopologyRefinement.fineSheafification).comp
        (Abelian.Ext.mk₀
          (coarseFineTopologyRefinement.commonCoefficientIso
            topologyCoefficient).hom) rfl) rfl
  rw [Abelian.Ext.mapExactFunctor_precomp_mk₀]
  simp only [Abelian.Ext.mk₀_comp_mk₀_assoc,
    Abelian.Ext.comp_assoc_of_third_deg_zero]

private theorem topologySheafHMap_on_sourceClass_ne_zero :
    coarseFineTopologyRefinement.sheafHMap topologyCoefficient
        nonzeroDegree topologySourceHOneClass ≠ 0 := by
  rw [← topologyCoarseMayerVietorisGlobalClass_eq_source,
    topologySheafHMap_on_coarseMayerVietorisGlobalClass]
  exact topologyMappedImageGlobalClass_ne_zero

private noncomputable def topologyFineOverlapHPrimeZeroEquiv :
    topologyCoefficient.fine.H' 0 topologyOverlapObject ≃+ ZMod 2 :=
  (hPrimeZeroSectionEquiv topologyOverlapObject
    topologyCoefficient.fine).trans topologyOverlapCoefficientEquiv

private noncomputable def topologyFineOverlapHPrimeZeroOne :
    topologyCoefficient.fine.H' 0 topologyOverlapObject :=
  topologyFineOverlapHPrimeZeroEquiv.symm 1

private theorem topologyFineOverlapHPrimeZeroOne_ne_zero :
    topologyFineOverlapHPrimeZeroOne ≠ 0 := by
  intro h
  have := congrArg topologyFineOverlapHPrimeZeroEquiv h
  simp [topologyFineOverlapHPrimeZeroOne] at this

private noncomputable instance topologyFineLeftHPrimeZeroSubsingleton :
    Subsingleton (topologyCoefficient.fine.H' 0 topologyLeftObject) :=
  by
    letI : Subsingleton
        (topologyCoefficient.fine.val.obj (op topologyLeftObject) : Type 1) := by
      change Subsingleton
        (topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
          (op topologyLeftObject) : Type 1)
      exact topologyLeftCoefficient_subsingleton
    exact (hPrimeZeroSectionEquiv topologyLeftObject
      topologyCoefficient.fine).toEquiv.subsingleton

private noncomputable instance topologyFineRightHPrimeZeroSubsingleton :
    Subsingleton (topologyCoefficient.fine.H' 0 topologyRightObject) :=
  by
    letI : Subsingleton
        (topologyCoefficient.fine.val.obj (op topologyRightObject) : Type 1) := by
      change Subsingleton
        (topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
          (op topologyRightObject) : Type 1)
      exact topologyRightCoefficient_subsingleton
    exact (hPrimeZeroSectionEquiv topologyRightObject
      topologyCoefficient.fine).toEquiv.subsingleton

private theorem topologyFineMayerVietoris_fromBiprod_zero :
    topologyFineMayerVietorisSquare.fromBiprod
      topologyCoefficient.fine 0 = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change
    ((topologyCoefficient.fine.H' 0 topologyLeftObject ⊞
      topologyCoefficient.fine.H' 0 topologyRightObject :
        AddCommGrpCat.{2}) : Type 2) at x
  have hx : x = 0 := by
    apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  rw [hx]
  simp

private noncomputable instance topologyFineMayerVietoris_delta_mono :
    Mono (topologyFineMayerVietorisSquare.δ
      topologyCoefficient.fine 0 1 rfl) :=
  ((topologyFineMayerVietorisSquare.sequence_exact
    topologyCoefficient.fine 0 1 rfl).exact 1).mono_g
      topologyFineMayerVietoris_fromBiprod_zero

private theorem topologyFineMayerVietoris_delta_one_ne_zero :
    topologyFineMayerVietorisSquare.δ topologyCoefficient.fine
      0 1 rfl topologyFineOverlapHPrimeZeroOne ≠ 0 := by
  intro h
  apply topologyFineOverlapHPrimeZeroOne_ne_zero
  apply (AddCommGrpCat.mono_iff_injective
    (topologyFineMayerVietorisSquare.δ
      topologyCoefficient.fine 0 1 rfl)).mp inferInstance
  simpa using h

private theorem topologyFineHOne_eq_zero_or_eq_target
    (y : topologyCoefficient.fine.H nonzeroDegree) :
    y = 0 ∨ y = topologyTargetHOneClass := by
  let x := topologyCechToFineHOneEquiv.symm y
  rcases topologyCechHOne_eq_zero_or_eq_one x with hx | hx
  · left
    dsimp [x] at hx
    rw [← topologyCechToFineHOneEquiv.apply_symm_apply y, hx]
    simp
  · right
    dsimp [x] at hx
    rw [← topologyCechToFineHOneEquiv.apply_symm_apply y, hx]
    rfl

private noncomputable def topologyFineMayerVietorisGlobalClass :
    topologyCoefficient.fine.H nonzeroDegree :=
  Cohomology.terminalHComparison topologyCoefficient.fine
    topologyBase topologyBaseIsTerminal 1
    (topologyFineMayerVietorisSquare.δ topologyCoefficient.fine
      0 1 rfl topologyFineOverlapHPrimeZeroOne)

private theorem topologyFineMayerVietorisGlobalClass_ne_zero :
    topologyFineMayerVietorisGlobalClass ≠ 0 := by
  intro h
  let e := Cohomology.terminalHComparison topologyCoefficient.fine
    topologyBase topologyBaseIsTerminal 1
  change e (topologyFineMayerVietorisSquare.δ topologyCoefficient.fine
    0 1 rfl topologyFineOverlapHPrimeZeroOne) = 0 at h
  have hmap :
      e (topologyFineMayerVietorisSquare.δ topologyCoefficient.fine
        0 1 rfl topologyFineOverlapHPrimeZeroOne) = e 0 := by
    simpa only [map_zero] using h
  exact topologyFineMayerVietoris_delta_one_ne_zero (e.injective hmap)

private theorem topologyFineMayerVietorisGlobalClass_eq_target :
    topologyFineMayerVietorisGlobalClass = topologyTargetHOneClass :=
  (topologyFineHOne_eq_zero_or_eq_target
    topologyFineMayerVietorisGlobalClass).resolve_left
      topologyFineMayerVietorisGlobalClass_ne_zero

private theorem topologyMappedImageGlobalClass_eq_target :
    topologyMappedImageGlobalClass = topologyTargetHOneClass :=
  (topologyFineHOne_eq_zero_or_eq_target
    topologyMappedImageGlobalClass).resolve_left
      topologyMappedImageGlobalClass_ne_zero

private theorem topologyMappedImageGlobalClass_eq_fineMayerVietorisGlobalClass :
    topologyMappedImageGlobalClass =
      topologyFineMayerVietorisGlobalClass := by
  rw [topologyMappedImageGlobalClass_eq_target,
    topologyFineMayerVietorisGlobalClass_eq_target]

private theorem topologySheafHMapCompCech_on_explicit_class :
    ((coarseFineTopologyRefinement.sheafHMap topologyCoefficient
      nonzeroDegree).comp
        (Cohomology.cechToSheafH topologyCoarseCover
          topologyObstructionSheaf topologyBaseIsTerminal
          topologyCoarseLerayCover nonzeroDegree)) topologyCechOneClass =
      topologyTargetHOneClass := by
  change coarseFineTopologyRefinement.sheafHMap topologyCoefficient
      nonzeroDegree topologySourceHOneClass = topologyTargetHOneClass
  rw [← topologyCoarseMayerVietorisGlobalClass_eq_source,
    topologySheafHMap_on_coarseMayerVietorisGlobalClass,
    topologyMappedImageGlobalClass_eq_fineMayerVietorisGlobalClass,
    topologyFineMayerVietorisGlobalClass_eq_target]

/--
The independent fine injective-resolution comparison agrees with the actual
Ext map induced by fine sheafification.
-/
theorem topologyCechToFineHOneEquiv_eq_sheafHMap_comp_cech :
    topologyCechToFineHOneEquiv.toAddMonoidHom =
      (coarseFineTopologyRefinement.sheafHMap
        topologyCoefficient nonzeroDegree).comp
        (Cohomology.cechToSheafH topologyCoarseCover
          topologyObstructionSheaf topologyBaseIsTerminal
          topologyCoarseLerayCover nonzeroDegree) := by
  apply AddMonoidHom.ext
  intro x
  rcases topologyCechHOne_eq_zero_or_eq_one x with hx | hx
  · rw [hx]
    simp
  · rw [hx]
    exact topologySheafHMapCompCech_on_explicit_class.symm

/-- The actual topology-change map carries the explicit source class to the fine class. -/
theorem topologySheafHMap_on_sourceClass :
    coarseFineTopologyRefinement.sheafHMap
        topologyCoefficient nonzeroDegree topologySourceHOneClass =
      topologyTargetHOneClass := by
  have h := DFunLike.congr_fun
    topologyCechToFineHOneEquiv_eq_sheafHMap_comp_cech
    topologyCechOneClass
  simpa [topologySourceHOneClass, topologyTargetHOneClass] using h.symm

/-- The strict topology change induces a nonzero map on actual degree-one sheaf cohomology. -/
theorem coarseFineSheafHMap_nonzero :
    coarseFineTopologyRefinement.sheafHMap
      topologyCoefficient nonzeroDegree ≠ 0 := by
  intro h
  apply topologySheafHMap_on_sourceClass_ne_zero
  have h' := DFunLike.congr_fun h topologySourceHOneClass
  simpa using h'

/--
The complete degree-one firing package records strictness, properness of the
fine topology, the nonzero fine class, and the nonzero topology-change map.
-/
theorem topologyActualHOneFiring :
    coarseTopology ≠ fineTopology ∧
      fineTopology ≠ ⊤ ∧
      topologyTargetHOneClass ≠ 0 ∧
      coarseFineTopologyRefinement.sheafHMap
        topologyCoefficient nonzeroDegree ≠ 0 := by
  exact ⟨coarseFineTopology_strict, fineTopology_ne_top,
    topologyTargetHOneClass_ne_zero, coarseFineSheafHMap_nonzero⟩

end AAT.AG.ReadingFunctorialityFinite
