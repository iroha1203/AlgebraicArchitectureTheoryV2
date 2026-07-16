import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Exact-functor coherence for Ext

This module proves the identity, natural-isomorphism, and composition laws for
the exact-functor action on `Abelian.Ext` used by reading functoriality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization

universe u₁ v₁ u₂ v₂ w₁ w₂ w₃ t₁ t₂

namespace CategoryTheory

/-- Uniqueness of a left adjoint is compatible with precomposition by an adjunction. -/
lemma Adjunction.comp_leftAdjointUniq_hom_app
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁}
    {H H' : C₂ ⥤ C₃} {I : C₃ ⥤ C₂}
    (a₀ : F ⊣ G) (a₁ : H ⊣ I) (a₂ : H' ⊣ I) (X : C₁) :
    ((a₀.comp a₁).leftAdjointUniq (a₀.comp a₂)).hom.app X =
      (a₁.leftAdjointUniq a₂).hom.app (F.obj X) := by
  apply ((a₀.comp a₁).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.comp_unit_app, Adjunction.comp_homEquiv]
  change a₀.unit.app X ≫ G.map (a₂.unit.app (F.obj X)) =
    a₀.homEquiv X _
      (a₁.homEquiv (F.obj X) _
        ((a₁.leftAdjointUniq a₂).hom.app (F.obj X)))
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [a₀.homEquiv_unit]

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
variable (F G : C ⥤ D)
variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/--
The derived-category isomorphism induced by an isomorphism of exact functors.

Implementation notes: this uses `Localization.liftNatIso` with the same
single-complex presentation as `mapDerivedCategory`.  An arbitrary derived
natural isomorphism would not expose the single-object compatibility needed by
the Ext naturality proof below.
-/
noncomputable def exactFunctorDerivedIso (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
      DerivedCategory.Q)

omit [HasDerivedCategory C] [HasDerivedCategory D]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] in
/-- Naturality of the single-complex comparison under an exact-functor isomorphism. -/
lemma singleMapHomologicalComplex_iso_naturality (e : F ≅ G) (X : C) :
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X ≫
        (CochainComplex.singleFunctor D 0).map (e.hom.app X) =
      (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app
          ((CochainComplex.singleFunctor C 0).obj X) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app X := by
  ext i
  simp only [HomologicalComplex.comp_f]
  by_cases hi : i = 0
  · subst i
    have hs :
        ((CochainComplex.singleFunctor D 0).map (e.hom.app X)).f 0 =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj X)).hom ≫
            e.hom.app X ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj X)).inv :=
      HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 (e.hom.app X)
    rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      hs, HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    change _ = e.hom.app (((CochainComplex.singleFunctor C 0).obj X).X 0) ≫ _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact e.hom.naturality_assoc
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj X)).inv
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne, hi]

/-- Compatibility of `exactFunctorDerivedIso` with the single-object comparison. -/
lemma exactFunctorDerivedIso_single_hom (e : F ≅ G) (X : C) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctor D 0).map (e.hom.app X) =
      (exactFunctorDerivedIso F G e).hom.app
          ((DerivedCategory.singleFunctor C 0).obj X) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app X := by
  dsimp [exactFunctorDerivedIso, Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ]
  change _ =
    (Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      F.mapDerivedCategory G.mapDerivedCategory
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
        DerivedCategory.Q).hom).app
          (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X)) ≫ _
  rw [Localization.liftNatTrans_app]
  simp only [Functor.map_id, Category.id_comp]
  have hF :
      (Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
        (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
        F.mapDerivedCategory).hom = F.mapDerivedCategoryFactors.hom := rfl
  have hG :
      (Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
        (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
        G.mapDerivedCategory).inv = G.mapDerivedCategoryFactors.inv := rfl
  rw [hF, hG]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [cancel_epi (F.mapDerivedCategoryFactors.hom.app
    ((CochainComplex.singleFunctor C 0).obj X))]
  have hsingle :
      (DerivedCategory.singleFunctor D 0).map (e.hom.app X) =
        DerivedCategory.Q.map
          ((CochainComplex.singleFunctor D 0).map (e.hom.app X)) := rfl
  have hwhisker :
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
        DerivedCategory.Q).hom.app
          ((CochainComplex.singleFunctor C 0).obj X) =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app
            ((CochainComplex.singleFunctor C 0).obj X)) := rfl
  rw [hsingle, hwhisker]
  erw [Category.comp_id, Category.id_comp]
  simpa only [Functor.map_comp] using congrArg
    (fun f => DerivedCategory.Q.map f)
    (singleMapHomologicalComplex_iso_naturality F G e X)

/-- Shift compatibility for the homological-complex map of a natural isomorphism. -/
noncomputable instance mapHomologicalComplexNatTrans_commShift (e : F ≅ G) :
    NatTrans.CommShift
      (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)) ℤ := by
  constructor
  intro n
  ext K i
  simp [Functor.mapHomologicalComplex_commShiftIso_eq,
    Functor.mapCochainComplexShiftIso, NatTrans.mapHomologicalComplex]

example (e : F ≅ G) : NatTrans.CommShift
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
      DerivedCategory.Q).hom ℤ := by
  change NatTrans.CommShift
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ))
      DerivedCategory.Q) ℤ
  infer_instance

example : NatTrans.CommShift F.mapDerivedCategoryFactors.hom ℤ := by
  infer_instance

example : NatTrans.CommShift G.mapDerivedCategoryFactors.inv ℤ := by
  infer_instance

/-- Shift compatibility for the derived isomorphism of exact functors. -/
noncomputable instance exactFunctorDerivedIso_hom_commShift (e : F ≅ G) :
    NatTrans.CommShift (exactFunctorDerivedIso F G e).hom ℤ := by
  let τ := (exactFunctorDerivedIso F G e).hom
  let σ := (Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
    DerivedCategory.Q).hom
  have hpre : Functor.whiskerLeft DerivedCategory.Q τ =
      F.mapDerivedCategoryFactors.hom ≫ σ ≫
        G.mapDerivedCategoryFactors.inv := by
    ext K
    dsimp [τ, σ, exactFunctorDerivedIso]
    rw [Localization.liftNatTrans_app]
    rfl
  haveI hσ : NatTrans.CommShift σ ℤ := by
    dsimp [σ]
    change NatTrans.CommShift
      (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ))
        DerivedCategory.Q) ℤ
    infer_instance
  haveI hpreComm : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Q τ) ℤ := by
    rw [hpre]
    infer_instance
  constructor
  intro n
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
  intro K
  change
    (F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj K) ≫
        (shiftFunctor (DerivedCategory D) n).map (τ.app (DerivedCategory.Q.obj K)) =
      τ.app ((DerivedCategory.Q.obj K)⟦n⟧) ≫
        (G.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj K)
  rw [← cancel_epi (F.mapDerivedCategory.map
    ((DerivedCategory.Q.commShiftIso n).hom.app K))]
  erw [τ.naturality_assoc]
  simpa only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Category.assoc] using
      (NatTrans.shift_app_comm
        (Functor.whiskerLeft DerivedCategory.Q τ) n K)

/-- Inverse-form single-object compatibility for `exactFunctorDerivedIso`. -/
@[reassoc]
lemma exactFunctorDerivedIso_single_inv (e : F ≅ G) (X : C) :
    (DerivedCategory.singleFunctor D 0).map (e.hom.app X) ≫
        (G.mapDerivedCategorySingleFunctor 0).inv.app X =
      (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        (exactFunctorDerivedIso F G e).hom.app
          ((DerivedCategory.singleFunctor C 0).obj X) := by
  rw [← cancel_epi ((F.mapDerivedCategorySingleFunctor 0).hom.app X)]
  rw [← Category.assoc, exactFunctorDerivedIso_single_hom F G e X]
  simp

/-- Mapping a shifted hom commutes with a shift-compatible natural transformation. -/
@[reassoc]
lemma ShiftedHom.map_natTrans_commShift
    {E₁ E₂ : Type*} [Category* E₁] [Category* E₂]
    [HasShift E₁ ℤ] [HasShift E₂ ℤ]
    (H K : E₁ ⥤ E₂) [H.CommShift ℤ] [K.CommShift ℤ]
    (τ : H ⟶ K) [NatTrans.CommShift τ ℤ]
    {X Y : E₁} {n : ℤ} (a : ShiftedHom X Y n) :
    τ.app X ≫ a.map K = a.map H ≫ (shiftFunctor E₂ n).map (τ.app Y) := by
  dsimp [ShiftedHom.map]
  rw [← τ.naturality_assoc]
  rw [NatTrans.app_shift]
  simp

section

variable [HasExt.{w₁} C] [HasExt.{w₂} D]

/-- Ext mapping is natural under an isomorphism of exact functors. -/
lemma mapExactFunctor_iso_naturality
    (e : F ≅ G)
    [NatTrans.CommShift (exactFunctorDerivedIso F G e).hom ℤ]
    {X Y : C} {n : Nat} (a : Abelian.Ext.{w₁} X Y n) :
    (Abelian.Ext.mk₀ (e.hom.app X)).comp (a.mapExactFunctor G) (zero_add n) =
      (a.mapExactFunctor F).comp (Abelian.Ext.mk₀ (e.hom.app Y)) (add_zero n) := by
  ext
  simp only [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
    Abelian.Ext.mapExactFunctor_hom]
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  rw [exactFunctorDerivedIso_single_inv_assoc F G e X]
  simp only [Category.assoc]
  rw [ShiftedHom.map_natTrans_commShift_assoc F.mapDerivedCategory G.mapDerivedCategory
    (exactFunctorDerivedIso F G e).hom a.hom]
  slice_lhs 3 5 =>
    rw [← Functor.map_comp, ← exactFunctorDerivedIso_single_hom F G e Y]
  slice_rhs 3 4 =>
    rw [← Functor.map_comp]

end

/-- Shift compatibility for the identity homological-complex comparison. -/
noncomputable instance mapHomologicalComplexIdIso_hom_commShift
    {E : Type u₁} [Category.{v₁} E] [Abelian E] :
    NatTrans.CommShift
      (Functor.mapHomologicalComplexIdIso E (ComplexShape.up ℤ)).hom ℤ := by
  constructor
  intro n
  ext K i
  simp [Functor.mapHomologicalComplexIdIso,
    Functor.mapHomologicalComplex_commShiftIso_eq,
    Functor.mapCochainComplexShiftIso]

/-- Mapping Ext through the identity exact functor is the identity. -/
lemma Abelian.Ext.mapExactFunctor_id
    {E : Type u₁} [Category.{v₁} E] [Abelian E]
    [HasExt.{w₁} E]
    {X Y : E} {n : Nat} (a : Abelian.Ext.{w₁} X Y n) :
    a.mapExactFunctor (Functor.id E) = a := by
  letI := HasDerivedCategory.standard E
  let Φ := (Functor.id E).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)
  let e : Φ.functor ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ Functor.id (DerivedCategory E) :=
    Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexIdIso E (ComplexShape.up ℤ))
        DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q ≪≫
        (Functor.rightUnitor DerivedCategory.Q).symm
  letI : NatTrans.CommShift e.hom ℤ := by
    dsimp [e]
    infer_instance
  have hsingleHom (Z : E) :
      (HomologicalComplex.singleMapHomologicalComplex
          (Functor.id E) (ComplexShape.up ℤ) 0).hom.app Z =
        (Functor.mapHomologicalComplexIdIso E (ComplexShape.up ℤ)).hom.app
          ((CochainComplex.singleFunctor E 0).obj Z) := by
    ext i
    by_cases hi : i = 0
    · subst i
      rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
      change (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℤ) 0 Z).hom ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℤ) 0 Z).inv = 𝟙 _
      simp
    · rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne
        (F := Functor.id E) (c := ComplexShape.up ℤ) hi Z]
      apply (HomologicalComplex.isZero_single_obj_X
        (c := ComplexShape.up ℤ) 0 Z i hi).eq_of_tgt
  have hsingleIso (Z : E) :
      (HomologicalComplex.singleMapHomologicalComplex
          (Functor.id E) (ComplexShape.up ℤ) 0).app Z =
        (Functor.mapHomologicalComplexIdIso E (ComplexShape.up ℤ)).app
          ((CochainComplex.singleFunctor E 0).obj Z) := by
    apply Iso.ext
    exact hsingleHom Z
  have hsingleInv (Z : E) :
      (HomologicalComplex.singleMapHomologicalComplex
          (Functor.id E) (ComplexShape.up ℤ) 0).inv.app Z =
        (Functor.mapHomologicalComplexIdIso E (ComplexShape.up ℤ)).inv.app
          ((CochainComplex.singleFunctor E 0).obj Z) := by
    exact congrArg Iso.inv (hsingleIso Z)
  change Φ.smallShiftedHomMap
      (((Functor.id E).mapCochainComplexSingleFunctor 0).app X)
      (((Functor.id E).mapCochainComplexSingleFunctor 0).app Y) a = a
  apply (SmallShiftedHom.equiv
    (HomologicalComplex.quasiIso E (ComplexShape.up ℤ))
    DerivedCategory.Q).injective
  rw [Φ.equiv_smallShiftedHomMap DerivedCategory.Q DerivedCategory.Q
    (((Functor.id E).mapCochainComplexSingleFunctor 0).app X)
    (((Functor.id E).mapCochainComplexSingleFunctor 0).app Y)
    (Functor.id (DerivedCategory E)) e a]
  dsimp [Φ, e]
  rw [← hsingleHom X, ← hsingleInv Y]
  simp [Functor.mapCochainComplexSingleFunctor, ← Functor.map_comp]
  rw [show DerivedCategory.Q.map
      (𝟙 ((HomologicalComplex.single E (ComplexShape.up ℤ) 0).obj Y)) = 𝟙 _ by
    exact DerivedCategory.Q.map_id _]
  apply ShiftedHom.comp_mk₀_id

/-- Exact-functor mapping commutes with degree-zero precomposition. -/
lemma Abelian.Ext.mapExactFunctor_precomp_mk₀
    [HasExt.{w₁} C] [HasExt.{w₂} D]
    {X' X Y : C} {n : Nat} (f : X' ⟶ X)
    (a : Abelian.Ext.{w₁} X Y n) :
    ((Abelian.Ext.mk₀ f).comp a (zero_add n)).mapExactFunctor F =
      (Abelian.Ext.mk₀ (F.map f)).comp (a.mapExactFunctor F)
        (zero_add n) := by
  ext
  simp only [Abelian.Ext.mapExactFunctor_hom, Abelian.Ext.comp_hom,
    Abelian.Ext.mk₀_hom]
  rw [ShiftedHom.mk₀_comp, ShiftedHom.mk₀_comp]
  dsimp [ShiftedHom.map]
  simp only [Functor.map_comp, Category.assoc]
  have hnat :
      (F.mapDerivedCategorySingleFunctor 0).inv.app X' ≫
          F.mapDerivedCategory.map
            ((DerivedCategory.singleFunctor C 0).map f) =
        (DerivedCategory.singleFunctor D 0).map (F.map f) ≫
          (F.mapDerivedCategorySingleFunctor 0).inv.app X :=
    ((F.mapDerivedCategorySingleFunctor 0).inv.naturality f).symm
  slice_lhs 1 2 => rw [hnat]
  simp only [Category.assoc]

/-- Exact-functor mapping commutes with degree-zero postcomposition. -/
lemma Abelian.Ext.mapExactFunctor_postcomp_mk₀
    [HasExt.{w₁} C] [HasExt.{w₂} D]
    {X Y Y' : C} {n : Nat} (a : Abelian.Ext.{w₁} X Y n)
    (g : Y ⟶ Y') :
    (a.comp (Abelian.Ext.mk₀ g) (add_zero n)).mapExactFunctor F =
      (a.mapExactFunctor F).comp (Abelian.Ext.mk₀ (F.map g))
        (add_zero n) := by
  ext
  simp only [Abelian.Ext.mapExactFunctor_hom, Abelian.Ext.comp_hom,
    Abelian.Ext.mk₀_hom]
  rw [ShiftedHom.comp_mk₀, ShiftedHom.comp_mk₀]
  dsimp [ShiftedHom.map]
  simp only [Functor.map_comp, Category.assoc]
  erw [(F.mapDerivedCategory.commShiftIso (n : ℤ)).hom.naturality_assoc]
  rw [Functor.comp_map]
  have hshift :
      (shiftFunctor (DerivedCategory D) (n : ℤ)).map
            (F.mapDerivedCategory.map
              ((DerivedCategory.singleFunctor C 0).map g)) ≫
          (shiftFunctor (DerivedCategory D) (n : ℤ)).map
            ((F.mapDerivedCategorySingleFunctor 0).hom.app Y') =
        (shiftFunctor (DerivedCategory D) (n : ℤ)).map
            ((F.mapDerivedCategorySingleFunctor 0).hom.app Y) ≫
          (shiftFunctor (DerivedCategory D) (n : ℤ)).map
            ((DerivedCategory.singleFunctor D 0).map (F.map g)) := by
    simpa only [Functor.map_comp] using congrArg
      (fun k => (shiftFunctor (DerivedCategory D) (n : ℤ)).map k)
      ((F.mapDerivedCategorySingleFunctor 0).hom.naturality g)
  slice_lhs 4 5 => rw [hshift]

section ExactFunctorComp

variable {E₁ : Type u₁} [Category.{v₁} E₁] [Abelian E₁]
variable {E₂ : Type u₂} [Category.{v₂} E₂] [Abelian E₂]
variable {E₃ : Type*} [Category* E₃] [Abelian E₃]
variable [HasDerivedCategory E₁] [HasDerivedCategory E₂]
  [HasDerivedCategory E₃]
variable (H : E₁ ⥤ E₂) (K : E₂ ⥤ E₃)
variable [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
variable [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
variable [(H ⋙ K).Additive]
  [PreservesFiniteLimits (H ⋙ K)] [PreservesFiniteColimits (H ⋙ K)]

/--
The canonical comparison between direct and iterated derived exact functors.

Implementation notes: the factor is assembled from the existing localization
factors and associators, so its components retain the concrete comparison used
by the Ext composition proof.  Choosing an opaque lifting isomorphism would
lose that component formula.
-/
noncomputable def exactFunctorCompFactors :
    DerivedCategory.Q ⋙ (H.mapDerivedCategory ⋙ K.mapDerivedCategory) ≅
      (H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (Functor.associator DerivedCategory.Q H.mapDerivedCategory
      K.mapDerivedCategory).symm ≪≫
    Functor.isoWhiskerRight H.mapDerivedCategoryFactors
      K.mapDerivedCategory ≪≫
    Functor.associator (H.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q K.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (H.mapHomologicalComplex (ComplexShape.up ℤ))
      K.mapDerivedCategoryFactors ≪≫
    (Functor.associator
      (H.mapHomologicalComplex (ComplexShape.up ℤ))
      (K.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q).symm

/--
Derived-category comparison for a composite of exact functors.

Implementation notes: the explicit factor above is installed as the
localization lifting before applying `Localization.liftNatIso`.  This fixes the
direct-to-iterated comparison to the same presentation used by
`mapExactFunctor`, rather than introducing an unrelated derived equivalence.
-/
noncomputable def exactFunctorCompDerivedIso :
    (H ⋙ K).mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ K.mapDerivedCategory := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso E₁ (ComplexShape.up ℤ))
      ((H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
      (H.mapDerivedCategory ⋙ K.mapDerivedCategory) :=
    ⟨exactFunctorCompFactors H K⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso E₁ (ComplexShape.up ℤ))
    ((H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    ((H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    (H ⋙ K).mapDerivedCategory
    (H.mapDerivedCategory ⋙ K.mapDerivedCategory) (Iso.refl _)

/-- Shift compatibility for the iterated derived-functor comparison. -/
noncomputable instance exactFunctorCompFactors_hom_commShift :
    NatTrans.CommShift (exactFunctorCompFactors H K).hom ℤ := by
  have h1 : NatTrans.CommShift
      (Functor.associator DerivedCategory.Q H.mapDerivedCategory
        K.mapDerivedCategory).inv ℤ := by infer_instance
  have h2 : NatTrans.CommShift
      (Functor.isoWhiskerRight H.mapDerivedCategoryFactors
        K.mapDerivedCategory).hom ℤ := by
    change NatTrans.CommShift
      (Functor.whiskerRight H.mapDerivedCategoryFactors.hom
        K.mapDerivedCategory) ℤ
    infer_instance
  have h3 : NatTrans.CommShift
      (Functor.associator (H.mapHomologicalComplex (ComplexShape.up ℤ))
        DerivedCategory.Q K.mapDerivedCategory).hom ℤ := by infer_instance
  have h4 : NatTrans.CommShift
      (Functor.isoWhiskerLeft (H.mapHomologicalComplex (ComplexShape.up ℤ))
        K.mapDerivedCategoryFactors).hom ℤ := by
    change NatTrans.CommShift
      (Functor.whiskerLeft (H.mapHomologicalComplex (ComplexShape.up ℤ))
        K.mapDerivedCategoryFactors.hom) ℤ
    infer_instance
  have h5 : NatTrans.CommShift
      (Functor.associator
        (H.mapHomologicalComplex (ComplexShape.up ℤ))
        (K.mapHomologicalComplex (ComplexShape.up ℤ))
        DerivedCategory.Q).inv ℤ := by infer_instance
  let t1 := (Functor.associator DerivedCategory.Q H.mapDerivedCategory
    K.mapDerivedCategory).inv
  let t2 := Functor.whiskerRight H.mapDerivedCategoryFactors.hom
    K.mapDerivedCategory
  let t3 := (Functor.associator
    (H.mapHomologicalComplex (ComplexShape.up ℤ))
    DerivedCategory.Q K.mapDerivedCategory).hom
  let t4 := Functor.whiskerLeft
    (H.mapHomologicalComplex (ComplexShape.up ℤ))
    K.mapDerivedCategoryFactors.hom
  let t5 := (Functor.associator
    (H.mapHomologicalComplex (ComplexShape.up ℤ))
    (K.mapHomologicalComplex (ComplexShape.up ℤ))
    DerivedCategory.Q).inv
  letI ht1 : NatTrans.CommShift t1 ℤ := by simpa [t1] using h1
  letI ht2 : NatTrans.CommShift t2 ℤ := by simpa [t2] using h2
  letI ht3 : NatTrans.CommShift t3 ℤ := by simpa [t3] using h3
  letI ht4 : NatTrans.CommShift t4 ℤ := by simpa [t4] using h4
  letI ht5 : NatTrans.CommShift t5 ℤ := by simpa [t5] using h5
  letI ht45 : NatTrans.CommShift (t4 ≫ t5) ℤ := by infer_instance
  letI ht345 : NatTrans.CommShift (t3 ≫ t4 ≫ t5) ℤ := by infer_instance
  letI ht2345 : NatTrans.CommShift (t2 ≫ t3 ≫ t4 ≫ t5) ℤ := by infer_instance
  have ht12345 : NatTrans.CommShift (t1 ≫ t2 ≫ t3 ≫ t4 ≫ t5) ℤ := by
    infer_instance
  have hshift (n : ℤ) :
      (((H ⋙ K).mapHomologicalComplex
        (ComplexShape.up ℤ)).commShiftIso n).hom =
        ((H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          K.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom := by
    ext X i
    rw [Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    simp [Functor.commShiftIso_comp_hom_app,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  dsimp [exactFunctorCompFactors]
  refine ⟨fun n ↦ ?_⟩
  ext X
  have h := NatTrans.shift_app_comm
    (t1 ≫ t2 ≫ t3 ≫ t4 ≫ t5) n X
  dsimp [t1, t2, t3, t4, t5] at h
  simpa [Functor.commShiftIso_comp_hom_app,
    hshift n] using h

/-- Shift compatibility for the direct-to-iterated derived comparison. -/
noncomputable instance exactFunctorCompDerivedIso_hom_commShift :
    NatTrans.CommShift (exactFunctorCompDerivedIso H K).hom ℤ := by
  letI htarget : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso E₁ (ComplexShape.up ℤ))
      ((H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
      (H.mapDerivedCategory ⋙ K.mapDerivedCategory) :=
    ⟨exactFunctorCompFactors H K⟩
  let τ := (exactFunctorCompDerivedIso H K).hom
  have hpre : Functor.whiskerLeft DerivedCategory.Q τ =
      (H ⋙ K).mapDerivedCategoryFactors.hom ≫
        (exactFunctorCompFactors H K).inv := by
    ext X
    dsimp [τ, exactFunctorCompDerivedIso]
    rw [Localization.liftNatTrans_app]
    have hdirect :
        (Localization.Lifting.iso DerivedCategory.Q
          (HomologicalComplex.quasiIso E₁ (ComplexShape.up ℤ))
          ((H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q)
          (H ⋙ K).mapDerivedCategory).hom =
            (H ⋙ K).mapDerivedCategoryFactors.hom := rfl
    have htarget' :
        (Localization.Lifting.iso DerivedCategory.Q
          (HomologicalComplex.quasiIso E₁ (ComplexShape.up ℤ))
          ((H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q)
          (H.mapDerivedCategory ⋙ K.mapDerivedCategory)).inv =
            (exactFunctorCompFactors H K).inv := rfl
    rw [hdirect, htarget']
    simp
  haveI hpreComm : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Q τ) ℤ := by
    rw [hpre]
    infer_instance
  constructor
  intro n
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso E₁ (ComplexShape.up ℤ))
  intro X
  change
    ((H ⋙ K).mapDerivedCategory.commShiftIso n).hom.app
          (DerivedCategory.Q.obj X) ≫
        (shiftFunctor (DerivedCategory E₃) n).map
          (τ.app (DerivedCategory.Q.obj X)) =
      τ.app ((DerivedCategory.Q.obj X)⟦n⟧) ≫
        ((H.mapDerivedCategory ⋙ K.mapDerivedCategory).commShiftIso n).hom.app
          (DerivedCategory.Q.obj X)
  rw [← cancel_epi ((H ⋙ K).mapDerivedCategory.map
    ((DerivedCategory.Q.commShiftIso n).hom.app X))]
  erw [τ.naturality_assoc]
  simpa only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Category.assoc] using
      (NatTrans.shift_app_comm
        (Functor.whiskerLeft DerivedCategory.Q τ) n X)

omit [HasDerivedCategory E₁] [HasDerivedCategory E₂]
    [HasDerivedCategory E₃]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [(H ⋙ K).Additive] [PreservesFiniteLimits (H ⋙ K)]
    [PreservesFiniteColimits (H ⋙ K)] in
/-- The single-complex comparison for a composite exact functor factors canonically. -/
lemma singleMapHomologicalComplex_comp_hom (X : E₁) :
    (HomologicalComplex.singleMapHomologicalComplex (H ⋙ K)
          (ComplexShape.up ℤ) 0).hom.app X =
      (K.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex H
            (ComplexShape.up ℤ) 0).hom.app X) ≫
        (HomologicalComplex.singleMapHomologicalComplex K
          (ComplexShape.up ℤ) 0).hom.app (H.obj X) := by
  ext i
  simp only [HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f]
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      Functor.comp_obj]
    simp
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne, hi]

/-- Forward single-object compatibility for composite exact functors. -/
lemma exactFunctorCompDerivedIso_single_hom (X : E₁) :
    (exactFunctorCompDerivedIso H K).hom.app
          ((DerivedCategory.singleFunctor E₁ 0).obj X) ≫
        K.mapDerivedCategory.map
          ((H.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (K.mapDerivedCategorySingleFunctor 0).hom.app (H.obj X) =
      ((H ⋙ K).mapDerivedCategorySingleFunctor 0).hom.app X := by
  letI htarget : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso E₁ (ComplexShape.up ℤ))
      ((H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
      (H.mapDerivedCategory ⋙ K.mapDerivedCategory) :=
    ⟨exactFunctorCompFactors H K⟩
  dsimp [exactFunctorCompDerivedIso,
    Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ]
  change
    (Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso E₁ (ComplexShape.up ℤ))
      ((H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
      ((H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
      (H ⋙ K).mapDerivedCategory
      (H.mapDerivedCategory ⋙ K.mapDerivedCategory)
      (Iso.refl _).hom).app
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor E₁ 0).obj X)) ≫ _ = _
  rw [Localization.liftNatTrans_app]
  have hdirect :
      (Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso E₁ (ComplexShape.up ℤ))
        ((H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q)
        (H ⋙ K).mapDerivedCategory).hom =
          (H ⋙ K).mapDerivedCategoryFactors.hom := rfl
  have htarget' :
      (Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso E₁ (ComplexShape.up ℤ))
        ((H ⋙ K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q)
        (H.mapDerivedCategory ⋙ K.mapDerivedCategory)).inv =
          (exactFunctorCompFactors H K).inv := rfl
  rw [hdirect, htarget']
  dsimp [exactFunctorCompFactors]
  simp only [Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [cancel_epi ((H ⋙ K).mapDerivedCategoryFactors.hom.app
    ((CochainComplex.singleFunctor E₁ 0).obj X))]
  have hpair :
      K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.inv.app
          ((CochainComplex.singleFunctor E₁ 0).obj X)) ≫
        K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app
          ((CochainComplex.singleFunctor E₁ 0).obj X)) = 𝟙 _ := by
    rw [← K.mapDerivedCategory.map_comp, Iso.inv_hom_id_app,
      K.mapDerivedCategory.map_id]
  rw [K.mapDerivedCategory.map_comp]
  slice_lhs 3 4 => rw [hpair]
  simp
  erw [K.mapDerivedCategory.map_id]
  simp only [Category.id_comp]
  erw [K.mapDerivedCategoryFactors.hom.naturality_assoc]
  have hKpair :
      K.mapDerivedCategoryFactors.inv.app
          ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor E₁ 0).obj X)) ≫
        K.mapDerivedCategoryFactors.hom.app
          ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor E₁ 0).obj X)) = 𝟙 _ := by
    exact Iso.inv_hom_id_app _ _
  slice_lhs 2 3 => erw [hKpair]
  rw [singleMapHomologicalComplex_comp_hom H K X,
    Functor.map_comp]
  erw [Category.id_comp]
  erw [Category.id_comp]
  rw [Functor.comp_map]

/-- Inverse single-object compatibility for composite exact functors. -/
@[reassoc]
lemma exactFunctorCompDerivedIso_single_inv (X : E₁) :
    ((H ⋙ K).mapDerivedCategorySingleFunctor 0).inv.app X ≫
        (exactFunctorCompDerivedIso H K).hom.app
          ((DerivedCategory.singleFunctor E₁ 0).obj X) =
      (K.mapDerivedCategorySingleFunctor 0).inv.app (H.obj X) ≫
        K.mapDerivedCategory.map
          ((H.mapDerivedCategorySingleFunctor 0).inv.app X) := by
  rw [← cancel_mono (K.mapDerivedCategory.map
    ((H.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (K.mapDerivedCategorySingleFunctor 0).hom.app (H.obj X))]
  rw [Category.assoc, Category.assoc,
    exactFunctorCompDerivedIso_single_hom H K X]
  have hDpair :
      ((H ⋙ K).mapDerivedCategorySingleFunctor 0).inv.app X ≫
        ((H ⋙ K).mapDerivedCategorySingleFunctor 0).hom.app X = 𝟙 _ := by
    exact Iso.inv_hom_id_app _ _
  have hHpair :
      K.mapDerivedCategory.map
          ((H.mapDerivedCategorySingleFunctor 0).inv.app X) ≫
        K.mapDerivedCategory.map
          ((H.mapDerivedCategorySingleFunctor 0).hom.app X) = 𝟙 _ := by
    rw [← K.mapDerivedCategory.map_comp, Iso.inv_hom_id_app,
      K.mapDerivedCategory.map_id]
  have hKpair :
      (K.mapDerivedCategorySingleFunctor 0).inv.app (H.obj X) ≫
        (K.mapDerivedCategorySingleFunctor 0).hom.app (H.obj X) = 𝟙 _ := by
    exact Iso.inv_hom_id_app _ _
  slice_lhs 1 2 => erw [hDpair]
  slice_rhs 2 3 => erw [hHpair]
  simp

/-- Iterated exact-functor mapping on Ext equals mapping by the composite functor. -/
lemma Abelian.Ext.mapExactFunctor_comp
    [HasExt.{w₁} E₁] [HasExt.{w₂} E₂] [HasExt.{w₃} E₃]
    {X Y : E₁} {n : Nat} (a : Abelian.Ext.{w₁} X Y n) :
    (a.mapExactFunctor H).mapExactFunctor K =
      a.mapExactFunctor (H ⋙ K) := by
  ext
  simp only [Abelian.Ext.mapExactFunctor_hom]
  dsimp [ShiftedHom.map]
  simp only [Functor.map_comp, Category.assoc]
  rw [← exactFunctorCompDerivedIso_single_inv_assoc H K X]
  rw [cancel_epi (((H ⋙ K).mapDerivedCategorySingleFunctor 0).inv.app X)]
  erw [(K.mapDerivedCategory.commShiftIso (n : ℤ)).hom.naturality_assoc]
  have hmap :
      K.mapDerivedCategory.map (H.mapDerivedCategory.map a.hom) ≫
          K.mapDerivedCategory.map
            ((H.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app
              ((DerivedCategory.singleFunctor E₁ 0).obj Y)) ≫
        (K.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app
          (H.mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor E₁ 0).obj Y)) =
      a.hom.map (H.mapDerivedCategory ⋙ K.mapDerivedCategory) := by
    slice_lhs 1 2 => rw [← K.mapDerivedCategory.map_comp]
    change (a.hom.map H.mapDerivedCategory).map K.mapDerivedCategory = _
    exact (ShiftedHom.comp_map a.hom H.mapDerivedCategory
      K.mapDerivedCategory).symm
  slice_lhs 2 4 => rw [hmap]
  slice_lhs 1 2 =>
    rw [ShiftedHom.map_natTrans_commShift
      (H ⋙ K).mapDerivedCategory
      (H.mapDerivedCategory ⋙ K.mapDerivedCategory)
      (exactFunctorCompDerivedIso H K).hom a.hom]
  slice_lhs 2 4 =>
    rw [Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp,
      exactFunctorCompDerivedIso_single_hom H K Y]
  simp only [ShiftedHom.map, Category.assoc]

end ExactFunctorComp

end CategoryTheory
