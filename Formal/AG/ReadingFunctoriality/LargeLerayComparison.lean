import Formal.AG.ReadingFunctoriality.LerayComparison

/-!
# Generic large-sheaf Leray comparison

This module generalizes the selected Čech-to-sheaf-cohomology comparison from
obstruction coefficients to an arbitrary additive sheaf in the actual result
universe.  The comparison is constructed from Mathlib's injective resolution,
the selected Čech bicomplex, and the two derived edge quasi-isomorphisms.
-/

noncomputable section

namespace AAT.AG.Cohomology

universe u

open CategoryTheory

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

namespace LargeLeray

/-- The chosen injective resolution of an arbitrary large additive sheaf. -/
private noncomputable def largeSheafInjectiveResolution
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    InjectiveResolution F := by
  letI := standardAddCommGrpSheafEnoughInjectives (S := S)
  exact InjectiveResolution.of F

/-- Mathlib's Ext model of `H'` computed by the chosen injective resolution. -/
private noncomputable def largeSheafHPrimeInjectiveEquiv
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (X : S.category) (n : Nat) :
    F.H' n X ≃+
      CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor
          (Sheaf S.topology AddCommGrpCat.{u + 1}) 0).obj
            ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
              (yoneda.obj X ⋙ AddCommGrpCat.free)))
        (largeSheafInjectiveResolution F).cochainComplex n :=
  (largeSheafInjectiveResolution F).extAddEquivCohomologyClass

/--
The first-quadrant bicomplex obtained by applying the actual selected Čech
complex functor to every object of the chosen injective resolution.

The outer complex direction is the resolution degree and the inner direction
is the selected Čech degree. Both differentials and their commutation law are
constructed by `Functor.mapHomologicalComplex`.
-/
noncomputable def selectedCechResolutionBicomplex
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    HomologicalComplex₂ AddCommGrpCat.{u + 1}
      (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (((sheafToPresheaf S.topology AddCommGrpCat.{u + 1}) ⋙
      selectedCechComplexFunctor 𝒰).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
    (largeSheafInjectiveResolution F).cocomplex

/-- The `(q,p)` object is the product of `I^q`-sections on selected `p`-overlaps. -/
@[simp] theorem selectedCechResolutionBicomplex_obj
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p : ℕ) :
    (((selectedCechResolutionBicomplex 𝒰 F).X q).X p : Type (u + 1)) =
      SelectedCechCochain 𝒰
        ((largeSheafInjectiveResolution F).cocomplex.X q).val p :=
  rfl

/-- The selected Čech differential is the alternating sum of face restrictions. -/
theorem selectedCechResolutionBicomplex_cech_d_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p : ℕ)
    (c : SelectedCechCochain 𝒰
      ((largeSheafInjectiveResolution F).cocomplex.X q).val p)
    (σ : (canonicalCoverRelative 𝒰).simplex (p + 1)) :
    (((selectedCechResolutionBicomplex 𝒰 F).X q).d p (p + 1)).hom c σ =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ i.1) •
        ((largeSheafInjectiveResolution F).cocomplex.X q).val.map
          ((canonicalCoverRelative 𝒰).faceRestriction p i σ).op
          (c ((canonicalCoverRelative 𝒰).face p i σ)) :=
  selectedCechComplexFunctor_obj_d_apply 𝒰 _ p c σ

/-- The resolution differential acts sectionwise in every selected Čech degree. -/
theorem selectedCechResolutionBicomplex_resolution_d_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p : ℕ)
    (c : SelectedCechCochain 𝒰
      ((largeSheafInjectiveResolution F).cocomplex.X q).val p)
    (σ : (canonicalCoverRelative 𝒰).simplex p) :
    (((selectedCechResolutionBicomplex 𝒰 F).d q (q + 1)).f p).hom c σ =
      ((largeSheafInjectiveResolution F).cocomplex.d q (q + 1)).val.app _
        (c σ) :=
  rfl

/-- The resolution and selected Čech differentials commute. -/
theorem selectedCechResolutionBicomplex_d_comm
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q q' p p' : ℕ) :
    ((selectedCechResolutionBicomplex 𝒰 F).d q q').f p ≫
        ((selectedCechResolutionBicomplex 𝒰 F).X q').d p p' =
      ((selectedCechResolutionBicomplex 𝒰 F).X q).d p p' ≫
        ((selectedCechResolutionBicomplex 𝒰 F).d q q').f p' :=
  HomologicalComplex₂.d_comm
    (selectedCechResolutionBicomplex 𝒰 F) q q' p p'

/--
The injective-resolution unit induces the canonical map from the actual
selected Čech complex to resolution degree zero.

Implementation notes: this is the selected Čech functor applied to
`InjectiveResolution.ι`; an edge map is not supplied as external data.
-/
noncomputable def selectedCechResolutionAugmentation
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    (selectedCechComplexFunctor 𝒰).obj F.val ⟶
      (selectedCechResolutionBicomplex 𝒰 F).X 0 :=
  (selectedCechComplexFunctor 𝒰).map
    ((largeSheafInjectiveResolution F).ι.f 0).val

/-- The resolution augmentation applies the unit to every selected section. -/
@[simp] theorem selectedCechResolutionAugmentation_f_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (p : ℕ)
    (c : SelectedCechCochain 𝒰 F.val p)
    (σ : (canonicalCoverRelative 𝒰).simplex p) :
    ((selectedCechResolutionAugmentation 𝒰 F).f p).hom c σ =
      ((largeSheafInjectiveResolution F).ι.f 0).val.app _ (c σ) :=
  rfl

/--
Evaluation at the base maps canonically to selected Čech degree zero.

Implementation notes: each component restricts a base section along the
selected chart inclusion. Naturality is the presheaf naturality square.
-/
noncomputable def baseToSelectedCechZero
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    (evaluation S.categoryᵒᵖ AddCommGrpCat.{u + 1}).obj
        (Opposite.op base) ⟶
      selectedCechComplexFunctor 𝒰 ⋙
        HomologicalComplex.eval AddCommGrpCat.{u + 1}
          (ComplexShape.up ℕ) 0 where
  app F := AddCommGrpCat.ofHom
    { toFun := fun x σ ↦
        F.map ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op x
      map_zero' := by
        funext σ
        exact map_zero _
      map_add' := by
        intro x y
        funext σ
        exact map_add _ _ _ }
  naturality F G η := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    funext σ
    change
      G.map ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op
          (η.app _ x) =
        η.app _
          (F.map ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op x)
    exact (ConcreteCategory.congr_hom
      (η.naturality ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op) x).symm

/-- The degree-zero cover augmentation is restriction along the selected chart. -/
@[simp] theorem baseToSelectedCechZero_app_apply
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (x : F.obj (Opposite.op base))
    (σ : (canonicalCoverRelative 𝒰).simplex 0) :
    ((baseToSelectedCechZero 𝒰).app F).hom x σ =
      F.map ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op x :=
  rfl

/--
The chosen injective resolution evaluated on the base object.

Implementation notes: this uses the `ℕ`-indexed `InjectiveResolution.cocomplex`
needed by the first-quadrant construction, rather than the `ℤ`-indexed
`cochainComplex` used by the Ext model. Their later comparison must pass
through the injective resolution's canonical degree isomorphisms.
-/
noncomputable def baseResolutionComplex
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (((sheafToPresheaf S.topology AddCommGrpCat.{u + 1}) ⋙
      (evaluation S.categoryᵒᵖ AddCommGrpCat.{u + 1}).obj
        (Opposite.op base)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
    (largeSheafInjectiveResolution F).cocomplex

/-- The degree `q` base-resolution object is `I^q(base)`. -/
@[simp] theorem baseResolutionComplex_X
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((baseResolutionComplex (base := base) F).X q : Type (u + 1)) =
      ((largeSheafInjectiveResolution F).cocomplex.X q).val.obj
        (Opposite.op base) :=
  rfl

/-- The base-resolution differential is evaluation of the resolution differential. -/
theorem baseResolutionComplex_d_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : ((largeSheafInjectiveResolution F).cocomplex.X q).val.obj
      (Opposite.op base)) :
    ((baseResolutionComplex (base := base) F).d q (q + 1)).hom x =
      ((largeSheafInjectiveResolution F).cocomplex.d q (q + 1)).val.app _ x :=
  rfl

/--
Morphisms from the sheafified free representable are canonically sections.

Implementation notes: this is the composite of the sheafification adjunction,
the free-abelian-group adjunction in the presheaf category, and Yoneda.  The
additive structure is therefore derived from the standard constructions rather
than supplied as comparison data.
-/
noncomputable def sheafifiedFreeYonedaHomAddEquiv
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (X : S.category)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    (((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj X ⋙ AddCommGrpCat.free) ⟶ F) : Type (u + 1)) ≃+
      (F.val.obj (Opposite.op X) : Type (u + 1)) := by
  let e₁ := (sheafificationAdjunction S.topology
    AddCommGrpCat.{u + 1}).homAddEquiv
      (yoneda.obj X ⋙ AddCommGrpCat.free) F
  let e₂ := (AddCommGrpCat.adj.whiskerRight S.categoryᵒᵖ).homEquiv
      (yoneda.obj X) F.val
  let e₃ : (yoneda.obj X ⟶ F.val ⋙ forget AddCommGrpCat) ≃
      (F.val ⋙ forget AddCommGrpCat).obj (Opposite.op X) :=
    yonedaEquiv
  exact
    { toFun := fun f ↦ e₃ (e₂ (e₁ f))
      invFun := fun x ↦ e₁.symm (e₂.symm (e₃.symm x))
      left_inv := by
        intro f
        change e₁.symm (e₂.symm (e₃.symm (e₃ (e₂ (e₁ f))))) = f
        rw [e₃.symm_apply_apply, e₂.symm_apply_apply, e₁.symm_apply_apply]
      right_inv := by
        intro x
        change e₃ (e₂ (e₁ (e₁.symm (e₂.symm (e₃.symm x))))) = x
        rw [e₁.apply_symm_apply, e₂.apply_symm_apply, e₃.apply_symm_apply]
      map_add' := by
        intro f g
        change e₃ (e₂ (e₁ (f + g))) =
          e₃ (e₂ (e₁ f)) + e₃ (e₂ (e₁ g))
        simp only [map_add]
        rfl }

/-- Postcomposition of free-representable morphisms is evaluation on sections. -/
theorem sheafifiedFreeYonedaHomAddEquiv_comp
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (X : S.category)
    {F G : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (f : ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj X ⋙ AddCommGrpCat.free)) ⟶ F)
    (g : F ⟶ G) :
    sheafifiedFreeYonedaHomAddEquiv X G (f ≫ g) =
      g.val.app (Opposite.op X)
        (sheafifiedFreeYonedaHomAddEquiv X F f) := by
  rfl

/--
Precomposition by a map of sheafified free representables is restriction of
sections.  The normal form is the section map `F.val.map a.op`, so downstream
proofs do not unfold the three adjunctions used by
`sheafifiedFreeYonedaHomAddEquiv`.
-/
theorem sheafifiedFreeYonedaHomAddEquiv_precomp
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {X Y : S.category}
    (a : X ⟶ Y)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    (f : ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj Y ⋙ AddCommGrpCat.free)) ⟶ F) :
    sheafifiedFreeYonedaHomAddEquiv X F
        ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
          (Functor.whiskerRight (yoneda.map a) AddCommGrpCat.free) ≫ f) =
      F.val.map a.op (sheafifiedFreeYonedaHomAddEquiv Y F f) := by
  change yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight S.categoryᵒᵖ).homEquiv
        (yoneda.obj X) F.val)
        (((sheafificationAdjunction S.topology AddCommGrpCat.{u + 1}).homEquiv
          (yoneda.obj X ⋙ AddCommGrpCat.free) F)
          ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
            (Functor.whiskerRight (yoneda.map a) AddCommGrpCat.free) ≫ f))) = _
  rw [(sheafificationAdjunction S.topology
    AddCommGrpCat.{u + 1}).homEquiv_naturality_left]
  change yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight S.categoryᵒᵖ).homEquiv
        (yoneda.obj X) F.val)
        (((Functor.whiskeringRight S.categoryᵒᵖ _ _).obj
          AddCommGrpCat.free).map (yoneda.map a) ≫
            ((sheafificationAdjunction S.topology AddCommGrpCat.{u + 1}).homEquiv
              (yoneda.obj Y ⋙ AddCommGrpCat.free) F) f)) = _
  rw [(AddCommGrpCat.adj.whiskerRight
    S.categoryᵒᵖ).homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ a).symm

/--
The base-resolution complex in the universe of Mathlib's `H'` value.

This universe lift is structural: it permits the homology object and the Ext
group to live in the same `AddCommGrpCat` while retaining
`baseResolutionComplex` as the small source complex.
-/
noncomputable def liftedBaseResolutionComplex
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    CochainComplex AddCommGrpCat.{u + 2} ℕ :=
  (AddCommGrpCat.uliftFunctor.{u + 2, u + 1}.mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (baseResolutionComplex (base := base) F)

/-- The lifted complex has the universe lift of the actual section group in each degree. -/
@[simp] theorem liftedBaseResolutionComplex_X
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((liftedBaseResolutionComplex (base := base) F).X q : Type (u + 2)) =
      ULift.{u + 2, u + 1}
        (((largeSheafInjectiveResolution F).cocomplex.X q).val.obj
          (Opposite.op base)) :=
  rfl

/--
The lifted differential is the universe lift of the evaluated injective-resolution
differential.  This is the no-unfold computation rule for the lifted complex.
-/
theorem liftedBaseResolutionComplex_d_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : ULift.{u + 2, u + 1}
      (((largeSheafInjectiveResolution F).cocomplex.X q).val.obj
        (Opposite.op base))) :
    ((liftedBaseResolutionComplex (base := base) F).d q (q + 1)).hom x =
      ULift.up
        (((largeSheafInjectiveResolution F).cocomplex.d q (q + 1)).val.app _ x.down) :=
  rfl

/-- A lifted base-resolution cycle determines a morphism from the free representable. -/
noncomputable def baseResolutionLiftedCycleMorphism
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (z : (liftedBaseResolutionComplex (base := base) F).cycles n) :
    ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj base ⋙ AddCommGrpCat.free)) ⟶
        (largeSheafInjectiveResolution F).cocomplex.X n :=
  (sheafifiedFreeYonedaHomAddEquiv base
    ((largeSheafInjectiveResolution F).cocomplex.X n)).symm
      (((liftedBaseResolutionComplex (base := base) F).iCycles n).hom z).down

/--
The section represented by `baseResolutionLiftedCycleMorphism` is the original
lifted cycle.  The right-hand side is the normal form used by later proofs.
-/
@[simp] theorem baseResolutionLiftedCycleMorphism_section
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (z : (liftedBaseResolutionComplex (base := base) F).cycles n) :
    sheafifiedFreeYonedaHomAddEquiv base
        ((largeSheafInjectiveResolution F).cocomplex.X n)
        (baseResolutionLiftedCycleMorphism (base := base) F n z) =
      (((liftedBaseResolutionComplex (base := base) F).iCycles n).hom z).down :=
  (sheafifiedFreeYonedaHomAddEquiv base
    ((largeSheafInjectiveResolution F).cocomplex.X n)).apply_symm_apply _

/-- The morphism represented by a lifted cycle is a cocycle in the injective resolution. -/
theorem baseResolutionLiftedCycleMorphism_comp_d
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (z : (liftedBaseResolutionComplex (base := base) F).cycles n) :
    baseResolutionLiftedCycleMorphism (base := base) F n z ≫
        (largeSheafInjectiveResolution F).cocomplex.d n (n + 1) = 0 := by
  apply (sheafifiedFreeYonedaHomAddEquiv base
    ((largeSheafInjectiveResolution F).cocomplex.X (n + 1))).injective
  rw [sheafifiedFreeYonedaHomAddEquiv_comp]
  rw [baseResolutionLiftedCycleMorphism_section]
  rw [map_zero]
  have h := ConcreteCategory.congr_hom
    ((liftedBaseResolutionComplex (base := base) F).iCycles_d n (n + 1)) z
  have hd := congrArg ULift.down h
  simpa only [liftedBaseResolutionComplex_d_apply, ConcreteCategory.comp_apply,
    map_zero] using hd

/--
The canonical cycle map from the lifted base resolution to actual `Sheaf.H'`.

The value is Mathlib's `InjectiveResolution.extMk`; neither an Ext class nor a
comparison map is accepted from the caller.
-/
noncomputable def baseResolutionLiftedCyclesToHPrime
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (liftedBaseResolutionComplex (base := base) F).cycles n ⟶
      (F).H' n base :=
  AddCommGrpCat.ofHom
    { toFun := fun z ↦
        (largeSheafInjectiveResolution F).extMk
          (baseResolutionLiftedCycleMorphism (base := base) F n z) (n + 1) rfl
          (baseResolutionLiftedCycleMorphism_comp_d (base := base) F n z)
      map_zero' := by
        have hf0 : baseResolutionLiftedCycleMorphism (base := base) F n 0 = 0 := by
          apply (sheafifiedFreeYonedaHomAddEquiv base
            ((largeSheafInjectiveResolution F).cocomplex.X n)).injective
          simp only [baseResolutionLiftedCycleMorphism_section, map_zero]
          rfl
        simpa only [hf0] using
          (largeSheafInjectiveResolution F).extMk_zero
            (X := (presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
              (yoneda.obj base ⋙ AddCommGrpCat.free)) (n + 1) rfl
      map_add' := by
        intro x y
        have hxy : baseResolutionLiftedCycleMorphism (base := base) F n (x + y) =
            baseResolutionLiftedCycleMorphism (base := base) F n x +
              baseResolutionLiftedCycleMorphism (base := base) F n y := by
          apply (sheafifiedFreeYonedaHomAddEquiv base
            ((largeSheafInjectiveResolution F).cocomplex.X n)).injective
          simp only [baseResolutionLiftedCycleMorphism_section, map_add]
          rfl
        simpa only [hxy] using ((largeSheafInjectiveResolution F).add_extMk
          (baseResolutionLiftedCycleMorphism (base := base) F n x)
          (baseResolutionLiftedCycleMorphism (base := base) F n y)
          (n + 1) rfl (baseResolutionLiftedCycleMorphism_comp_d (base := base) F n x)
          (baseResolutionLiftedCycleMorphism_comp_d (base := base) F n y)).symm }

/-- No-unfold API: the lifted cycle map is the standard Ext cocycle constructor. -/
@[simp] theorem baseResolutionLiftedCyclesToHPrime_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (z : (liftedBaseResolutionComplex (base := base) F).cycles n) :
    (baseResolutionLiftedCyclesToHPrime (base := base) F n).hom z =
      (largeSheafInjectiveResolution F).extMk
        (baseResolutionLiftedCycleMorphism (base := base) F n z) (n + 1) rfl
        (baseResolutionLiftedCycleMorphism_comp_d (base := base) F n z) :=
  rfl

private theorem liftedBaseResolutionToCycles_comp_cyclesToHPrime
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (liftedBaseResolutionComplex (base := base) F).toCycles
          ((ComplexShape.up ℕ).prev n) n ≫
        baseResolutionLiftedCyclesToHPrime F n = 0 := by
  cases n with
  | zero =>
      rw [(liftedBaseResolutionComplex (base := base) F).toCycles_eq_zero
        (i := (ComplexShape.up ℕ).prev 0) (j := 0) (by simp)]
      simp
  | succ n =>
      rw [CochainComplex.prev_nat_succ]
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      let z := ((liftedBaseResolutionComplex (base := base) F).toCycles
        n (n + 1)).hom x
      let hz := baseResolutionLiftedCycleMorphism_comp_d
        (base := base) F (n + 1) z
      change (largeSheafInjectiveResolution F).extMk
          (baseResolutionLiftedCycleMorphism (base := base) F (n + 1) z)
          (n + 2) rfl hz = 0
      rw [(largeSheafInjectiveResolution F).extMk_eq_zero_iff
        (baseResolutionLiftedCycleMorphism (base := base) F (n + 1) z)
        (n + 2) rfl hz n rfl]
      let g := (sheafifiedFreeYonedaHomAddEquiv base
        ((largeSheafInjectiveResolution F).cocomplex.X n)).symm x.down
      refine ⟨g, ?_⟩
      apply (sheafifiedFreeYonedaHomAddEquiv base
        ((largeSheafInjectiveResolution F).cocomplex.X (n + 1))).injective
      rw [sheafifiedFreeYonedaHomAddEquiv_comp]
      rw [show sheafifiedFreeYonedaHomAddEquiv base
          ((largeSheafInjectiveResolution F).cocomplex.X n) g = x.down by
        exact (sheafifiedFreeYonedaHomAddEquiv base
          ((largeSheafInjectiveResolution F).cocomplex.X n)).apply_symm_apply _]
      rw [baseResolutionLiftedCycleMorphism_section]
      change
        ((largeSheafInjectiveResolution F).cocomplex.d n (n + 1)).val.app _ x.down =
          (((liftedBaseResolutionComplex (base := base) F).iCycles (n + 1)).hom z).down
      have h := ConcreteCategory.congr_hom
        ((liftedBaseResolutionComplex (base := base) F).toCycles_i n (n + 1)) x
      have hd := congrArg ULift.down h
      simpa only [z, liftedBaseResolutionComplex_d_apply,
        ConcreteCategory.comp_apply] using hd.symm

private noncomputable def liftedBaseResolutionHomologyToHPrime
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (liftedBaseResolutionComplex (base := base) F).homology n ⟶
      (F).H' n base :=
  ((liftedBaseResolutionComplex (base := base) F).sc n).descHomology
    (baseResolutionLiftedCyclesToHPrime F n) (by
      change (liftedBaseResolutionComplex (base := base) F).toCycles
          ((ComplexShape.up ℕ).prev n) n ≫
        baseResolutionLiftedCyclesToHPrime F n = 0
      exact liftedBaseResolutionToCycles_comp_cyclesToHPrime F n)

private theorem liftedBaseResolutionHomologyToHPrime_homologyπ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (liftedBaseResolutionComplex (base := base) F).homologyπ n ≫
        liftedBaseResolutionHomologyToHPrime F n =
      baseResolutionLiftedCyclesToHPrime F n := by
  exact ((liftedBaseResolutionComplex (base := base) F).sc n).π_descHomology
    (baseResolutionLiftedCyclesToHPrime F n) _

private theorem liftedBaseResolutionHomologyToHPrime_surjective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Surjective
      (liftedBaseResolutionHomologyToHPrime (base := base) F n) := by
  intro α
  obtain ⟨f, hf, hα⟩ :=
    (largeSheafInjectiveResolution F).extMk_surjective α (n + 1) rfl
  let s := sheafifiedFreeYonedaHomAddEquiv base
    ((largeSheafInjectiveResolution F).cocomplex.X n) f
  have hs :
      ((largeSheafInjectiveResolution F).cocomplex.d n (n + 1)).val.app _ s = 0 := by
    have h := congrArg
      (sheafifiedFreeYonedaHomAddEquiv base
        ((largeSheafInjectiveResolution F).cocomplex.X (n + 1))) hf
    simpa only [sheafifiedFreeYonedaHomAddEquiv_comp, map_zero] using h
  let x : (liftedBaseResolutionComplex (base := base) F).X n := ULift.up s
  have hx :
      (((liftedBaseResolutionComplex (base := base) F).sc n).g).hom x = 0 := by
    change ((liftedBaseResolutionComplex (base := base) F).d n
      ((ComplexShape.up ℕ).next n)).hom x = 0
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp]
    simpa only [x, liftedBaseResolutionComplex_d_apply] using congrArg ULift.up hs
  let z : (liftedBaseResolutionComplex (base := base) F).cycles n :=
    (((liftedBaseResolutionComplex (base := base) F).sc n).abCyclesIso.inv).hom
      ⟨x, hx⟩
  have hz : baseResolutionLiftedCycleMorphism (base := base) F n z = f := by
    apply (sheafifiedFreeYonedaHomAddEquiv base
      ((largeSheafInjectiveResolution F).cocomplex.X n)).injective
    rw [baseResolutionLiftedCycleMorphism_section]
    change (((liftedBaseResolutionComplex (base := base) F).iCycles n).hom z).down = s
    have hi := ((liftedBaseResolutionComplex (base := base) F).sc n).abCyclesIso_inv_apply_iCycles
      ⟨x, hx⟩
    have hid := congrArg (fun y ↦ ULift.down y) hi
    simpa only [z, x] using hid
  refine ⟨((liftedBaseResolutionComplex (base := base) F).homologyπ n).hom z, ?_⟩
  have hmap := ConcreteCategory.congr_hom
    (liftedBaseResolutionHomologyToHPrime_homologyπ (base := base) F n) z
  rw [ConcreteCategory.comp_apply] at hmap
  rw [hmap]
  change (largeSheafInjectiveResolution F).extMk
      (baseResolutionLiftedCycleMorphism (base := base) F n z) (n + 1) rfl
        (baseResolutionLiftedCycleMorphism_comp_d (base := base) F n z) = α
  simpa only [hz] using hα

private theorem baseResolutionExtMk_zero_eq_zero_iff
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    (f : ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj base ⋙ AddCommGrpCat.free)) ⟶
        (largeSheafInjectiveResolution F).cocomplex.X 0)
    (hf : f ≫ (largeSheafInjectiveResolution F).cocomplex.d 0 1 = 0) :
    (largeSheafInjectiveResolution F).extMk f 1 rfl hf = 0 ↔ f = 0 := by
  let R := largeSheafInjectiveResolution F
  change R.extMk f 1 rfl hf = 0 ↔ f = 0
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    R.extEquivCohomologyClass_extMk, R.extEquivCohomologyClass_zero,
    CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff]
  rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff
    _ _ _ _ _ (-1) (by lia)]
  constructor
  · rintro ⟨g, hg⟩
    have hg0 : g = 0 :=
      (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 (-1) (by lia)).eq_of_tgt _ _
    rw [hg0] at hg
    simp only [Limits.zero_comp] at hg
    apply (cancel_mono (R.cochainComplexXIso 0 0 rfl).inv).1
    simpa only [Limits.zero_comp] using hg.symm
  · rintro rfl
    refine ⟨0, ?_⟩
    simp

private theorem liftedBaseResolutionHomologyToHPrime_injective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Injective
      (liftedBaseResolutionHomologyToHPrime (base := base) F n) := by
  intro a b hab
  have hab0 :
      (liftedBaseResolutionHomologyToHPrime (base := base) F n).hom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨z, hz⟩ := ((AddCommGrpCat.epi_iff_surjective
    ((liftedBaseResolutionComplex (base := base) F).homologyπ n)).mp
      inferInstance) (a - b)
  have hcycle : (baseResolutionLiftedCyclesToHPrime F n).hom z = 0 := by
    have hmap := ConcreteCategory.congr_hom
      (liftedBaseResolutionHomologyToHPrime_homologyπ (base := base) F n) z
    rw [ConcreteCategory.comp_apply] at hmap
    rw [← hmap, hz, hab0]
  have hzclass :
      ((liftedBaseResolutionComplex (base := base) F).homologyπ n).hom z = 0 := by
    cases n with
    | zero =>
        have hf : baseResolutionLiftedCycleMorphism (base := base) F 0 z = 0 := by
          apply (baseResolutionExtMk_zero_eq_zero_iff (base := base) F
            (baseResolutionLiftedCycleMorphism (base := base) F 0 z)
            (baseResolutionLiftedCycleMorphism_comp_d (base := base) F 0 z)).mp
          exact hcycle
        have hi0 :
            ((liftedBaseResolutionComplex (base := base) F).iCycles 0).hom z = 0 := by
          apply ULift.down_injective
          have h := congrArg
            (sheafifiedFreeYonedaHomAddEquiv base
              ((largeSheafInjectiveResolution F).cocomplex.X 0)) hf
          simpa only [baseResolutionLiftedCycleMorphism_section, map_zero] using h
        have hz0 : z = 0 :=
          (AddCommGrpCat.mono_iff_injective
            ((liftedBaseResolutionComplex (base := base) F).iCycles 0)).1
              inferInstance (by simpa only [map_zero] using hi0)
        rw [hz0]
        exact map_zero _
    | succ p =>
        let f := baseResolutionLiftedCycleMorphism (base := base) F (p + 1) z
        let hf := baseResolutionLiftedCycleMorphism_comp_d
          (base := base) F (p + 1) z
        have hext : (largeSheafInjectiveResolution F).extMk f (p + 2) rfl hf = 0 := by
          exact hcycle
        obtain ⟨g, hg⟩ := ((largeSheafInjectiveResolution F).extMk_eq_zero_iff
          f (p + 2) rfl hf p rfl).mp hext
        let x : (liftedBaseResolutionComplex (base := base) F).X p :=
          ULift.up (sheafifiedFreeYonedaHomAddEquiv base
            ((largeSheafInjectiveResolution F).cocomplex.X p) g)
        let z' := ((liftedBaseResolutionComplex (base := base) F).toCycles
          p (p + 1)).hom x
        have hzz' : z = z' := by
          apply (AddCommGrpCat.mono_iff_injective
            ((liftedBaseResolutionComplex (base := base) F).iCycles (p + 1))).1
              inferInstance
          apply ULift.down_injective
          have hz_under :
              (((liftedBaseResolutionComplex (base := base) F).iCycles (p + 1)).hom z).down =
                sheafifiedFreeYonedaHomAddEquiv base
                  ((largeSheafInjectiveResolution F).cocomplex.X (p + 1)) f := by
            simpa only [f] using
              (baseResolutionLiftedCycleMorphism_section
                (base := base) F (p + 1) z).symm
          have hboundary := ConcreteCategory.congr_hom
            ((liftedBaseResolutionComplex (base := base) F).toCycles_i p (p + 1)) x
          have hboundary_down := congrArg ULift.down hboundary
          rw [hz_under]
          rw [← hg, sheafifiedFreeYonedaHomAddEquiv_comp]
          simpa only [z', x, liftedBaseResolutionComplex_d_apply,
            ConcreteCategory.comp_apply] using hboundary_down.symm
        rw [hzz']
        have hzero := ConcreteCategory.congr_hom
          ((liftedBaseResolutionComplex (base := base) F).toCycles_comp_homologyπ
            p (p + 1)) x
        simpa only [z', ConcreteCategory.comp_apply, map_zero] using hzero
  have hab_eq : a - b = 0 := by
    rw [← hz]
    exact hzclass
  exact sub_eq_zero.mp hab_eq

private noncomputable def liftedBaseResolutionHomologyEquivHPrime
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    ((liftedBaseResolutionComplex (base := base) F).homology n : Type (u + 2)) ≃+
      ((F).H' n base : Type (u + 2)) :=
  AddEquiv.ofBijective
    (liftedBaseResolutionHomologyToHPrime (base := base) F n).hom
    ⟨liftedBaseResolutionHomologyToHPrime_injective F n,
      liftedBaseResolutionHomologyToHPrime_surjective F n⟩

/-- Homology commutes with the structural universe lift of the base resolution. -/
noncomputable def liftedBaseResolutionHomologyIso
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (liftedBaseResolutionComplex (base := base) F).homology n ≅
      AddCommGrpCat.uliftFunctor.{u + 2, u + 1}.obj
        ((baseResolutionComplex (base := base) F).homology n) :=
  ((baseResolutionComplex (base := base) F).sc n).mapHomologyIso
    AddCommGrpCat.uliftFunctor.{u + 2, u + 1}

/--
Canonical identification of base-resolution homology with actual
`Sheaf.H'`.

It is assembled from the universe-lift homology isomorphism and the Ext
cocycle construction above.  No arbitrary complex, equivalence, comparison
map, or bijectivity premise is accepted.
-/
noncomputable def baseResolutionHomologyEquivHPrime
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    ((baseResolutionComplex (base := base) F).homology n : Type (u + 1)) ≃+
      ((F).H' n base : Type (u + 2)) :=
  AddEquiv.ulift.{u + 1, u + 2}.symm |>.trans
    ((liftedBaseResolutionHomologyIso (base := base) F n).symm.addCommGroupIsoToAddEquiv.trans
      (liftedBaseResolutionHomologyEquivHPrime (base := base) F n))

private theorem liftedBaseResolutionHomologyEquivHPrime_homologyπ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (z : (liftedBaseResolutionComplex (base := base) F).cycles n) :
    liftedBaseResolutionHomologyEquivHPrime F n
        (((liftedBaseResolutionComplex (base := base) F).homologyπ n).hom z) =
      (baseResolutionLiftedCyclesToHPrime F n).hom z := by
  change (liftedBaseResolutionHomologyToHPrime (base := base) F n).hom
      (((liftedBaseResolutionComplex (base := base) F).homologyπ n).hom z) = _
  have h := ConcreteCategory.congr_hom
    (liftedBaseResolutionHomologyToHPrime_homologyπ (base := base) F n) z
  simpa only [ConcreteCategory.comp_apply] using h

private theorem liftedBaseResolutionHomologyIso_inv_homologyπ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 2, u + 1}.map
          ((baseResolutionComplex (base := base) F).homologyπ n) ≫
        (liftedBaseResolutionHomologyIso (base := base) F n).inv =
      (((baseResolutionComplex (base := base) F).sc n).mapCyclesIso
          AddCommGrpCat.uliftFunctor.{u + 2, u + 1}).inv ≫
        (liftedBaseResolutionComplex (base := base) F).homologyπ n := by
  let K := baseResolutionComplex (base := base) F
  let F := AddCommGrpCat.uliftFunctor.{u + 2, u + 1}
  let h := (K.sc n).leftHomologyData
  change F.map (K.homologyπ n) ≫ ((K.sc n).mapHomologyIso F).inv =
    ((K.sc n).mapCyclesIso F).inv ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ n
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  dsimp only [HomologicalComplex.homologyπ, Iso.trans_inv,
    Functor.mapIso, Iso.symm_inv]
  simp only [Category.assoc]
  rw [← Category.assoc, ← F.map_comp,
    h.homologyπ_comp_homologyIso_hom, F.map_comp]
  change F.map h.cyclesIso.hom ≫ (h.map F).π ≫
    (h.map F).homologyIso.inv = _
  rw [(h.map F).π_comp_homologyIso_inv]
  rfl

/--
Representative formula for the base-resolution comparison.

A small homology class represented by `z` is first transported through the
canonical universe-lift cycle isomorphism and then sent by the actual Ext
cocycle constructor fixed above.
-/
theorem baseResolutionHomologyEquivHPrime_homologyπ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (z : (baseResolutionComplex (base := base) F).cycles n) :
    baseResolutionHomologyEquivHPrime F n
        (((baseResolutionComplex (base := base) F).homologyπ n).hom z) =
      (baseResolutionLiftedCyclesToHPrime F n).hom
        (((((baseResolutionComplex (base := base) F).sc n).mapCyclesIso
          AddCommGrpCat.uliftFunctor.{u + 2, u + 1}).inv).hom (ULift.up z)) := by
  simp only [baseResolutionHomologyEquivHPrime, AddEquiv.trans_apply]
  have h := ConcreteCategory.congr_hom
    (liftedBaseResolutionHomologyIso_inv_homologyπ (base := base) F n)
      (ULift.up z)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  have h' :
      (liftedBaseResolutionHomologyIso (base := base) F n).inv.hom
          (ULift.up (((baseResolutionComplex (base := base) F).homologyπ n).hom z)) =
        ((liftedBaseResolutionComplex (base := base) F).homologyπ n).hom
          (((((baseResolutionComplex (base := base) F).sc n).mapCyclesIso
            AddCommGrpCat.uliftFunctor.{u + 2, u + 1}).inv).hom (ULift.up z)) := by
    exact h
  change liftedBaseResolutionHomologyEquivHPrime (base := base) F n
      ((liftedBaseResolutionHomologyIso (base := base) F n).inv.hom
        (ULift.up (((baseResolutionComplex (base := base) F).homologyπ n).hom z))) = _
  rw [h']
  exact liftedBaseResolutionHomologyEquivHPrime_homologyπ (base := base) F n _

/--
The base-resolution complex maps to the selected degree-zero column.

Implementation notes: this is `baseToSelectedCechZero` mapped across the
chosen injective resolution, so compatibility with the resolution
differential is inherited from naturality.
-/
noncomputable def baseResolutionToSelectedCechZero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    baseResolutionComplex (base := base) F ⟶
      (selectedCechResolutionBicomplex 𝒰 F).flip.X 0 :=
  (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft
      (sheafToPresheaf S.topology AddCommGrpCat.{u + 1})
      (baseToSelectedCechZero 𝒰))
    (ComplexShape.up ℕ)).app
      (largeSheafInjectiveResolution F).cocomplex

/-- The vertical edge map restricts each base section to every selected chart. -/
@[simp] theorem baseResolutionToSelectedCechZero_f_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : ((largeSheafInjectiveResolution F).cocomplex.X q).val.obj
      (Opposite.op base))
    (σ : (canonicalCoverRelative 𝒰).simplex 0) :
    ((baseResolutionToSelectedCechZero 𝒰 F).f q).hom x σ =
      ((largeSheafInjectiveResolution F).cocomplex.X q).val.map
        ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op x :=
  rfl


/-- The resolution augmentation is killed by the first resolution differential. -/
theorem selectedCechResolutionAugmentation_comp_resolution_d
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (p : ℕ) :
    (selectedCechResolutionAugmentation 𝒰 F).f p ≫
        ((selectedCechResolutionBicomplex 𝒰 F).d 0 1).f p = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  funext σ
  have h := congrArg
    (fun f => f.val.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap p σ)))
    (largeSheafInjectiveResolution F).ι_f_zero_comp_complex_d
  have hx := ConcreteCategory.congr_hom h (c σ)
  simpa only [ConcreteCategory.comp_apply,
    selectedCechResolutionAugmentation_f_apply,
    selectedCechResolutionBicomplex_resolution_d_apply, map_zero] using hx

/-- Restricting a base section gives a selected Čech zero-cocycle. -/
theorem baseResolutionToSelectedCechZero_comp_cech_d
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (baseResolutionToSelectedCechZero 𝒰 F).f q ≫
        ((selectedCechResolutionBicomplex 𝒰 F).X q).d 0 1 = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext σ
  change (((selectedCechResolutionBicomplex 𝒰 F).X q).d 0 1).hom
      (((baseResolutionToSelectedCechZero 𝒰 F).f q).hom x) σ = 0
  rw [selectedCechResolutionBicomplex_cech_d_apply]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_smul,
    baseResolutionToSelectedCechZero_f_apply]
  let F := ((largeSheafInjectiveResolution F).cocomplex.X q).val ⋙
    forget AddCommGrpCat.{u + 1}
  change F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op
        (F.map ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 0 σ) 0)).op x) +
      -F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op
        (F.map ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 1 σ) 0)).op x) = 0
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
  have hmor :
      ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 0 σ) 0)).op ≫
          ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op =
        ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 1 σ) 0)).op ≫
          ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op :=
    Subsingleton.elim _ _
  rw [hmor]
  simp

/--
Implementation notes: the total construction uses the standard cochain sign
convention `ε₁ = 1` and `ε₂(q,p) = (-1)^q`, matching the resolution-first
presentation of the selected Čech bicomplex. A caller-supplied sign witness is
rejected because the sign is part of this canonical presentation, not a
premise of the comparison.
-/
private instance : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by dsimp; omega
  add_rel p q r (hpq : p + 1 = q) := by dsimp; omega
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [pow_succ]
    simp

/--
The actual total complex of the injective-resolution selected Čech
bicomplex.  Its degree `n` is the coproduct of bidegrees `(q,p)` with
`q + p = n`, and its differential is Mathlib's signed total differential.

Implementation notes: this is Mathlib's `HomologicalComplex₂.total`, so the
comparison uses the actual total complex and its coproduct API. A bespoke
complex carrying preselected differential data is rejected because it would
replace, rather than construct, the totalization required here.
-/
noncomputable def selectedCechResolutionTotalComplex
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (selectedCechResolutionBicomplex 𝒰 F).total (ComplexShape.up ℕ)

/--
On every total summand, the total differential is the sum of Mathlib's
signed resolution and selected Čech components.
-/
theorem selectedCechResolutionTotalComplex_ι_d
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p n n' : ℕ) (h : q + p = n) :
    (selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) q p n h ≫
        (selectedCechResolutionTotalComplex 𝒰 F).d n n' =
      (selectedCechResolutionBicomplex 𝒰 F).d₁
          (ComplexShape.up ℕ) q p n' +
        (selectedCechResolutionBicomplex 𝒰 F).d₂
          (ComplexShape.up ℕ) q p n' := by
  change _ ≫ ((selectedCechResolutionBicomplex 𝒰 F).total
    (ComplexShape.up ℕ)).d n n' = _
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]

/--
The selected Čech complex maps to the total complex through resolution
degree zero.  The horizontal term vanishes by the resolution unit law and
the vertical term is the selected Čech differential.

Implementation notes: the map is constructed from the actual augmentation
and the `(0,p)` total-summand inclusion. An arbitrary edge chain map supplied
as input is rejected because its chain-map law would leave the resolution
unit compatibility unproved.
-/
noncomputable def selectedCechToResolutionTotal
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    (selectedCechComplexFunctor 𝒰).obj F.val ⟶
      selectedCechResolutionTotalComplex 𝒰 F where
  f p := (selectedCechResolutionAugmentation 𝒰 F).f p ≫
    (selectedCechResolutionBicomplex 𝒰 F).ιTotal
      (ComplexShape.up ℕ) 0 p p (by simp)
  comm' p p' hp := by
    change p + 1 = p' at hp
    have hε1 : ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (0, p) = 1 := rfl
    have hε2 : ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (0, p) = 1 := by
      change (-1 : ℤˣ) ^ (0 : ℕ) = 1
      simp
    rw [Category.assoc, selectedCechResolutionTotalComplex_ι_d]
    rw [HomologicalComplex₂.d₁_eq
      (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
      (i₁ := 0) (i₁' := 1) (by simp) p p' (by
        change 1 + p = p'
        omega)]
    rw [HomologicalComplex₂.d₂_eq
      (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
      0 hp p' (by
        change 0 + p' = p'
        omega)]
    rw [hε1, hε2]
    simp only [one_smul]
    rw [Preadditive.comp_add]
    rw [← Category.assoc]
    rw [selectedCechResolutionAugmentation_comp_resolution_d]
    simp only [Limits.zero_comp, zero_add]
    rw [← Category.assoc]
    rw [(selectedCechResolutionAugmentation 𝒰 F).comm p p']
    simp

/-- The selected-edge component is the augmentation followed by its summand inclusion. -/
theorem selectedCechToResolutionTotal_f
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (p : ℕ) :
    (selectedCechToResolutionTotal 𝒰 F).f p =
      (selectedCechResolutionAugmentation 𝒰 F).f p ≫
        (selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) 0 p p (by simp) :=
  rfl

/--
The base-resolution complex maps to the total complex through selected Čech
degree zero.  The resolution term is inherited from naturality and the Čech
term vanishes because restriction from the base is a zero-cocycle.

Implementation notes: the map is constructed from actual restriction to
selected overlaps and the `(q,0)` total-summand inclusion. An externally
chosen edge map is rejected because it would bypass the zero-cocycle proof
from the face maps.
-/
noncomputable def baseResolutionToSelectedCechTotal
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    baseResolutionComplex (base := base) F ⟶
      selectedCechResolutionTotalComplex 𝒰 F where
  f q := (baseResolutionToSelectedCechZero 𝒰 F).f q ≫
    (selectedCechResolutionBicomplex 𝒰 F).ιTotal
      (ComplexShape.up ℕ) q 0 q (by simp)
  comm' q q' hq := by
    change q + 1 = q' at hq
    have hε1 : ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (q, 0) = 1 := rfl
    have hcomm :
        (baseResolutionToSelectedCechZero 𝒰 F).f q ≫
            ((selectedCechResolutionBicomplex 𝒰 F).d q q').f 0 =
          (baseResolutionComplex (base := base) F).d q q' ≫
            (baseResolutionToSelectedCechZero 𝒰 F).f q' := by
      simpa using (baseResolutionToSelectedCechZero 𝒰 F).comm q q'
    rw [Category.assoc, selectedCechResolutionTotalComplex_ι_d]
    rw [HomologicalComplex₂.d₁_eq
      (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
      hq 0 q' (by
        change q' + 0 = q'
        omega)]
    rw [HomologicalComplex₂.d₂_eq
      (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
      q (i₂ := 0) (i₂' := 1) (by simp) q' (by
        change q + 1 = q'
        omega)]
    rw [hε1]
    simp only [one_smul]
    rw [Preadditive.comp_add]
    rw [← Category.assoc]
    rw [hcomm]
    rw [Linear.comp_units_smul]
    rw [← Category.assoc]
    rw [baseResolutionToSelectedCechZero_comp_cech_d]
    simp only [Limits.zero_comp, smul_zero, add_zero]
    simp

/-- The base-edge component is restriction followed by its summand inclusion. -/
theorem baseResolutionToSelectedCechTotal_f
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (baseResolutionToSelectedCechTotal 𝒰 F).f q =
      (baseResolutionToSelectedCechZero 𝒰 F).f q ≫
        (selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) q 0 q (by simp) :=
  rfl


/--
A selected cover is Leray for an additive sheaf when actual local
`Sheaf.H'` vanishes in every positive degree on every selected overlap.

Implementation notes: this is only the mathematical vanishing condition. It
does not store a comparison map, exactness proof, homology equivalence, or
collapse conclusion; those are derived below from the actual injective
resolution.
-/
def IsLerayFor
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})] :
    Prop :=
  ∀ q, 0 < q →
    ∀ p, ∀ σ : (canonicalCoverRelative 𝒰).simplex p,
      Subsingleton
        ((F).H' q
          ((canonicalCoverRelative 𝒰).overlap p σ))

/--
The actual resolution column at a fixed selected Čech degree.

Implementation notes: the column is obtained by Mathlib's
`HomologicalComplex₂.flipFunctor` from the actual selected Čech-resolution
bicomplex. A separately supplied column complex is rejected because it would
disconnect later exactness from that bicomplex.
-/
noncomputable def selectedCechResolutionColumn
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (p : ℕ) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{u + 1}
    (ComplexShape.up ℕ) (ComplexShape.up ℕ)).obj
      (selectedCechResolutionBicomplex 𝒰 F)).X p

/-- The column object is the product of resolution sections on selected overlaps. -/
@[simp] theorem selectedCechResolutionColumn_X
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (p q : ℕ) :
    ((selectedCechResolutionColumn 𝒰 F p).X q : Type (u + 1)) =
      SelectedCechCochain 𝒰
        ((largeSheafInjectiveResolution F).cocomplex.X q).val p :=
  rfl

/-- The column differential applies the injective-resolution differential pointwise. -/
theorem selectedCechResolutionColumn_d_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (p q : ℕ)
    (c : SelectedCechCochain 𝒰
      ((largeSheafInjectiveResolution F).cocomplex.X q).val p)
    (σ : (canonicalCoverRelative 𝒰).simplex p) :
    ((selectedCechResolutionColumn 𝒰 F p).d q (q + 1)).hom c σ =
      ((largeSheafInjectiveResolution F).cocomplex.d q (q + 1)).val.app _
        (c σ) :=
  rfl

/-- Leray vanishing kills positive-degree resolution homology on each overlap. -/
theorem IsLerayFor.overlapBaseResolutionHomology_subsingleton
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (q : ℕ) (hq : 0 < q) (p : ℕ)
    (σ : (canonicalCoverRelative 𝒰).simplex p) :
    Subsingleton
      ((baseResolutionComplex
        (base := (canonicalCoverRelative 𝒰).overlap p σ) F).homology q :
          Type (u + 1)) := by
  let e := baseResolutionHomologyEquivHPrime
    (base := (canonicalCoverRelative 𝒰).overlap p σ) F q
  letI := hLeray q hq p σ
  exact e.injective.subsingleton

/-- Leray vanishing makes each overlap-evaluated resolution exact in positive degree. -/
theorem IsLerayFor.overlapBaseResolution_exactAt
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (q : ℕ) (hq : 0 < q) (p : ℕ)
    (σ : (canonicalCoverRelative 𝒰).simplex p) :
    (baseResolutionComplex
      (base := (canonicalCoverRelative 𝒰).overlap p σ) F).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact hLeray.overlapBaseResolutionHomology_subsingleton q hq p σ

/--
Every actual resolution column is exact in positive degree under the Leray
condition. Preimages are chosen on each overlap and assembled into the actual
selected-cochain product.
-/
theorem IsLerayFor.selectedCechResolutionColumn_exactAt
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (q : ℕ) (hq : 0 < q) (p : ℕ) :
    (selectedCechResolutionColumn 𝒰 F p).ExactAt q := by
  rcases q with _ | q
  · omega
  rw [(selectedCechResolutionColumn 𝒰 F p).exactAt_iff'
    q (q + 1) (q + 2) (CochainComplex.prev_nat_succ q) (by simp)]
  rw [ShortComplex.ab_exact_iff_ker_le_range]
  intro x hx
  change ((selectedCechResolutionColumn 𝒰 F p).d (q + 1) (q + 2)).hom x = 0 at hx
  change ∃ y, ((selectedCechResolutionColumn 𝒰 F p).d q (q + 1)).hom y = x
  have hpreimage : ∀ σ : (canonicalCoverRelative 𝒰).simplex p,
      ∃ y : ((largeSheafInjectiveResolution F).cocomplex.X q).val.obj
          (Opposite.op ((canonicalCoverRelative 𝒰).overlap p σ)),
        ((largeSheafInjectiveResolution F).cocomplex.d q (q + 1)).val.app _ y =
          x σ := by
    intro σ
    let K := baseResolutionComplex
      (base := (canonicalCoverRelative 𝒰).overlap p σ) F
    have hlocal := hLeray.overlapBaseResolution_exactAt (q + 1) (by omega) p σ
    rw [K.exactAt_iff' q (q + 1) (q + 2)
      (CochainComplex.prev_nat_succ q) (by simp)] at hlocal
    rw [ShortComplex.ab_exact_iff_ker_le_range] at hlocal
    have hxσ :
        ((largeSheafInjectiveResolution F).cocomplex.d
          (q + 1) (q + 2)).val.app _ (x σ) = 0 := by
      calc
        _ = ((selectedCechResolutionColumn 𝒰 F p).d
              (q + 1) (q + 2)).hom x σ := by
            symm
            simpa [Nat.add_assoc] using
              selectedCechResolutionColumn_d_apply 𝒰 F p (q + 1) x σ
        _ = 0 := congrFun hx σ
    have hxK : x σ ∈ ((K.d (q + 1) (q + 2)).hom).ker := by
      change (K.d (q + 1) (q + 2)).hom (x σ) = 0
      rw [baseResolutionComplex_d_apply]
      exact hxσ
    rcases hlocal hxK with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [← baseResolutionComplex_d_apply]
    exact hy
  choose y hy using hpreimage
  refine ⟨fun σ => y σ, ?_⟩
  funext σ
  rw [selectedCechResolutionColumn_d_apply]
  exact hy σ

/-- Positive-degree homology of every actual resolution column is trivial. -/
theorem IsLerayFor.selectedCechResolutionColumn_homology_subsingleton
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (q : ℕ) (hq : 0 < q) (p : ℕ) :
    Subsingleton
      ((selectedCechResolutionColumn 𝒰 F p).homology q : Type (u + 1)) := by
  rw [← AddCommGrpCat.isZero_iff_subsingleton]
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact hLeray.selectedCechResolutionColumn_exactAt q hq p

/--
The resolution augmentation is exact at degree zero in every selected Čech
degree. Exactness is mapped from the actual injective resolution through each
overlap evaluation and the resulting preimages are assembled pointwise.
-/
theorem selectedCechResolutionAugmentation_exactAtZero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (p : ℕ) :
    Function.Exact
      ((selectedCechResolutionAugmentation 𝒰 F).f p).hom
      (((selectedCechResolutionBicomplex 𝒰 F).d 0 1).f p).hom := by
  let R := largeSheafInjectiveResolution F
  intro x
  constructor
  · intro hx
    have hpreimage : ∀ σ : (canonicalCoverRelative 𝒰).simplex p,
        ∃ y : F.val.obj
            (Opposite.op ((canonicalCoverRelative 𝒰).overlap p σ)),
          ((R.ι.f 0).val.app _).hom y = x σ := by
      intro σ
      let E := sheafToPresheaf S.topology AddCommGrpCat.{u + 1} ⋙
        (evaluation S.categoryᵒᵖ AddCommGrpCat.{u + 1}).obj
          (Opposite.op ((canonicalCoverRelative 𝒰).overlap p σ))
      let K := ShortComplex.mk (R.ι.f 0) (R.cocomplex.d 0 1)
        R.ι_f_zero_comp_complex_d
      have hK : K.Exact := R.exact₀
      have hmap : (K.map E).Exact :=
        hK.map_of_mono_of_preservesKernel E (by infer_instance) (by infer_instance)
      have hfun : Function.Exact (E.map (R.ι.f 0))
          (E.map (R.cocomplex.d 0 1)) :=
        (ShortComplex.ab_exact_iff_function_exact (S := K.map E)).mp hmap
      apply (hfun (x σ)).mp
      change ((R.cocomplex.d 0 1).val.app _).hom (x σ) = 0
      calc
        _ = ((((selectedCechResolutionBicomplex 𝒰 F).d 0 1).f p).hom x) σ := by
          symm
          exact selectedCechResolutionBicomplex_resolution_d_apply
            𝒰 F 0 p x σ
        _ = 0 := congrFun hx σ
    choose y hy using hpreimage
    refine ⟨fun σ => y σ, ?_⟩
    funext σ
    rw [selectedCechResolutionAugmentation_f_apply]
    exact hy σ
  · rintro ⟨c, rfl⟩
    exact ConcreteCategory.congr_hom
      (selectedCechResolutionAugmentation_comp_resolution_d 𝒰 F p) c

/--
Restriction maps of an injective additive sheaf on an AAT context site are
surjective. The proof represents a section by a morphism from the sheafified
free Yoneda object and extends that morphism across the mono induced by the
context arrow.
-/
theorem injectiveSheaf_restriction_surjective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (I : Sheaf S.topology AddCommGrpCat.{u + 1})
    [Injective I]
    {X Y : S.category} (f : X ⟶ Y) :
    Function.Surjective (I.val.map f.op) := by
  let P (Z : S.category) :=
    (presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj Z ⋙ AddCommGrpCat.free)
  let m : P X ⟶ P Y :=
    (presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
      (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free)
  letI : Mono f := by
    constructor
    intro Z g h _
    exact Subsingleton.elim g h
  letI : Mono m := by
    dsimp [m, P]
    infer_instance
  intro x
  let h : P X ⟶ I :=
    (sheafifiedFreeYonedaHomAddEquiv X I).symm x
  let e : P Y ⟶ I := Injective.factorThru h m
  refine ⟨sheafifiedFreeYonedaHomAddEquiv Y I e, ?_⟩
  rw [← sheafifiedFreeYonedaHomAddEquiv_precomp f I e]
  change sheafifiedFreeYonedaHomAddEquiv X I (m ≫ e) = x
  rw [Injective.comp_factorThru]
  exact (sheafifiedFreeYonedaHomAddEquiv X I).apply_symm_apply x

private def selectedCechSingle
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (i : 𝒰.Index) : (canonicalCoverRelative 𝒰).simplex 0 :=
  fun _ => i

private def selectedCechPair
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (i j : 𝒰.Index) : (canonicalCoverRelative 𝒰).simplex 1 :=
  Fin.cases j (fun _ => i)

private theorem selectedCechPair_face_zero
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (i j : 𝒰.Index) :
    (canonicalCoverRelative 𝒰).face 0 0 (selectedCechPair 𝒰 i j) =
      selectedCechSingle 𝒰 i := by
  rfl

private theorem selectedCechPair_face_one
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (i j : 𝒰.Index) :
    (canonicalCoverRelative 𝒰).face 0 1 (selectedCechPair 𝒰 i j) =
      selectedCechSingle 𝒰 j := by
  funext k
  exact Fin.eq_zero k ▸ rfl

private noncomputable def selectedCechPairLift
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (i j : 𝒰.Index) {Z : S.category}
    (gi : Z ⟶ (canonicalCoverRelative 𝒰).chart i)
    (gj : Z ⟶ (canonicalCoverRelative 𝒰).chart j) :
    Z ⟶ (canonicalCoverRelative 𝒰).overlap 1 (selectedCechPair 𝒰 i j) := by
  apply homOfLE
  exact S.overlap.overlap_lift
    (𝒰.inclusion j) (𝒰.inclusion i) (leOfHom gj) (leOfHom gi)

private theorem selectedCechZeroCompatible
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (c : SelectedCechCochain 𝒰 F 0)
    (hc : (((selectedCechComplexFunctor 𝒰).obj F).d 0 1).hom c = 0) :
    Presieve.Arrows.Compatible (F ⋙ forget AddCommGrpCat.{u + 1})
      (fun i => homOfLE (𝒰.inclusion i))
      (fun i => c (selectedCechSingle 𝒰 i)) := by
  intro i j Z gi gj _
  let σ := selectedCechPair 𝒰 i j
  let k := selectedCechPairLift 𝒰 i j gi gj
  let ri : (canonicalCoverRelative 𝒰).overlap 1 σ ⟶
      (canonicalCoverRelative 𝒰).chart i :=
    (canonicalCoverRelative 𝒰).faceRestriction 0 0 σ ≫
      eqToHom (congrArg ((canonicalCoverRelative 𝒰).overlap 0)
        (selectedCechPair_face_zero 𝒰 i j))
  let rj : (canonicalCoverRelative 𝒰).overlap 1 σ ⟶
      (canonicalCoverRelative 𝒰).chart j :=
    (canonicalCoverRelative 𝒰).faceRestriction 0 1 σ ≫
      eqToHom (congrArg ((canonicalCoverRelative 𝒰).overlap 0)
        (selectedCechPair_face_one 𝒰 i j))
  have hdiff := congrFun hc σ
  rw [selectedCechComplexFunctor_obj_d_apply, Fin.sum_univ_two] at hdiff
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_smul] at hdiff
  have hraw :
      F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op
          (c ((canonicalCoverRelative 𝒰).face 0 0 σ)) =
        F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op
          (c ((canonicalCoverRelative 𝒰).face 0 1 σ)) := by
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg, Pi.zero_apply] using hdiff
  have hi :
      F.map ri.op (c (selectedCechSingle 𝒰 i)) =
        F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op
          (c ((canonicalCoverRelative 𝒰).face 0 0 σ)) := by
    simp [ri, σ]
    congr 1
  have hj :
      F.map rj.op (c (selectedCechSingle 𝒰 j)) =
        F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op
          (c ((canonicalCoverRelative 𝒰).face 0 1 σ)) := by
    simp [rj, σ]
    congr 2
    funext x
    exact Fin.eq_zero x ▸ rfl
  have hlocal : F.map ri.op (c (selectedCechSingle 𝒰 i)) =
      F.map rj.op (c (selectedCechSingle 𝒰 j)) :=
    hi.trans (hraw.trans hj.symm)
  change F.map gi.op (c (selectedCechSingle 𝒰 i)) =
    F.map gj.op (c (selectedCechSingle 𝒰 j))
  have hki : ri.op ≫ k.op = gi.op := Subsingleton.elim _ _
  have hkj : rj.op ≫ k.op = gj.op := Subsingleton.elim _ _
  calc
    _ = F.map k.op (F.map ri.op (c (selectedCechSingle 𝒰 i))) := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, hki]
      rfl
    _ = F.map k.op (F.map rj.op (c (selectedCechSingle 𝒰 j))) :=
      congrArg _ hlocal
    _ = _ := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, hkj]
      rfl

private theorem baseToSelectedCechZero_comp_cech_d
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (baseToSelectedCechZero 𝒰).app F ≫
        ((selectedCechComplexFunctor 𝒰).obj F).d 0 1 = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext σ
  change (((selectedCechComplexFunctor 𝒰).obj F).d 0 1).hom
      (((baseToSelectedCechZero 𝒰).app F).hom x) σ = 0
  rw [selectedCechComplexFunctor_obj_d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_smul, baseToSelectedCechZero_app_apply]
  let F' := F ⋙ forget AddCommGrpCat.{u + 1}
  change F'.map ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op
        (F'.map ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 0 σ) 0)).op x) +
      -F'.map ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op
        (F'.map ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 1 σ) 0)).op x) = 0
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
  have hmor :
      ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 0 σ) 0)).op ≫
          ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op =
        ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 1 σ) 0)).op ≫
          ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op :=
    Subsingleton.elim _ _
  rw [hmor]
  simp

/--
The selected Čech augmentation is exact at degree zero for every actual sheaf.
The proof converts the degree-zero cocycle equation into compatibility for the
selected covering family and applies the sheaf gluing condition on its generated
covering sieve.
-/
theorem sheaf_selectedCechAugmentation_exactAtZero
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (I : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    Function.Exact
      ((baseToSelectedCechZero 𝒰).app I.val).hom
      (((selectedCechComplexFunctor 𝒰).obj I.val).d 0 1).hom := by
  intro c
  constructor
  · intro hc
    have hTypePresheaf : Presheaf.IsSheaf S.topology
        (I.val ⋙ forget AddCommGrpCat.{u + 1}) :=
      (Presheaf.isSheaf_iff_isSheaf_forget
        (J := S.topology) (P' := I.val)
        (forget AddCommGrpCat.{u + 1})).mp I.cond
    have hType : Presieve.IsSheaf S.topology
        (I.val ⋙ forget AddCommGrpCat.{u + 1}) :=
      (isSheaf_iff_isSheaf_of_type S.topology
        (I.val ⋙ forget AddCommGrpCat.{u + 1})).mp hTypePresheaf
    have hgen := hType (Sieve.generate 𝒰.presieve) 𝒰.mem_topology
    have hcover : Presieve.IsSheafFor
        (I.val ⋙ forget AddCommGrpCat.{u + 1}) 𝒰.presieve :=
      (Presieve.isSheafFor_iff_generate 𝒰.presieve).mpr hgen
    have hglue := (Presieve.isSheafFor_arrows_iff
      (I.val ⋙ forget AddCommGrpCat.{u + 1})
      (fun i => homOfLE (𝒰.inclusion i))).mp hcover
      (fun i => c (selectedCechSingle 𝒰 i))
      (selectedCechZeroCompatible 𝒰 I.val c hc)
    obtain ⟨t, ht, _⟩ := hglue
    refine ⟨t, ?_⟩
    funext σ
    have hσ : σ = selectedCechSingle 𝒰 (σ 0) := by
      funext k
      exact Fin.eq_zero k ▸ rfl
    rw [hσ]
    exact ht (σ 0)
  · rintro ⟨t, rfl⟩
    exact ConcreteCategory.congr_hom
      (baseToSelectedCechZero_comp_cech_d 𝒰 I.val) t

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

private abbrev SelectedCechFreeGenerator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (X : S.category) :=
  Σ σ : (canonicalCoverRelative 𝒰).simplex n,
    X ⟶ (canonicalCoverRelative 𝒰).overlap n σ

private def selectedCechFreeGeneratorMap
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {X Y : S.categoryᵒᵖ} (f : X ⟶ Y) :
    SelectedCechFreeGenerator 𝒰 n X.unop → SelectedCechFreeGenerator 𝒰 n Y.unop :=
  fun g => ⟨g.1, f.unop ≫ g.2⟩

@[simp] private theorem selectedCechFreeGeneratorMap_id
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (X : S.categoryᵒᵖ) :
    selectedCechFreeGeneratorMap 𝒰 n (𝟙 X) = id := by
  funext g
  rcases g with ⟨σ, g⟩
  simp [selectedCechFreeGeneratorMap]

private theorem selectedCechFreeGeneratorMap_comp
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {X Y Z : S.categoryᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    selectedCechFreeGeneratorMap 𝒰 n (f ≫ g) =
      selectedCechFreeGeneratorMap 𝒰 n g ∘ selectedCechFreeGeneratorMap 𝒰 n f := by
  funext h
  rcases h with ⟨σ, h⟩
  simp [selectedCechFreeGeneratorMap]

private noncomputable def selectedCechFreePresheaf
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj X := AddCommGrpCat.of (FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 n X.unop))
  map {X Y} f := AddCommGrpCat.ofHom
    (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n f))
  map_id X := by
    change AddCommGrpCat.ofHom
      (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n (𝟙 X))) = 𝟙 _
    rw [selectedCechFreeGeneratorMap_id, FreeAbelianGroup.map_id]
    rfl
  map_comp f g := by
    change AddCommGrpCat.ofHom
        (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n (f ≫ g))) =
      AddCommGrpCat.ofHom (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n f)) ≫
        AddCommGrpCat.ofHom (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n g))
    rw [selectedCechFreeGeneratorMap_comp, FreeAbelianGroup.map_comp]
    rfl

@[simp] private theorem selectedCechFreePresheaf_map_of
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {X Y : S.categoryᵒᵖ} (f : X ⟶ Y)
    (g : SelectedCechFreeGenerator 𝒰 n X.unop) :
    (selectedCechFreePresheaf 𝒰 n).map f (FreeAbelianGroup.of g) =
      FreeAbelianGroup.of ⟨g.1, f.unop ≫ g.2⟩ := by
  change FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n f)
      (FreeAbelianGroup.of g) = _
  exact FreeAbelianGroup.map_of_apply g

private def selectedCechFreeFaceGenerator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (i : Fin (n + 2)) {X : S.category}
    (g : SelectedCechFreeGenerator 𝒰 (n + 1) X) : SelectedCechFreeGenerator 𝒰 n X :=
  ⟨(canonicalCoverRelative 𝒰).face n i g.1,
    g.2 ≫ (canonicalCoverRelative 𝒰).faceRestriction n i g.1⟩

private def selectedCechFreeBoundaryGenerator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {X : S.category} :
    SelectedCechFreeGenerator 𝒰 (n + 1) X → FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 n X) :=
  fun g => ∑ i : Fin (n + 2),
    ((-1 : ℤ) ^ i.1) • FreeAbelianGroup.of
      (selectedCechFreeFaceGenerator 𝒰 n i g)

private noncomputable def selectedCechFreeBoundary
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) : selectedCechFreePresheaf 𝒰 (n + 1) ⟶ selectedCechFreePresheaf 𝒰 n where
  app X := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n))
  naturality X Y f := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro g
    change FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n)
        (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 (n + 1) f)
          (FreeAbelianGroup.of g)) =
      FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n f)
        (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n)
          (FreeAbelianGroup.of g))
    rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
    simp only [selectedCechFreeBoundaryGenerator, map_sum, map_zsmul,
      FreeAbelianGroup.map_of_apply]
    apply Finset.sum_congr rfl
    intro i _
    congr 2

@[simp] private theorem selectedCechFreeBoundary_app_of
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (X : S.categoryᵒᵖ)
    (g : SelectedCechFreeGenerator 𝒰 (n + 1) X.unop) :
    (selectedCechFreeBoundary 𝒰 n).app X (FreeAbelianGroup.of g) =
      selectedCechFreeBoundaryGenerator 𝒰 n g := by
  exact FreeAbelianGroup.lift_apply_of (selectedCechFreeBoundaryGenerator 𝒰 n) g

private def selectedCechFreeSimplexGeneratorMap
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {x y : SimplexCategory} (f : x ⟶ y) {X : S.category} :
    SelectedCechFreeGenerator 𝒰 y.len X → SelectedCechFreeGenerator 𝒰 x.len X :=
  fun g =>
    ⟨fun i => g.1 (f.toOrderHom i),
      g.2 ≫ canonicalTupleOverlapMap 𝒰 f g.1⟩

private noncomputable def selectedCechFreeSimplexMap
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {x y : SimplexCategory} (f : x ⟶ y) :
    selectedCechFreePresheaf 𝒰 y.len ⟶ selectedCechFreePresheaf 𝒰 x.len where
  app X := AddCommGrpCat.ofHom
    (FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 f))
  naturality X Y g := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro h
    change FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 f)
        (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 y.len g)
          (FreeAbelianGroup.of h)) =
      FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 x.len g)
        (FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 f)
          (FreeAbelianGroup.of h))
    simp only [FreeAbelianGroup.map_of_apply]
    congr 2

@[simp] private theorem selectedCechFreeSimplexMap_app_of
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {x y : SimplexCategory} (f : x ⟶ y) (X : S.categoryᵒᵖ)
    (g : SelectedCechFreeGenerator 𝒰 y.len X.unop) :
    (selectedCechFreeSimplexMap 𝒰 f).app X (FreeAbelianGroup.of g) =
      FreeAbelianGroup.of (selectedCechFreeSimplexGeneratorMap 𝒰 f g) := by
  exact FreeAbelianGroup.map_of_apply g

@[simp] private theorem selectedCechFreeSimplexMap_id
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (x : SimplexCategory) :
    selectedCechFreeSimplexMap 𝒰 (𝟙 x) = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro g
  change FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 (𝟙 x))
      (FreeAbelianGroup.of g) = FreeAbelianGroup.of g
  rw [FreeAbelianGroup.map_of_apply]
  congr 2

private theorem selectedCechFreeSimplexMap_comp
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {x y z : SimplexCategory} (f : x ⟶ y) (g : y ⟶ z) :
    selectedCechFreeSimplexMap 𝒰 (f ≫ g) =
      selectedCechFreeSimplexMap 𝒰 g ≫ selectedCechFreeSimplexMap 𝒰 f := by
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro h
  change FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 (f ≫ g))
      (FreeAbelianGroup.of h) =
    FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 f)
      (FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 g)
        (FreeAbelianGroup.of h))
  rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.map_of_apply,
    FreeAbelianGroup.map_of_apply]
  apply congrArg FreeAbelianGroup.of
  apply Sigma.ext
  · funext i
    rfl
  · exact heq_of_eq (Subsingleton.elim _ _)

private noncomputable def selectedCechFreeSimplicialObject
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    SimplicialObject (S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) where
  obj x := selectedCechFreePresheaf 𝒰 x.unop.len
  map f := selectedCechFreeSimplexMap 𝒰 f.unop
  map_id x := by
    exact selectedCechFreeSimplexMap_id 𝒰 x.unop
  map_comp f g := by
    exact selectedCechFreeSimplexMap_comp 𝒰 g.unop f.unop

/-- Free chain complex generated by selected simplices and their overlap arrows. -/
noncomputable def selectedCechFreeChain
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ChainComplex (S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ :=
  AlgebraicTopology.alternatingFaceMapComplex
    (S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) |>.obj
      (selectedCechFreeSimplicialObject 𝒰)

private theorem selectedCechFreeSimplicial_delta_app_of
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (i : Fin (n + 2)) (X : S.categoryᵒᵖ)
    (g : SelectedCechFreeGenerator 𝒰 (n + 1) X.unop) :
    (((-1 : ℤ) ^ (i : ℕ) •
      (selectedCechFreeSimplicialObject 𝒰).δ i).app X).hom
        (FreeAbelianGroup.of g) =
      ((-1 : ℤ) ^ (i : ℕ)) •
        FreeAbelianGroup.of (selectedCechFreeFaceGenerator 𝒰 n i g) := by
  rw [NatTrans.app_zsmul]
  change (((-1 : ℤ) ^ (i : ℕ)) •
      FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 (SimplexCategory.δ i)))
        (FreeAbelianGroup.of g) = _
  rw [show (((( -1 : ℤ) ^ (i : ℕ)) •
      FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 (SimplexCategory.δ i)))
        (FreeAbelianGroup.of g)) =
      ((-1 : ℤ) ^ (i : ℕ)) •
        FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 (SimplexCategory.δ i))
          (FreeAbelianGroup.of g) from rfl,
    FreeAbelianGroup.map_of_apply]
  rfl

private theorem selectedCechFreeChain_d_eq_selectedCechFreeBoundary
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) :
    (selectedCechFreeChain 𝒰).d (n + 1) n = selectedCechFreeBoundary 𝒰 n := by
  unfold selectedCechFreeChain
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro g
  change
    ((∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (selectedCechFreeSimplicialObject 𝒰).δ i).app X) (FreeAbelianGroup.of g) = _
  rw [show
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (selectedCechFreeSimplicialObject 𝒰).δ i).app X =
        ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ) •
          (selectedCechFreeSimplicialObject 𝒰).δ i).app X by
      simpa using map_sum
        (NatTrans.appHom (F := selectedCechFreePresheaf 𝒰 (n + 1))
          (G := selectedCechFreePresheaf 𝒰 n) X)
        (fun i : Fin (n + 2) => (-1 : ℤ) ^ (i : ℕ) •
          (selectedCechFreeSimplicialObject 𝒰).δ i) Finset.univ]
  let ev : ((selectedCechFreePresheaf 𝒰 (n + 1)).obj X ⟶
      (selectedCechFreePresheaf 𝒰 n).obj X) →+
      ((selectedCechFreePresheaf 𝒰 n).obj X : Type (u + 1)) :=
    { toFun := fun (f : (selectedCechFreePresheaf 𝒰 (n + 1)).obj X ⟶
        (selectedCechFreePresheaf 𝒰 n).obj X) => f.hom (FreeAbelianGroup.of g)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ) •
    (selectedCechFreeSimplicialObject 𝒰).δ i).app X) = _
  rw [show ev (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ) •
      (selectedCechFreeSimplicialObject 𝒰).δ i).app X) =
        ∑ i : Fin (n + 2), ev
          (((-1 : ℤ) ^ (i : ℕ) •
            (selectedCechFreeSimplicialObject 𝒰).δ i).app X) by
      simpa using map_sum ev
        (fun i : Fin (n + 2) => ((-1 : ℤ) ^ (i : ℕ) •
          (selectedCechFreeSimplicialObject 𝒰).δ i).app X) Finset.univ]
  dsimp [ev]
  calc
    _ = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        FreeAbelianGroup.of (selectedCechFreeFaceGenerator 𝒰 n i g) := by
      apply Finset.sum_congr rfl
      intro i _
      exact selectedCechFreeSimplicial_delta_app_of 𝒰 n i X g
    _ = _ := by
      change (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          FreeAbelianGroup.of (selectedCechFreeFaceGenerator 𝒰 n i g)) =
        FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n)
          (FreeAbelianGroup.of g)
      rw [FreeAbelianGroup.lift_apply_of]
      rfl

private def selectedCechPrependSimplex
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} (i : 𝒰.Index)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    (canonicalCoverRelative 𝒰).simplex (n + 1) :=
  Fin.cases i σ

private theorem selectedCechPrependSimplex_face_zero
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} (i : 𝒰.Index)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    (canonicalCoverRelative 𝒰).face n 0 (selectedCechPrependSimplex 𝒰 i σ) = σ := by
  funext k
  rfl

private theorem selectedCechPrependSimplex_face_succ
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} (i : 𝒰.Index)
    (σ : (canonicalCoverRelative 𝒰).simplex (n + 1))
    (j : Fin (n + 2)) :
    (canonicalCoverRelative 𝒰).face (n + 1) j.succ
        (selectedCechPrependSimplex 𝒰 i σ) =
      selectedCechPrependSimplex 𝒰 i ((canonicalCoverRelative 𝒰).face n j σ) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · simp [canonicalCoverRelative_face,
      Site.FinitePosetCechCanonicalTupleSimplex.simplexMap_apply,
      SimplexCategory.δ, selectedCechPrependSimplex]

private noncomputable def selectedCechPrependLift
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (g : SelectedCechFreeGenerator 𝒰 n Y) :
    Y ⟶ (canonicalCoverRelative 𝒰).overlap (n + 1)
      (selectedCechPrependSimplex 𝒰 i g.1) :=
  canonicalTupleOverlapLift 𝒰 (selectedCechPrependSimplex 𝒰 i g.1)
    (Fin.cases a (fun k => g.2 ≫ canonicalTupleOverlapProjection 𝒰 g.1 k))

private noncomputable def selectedCechPrependGenerator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (g : SelectedCechFreeGenerator 𝒰 n Y) : SelectedCechFreeGenerator 𝒰 (n + 1) Y :=
  ⟨selectedCechPrependSimplex 𝒰 i g.1, selectedCechPrependLift 𝒰 i a g⟩

private def selectedCechContractionGenerator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i) :
    SelectedCechFreeGenerator 𝒰 n Y → FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y) :=
  fun g => FreeAbelianGroup.of (selectedCechPrependGenerator 𝒰 i a g)

private def selectedCechContraction
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i) :
    FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 n Y) →+
      FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y) :=
  FreeAbelianGroup.lift (selectedCechContractionGenerator 𝒰 i a)

private theorem selectedCechFreeFaceGenerator_zero_prepend
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (g : SelectedCechFreeGenerator 𝒰 n Y) :
    selectedCechFreeFaceGenerator 𝒰 n 0 (selectedCechPrependGenerator 𝒰 i a g) = g := by
  have hface := selectedCechPrependSimplex_face_zero 𝒰 i g.1
  apply Sigma.ext hface
  apply Quiver.heq_of_homOfEq_ext rfl
    (congrArg ((canonicalCoverRelative 𝒰).overlap n) hface)
  exact Subsingleton.elim _ _

private theorem selectedCechFreeFaceGenerator_succ_prepend
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (g : SelectedCechFreeGenerator 𝒰 (n + 1) Y) (j : Fin (n + 2)) :
    selectedCechFreeFaceGenerator 𝒰 (n + 1) j.succ (selectedCechPrependGenerator 𝒰 i a g) =
      selectedCechPrependGenerator 𝒰 i a (selectedCechFreeFaceGenerator 𝒰 n j g) := by
  have hface := selectedCechPrependSimplex_face_succ 𝒰 i g.1 j
  apply Sigma.ext hface
  apply Quiver.heq_of_homOfEq_ext rfl
    (congrArg ((canonicalCoverRelative 𝒰).overlap (n + 1)) hface)
  exact Subsingleton.elim _ _

private theorem selectedCechFreeBoundary_contraction_generator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (g : SelectedCechFreeGenerator 𝒰 (n + 1) Y) :
    FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 (n + 1))
        (selectedCechContraction 𝒰 i a (FreeAbelianGroup.of g)) +
      selectedCechContraction 𝒰 i a
        (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n)
          (FreeAbelianGroup.of g)) =
      FreeAbelianGroup.of g := by
  simp only [selectedCechContraction, selectedCechContractionGenerator,
    FreeAbelianGroup.lift_apply_of,
    selectedCechFreeBoundaryGenerator, map_sum, map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul,
    selectedCechFreeFaceGenerator_zero_prepend, Fin.val_succ,
    selectedCechFreeFaceGenerator_succ_prepend]
  have hpow (x : Fin (n + 2)) :
      (-1 : ℤ) ^ (x.1 + 1) = -((-1 : ℤ) ^ x.1) := by
    rw [pow_succ]
    ring
  simp_rw [hpow]
  simp only [neg_zsmul, Finset.sum_neg_distrib]
  abel

private theorem selectedCechFreeBoundary_contraction
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (x : FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y)) :
    FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 (n + 1))
        (selectedCechContraction 𝒰 i a x) +
      selectedCechContraction 𝒰 i a
        (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n) x) = x := by
  let lhs : FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y) →+
      FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y) :=
    (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 (n + 1))).comp
        (selectedCechContraction 𝒰 i a) +
      (selectedCechContraction 𝒰 i a).comp
        (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n))
  have hlhs : lhs = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro g
    exact selectedCechFreeBoundary_contraction_generator 𝒰 n i a g
  exact DFunLike.congr_fun hlhs x

/-- The free selected Čech boundary is locally surjective onto positive-degree cycles. -/
theorem selectedCechFreeBoundaryToCycles_isLocallySurjective
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) :
    Presheaf.IsLocallySurjective S.topology
      ((selectedCechFreeChain 𝒰).sc' (n + 2) (n + 1) n).toCycles := by
  classical
  let SC := (selectedCechFreeChain 𝒰).sc' (n + 2) (n + 1) n
  constructor
  intro X s
  let x : FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) X) :=
    (SC.iCycles.app (Opposite.op X)).hom s
  cases isEmpty_or_nonempty (SelectedCechFreeGenerator 𝒰 (n + 1) X) with
  | inl hEmpty =>
      haveI : IsEmpty (SelectedCechFreeGenerator 𝒰 (n + 1) X) := hEmpty
      have hx : x = 0 := Subsingleton.elim _ _
      refine S.topology.superset_covering ?_ (S.topology.top_mem X)
      intro Y f _
      rw [Presheaf.imageSieve_apply]
      refine ⟨0, ?_⟩
      apply (AddCommGrpCat.mono_iff_injective
        (SC.iCycles.app (Opposite.op Y))).mp inferInstance
      change (((SC.toCycles ≫ SC.iCycles).app (Opposite.op Y)).hom 0) =
        (SC.iCycles.app (Opposite.op Y)).hom
          ((SC.cycles.map f.op).hom s)
      rw [SC.toCycles_i]
      simp only [map_zero]
      rw [NatTrans.naturality_apply SC.iCycles f.op s]
      change 0 = (selectedCechFreePresheaf 𝒰 (n + 1)).map f.op x
      rw [hx, map_zero]
  | inr hNonempty =>
      let g₀ : SelectedCechFreeGenerator 𝒰 (n + 1) X := Classical.choice hNonempty
      let b : X ⟶ base :=
        g₀.2 ≫ canonicalTupleOverlapProjection 𝒰 g₀.1 0 ≫
          (canonicalCoverRelative 𝒰).inclusion (g₀.1 0)
      refine S.topology.superset_covering ?_
        (S.topology.pullback_stable b (Site.AATCoverageFamily.mem_topology 𝒰))
      intro Y f hf
      rw [Presheaf.imageSieve_apply]
      rw [Sieve.pullback_apply] at hf
      rcases hf with ⟨Z, a, c, hc, hfac⟩
      let i : 𝒰.Index := hc.idx
      let chartFactor : Y ⟶ (canonicalCoverRelative 𝒰).chart i :=
        a ≫ eqToHom hc.obj_idx.symm
      let xY : FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y) :=
        (selectedCechFreePresheaf 𝒰 (n + 1)).map f.op x
      let primitive : (SC.X₁.obj (Opposite.op Y) : Type (u + 1)) := by
        change FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 2) Y)
        exact selectedCechContraction 𝒰 i chartFactor xY
      refine ⟨primitive, ?_⟩
      apply (AddCommGrpCat.mono_iff_injective
        (SC.iCycles.app (Opposite.op Y))).mp inferInstance
      change (((SC.toCycles ≫ SC.iCycles).app (Opposite.op Y)).hom primitive) =
        (SC.iCycles.app (Opposite.op Y)).hom
          ((SC.cycles.map f.op).hom s)
      rw [SC.toCycles_i]
      rw [NatTrans.naturality_apply SC.iCycles f.op s]
      change (((selectedCechFreeChain 𝒰).d (n + 2) (n + 1)).app
          (Opposite.op Y)).hom primitive = xY
      rw [selectedCechFreeChain_d_eq_selectedCechFreeBoundary]
      change FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 (n + 1))
          primitive = xY
      have hcycleX : (SC.g.app (Opposite.op X)).hom x = 0 := by
        dsimp [x]
        change (((SC.iCycles ≫ SC.g).app (Opposite.op X)).hom s) = 0
        rw [SC.iCycles_g]
        rfl
      have hcycleY' : (SC.g.app (Opposite.op Y)).hom xY = 0 := by
        dsimp [xY]
        change (SC.g.app (Opposite.op Y)).hom
          ((SC.X₂.map f.op).hom x) = 0
        rw [NatTrans.naturality_apply SC.g f.op x, hcycleX, map_zero]
      have hcycleY :
          FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n) xY = 0 := by
        change ((selectedCechFreeBoundary 𝒰 n).app (Opposite.op Y)).hom xY = 0
        rw [← selectedCechFreeChain_d_eq_selectedCechFreeBoundary]
        exact hcycleY'
      have hcontract := selectedCechFreeBoundary_contraction 𝒰 n i chartFactor xY
      dsimp [primitive]
      rw [hcycleY, map_zero, add_zero] at hcontract
      exact hcontract

private noncomputable def selectedCechFreePresheafHomOfCochain
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (c : SelectedCechCochain 𝒰 F n) : selectedCechFreePresheaf 𝒰 n ⟶ F where
  app X := AddCommGrpCat.ofHom
    (FreeAbelianGroup.lift (fun g => F.map g.2.op (c g.1)))
  naturality X Y f := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro g
    change FreeAbelianGroup.lift (fun g => F.map g.2.op (c g.1))
        (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n f)
          (FreeAbelianGroup.of g)) =
      F.map f
        (FreeAbelianGroup.lift (fun g => F.map g.2.op (c g.1))
          (FreeAbelianGroup.of g))
    rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
    rw [← ConcreteCategory.comp_apply, ← F.map_comp]
    rfl

@[simp] private theorem selectedCechFreePresheafHomOfCochain_app_of
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (c : SelectedCechCochain 𝒰 F n) (X : S.categoryᵒᵖ)
    (g : SelectedCechFreeGenerator 𝒰 n X.unop) :
    (selectedCechFreePresheafHomOfCochain 𝒰 F n c).app X
        (FreeAbelianGroup.of g) = F.map g.2.op (c g.1) :=
  FreeAbelianGroup.lift_apply_of _ _

private noncomputable def selectedCechFreePresheafHomAddEquiv
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    ((selectedCechFreePresheaf 𝒰 n ⟶ F) : Type (u + 1)) ≃+
      SelectedCechCochain 𝒰 F n := by
  let toFun : (selectedCechFreePresheaf 𝒰 n ⟶ F) →
      SelectedCechCochain 𝒰 F n := fun η σ =>
    η.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap n σ))
      (FreeAbelianGroup.of ⟨σ, 𝟙 _⟩)
  let invFun : SelectedCechCochain 𝒰 F n →
      (selectedCechFreePresheaf 𝒰 n ⟶ F) :=
    selectedCechFreePresheafHomOfCochain 𝒰 F n
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro η
        apply NatTrans.ext
        funext X
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro g
        dsimp [invFun]
        calc
          _ = F.map g.2.op (toFun η g.1) :=
            selectedCechFreePresheafHomOfCochain_app_of 𝒰 F n (toFun η) X g
          _ = η.app X ((selectedCechFreePresheaf 𝒰 n).map g.2.op
              (FreeAbelianGroup.of ⟨g.1, 𝟙 _⟩)) :=
            (NatTrans.naturality_apply η g.2.op
              (FreeAbelianGroup.of ⟨g.1, 𝟙 _⟩)).symm
          _ = η.app X (FreeAbelianGroup.of g) := by
            rw [selectedCechFreePresheaf_map_of]
            congr 3
      right_inv := by
        intro c
        funext σ
        dsimp [invFun, toFun]
        rw [selectedCechFreePresheafHomOfCochain_app_of]
        change F.map (𝟙 _).op (c σ) = c σ
        simpa only using FunctorToTypes.map_id_apply
          (F := F ⋙ forget AddCommGrpCat.{u + 1}) (c σ)
      map_add' := by
        intro η θ
        funext σ
        rfl }

@[simp] private theorem selectedCechFreePresheafHomAddEquiv_apply
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (η : selectedCechFreePresheaf 𝒰 n ⟶ F)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    selectedCechFreePresheafHomAddEquiv 𝒰 F n η σ =
      η.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap n σ))
        (FreeAbelianGroup.of ⟨σ, 𝟙 _⟩) :=
  rfl

private theorem selectedCechFreePresheafHomAddEquiv_precomp_boundary
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (η : selectedCechFreePresheaf 𝒰 n ⟶ F) :
    selectedCechFreePresheafHomAddEquiv 𝒰 F (n + 1)
        (selectedCechFreeBoundary 𝒰 n ≫ η) =
      (((selectedCechComplexFunctor 𝒰).obj F).d n (n + 1)).hom
        (selectedCechFreePresheafHomAddEquiv 𝒰 F n η) := by
  funext σ
  rw [selectedCechComplexFunctor_obj_d_apply]
  rw [selectedCechFreePresheafHomAddEquiv_apply]
  change η.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap (n + 1) σ))
      ((selectedCechFreeBoundary 𝒰 n).app
        (Opposite.op ((canonicalCoverRelative 𝒰).overlap (n + 1) σ))
        (FreeAbelianGroup.of ⟨σ, 𝟙 _⟩)) = _
  rw [selectedCechFreeBoundary_app_of]
  simp_rw [selectedCechFreePresheafHomAddEquiv_apply]
  simp only [selectedCechFreeBoundaryGenerator, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  let τ := (canonicalCoverRelative 𝒰).face n i σ
  let r := (canonicalCoverRelative 𝒰).faceRestriction n i σ
  change ((-1 : ℤ) ^ (i : ℕ)) •
      η.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap (n + 1) σ))
        (FreeAbelianGroup.of (selectedCechFreeFaceGenerator 𝒰 n i ⟨σ, 𝟙 _⟩)) =
    ((-1 : ℤ) ^ (i : ℕ)) •
      F.map r.op
        (η.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap n τ))
          (FreeAbelianGroup.of ⟨τ, 𝟙 _⟩))
  congr 1
  simpa [τ, r, selectedCechFreeFaceGenerator] using
    NatTrans.naturality_apply η r.op
      (FreeAbelianGroup.of ⟨τ, 𝟙 _⟩)

/-- Sheafification of the selected free Čech chain complex. -/
noncomputable def selectedCechFreeSheafChain
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ChainComplex (Sheaf S.topology AddCommGrpCat.{u + 1}) ℕ :=
  ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (selectedCechFreeChain 𝒰)

private noncomputable def selectedCechFreeSheafHomAddEquiv
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (I : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (((selectedCechFreeSheafChain 𝒰).X n ⟶ I) : Type (u + 1)) ≃+
      SelectedCechCochain 𝒰 I.val n := by
  change ((((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
    (selectedCechFreePresheaf 𝒰 n)) ⟶ I) : Type (u + 1)) ≃+ _
  exact ((sheafificationAdjunction S.topology
    AddCommGrpCat.{u + 1}).homAddEquiv (selectedCechFreePresheaf 𝒰 n) I).trans
      (selectedCechFreePresheafHomAddEquiv 𝒰 I.val n)

@[simp] private theorem selectedCechFreeSheafHomAddEquiv_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (I : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (f : (selectedCechFreeSheafChain 𝒰).X n ⟶ I) :
    selectedCechFreeSheafHomAddEquiv 𝒰 I n f =
      selectedCechFreePresheafHomAddEquiv 𝒰 I.val n
        ((sheafificationAdjunction S.topology
          AddCommGrpCat.{u + 1}).homAddEquiv (selectedCechFreePresheaf 𝒰 n) I f) :=
  rfl

private theorem selectedCechFreeSheafHomAddEquiv_precomp_d
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (I : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (f : (selectedCechFreeSheafChain 𝒰).X n ⟶ I) :
    selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 1)
        ((selectedCechFreeSheafChain 𝒰).d (n + 1) n ≫ f) =
      (((selectedCechComplexFunctor 𝒰).obj I.val).d n (n + 1)).hom
        (selectedCechFreeSheafHomAddEquiv 𝒰 I n f) := by
  rw [selectedCechFreeSheafHomAddEquiv_apply,
    selectedCechFreeSheafHomAddEquiv_apply]
  have hd : (selectedCechFreeSheafChain 𝒰).d (n + 1) n =
      (presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
        (selectedCechFreeBoundary 𝒰 n) := by
    change (presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
        ((selectedCechFreeChain 𝒰).d (n + 1) n) = _
    rw [selectedCechFreeChain_d_eq_selectedCechFreeBoundary]
  rw [hd]
  have hadj := (sheafificationAdjunction S.topology
    AddCommGrpCat.{u + 1}).homEquiv_naturality_left
      (selectedCechFreeBoundary 𝒰 n) f
  change
    ((sheafificationAdjunction S.topology
      AddCommGrpCat.{u + 1}).homAddEquiv (selectedCechFreePresheaf 𝒰 (n + 1)) I)
        ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
          (selectedCechFreeBoundary 𝒰 n) ≫ f) =
      selectedCechFreeBoundary 𝒰 n ≫
        ((sheafificationAdjunction S.topology
          AddCommGrpCat.{u + 1}).homAddEquiv (selectedCechFreePresheaf 𝒰 n) I) f at hadj
  rw [hadj]
  exact selectedCechFreePresheafHomAddEquiv_precomp_boundary 𝒰 I.val n _

/-- The sheafified free selected Čech chain is exact in every positive degree. -/
theorem selectedCechFreeSheafChain_exactAt_succ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) :
    (selectedCechFreeSheafChain 𝒰).ExactAt (n + 1) := by
  let F := presheafToSheaf S.topology AddCommGrpCat.{u + 1}
  let P := (selectedCechFreeChain 𝒰).sc' (n + 2) (n + 1) n
  have hlocal : Presheaf.IsLocallySurjective S.topology P.toCycles :=
    selectedCechFreeBoundaryToCycles_isLocallySurjective 𝒰 n
  have hsheafLocal : Sheaf.IsLocallySurjective (F.map P.toCycles) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
      S.topology P.toCycles).mpr hlocal
  letI : Sheaf.IsLocallySurjective (F.map P.toCycles) := hsheafLocal
  haveI : Epi (F.map P.toCycles) := inferInstance
  have hmapCycles :
      F.map P.toCycles =
        (P.map F).toCycles ≫ (P.mapCyclesIso F).hom := by
    rw [← cancel_mono (F.map P.iCycles)]
    rw [Category.assoc, P.mapCyclesIso_hom_iCycles,
      (P.map F).toCycles_i]
    rw [← F.map_comp, P.toCycles_i]
    rfl
  haveI : Epi ((P.map F).toCycles ≫ (P.mapCyclesIso F).hom) := by
    rw [← hmapCycles]
    infer_instance
  haveI : Epi (P.map F).toCycles :=
    (epi_comp_iff_of_isIso (P.map F).toCycles (P.mapCyclesIso F).hom).mp
      inferInstance
  have hExact : (P.map F).Exact :=
    (ShortComplex.exact_iff_epi_toCycles (P.map F)).mpr inferInstance
  rw [(selectedCechFreeSheafChain 𝒰).exactAt_iff'
    (n + 2) (n + 1) n (by simp) (by simp)]
  change (P.map F).Exact
  exact hExact

/-- An injective sheaf has exact selected Čech cochains in every positive degree. -/
theorem injectiveSheaf_selectedCech_exactAt
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (I : Sheaf S.topology AddCommGrpCat.{u + 1})
    [Injective I]
    (p : ℕ) (hp : 0 < p) :
    ((selectedCechComplexFunctor 𝒰).obj I.val).ExactAt p := by
  rcases p with _ | n
  · omega
  rw [((selectedCechComplexFunctor 𝒰).obj I.val).exactAt_iff'
    n (n + 1) (n + 2) (CochainComplex.prev_nat_succ n) (by simp)]
  rw [ShortComplex.ab_exact_iff_ker_le_range]
  intro c hc
  let T := (selectedCechFreeSheafChain 𝒰).sc' (n + 2) (n + 1) n
  have hT : T.Exact := by
    rw [← (selectedCechFreeSheafChain 𝒰).exactAt_iff'
      (n + 2) (n + 1) n (by simp) (by simp)]
    exact selectedCechFreeSheafChain_exactAt_succ 𝒰 n
  let f : T.X₂ ⟶ I :=
    (selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 1)).symm c
  have hf : T.f ≫ f = 0 := by
    apply (selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 2)).injective
    change selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 2)
        ((selectedCechFreeSheafChain 𝒰).d (n + 2) (n + 1) ≫ f) =
      selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 2) 0
    rw [selectedCechFreeSheafHomAddEquiv_precomp_d, map_zero]
    rw [(selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 1)).apply_symm_apply c]
    change (((selectedCechComplexFunctor 𝒰).obj I.val).d
      (n + 1) (n + 2)).hom c = 0
    exact hc
  let primitive : T.X₃ ⟶ I := hT.descToInjective f hf
  refine ⟨selectedCechFreeSheafHomAddEquiv 𝒰 I n primitive, ?_⟩
  change (((selectedCechComplexFunctor 𝒰).obj I.val).d n (n + 1)).hom
      (selectedCechFreeSheafHomAddEquiv 𝒰 I n primitive) = c
  rw [← selectedCechFreeSheafHomAddEquiv_precomp_d]
  change selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 1)
      (T.g ≫ primitive) = c
  rw [hT.comp_descToInjective]
  exact (selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 1)).apply_symm_apply c

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- Projection from a fixed total degree to a chosen bidegree on that diagonal. -/
private noncomputable def selectedCechResolutionTotalProjection
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p n : ℕ) (h : q + p = n) :
    (selectedCechResolutionTotalComplex 𝒰 F).X n ⟶
      ((selectedCechResolutionBicomplex 𝒰 F).X q).X p :=
  by
    subst n
    exact (selectedCechResolutionBicomplex 𝒰 F).totalDesc
      (fun q' p' _ =>
        if hq : q' = q then
          if hp : p' = p then
            ((selectedCechResolutionBicomplex 𝒰 F).XXIsoOfEq _ _ _ hq hp).hom
          else 0
        else 0)

private theorem selectedCechResolutionTotal_ι_projection_general
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p n : ℕ) (h : q + p = n)
    (q' p' : ℕ) (h' : q' + p' = n) :
    (selectedCechResolutionBicomplex 𝒰 F).ιTotal
        (ComplexShape.up ℕ) q' p' n h' ≫
      selectedCechResolutionTotalProjection 𝒰 F q p n h =
        if hq : q' = q then
          if hp : p' = p then
            ((selectedCechResolutionBicomplex 𝒰 F).XXIsoOfEq _ _ _ hq hp).hom
          else 0
        else 0 := by
  subst n
  rw [selectedCechResolutionTotalProjection]
  exact (selectedCechResolutionBicomplex 𝒰 F).ι_totalDesc
    (c₁₂ := ComplexShape.up ℕ) (i₁₂ := q + p)
    (fun (q'' p'' : ℕ) (_ : q'' + p'' = q + p) =>
      if hq'' : q'' = q then
        if hp'' : p'' = p then
          ((selectedCechResolutionBicomplex 𝒰 F).XXIsoOfEq
            _ _ _ hq'' hp'').hom
        else 0
      else 0)
    q' p' h'

@[simp] private theorem selectedCechResolutionTotal_ι_projection_self
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p n : ℕ) (h : q + p = n) :
    (selectedCechResolutionBicomplex 𝒰 F).ιTotal
        (ComplexShape.up ℕ) q p n h ≫
      selectedCechResolutionTotalProjection 𝒰 F q p n h = 𝟙 _ := by
  rw [selectedCechResolutionTotal_ι_projection_general]
  simp

/-- Projection from total degree `n` to the `q, n - q` diagonal component. -/
private noncomputable def selectedCechResolutionTotalDiagonalProjection
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) (q : Fin (n + 1)) :
    (selectedCechResolutionTotalComplex 𝒰 F).X n ⟶
      ((selectedCechResolutionBicomplex 𝒰 F).X q).X (n - q) :=
  selectedCechResolutionTotalProjection 𝒰 F q (n - q) n (by omega)

private theorem selectedCechResolutionTotal_ι_projection
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n q' p' : ℕ) (h : q' + p' = n)
    (q : Fin (n + 1)) :
    (selectedCechResolutionBicomplex 𝒰 F).ιTotal
        (ComplexShape.up ℕ) q' p' n h ≫
      selectedCechResolutionTotalDiagonalProjection 𝒰 F n q =
        if hq : q' = q then
          ((selectedCechResolutionBicomplex 𝒰 F).XXIsoOfEq _ _ _ hq (by
            subst hq
            omega)).hom
        else 0 := by
  rw [selectedCechResolutionTotalDiagonalProjection,
    selectedCechResolutionTotal_ι_projection_general]
  by_cases hq : q' = q
  · subst hq
    have hp : p' = n - q := by omega
    simp [hp]
  · simp [hq]

/-- Inclusion of the `q, n - q` diagonal component into total degree `n`. -/
private noncomputable def selectedCechResolutionTotalDiagonalInclusion
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) (q : Fin (n + 1)) :
    ((selectedCechResolutionBicomplex 𝒰 F).X q).X (n - q) ⟶
      (selectedCechResolutionTotalComplex 𝒰 F).X n :=
  (selectedCechResolutionBicomplex 𝒰 F).ιTotal
    (ComplexShape.up ℕ) q (n - q) n (by
      change (q : ℕ) + (n - q) = n
      omega)

@[simp] private theorem selectedCechResolutionTotal_projection_inclusion
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) (q : Fin (n + 1)) :
    selectedCechResolutionTotalDiagonalInclusion 𝒰 F n q ≫
      selectedCechResolutionTotalDiagonalProjection 𝒰 F n q = 𝟙 _ := by
  rw [selectedCechResolutionTotalDiagonalInclusion,
    selectedCechResolutionTotal_ι_projection]
  simp

private theorem selectedCechResolutionTotal_inclusion_projection_ne
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) (q r : Fin (n + 1)) (hqr : q ≠ r) :
    selectedCechResolutionTotalDiagonalInclusion 𝒰 F n q ≫
      selectedCechResolutionTotalDiagonalProjection 𝒰 F n r = 0 := by
  have hval : (q : ℕ) ≠ (r : ℕ) := by
    intro h
    exact hqr (Fin.ext h)
  rw [selectedCechResolutionTotalDiagonalInclusion,
    selectedCechResolutionTotal_ι_projection]
  simp [hval]

private theorem selectedCechResolutionTotal_decomposition
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    ∑ q : Fin (n + 1),
        selectedCechResolutionTotalDiagonalProjection 𝒰 F n q ≫
          selectedCechResolutionTotalDiagonalInclusion 𝒰 F n q =
      𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro q' p' h
  change q' + p' = n at h
  let q : Fin (n + 1) := ⟨q', by omega⟩
  rw [Preadditive.comp_sum]
  rw [Finset.sum_eq_single q]
  · rw [← Category.assoc, selectedCechResolutionTotal_ι_projection]
    simp [q, selectedCechResolutionTotalDiagonalInclusion]
    exact (Category.comp_id _).symm
  · intro r _ hr
    rw [← Category.assoc, selectedCechResolutionTotal_ι_projection]
    have hqr : q' ≠ r := by
      intro eq
      apply hr
      apply Fin.ext
      exact eq.symm
    simp [hqr]
  · simp

private theorem selectedCechResolutionTotal_ι_d_projection_resolution
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p : ℕ) :
    ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) q p (q + p) (by
            change q + p = q + p
            rfl) ≫
        (selectedCechResolutionTotalComplex 𝒰 F).d (q + p) (q + p + 1)) ≫
      selectedCechResolutionTotalProjection 𝒰 F (q + 1) p
        (q + p + 1) (by omega) =
      ((selectedCechResolutionBicomplex 𝒰 F).d q (q + 1)).f p := by
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    (i₁ := q) (i₁' := q + 1) (by simp) p (q + p + 1) (by
      change q + 1 + p = q + p + 1
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    q (i₂ := p) (i₂' := p + 1) (by simp) (q + p + 1) (by
      change q + (p + 1) = q + p + 1
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  simp

private theorem selectedCechResolutionTotal_ι_d_projection_cech
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p : ℕ) :
    ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) q p (q + p) (by
            change q + p = q + p
            rfl) ≫
        (selectedCechResolutionTotalComplex 𝒰 F).d (q + p) (q + p + 1)) ≫
      selectedCechResolutionTotalProjection 𝒰 F q (p + 1)
        (q + p + 1) (by omega) =
      ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
          (ComplexShape.up ℕ) (q, p) •
        ((selectedCechResolutionBicomplex 𝒰 F).X q).d p (p + 1) := by
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    (i₁ := q) (i₁' := q + 1) (by simp) p (q + p + 1) (by
      change q + 1 + p = q + p + 1
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    q (i₂ := p) (i₂' := p + 1) (by simp) (q + p + 1) (by
      change q + (p + 1) = q + p + 1
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  simp

private theorem selectedCechResolutionTotal_d_projection_succ_succ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p : ℕ) :
    (selectedCechResolutionTotalComplex 𝒰 F).d
          (q + p + 1) (q + p + 2) ≫
        selectedCechResolutionTotalProjection 𝒰 F (q + 1) (p + 1)
          (q + p + 2) (by omega) =
      selectedCechResolutionTotalProjection 𝒰 F q (p + 1)
          (q + p + 1) (by omega) ≫
          ((selectedCechResolutionBicomplex 𝒰 F).d q (q + 1)).f (p + 1) +
        selectedCechResolutionTotalProjection 𝒰 F (q + 1) p
          (q + p + 1) (by omega) ≫
          (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (q + 1, p) •
            ((selectedCechResolutionBicomplex 𝒰 F).X (q + 1)).d p (p + 1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change a + b = q + p + 1 at h
  simp only [← Category.assoc, Preadditive.comp_add]
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    (i₁ := a) (i₁' := a + 1) (by simp) b (q + p + 2) (by
      change a + 1 + b = q + p + 2
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    a (i₂ := b) (i₂' := b + 1) (by simp) (q + p + 2) (by
      change a + (b + 1) = q + p + 2
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  by_cases haq : a = q
  · have hb : b = p + 1 := by omega
    subst a
    subst b
    simp
  · by_cases haqs : a = q + 1
    · have hb : b = p := by omega
      subst a
      subst b
      simp
    · simp [haq, haqs]

private theorem selectedCechResolutionTotal_d_projection_succ_zero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (selectedCechResolutionTotalComplex 𝒰 F).d q (q + 1) ≫
        selectedCechResolutionTotalProjection 𝒰 F (q + 1) 0 (q + 1) (by omega) =
      selectedCechResolutionTotalProjection 𝒰 F q 0 q (by omega) ≫
        ((selectedCechResolutionBicomplex 𝒰 F).d q (q + 1)).f 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change a + b = q at h
  simp only [← Category.assoc]
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    (i₁ := a) (i₁' := a + 1) (by simp) b (q + 1) (by
      change a + 1 + b = q + 1
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    a (i₂ := b) (i₂' := b + 1) (by simp) (q + 1) (by
      change a + (b + 1) = q + 1
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  by_cases haq : a = q
  · have hb : b = 0 := by omega
    subst a
    subst b
    simp
  · simp [haq]

private theorem selectedCechResolutionTotal_d_projection_zero_succ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (p : ℕ) :
    (selectedCechResolutionTotalComplex 𝒰 F).d p (p + 1) ≫
        selectedCechResolutionTotalProjection 𝒰 F 0 (p + 1) (p + 1) (by omega) =
      selectedCechResolutionTotalProjection 𝒰 F 0 p p (by omega) ≫
        (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
            (ComplexShape.up ℕ) (0, p) •
          ((selectedCechResolutionBicomplex 𝒰 F).X 0).d p (p + 1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change a + b = p at h
  simp only [← Category.assoc]
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    (i₁ := a) (i₁' := a + 1) (by simp) b (p + 1) (by
      change a + 1 + b = p + 1
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    a (i₂ := b) (i₂' := b + 1) (by simp) (p + 1) (by
      change a + (b + 1) = p + 1
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  by_cases ha0 : a = 0
  · have hb : b = p := by omega
    subst a
    subst b
    simp
  · simp [ha0]

private theorem selectedCechResolutionTotal_ι_d_projection_zero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p r s : ℕ)
    (htotal : r + s = q + p + 1)
    (hres : q + 1 ≠ r ∨ p ≠ s)
    (hcech : q ≠ r ∨ p + 1 ≠ s) :
    ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) q p (q + p) (by
            change q + p = q + p
            rfl) ≫
        (selectedCechResolutionTotalComplex 𝒰 F).d (q + p) (q + p + 1)) ≫
      selectedCechResolutionTotalProjection 𝒰 F r s (q + p + 1) htotal = 0 := by
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    (i₁ := q) (i₁' := q + 1) (by simp) p (q + p + 1) (by
      change q + 1 + p = q + p + 1
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    q (i₂ := p) (i₂' := p + 1) (by simp) (q + p + 1) (by
      change q + (p + 1) = q + p + 1
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  rcases hres with hres | hres <;> rcases hcech with hcech | hcech <;>
    simp [hres, hcech]

private theorem selectedCechResolutionTotal_ι_d_projection_resolution_explicit
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p n n' : ℕ)
    (hn : q + p = n) (hn' : q + 1 + p = n') :
    ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) q p n hn ≫
        (selectedCechResolutionTotalComplex 𝒰 F).d n n') ≫
      selectedCechResolutionTotalProjection 𝒰 F (q + 1) p n' hn' =
      ((selectedCechResolutionBicomplex 𝒰 F).d q (q + 1)).f p := by
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    (i₁ := q) (i₁' := q + 1) (by simp) p n' hn']
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    q (i₂ := p) (i₂' := p + 1) (by simp) n' (by
      change q + (p + 1) = n'
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  simp

private theorem selectedCechResolutionTotal_ι_d_projection_zero_explicit
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p n n' r s : ℕ)
    (hn : q + p = n) (hn' : q + p + 1 = n') (htarget : r + s = n')
    (hres : q + 1 ≠ r ∨ p ≠ s)
    (hcech : q ≠ r ∨ p + 1 ≠ s) :
    ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) q p n hn ≫
        (selectedCechResolutionTotalComplex 𝒰 F).d n n') ≫
      selectedCechResolutionTotalProjection 𝒰 F r s n' htarget = 0 := by
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    (i₁ := q) (i₁' := q + 1) (by simp) p n' (by
      change q + 1 + p = n'
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    q (i₂ := p) (i₂' := p + 1) (by simp) n' (by
      change q + (p + 1) = n'
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  rcases hres with hres | hres <;> rcases hcech with hcech | hcech <;>
    simp [hres, hcech]

/-- Predicate saying that no resolution component above `m` occurs in total degree `n`. -/
private def SelectedCechResolutionTotalSupportedAtMost
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n m : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n) : Prop :=
  ∀ q p : ℕ, ∀ h : q + p = n, m < q →
    (selectedCechResolutionTotalProjection 𝒰 F q p n h).hom x = 0

private theorem selectedCechResolutionTotal_supportedAtMost_top
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n) :
    SelectedCechResolutionTotalSupportedAtMost 𝒰 F n n x := by
  intro q p hqp hq
  omega

private theorem IsLerayFor.selectedCechResolutionTotal_eliminateColumn
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (m p : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X (m + 1 + p))
    (hcycle : ((selectedCechResolutionTotalComplex 𝒰 F).d
      (m + 1 + p) (m + 1 + p + 1)).hom x = 0)
    (hsupp : SelectedCechResolutionTotalSupportedAtMost
      𝒰 F (m + 1 + p) (m + 1) x) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (m + p),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + p) (m + 1 + p)).hom y
      SelectedCechResolutionTotalSupportedAtMost 𝒰 F (m + 1 + p) m x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + 1 + p) (m + 1 + p + 1)).hom x' = 0 := by
  let xcomp : ((selectedCechResolutionBicomplex 𝒰 F).X (m + 1)).X p :=
    (selectedCechResolutionTotalProjection 𝒰 F (m + 1) p
      (m + 1 + p) (by omega)).hom x
  have hxcycle :
      (((selectedCechResolutionBicomplex 𝒰 F).d (m + 1) (m + 2)).f p).hom
        xcomp = 0 := by
    rcases p with _ | p
    · calc
        _ = (selectedCechResolutionTotalProjection 𝒰 F (m + 1) 0
              (m + 1) (by omega) ≫
            ((selectedCechResolutionBicomplex 𝒰 F).d (m + 1) (m + 2)).f 0).hom x := by
              rfl
        _ = (((selectedCechResolutionTotalComplex 𝒰 F).d (m + 1) (m + 2) ≫
              selectedCechResolutionTotalProjection 𝒰 F (m + 2) 0
                (m + 2) (by omega)).hom x) := by
              rw [selectedCechResolutionTotal_d_projection_succ_zero]
        _ = 0 := by
              change (selectedCechResolutionTotalProjection 𝒰 F (m + 2) 0
                (m + 2) (by omega)).hom
                  (((selectedCechResolutionTotalComplex 𝒰 F).d
                    (m + 1) (m + 2)).hom x) = 0
              rw [hcycle, map_zero]
    · have hrzero :
          (selectedCechResolutionTotalProjection 𝒰 F (m + 2) p
            (m + 1 + (p + 1)) (by omega)).hom x = 0 :=
        hsupp (m + 2) p (by omega) (by omega)
      have hleft :
          (((selectedCechResolutionTotalComplex 𝒰 F).d
              (m + 1 + (p + 1)) (m + 1 + (p + 1) + 1) ≫
            selectedCechResolutionTotalProjection 𝒰 F (m + 2) (p + 1)
              (m + 1 + (p + 1) + 1) (by omega)).hom x) = 0 := by
        change (selectedCechResolutionTotalProjection 𝒰 F (m + 2) (p + 1)
          (m + 1 + (p + 1) + 1) (by omega)).hom
            (((selectedCechResolutionTotalComplex 𝒰 F).d
              (m + 1 + (p + 1)) (m + 1 + (p + 1) + 1)).hom x) = 0
        rw [hcycle, map_zero]
      have hformula := ConcreteCategory.congr_hom
        (selectedCechResolutionTotal_d_projection_succ_succ 𝒰 F (m + 1) p) x
      have hformula' :
          (((selectedCechResolutionTotalComplex 𝒰 F).d
              (m + 1 + (p + 1)) (m + 1 + (p + 1) + 1) ≫
            selectedCechResolutionTotalProjection 𝒰 F (m + 2) (p + 1)
              (m + 1 + (p + 1) + 1) (by omega)).hom x) =
            (((selectedCechResolutionBicomplex 𝒰 F).d (m + 1) (m + 2)).f
                (p + 1)).hom xcomp +
              (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
                  (ComplexShape.up ℕ) (m + 2, p) •
                ((selectedCechResolutionBicomplex 𝒰 F).X (m + 2)).d
                  p (p + 1)).hom
                ((selectedCechResolutionTotalProjection 𝒰 F (m + 2) p
                  (m + 1 + (p + 1)) (by omega)).hom x) := by
        simpa only [Nat.add_assoc] using hformula
      have hsum :
          (((selectedCechResolutionBicomplex 𝒰 F).d (m + 1) (m + 2)).f
              (p + 1)).hom xcomp +
            (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
                (ComplexShape.up ℕ) (m + 2, p) •
              ((selectedCechResolutionBicomplex 𝒰 F).X (m + 2)).d
                p (p + 1)).hom
              ((selectedCechResolutionTotalProjection 𝒰 F (m + 2) p
                (m + 1 + (p + 1)) (by omega)).hom x) = 0 := by
        calc
          _ = (((selectedCechResolutionTotalComplex 𝒰 F).d
                (m + 1 + (p + 1)) (m + 1 + (p + 1) + 1) ≫
              selectedCechResolutionTotalProjection 𝒰 F (m + 2) (p + 1)
                (m + 1 + (p + 1) + 1) (by omega)).hom x) := hformula'.symm
          _ = 0 := hleft
      rw [hrzero, map_zero, add_zero] at hsum
      exact hsum
  let C := selectedCechResolutionColumn 𝒰 F p
  have hexact : C.ExactAt (m + 1) :=
    hLeray.selectedCechResolutionColumn_exactAt (m + 1) (by omega) p
  rw [C.exactAt_iff' m (m + 1) (m + 2) (by simp) (by simp)] at hexact
  rw [ShortComplex.ab_exact_iff_ker_le_range] at hexact
  have hxmem : xcomp ∈ ((C.d (m + 1) (m + 2)).hom).ker := by
    change ((C.d (m + 1) (m + 2)).hom xcomp = 0)
    exact hxcycle
  rcases hexact hxmem with ⟨ycomp, hycomp⟩
  change (C.d m (m + 1)).hom ycomp = xcomp at hycomp
  let y : (selectedCechResolutionTotalComplex 𝒰 F).X (m + p) :=
    ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
      (ComplexShape.up ℕ) m p (m + p) (by
        change m + p = m + p
        rfl)).hom ycomp
  refine ⟨y, ?_, ?_⟩
  · intro r s hrs hmr
    change (selectedCechResolutionTotalProjection 𝒰 F r s
      (m + 1 + p) hrs).hom
      (x - ((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + p) (m + 1 + p)).hom y) = 0
    rw [map_sub]
    by_cases hr : r = m + 1
    · subst r
      have hs : s = p := by omega
      subst s
      have hboundary := ConcreteCategory.congr_hom
        (selectedCechResolutionTotal_ι_d_projection_resolution_explicit
          𝒰 F m p (m + p) (m + 1 + p) (by rfl) (by rfl)) ycomp
      have hboundary' :
          (selectedCechResolutionTotalProjection 𝒰 F (m + 1) p
            (m + 1 + p) (by omega)).hom
            (((selectedCechResolutionTotalComplex 𝒰 F).d
              (m + p) (m + 1 + p)).hom y) =
            (C.d m (m + 1)).hom ycomp := by
        simpa only [y, Nat.add_assoc] using hboundary
      change xcomp -
        (selectedCechResolutionTotalProjection 𝒰 F (m + 1) p
          (m + 1 + p) (by omega)).hom
          (((selectedCechResolutionTotalComplex 𝒰 F).d
            (m + p) (m + 1 + p)).hom y) = 0
      rw [hboundary', hycomp]
      simp
    · have hxzero := hsupp r s hrs (by omega)
      rw [hxzero, zero_sub]
      have hzero := ConcreteCategory.congr_hom
        (selectedCechResolutionTotal_ι_d_projection_zero_explicit
          𝒰 F m p (m + p) (m + 1 + p) r s
          (by rfl) (by omega) hrs
          (Or.inl (by omega)) (Or.inl (by omega))) ycomp
      have hzero' :
          (selectedCechResolutionTotalProjection 𝒰 F r s
            (m + 1 + p) hrs).hom
            (((selectedCechResolutionTotalComplex 𝒰 F).d
              (m + p) (m + 1 + p)).hom y) = 0 := by
        simpa only [y, Nat.add_assoc, map_zero] using hzero
      change -(selectedCechResolutionTotalProjection 𝒰 F r s
        (m + 1 + p) hrs).hom
          (((selectedCechResolutionTotalComplex 𝒰 F).d
            (m + p) (m + 1 + p)).hom y) = 0
      rw [hzero']
      simp
  · rw [map_sub, hcycle]
    change 0 -
      (((selectedCechResolutionTotalComplex 𝒰 F).d (m + p) (m + 1 + p) ≫
        (selectedCechResolutionTotalComplex 𝒰 F).d
          (m + 1 + p) (m + 1 + p + 1)).hom y) = 0
    rw [HomologicalComplex.d_comp_d]
    simp

private noncomputable def selectedCechResolutionTotalDegreeAddEquiv
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) {n n' : ℕ} (h : n = n') :
    ((selectedCechResolutionTotalComplex 𝒰 F).X n : Type (u + 1)) ≃+
      ((selectedCechResolutionTotalComplex 𝒰 F).X n' : Type (u + 1)) := by
  subst h
  exact AddEquiv.refl _

@[simp] private theorem selectedCechResolutionTotalDegreeAddEquiv_rfl
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    selectedCechResolutionTotalDegreeAddEquiv 𝒰 F (rfl : n = n) =
      AddEquiv.refl _ :=
  rfl

private theorem selectedCechResolutionTotal_d_transport_source
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) {n n' k : ℕ} (h : n = n')
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n) :
    ((selectedCechResolutionTotalComplex 𝒰 F).d n k).hom x =
      ((selectedCechResolutionTotalComplex 𝒰 F).d n' k).hom
        (selectedCechResolutionTotalDegreeAddEquiv 𝒰 F h x) := by
  subst h
  rfl

private theorem IsLerayFor.selectedCechResolutionTotal_eliminateColumnAt
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (n m p : ℕ) (hdegree : m + 1 + p = n)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hcycle : ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x = 0)
    (hsupp : SelectedCechResolutionTotalSupportedAtMost 𝒰 F n (m + 1) x) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (n - 1),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y
      SelectedCechResolutionTotalSupportedAtMost 𝒰 F n m x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' = 0 := by
  subst n
  rcases hLeray.selectedCechResolutionTotal_eliminateColumn m p x hcycle hsupp with
    ⟨y, hsupp', hcycle'⟩
  have hprev : m + p = m + 1 + p - 1 := by omega
  let y' : (selectedCechResolutionTotalComplex 𝒰 F).X (m + 1 + p - 1) :=
    selectedCechResolutionTotalDegreeAddEquiv 𝒰 F hprev y
  refine ⟨y', ?_⟩
  have hd := selectedCechResolutionTotal_d_transport_source
    𝒰 F (k := m + 1 + p) hprev y
  change
    SelectedCechResolutionTotalSupportedAtMost 𝒰 F (m + 1 + p) m
        (x - ((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + 1 + p - 1) (m + 1 + p)).hom y') ∧
      ((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + 1 + p) (m + 1 + p + 1)).hom
        (x - ((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + 1 + p - 1) (m + 1 + p)).hom y') = 0
  rw [← hd]
  exact ⟨hsupp', hcycle'⟩

private theorem IsLerayFor.selectedCechResolutionTotal_normalizeColumnsAux
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (n k : ℕ) (hk : k ≤ n)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hcycle : ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x = 0)
    (hsupp : SelectedCechResolutionTotalSupportedAtMost 𝒰 F n k x) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (n - 1),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y
      SelectedCechResolutionTotalSupportedAtMost 𝒰 F n 0 x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' = 0 := by
  induction k generalizing x with
  | zero =>
      refine ⟨0, ?_⟩
      simp only [map_zero, sub_zero]
      exact ⟨hsupp, hcycle⟩
  | succ k ih =>
      let p := n - (k + 1)
      have hdegree : k + 1 + p = n := by
        dsimp [p]
        omega
      rcases hLeray.selectedCechResolutionTotal_eliminateColumnAt
          n k p hdegree x hcycle hsupp with ⟨y₁, hsupp₁, hcycle₁⟩
      let x₁ := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y₁
      rcases ih (by omega) x₁ hcycle₁ hsupp₁ with ⟨y₂, hsupp₂, hcycle₂⟩
      refine ⟨y₁ + y₂, ?_⟩
      have hmap :
          ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom (y₁ + y₂) =
            ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y₁ +
              ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y₂ :=
        map_add _ y₁ y₂
      rw [hmap]
      dsimp only
      have hx :
          x - (((selectedCechResolutionTotalComplex 𝒰 F).d
              (n - 1) n).hom y₁ +
            ((selectedCechResolutionTotalComplex 𝒰 F).d
              (n - 1) n).hom y₂) =
          x₁ - ((selectedCechResolutionTotalComplex 𝒰 F).d
            (n - 1) n).hom y₂ := by
        dsimp [x₁]
        abel
      rw [hx]
      exact ⟨hsupp₂, hcycle₂⟩

private theorem IsLerayFor.selectedCechResolutionTotal_normalizeColumns
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (n : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hcycle : ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x = 0) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (n - 1),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y
      SelectedCechResolutionTotalSupportedAtMost 𝒰 F n 0 x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' = 0 :=
  hLeray.selectedCechResolutionTotal_normalizeColumnsAux n n (by rfl) x hcycle
    (selectedCechResolutionTotal_supportedAtMost_top 𝒰 F n x)

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

private theorem selectedCechResolutionAugmentation_f_injective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (p : ℕ) :
    Function.Injective ((selectedCechResolutionAugmentation 𝒰 F).f p).hom := by
  intro x y hxy
  funext σ
  have hσ := congrFun hxy σ
  rw [selectedCechResolutionAugmentation_f_apply,
    selectedCechResolutionAugmentation_f_apply] at hσ
  let f := ((largeSheafInjectiveResolution F).ι.f 0).val.app
    (Opposite.op ((canonicalCoverRelative 𝒰).overlap p σ))
  exact (AddCommGrpCat.mono_iff_injective f).mp inferInstance hσ

private theorem selectedCechResolutionTotal_eq_zeroColumn_of_supportedAtMost
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hsupp : SelectedCechResolutionTotalSupportedAtMost 𝒰 F n 0 x) :
    x = ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) 0 n n (by simp)).hom
        ((selectedCechResolutionTotalProjection 𝒰 F 0 n n (by simp)).hom x) := by
  let q0 : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  let ev :
      (((selectedCechResolutionTotalComplex 𝒰 F).X n ⟶
          (selectedCechResolutionTotalComplex 𝒰 F).X n)) →+
        ((selectedCechResolutionTotalComplex 𝒰 F).X n : Type (u + 1)) :=
    { toFun := fun f => f.hom x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hdec := ConcreteCategory.congr_hom
    (selectedCechResolutionTotal_decomposition 𝒰 F n) x
  change ev (∑ q : Fin (n + 1),
      selectedCechResolutionTotalDiagonalProjection 𝒰 F n q ≫
        selectedCechResolutionTotalDiagonalInclusion 𝒰 F n q) = ev (𝟙 _) at hdec
  rw [map_sum] at hdec
  change
    (∑ q : Fin (n + 1),
      (selectedCechResolutionTotalDiagonalInclusion 𝒰 F n q).hom
        ((selectedCechResolutionTotalDiagonalProjection 𝒰 F n q).hom x)) = x at hdec
  have hsum :
      (∑ q : Fin (n + 1),
        (selectedCechResolutionTotalDiagonalInclusion 𝒰 F n q).hom
          ((selectedCechResolutionTotalDiagonalProjection 𝒰 F n q).hom x)) =
        (selectedCechResolutionTotalDiagonalInclusion 𝒰 F n q0).hom
          ((selectedCechResolutionTotalDiagonalProjection 𝒰 F n q0).hom x) := by
    apply Finset.sum_eq_single q0
    · intro q _ hq
      have hqne : (q : ℕ) ≠ 0 := by
        intro hz
        apply hq
        apply Fin.ext
        simpa only [q0] using hz
      have hqpos : 0 < (q : ℕ) := by
        omega
      have hz := hsupp q (n - q) (by omega) hqpos
      rw [selectedCechResolutionTotalDiagonalProjection, hz, map_zero]
    · simp
  simpa only [q0, selectedCechResolutionTotalDiagonalInclusion,
    selectedCechResolutionTotalDiagonalProjection, Nat.cast_zero,
    Nat.zero_add, Nat.sub_zero] using hdec.symm.trans hsum

private theorem cochainHomologyπ_eq_zero_iff_boundary
    (K : CochainComplex AddCommGrpCat.{u + 1} ℕ) (n : ℕ)
    (z : K.cycles n) :
    (K.homologyπ n).hom z = 0 ↔
      ∃ y : K.X (n - 1),
        (K.d (n - 1) n).hom y = (K.iCycles n).hom z := by
  let Q := ShortComplex.mk (K.toCycles (n - 1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ (n - 1) n)
  have hQ : Q.Exact := ShortComplex.exact_of_g_is_cokernel _
    (K.homologyIsCokernel (n - 1) n (by cases n <;> simp))
  have hfun : Function.Exact Q.f.hom Q.g.hom :=
    (ShortComplex.ab_exact_iff_function_exact (S := Q)).mp hQ
  constructor
  · intro hz
    rcases (hfun z).mp hz with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have hi := congrArg (K.iCycles n).hom hy
    have hcomp := ConcreteCategory.congr_hom (K.toCycles_i (n - 1) n) y
    rw [ConcreteCategory.comp_apply] at hcomp
    exact hcomp.symm.trans hi
  · rintro ⟨y, hy⟩
    apply (hfun z).mpr
    refine ⟨y, ?_⟩
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    have hcomp := ConcreteCategory.congr_hom (K.toCycles_i (n - 1) n) y
    rw [ConcreteCategory.comp_apply] at hcomp
    exact hcomp.trans hy

private theorem selectedCechResolutionTotal_ι_d_projection_cech_explicit
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p n n' : ℕ)
    (hn : q + p = n) (hn' : q + p + 1 = n') :
    ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) q p n hn ≫
        (selectedCechResolutionTotalComplex 𝒰 F).d n n') ≫
      selectedCechResolutionTotalProjection 𝒰 F q (p + 1) n' hn' =
      ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
          (ComplexShape.up ℕ) (q, p) •
        ((selectedCechResolutionBicomplex 𝒰 F).X q).d p (p + 1) := by
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    (i₁ := q) (i₁' := q + 1) (by simp) p n' (by
      change q + 1 + p = n'
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    q (i₂ := p) (i₂' := p + 1) (by simp) n' hn']
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  simp

private theorem IsLerayFor.selectedCechToResolutionTotal_homologyMap_surjective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F) (n : ℕ) :
    Function.Surjective
      (HomologicalComplex.homologyMap
        (selectedCechToResolutionTotal 𝒰 F) n).hom := by
  let K := (selectedCechComplexFunctor 𝒰).obj F.val
  let T := selectedCechResolutionTotalComplex 𝒰 F
  let e := selectedCechToResolutionTotal 𝒰 F
  intro α
  have hπsurj : Function.Surjective (T.homologyπ n).hom :=
    (AddCommGrpCat.epi_iff_surjective (T.homologyπ n)).mp inferInstance
  rcases hπsurj α with ⟨z, rfl⟩
  let x : T.X n := (T.iCycles n).hom z
  have hxcycle : (T.d n (n + 1)).hom x = 0 := by
    have h := ConcreteCategory.congr_hom (T.iCycles_d n (n + 1)) z
    simpa only [x, ConcreteCategory.comp_apply, map_zero] using h
  rcases hLeray.selectedCechResolutionTotal_normalizeColumns n x hxcycle with
    ⟨y, hsupp, hx'cycle⟩
  let x' : T.X n := x - (T.d (n - 1) n).hom y
  have hx'cycle' :
      ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' = 0 := by
    simpa only [x'] using hx'cycle
  let a0 := (selectedCechResolutionTotalProjection 𝒰 F 0 n n (by simp)).hom x'
  have hx'eq :
      x' = ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) 0 n n (by simp)).hom a0 :=
    selectedCechResolutionTotal_eq_zeroColumn_of_supportedAtMost
      𝒰 F n x' hsupp
  have ha0res :
      (((selectedCechResolutionBicomplex 𝒰 F).d 0 1).f n).hom a0 = 0 := by
    have hformula := ConcreteCategory.congr_hom
      (selectedCechResolutionTotal_ι_d_projection_resolution_explicit
        𝒰 F 0 n n (n + 1) (by omega) (by omega)) a0
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hformula
    rw [← hformula]
    rw [← hx'eq]
    have hp := congrArg
      (selectedCechResolutionTotalProjection 𝒰 F (0 + 1) n (n + 1)
        (by omega)).hom hx'cycle'
    simpa only [map_zero] using hp
  have ha0cech :
      (((selectedCechResolutionBicomplex 𝒰 F).X 0).d n (n + 1)).hom a0 = 0 := by
    have hformula := ConcreteCategory.congr_hom
      (selectedCechResolutionTotal_ι_d_projection_cech_explicit
        𝒰 F 0 n n (n + 1) (by omega) (by omega)) a0
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hformula
    have hsigned :
        (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (0, n) •
            ((selectedCechResolutionBicomplex 𝒰 F).X 0).d n (n + 1)).hom a0 = 0 := by
      rw [← hformula]
      rw [← hx'eq]
      have hp := congrArg
        (selectedCechResolutionTotalProjection 𝒰 F 0 (n + 1) (n + 1)
          (by omega)).hom hx'cycle'
      simpa only [map_zero] using hp
    simpa using hsigned
  rcases (selectedCechResolutionAugmentation_exactAtZero 𝒰 F n a0).mp ha0res with
    ⟨a, ha⟩
  have hacycle : (K.d n (n + 1)).hom a = 0 := by
    apply selectedCechResolutionAugmentation_f_injective 𝒰 F (n + 1)
    have hcomm := ConcreteCategory.congr_hom
      ((selectedCechResolutionAugmentation 𝒰 F).comm n (n + 1)) a
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomm
    calc
      ((selectedCechResolutionAugmentation 𝒰 F).f (n + 1)).hom
          ((K.d n (n + 1)).hom a) =
        (((selectedCechResolutionBicomplex 𝒰 F).X 0).d n (n + 1)).hom
          (((selectedCechResolutionAugmentation 𝒰 F).f n).hom a) := hcomm.symm
      _ = (((selectedCechResolutionBicomplex 𝒰 F).X 0).d n (n + 1)).hom a0 := by rw [ha]
      _ = 0 := ha0cech
      _ = ((selectedCechResolutionAugmentation 𝒰 F).f (n + 1)).hom 0 := by
        rw [map_zero]
  have hacycleSc : (K.sc n).g.hom a = 0 := by
    change (K.d n ((ComplexShape.up ℕ).next n)).hom a = 0
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp]
    exact hacycle
  let za : K.cycles n := ((K.sc n).abCyclesIso.inv).hom ⟨a, hacycleSc⟩
  have hza_i : (K.iCycles n).hom za = a := by
    simpa only [za] using (K.sc n).abCyclesIso_inv_apply_iCycles ⟨a, hacycleSc⟩
  have hx'cycleSc : (T.sc n).g.hom x' = 0 := by
    change (T.d n ((ComplexShape.up ℕ).next n)).hom x' = 0
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp]
    simpa only [x'] using hx'cycle
  let z' : T.cycles n := ((T.sc n).abCyclesIso.inv).hom ⟨x', hx'cycleSc⟩
  have hz'_i : (T.iCycles n).hom z' = x' := by
    simpa only [z'] using (T.sc n).abCyclesIso_inv_apply_iCycles ⟨x', hx'cycleSc⟩
  have hdiffcycle : (T.homologyπ n).hom (z - z') = 0 := by
    apply (cochainHomologyπ_eq_zero_iff_boundary T n (z - z')).mpr
    refine ⟨y, ?_⟩
    rw [map_sub, hz'_i]
    change (T.d (n - 1) n).hom y = x - x'
    dsimp [x']
    abel
  have hclasses : (T.homologyπ n).hom z' = (T.homologyπ n).hom z := by
    rw [map_sub, sub_eq_zero] at hdiffcycle
    exact hdiffcycle.symm
  have hcycles :
      (HomologicalComplex.cyclesMap e n).hom za = z' := by
    apply (AddCommGrpCat.mono_iff_injective (T.iCycles n)).mp inferInstance
    have hmap := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i e n) za
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap
    rw [hmap, hza_i, hz'_i, hx'eq]
    dsimp only [e]
    rw [selectedCechToResolutionTotal_f, ConcreteCategory.comp_apply, ha]
    rfl
  refine ⟨(K.homologyπ n).hom za, ?_⟩
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality e n) za
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [hnat, hcycles, hclasses]

private theorem selectedCechResolutionTotal_horizontalCycle_succ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (m p : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X (m + 1 + (p + 1)))
    (hsupp : SelectedCechResolutionTotalSupportedAtMost 𝒰 F
      (m + 1 + (p + 1)) (m + 1) x)
    (hdiff : SelectedCechResolutionTotalSupportedAtMost 𝒰 F
      (m + 1 + (p + 1) + 1) 0
      (((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + 1 + (p + 1)) (m + 1 + (p + 1) + 1)).hom x)) :
    (((selectedCechResolutionBicomplex 𝒰 F).d (m + 1) (m + 2)).f
        (p + 1)).hom
      ((selectedCechResolutionTotalProjection 𝒰 F (m + 1) (p + 1)
        (m + 1 + (p + 1)) (by omega)).hom x) = 0 := by
  have hrzero :
      (selectedCechResolutionTotalProjection 𝒰 F (m + 2) p
        (m + 1 + (p + 1)) (by omega)).hom x = 0 :=
    hsupp (m + 2) p (by omega) (by omega)
  have hleft := hdiff (m + 2) (p + 1) (by omega) (by omega)
  have hformula := ConcreteCategory.congr_hom
    (selectedCechResolutionTotal_d_projection_succ_succ 𝒰 F (m + 1) p) x
  have hformula' :
      (((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + 1 + (p + 1)) (m + 1 + (p + 1) + 1) ≫
        selectedCechResolutionTotalProjection 𝒰 F (m + 2) (p + 1)
          (m + 1 + (p + 1) + 1) (by omega)).hom x) =
        (((selectedCechResolutionBicomplex 𝒰 F).d (m + 1) (m + 2)).f
            (p + 1)).hom
            ((selectedCechResolutionTotalProjection 𝒰 F (m + 1) (p + 1)
              (m + 1 + (p + 1)) (by omega)).hom x) +
          (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (m + 2, p) •
            ((selectedCechResolutionBicomplex 𝒰 F).X (m + 2)).d
              p (p + 1)).hom
            ((selectedCechResolutionTotalProjection 𝒰 F (m + 2) p
              (m + 1 + (p + 1)) (by omega)).hom x) := by
    simpa only [Nat.add_assoc] using hformula
  have hsum :
      (((selectedCechResolutionBicomplex 𝒰 F).d (m + 1) (m + 2)).f
          (p + 1)).hom
          ((selectedCechResolutionTotalProjection 𝒰 F (m + 1) (p + 1)
            (m + 1 + (p + 1)) (by omega)).hom x) +
        (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
            (ComplexShape.up ℕ) (m + 2, p) •
          ((selectedCechResolutionBicomplex 𝒰 F).X (m + 2)).d
            p (p + 1)).hom
          ((selectedCechResolutionTotalProjection 𝒰 F (m + 2) p
            (m + 1 + (p + 1)) (by omega)).hom x) = 0 := by
    calc
      _ = (((selectedCechResolutionTotalComplex 𝒰 F).d
            (m + 1 + (p + 1)) (m + 1 + (p + 1) + 1) ≫
          selectedCechResolutionTotalProjection 𝒰 F (m + 2) (p + 1)
            (m + 1 + (p + 1) + 1) (by omega)).hom x) := hformula'.symm
      _ = 0 := hleft
  rw [hrzero, map_zero, add_zero] at hsum
  exact hsum

private theorem selectedCechResolutionTotal_horizontalCycle_zero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (m : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X (m + 1))
    (hdiff : SelectedCechResolutionTotalSupportedAtMost 𝒰 F
      (m + 2) 0
      (((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + 1) (m + 2)).hom x)) :
    (((selectedCechResolutionBicomplex 𝒰 F).d (m + 1) (m + 2)).f 0).hom
      ((selectedCechResolutionTotalProjection 𝒰 F (m + 1) 0
        (m + 1) (by omega)).hom x) = 0 := by
  calc
    _ = (selectedCechResolutionTotalProjection 𝒰 F (m + 1) 0
          (m + 1) (by omega) ≫
        ((selectedCechResolutionBicomplex 𝒰 F).d (m + 1) (m + 2)).f 0).hom x := by
          rfl
    _ = (((selectedCechResolutionTotalComplex 𝒰 F).d (m + 1) (m + 2) ≫
          selectedCechResolutionTotalProjection 𝒰 F (m + 2) 0
            (m + 2) (by omega)).hom x) := by
          rw [selectedCechResolutionTotal_d_projection_succ_zero]
    _ = 0 := hdiff (m + 2) 0 (by omega) (by omega)

private theorem selectedCechResolutionTotal_sub_boundary_supportedAtMost
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (m p : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X (m + 1 + p))
    (hsupp : SelectedCechResolutionTotalSupportedAtMost 𝒰 F
      (m + 1 + p) (m + 1) x)
    (ycomp : ((selectedCechResolutionBicomplex 𝒰 F).X m).X p)
    (y : (selectedCechResolutionTotalComplex 𝒰 F).X (m + p))
    (hy : y = ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
      (ComplexShape.up ℕ) m p (m + p) (by rfl)).hom ycomp)
    (hycomp :
      (((selectedCechResolutionBicomplex 𝒰 F).d m (m + 1)).f p).hom ycomp =
        (selectedCechResolutionTotalProjection 𝒰 F (m + 1) p
          (m + 1 + p) (by omega)).hom x) :
    SelectedCechResolutionTotalSupportedAtMost 𝒰 F (m + 1 + p) m
      (x - ((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + p) (m + 1 + p)).hom y) := by
  subst y
  intro r s hrs hmr
  change (selectedCechResolutionTotalProjection 𝒰 F r s
    (m + 1 + p) hrs).hom
    (x - ((selectedCechResolutionTotalComplex 𝒰 F).d
      (m + p) (m + 1 + p)).hom
        (((selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) m p (m + p) (by rfl)).hom ycomp)) = 0
  rw [map_sub]
  by_cases hr : r = m + 1
  · subst r
    have hs : s = p := by omega
    subst s
    have himage := ConcreteCategory.congr_hom
      (selectedCechResolutionTotal_ι_d_projection_resolution_explicit
        𝒰 F m p (m + p) (m + 1 + p) (by rfl) (by rfl)) ycomp
    have himage' :
        (selectedCechResolutionTotalProjection 𝒰 F (m + 1) p
          (m + 1 + p) (by omega)).hom
          (((selectedCechResolutionTotalComplex 𝒰 F).d
            (m + p) (m + 1 + p)).hom
              (((selectedCechResolutionBicomplex 𝒰 F).ιTotal
                (ComplexShape.up ℕ) m p (m + p) (by rfl)).hom ycomp)) =
          (((selectedCechResolutionBicomplex 𝒰 F).d m (m + 1)).f p).hom
            ycomp := by
      simpa only [Nat.add_assoc] using himage
    rw [himage', hycomp]
    simp
  · have hxzero := hsupp r s hrs (by omega)
    rw [hxzero, zero_sub]
    have hzero := ConcreteCategory.congr_hom
      (selectedCechResolutionTotal_ι_d_projection_zero_explicit
        𝒰 F m p (m + p) (m + 1 + p) r s
        (by rfl) (by omega) hrs
        (Or.inl (by omega)) (Or.inl (by omega))) ycomp
    have hzero' :
        (selectedCechResolutionTotalProjection 𝒰 F r s
          (m + 1 + p) hrs).hom
          (((selectedCechResolutionTotalComplex 𝒰 F).d
            (m + p) (m + 1 + p)).hom
              (((selectedCechResolutionBicomplex 𝒰 F).ιTotal
                (ComplexShape.up ℕ) m p (m + p) (by rfl)).hom ycomp)) = 0 := by
      simpa only [Nat.add_assoc, map_zero] using hzero
    rw [hzero']
    simp

private theorem selectedCechResolutionTotal_d_sub_boundary
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (m p : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X (m + 1 + p))
    (y : (selectedCechResolutionTotalComplex 𝒰 F).X (m + p)) :
    ((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + 1 + p) (m + 1 + p + 1)).hom
        (x - ((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + p) (m + 1 + p)).hom y) =
      ((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + 1 + p) (m + 1 + p + 1)).hom x := by
  rw [map_sub]
  change
    ((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + 1 + p) (m + 1 + p + 1)).hom x -
      (((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + p) (m + 1 + p) ≫
        (selectedCechResolutionTotalComplex 𝒰 F).d
          (m + 1 + p) (m + 1 + p + 1)).hom y) =
    ((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + 1 + p) (m + 1 + p + 1)).hom x
  rw [HomologicalComplex.d_comp_d]
  simp

private theorem IsLerayFor.selectedCechResolutionTotal_eliminateColumnOfDifferentialSupported
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (m p : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X (m + 1 + p))
    (hsupp : SelectedCechResolutionTotalSupportedAtMost 𝒰 F
      (m + 1 + p) (m + 1) x)
    (hdiff : SelectedCechResolutionTotalSupportedAtMost 𝒰 F
      (m + 1 + p + 1) 0
      (((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + 1 + p) (m + 1 + p + 1)).hom x)) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (m + p),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + p) (m + 1 + p)).hom y
      SelectedCechResolutionTotalSupportedAtMost 𝒰 F (m + 1 + p) m x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + 1 + p) (m + 1 + p + 1)).hom x' =
      ((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + 1 + p) (m + 1 + p + 1)).hom x := by
  let xcomp : ((selectedCechResolutionBicomplex 𝒰 F).X (m + 1)).X p :=
    (selectedCechResolutionTotalProjection 𝒰 F (m + 1) p
      (m + 1 + p) (by omega)).hom x
  have hxcycle :
      (((selectedCechResolutionBicomplex 𝒰 F).d (m + 1) (m + 2)).f p).hom
        xcomp = 0 := by
    rcases p with _ | p
    · simpa only [Nat.add_zero] using
        selectedCechResolutionTotal_horizontalCycle_zero m x hdiff
    · exact selectedCechResolutionTotal_horizontalCycle_succ m p x hsupp hdiff
  let C := selectedCechResolutionColumn 𝒰 F p
  have hexact : C.ExactAt (m + 1) :=
    hLeray.selectedCechResolutionColumn_exactAt (m + 1) (by omega) p
  rw [C.exactAt_iff' m (m + 1) (m + 2) (by simp) (by simp)] at hexact
  rw [ShortComplex.ab_exact_iff_ker_le_range] at hexact
  have hxmem : xcomp ∈ ((C.d (m + 1) (m + 2)).hom).ker := by
    change ((C.d (m + 1) (m + 2)).hom xcomp = 0)
    exact hxcycle
  rcases hexact hxmem with ⟨ycomp, hycomp⟩
  change (C.d m (m + 1)).hom ycomp = xcomp at hycomp
  let y : (selectedCechResolutionTotalComplex 𝒰 F).X (m + p) :=
    ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
      (ComplexShape.up ℕ) m p (m + p) (by
        change m + p = m + p
        rfl)).hom ycomp
  refine ⟨y, ?_, ?_⟩
  · exact selectedCechResolutionTotal_sub_boundary_supportedAtMost
      m p x hsupp ycomp y rfl hycomp
  · exact selectedCechResolutionTotal_d_sub_boundary m p x y

private theorem IsLerayFor.selectedCechResolutionTotal_eliminateColumnOfDifferentialSupportedAt
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (n m p : ℕ) (hdegree : m + 1 + p = n)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hsupp : SelectedCechResolutionTotalSupportedAtMost 𝒰 F n (m + 1) x)
    (hdiff : SelectedCechResolutionTotalSupportedAtMost 𝒰 F (n + 1) 0
      (((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x)) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (n - 1),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y
      SelectedCechResolutionTotalSupportedAtMost 𝒰 F n m x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' =
          ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x := by
  subst n
  rcases hLeray.selectedCechResolutionTotal_eliminateColumnOfDifferentialSupported
      m p x hsupp hdiff with ⟨y, hsupp', hdiff'⟩
  have hprev : m + p = m + 1 + p - 1 := by omega
  let y' : (selectedCechResolutionTotalComplex 𝒰 F).X (m + 1 + p - 1) :=
    selectedCechResolutionTotalDegreeAddEquiv 𝒰 F hprev y
  refine ⟨y', ?_⟩
  have hd := selectedCechResolutionTotal_d_transport_source
    𝒰 F (k := m + 1 + p) hprev y
  change
    SelectedCechResolutionTotalSupportedAtMost 𝒰 F (m + 1 + p) m
        (x - ((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + 1 + p - 1) (m + 1 + p)).hom y') ∧
      ((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + 1 + p) (m + 1 + p + 1)).hom
        (x - ((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + 1 + p - 1) (m + 1 + p)).hom y') =
      ((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + 1 + p) (m + 1 + p + 1)).hom x
  rw [← hd]
  exact ⟨hsupp', hdiff'⟩

private theorem IsLerayFor.selectedCechResolutionTotal_normalizePreimageAux
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (n k : ℕ) (hk : k ≤ n)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hsupp : SelectedCechResolutionTotalSupportedAtMost 𝒰 F n k x)
    (hdiff : SelectedCechResolutionTotalSupportedAtMost 𝒰 F (n + 1) 0
      (((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x)) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (n - 1),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y
      SelectedCechResolutionTotalSupportedAtMost 𝒰 F n 0 x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' =
          ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x := by
  induction k generalizing x with
  | zero =>
      refine ⟨0, ?_⟩
      simp only [map_zero, sub_zero]
      exact ⟨hsupp, trivial⟩
  | succ k ih =>
      let p := n - (k + 1)
      have hdegree : k + 1 + p = n := by
        dsimp [p]
        omega
      rcases hLeray.selectedCechResolutionTotal_eliminateColumnOfDifferentialSupportedAt
          n k p hdegree x hsupp hdiff with ⟨y₁, hsupp₁, hdiff₁⟩
      let x₁ := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y₁
      have hdiffForX₁ : SelectedCechResolutionTotalSupportedAtMost 𝒰 F (n + 1) 0
          (((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x₁) := by
        rw [hdiff₁]
        exact hdiff
      rcases ih (by omega) x₁ hsupp₁ hdiffForX₁ with
        ⟨y₂, hsupp₂, hdiff₂⟩
      refine ⟨y₁ + y₂, ?_⟩
      have hmap :
          ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom (y₁ + y₂) =
            ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y₁ +
              ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y₂ :=
        map_add _ y₁ y₂
      rw [hmap]
      dsimp only
      have hx :
          x - (((selectedCechResolutionTotalComplex 𝒰 F).d
              (n - 1) n).hom y₁ +
            ((selectedCechResolutionTotalComplex 𝒰 F).d
              (n - 1) n).hom y₂) =
          x₁ - ((selectedCechResolutionTotalComplex 𝒰 F).d
            (n - 1) n).hom y₂ := by
        dsimp [x₁]
        abel
      rw [hx]
      exact ⟨hsupp₂, hdiff₂.trans hdiff₁⟩

private theorem IsLerayFor.selectedCechResolutionTotal_normalizePreimage
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F)
    (n : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hdiff : SelectedCechResolutionTotalSupportedAtMost 𝒰 F (n + 1) 0
      (((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x)) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (n - 1),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y
      SelectedCechResolutionTotalSupportedAtMost 𝒰 F n 0 x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' =
          ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x :=
  hLeray.selectedCechResolutionTotal_normalizePreimageAux n n (by rfl) x
    (selectedCechResolutionTotal_supportedAtMost_top 𝒰 F n x) hdiff

private theorem selectedCechToResolutionTotal_f_supportedAtMost_zero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (a : ((selectedCechComplexFunctor 𝒰).obj
      F.val).X n) :
    SelectedCechResolutionTotalSupportedAtMost 𝒰 F n 0
      (((selectedCechToResolutionTotal 𝒰 F).f n).hom a) := by
  intro q p hqp hq
  rw [selectedCechToResolutionTotal_f, ConcreteCategory.comp_apply]
  have hformula := ConcreteCategory.congr_hom
    (selectedCechResolutionTotal_ι_projection_general 𝒰 F
      q p n hqp 0 n (by simp))
    (((selectedCechResolutionAugmentation 𝒰 F).f n).hom a)
  rw [ConcreteCategory.comp_apply] at hformula
  have h0q : (0 : ℕ) ≠ q := by omega
  simpa only [dif_neg h0q, map_zero] using hformula

private theorem selectedCechToResolutionTotal_f_injective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Injective ((selectedCechToResolutionTotal 𝒰 F).f n).hom := by
  intro a b hab
  apply selectedCechResolutionAugmentation_f_injective 𝒰 F n
  have hp := congrArg
    (selectedCechResolutionTotalProjection 𝒰 F 0 n n (by simp)).hom hab
  rw [selectedCechToResolutionTotal_f, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply] at hp
  have hself := selectedCechResolutionTotal_ι_projection_self 𝒰 F 0 n n (by simp)
  have hselfa := ConcreteCategory.congr_hom hself
    (((selectedCechResolutionAugmentation 𝒰 F).f n).hom a)
  have hselfb := ConcreteCategory.congr_hom hself
    (((selectedCechResolutionAugmentation 𝒰 F).f n).hom b)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hselfa hselfb
  exact hselfa.symm.trans (hp.trans hselfb)

private theorem selectedCechToResolutionTotal_f_projection_zero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (a : ((selectedCechComplexFunctor 𝒰).obj
      F.val).X n) :
    (selectedCechResolutionTotalProjection 𝒰 F 0 n n (by simp)).hom
        (((selectedCechToResolutionTotal 𝒰 F).f n).hom a) =
      ((selectedCechResolutionAugmentation 𝒰 F).f n).hom a := by
  rw [selectedCechToResolutionTotal_f, ConcreteCategory.comp_apply]
  have hself := selectedCechResolutionTotal_ι_projection_self 𝒰 F 0 n n (by simp)
  have h := ConcreteCategory.congr_hom hself
    (((selectedCechResolutionAugmentation 𝒰 F).f n).hom a)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
  exact h

private theorem IsLerayFor.selectedCechToResolutionTotal_homologyMap_injective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F) (n : ℕ) :
    Function.Injective
      (HomologicalComplex.homologyMap
        (selectedCechToResolutionTotal 𝒰 F) n).hom := by
  let K := (selectedCechComplexFunctor 𝒰).obj F.val
  let T := selectedCechResolutionTotalComplex 𝒰 F
  let e := selectedCechToResolutionTotal 𝒰 F
  intro α β hαβ
  have hmapzero :
      (HomologicalComplex.homologyMap e n).hom (α - β) = 0 := by
    rw [map_sub, hαβ, sub_self]
  have hπsurj : Function.Surjective (K.homologyπ n).hom :=
    (AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance
  rcases hπsurj (α - β) with ⟨z, hz⟩
  have hzmapzero :
      (HomologicalComplex.homologyMap e n).hom ((K.homologyπ n).hom z) = 0 := by
    rw [hz]
    exact hmapzero
  let zt : T.cycles n := (HomologicalComplex.cyclesMap e n).hom z
  have hztclass : (T.homologyπ n).hom zt = 0 := by
    have hnat := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality e n) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
    rw [← hnat]
    exact hzmapzero
  rcases (cochainHomologyπ_eq_zero_iff_boundary T n zt).mp hztclass with
    ⟨w, hw⟩
  let a : K.X n := (K.iCycles n).hom z
  have hzt_i :
      (T.iCycles n).hom zt = (e.f n).hom a := by
    have hmap := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i e n) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap
    exact hmap
  have hzclasszero : (K.homologyπ n).hom z = 0 := by
    rcases n with _ | k
    · have hztzero : (T.iCycles 0).hom zt = 0 := by
        rw [← hw]
        rw [T.shape 0 0 (by simp)]
        rfl
      have hedgezero : (e.f 0).hom a = 0 := hzt_i.symm.trans hztzero
      have hazero : a = 0 := by
        apply selectedCechToResolutionTotal_f_injective 𝒰 F 0
        simpa only [map_zero] using hedgezero
      have hzzero : z = 0 := by
        apply (AddCommGrpCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
        simpa only [a, map_zero] using hazero
      rw [hzzero, map_zero]
    · have hedgeSupp := selectedCechToResolutionTotal_f_supportedAtMost_zero
          𝒰 F (k + 1) a
      have hprev : k + 1 - 1 = k := by omega
      let w0 : T.X k := selectedCechResolutionTotalDegreeAddEquiv 𝒰 F hprev w
      have hdw0 := selectedCechResolutionTotal_d_transport_source
        𝒰 F (k := k + 1) hprev w
      have hw0 : (T.d k (k + 1)).hom w0 = (T.iCycles (k + 1)).hom zt := by
        exact hdw0.symm.trans hw
      have hdiff : SelectedCechResolutionTotalSupportedAtMost 𝒰 F (k + 1) 0
          ((T.d k (k + 1)).hom w0) := by
        rw [hw0, hzt_i]
        exact hedgeSupp
      rcases hLeray.selectedCechResolutionTotal_normalizePreimage k w0 hdiff with
        ⟨v, hw'supp, hw'diff⟩
      let w' : T.X k := w0 - (T.d (k - 1) k).hom v
      have hw'diff' : (T.d k (k + 1)).hom w' = (T.d k (k + 1)).hom w0 := by
        simpa only [w'] using hw'diff
      let b0 := (selectedCechResolutionTotalProjection 𝒰 F 0 k k (by simp)).hom w'
      have hw'eq :
          w' = ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
            (ComplexShape.up ℕ) 0 k k (by simp)).hom b0 :=
        selectedCechResolutionTotal_eq_zeroColumn_of_supportedAtMost
          𝒰 F k w' hw'supp
      have hb0res :
          (((selectedCechResolutionBicomplex 𝒰 F).d 0 1).f k).hom b0 = 0 := by
        have hformula := ConcreteCategory.congr_hom
          (selectedCechResolutionTotal_ι_d_projection_resolution_explicit
            𝒰 F 0 k k (k + 1) (by omega) (by omega)) b0
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hformula
        rw [← hformula]
        rw [← hw'eq]
        have hp₁ := congrArg
          (selectedCechResolutionTotalProjection 𝒰 F (0 + 1) k (k + 1)
            (by omega)).hom hw'diff'
        have hp₂ := congrArg
          (selectedCechResolutionTotalProjection 𝒰 F (0 + 1) k (k + 1)
            (by omega)).hom hw0
        have hp₃ := congrArg
          (selectedCechResolutionTotalProjection 𝒰 F (0 + 1) k (k + 1)
            (by omega)).hom hzt_i
        exact hp₁.trans (hp₂.trans (hp₃.trans
          (hedgeSupp (0 + 1) k (by omega) (by omega))))
      rcases (selectedCechResolutionAugmentation_exactAtZero 𝒰 F k b0).mp hb0res with
        ⟨b, hb⟩
      have hb0cech :
          (((selectedCechResolutionBicomplex 𝒰 F).X 0).d k (k + 1)).hom b0 =
            ((selectedCechResolutionAugmentation 𝒰 F).f (k + 1)).hom a := by
        have hformula := ConcreteCategory.congr_hom
          (selectedCechResolutionTotal_ι_d_projection_cech_explicit
            𝒰 F 0 k k (k + 1) (by omega) (by omega)) b0
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hformula
        have hformula' :
            (selectedCechResolutionTotalProjection 𝒰 F 0 (k + 1) (k + 1)
                (by omega)).hom
              (((selectedCechResolutionTotalComplex 𝒰 F).d k (k + 1)).hom
                (((selectedCechResolutionBicomplex 𝒰 F).ιTotal
                  (ComplexShape.up ℕ) 0 k k (by simp)).hom b0)) =
              (((selectedCechResolutionBicomplex 𝒰 F).X 0).d
                k (k + 1)).hom b0 := by
          simpa using hformula
        rw [← hformula']
        rw [← hw'eq]
        have hp₁ := congrArg
          (selectedCechResolutionTotalProjection 𝒰 F 0 (k + 1) (k + 1)
            (by omega)).hom hw'diff'
        have hp₂ := congrArg
          (selectedCechResolutionTotalProjection 𝒰 F 0 (k + 1) (k + 1)
            (by omega)).hom hw0
        exact hp₁.trans (hp₂.trans
          ((congrArg
            (selectedCechResolutionTotalProjection 𝒰 F 0 (k + 1) (k + 1)
              (by omega)).hom hzt_i).trans
            (selectedCechToResolutionTotal_f_projection_zero 𝒰 F (k + 1) a)))
      have hba : (K.d k (k + 1)).hom b = a := by
        apply selectedCechResolutionAugmentation_f_injective 𝒰 F (k + 1)
        have hcomm := ConcreteCategory.congr_hom
          ((selectedCechResolutionAugmentation 𝒰 F).comm k (k + 1)) b
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomm
        calc
          ((selectedCechResolutionAugmentation 𝒰 F).f (k + 1)).hom
              ((K.d k (k + 1)).hom b) =
            (((selectedCechResolutionBicomplex 𝒰 F).X 0).d k (k + 1)).hom
              (((selectedCechResolutionAugmentation 𝒰 F).f k).hom b) := hcomm.symm
          _ = (((selectedCechResolutionBicomplex 𝒰 F).X 0).d k (k + 1)).hom b0 := by
            rw [hb]
          _ = ((selectedCechResolutionAugmentation 𝒰 F).f (k + 1)).hom a := hb0cech
      apply (cochainHomologyπ_eq_zero_iff_boundary K (k + 1) z).mpr
      refine ⟨b, ?_⟩
      simpa only [Nat.add_sub_cancel_right, a] using hba
  have hsubzero : α - β = 0 := by
    rw [← hz]
    exact hzclasszero
  exact sub_eq_zero.mp hsubzero

/-- Leray vanishing makes the selected Čech edge an actual quasi-isomorphism. -/
theorem IsLerayFor.selectedCechToResolutionTotal_quasiIso
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (hLeray : IsLerayFor 𝒰 F) :
    QuasiIso (selectedCechToResolutionTotal 𝒰 F) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨hLeray.selectedCechToResolutionTotal_homologyMap_injective n,
    hLeray.selectedCechToResolutionTotal_homologyMap_surjective n⟩

/-- Homology equivalence induced by the selected Čech edge quasi-isomorphism. -/
noncomputable def selectedCechToResolutionTotalHomologyEquiv
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    (hLeray : IsLerayFor 𝒰 F) (n : ℕ) :
    (((selectedCechComplexFunctor 𝒰).obj
      F.val).homology n : Type (u + 1)) ≃+
      ((selectedCechResolutionTotalComplex 𝒰 F).homology n : Type (u + 1)) := by
  letI : QuasiIso (selectedCechToResolutionTotal 𝒰 F) :=
    hLeray.selectedCechToResolutionTotal_quasiIso
  exact (isoOfQuasiIsoAt
    (selectedCechToResolutionTotal 𝒰 F) n).addCommGroupIsoToAddEquiv

private theorem baseToSelectedCechZero_app_injective
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (I : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    Function.Injective ((baseToSelectedCechZero 𝒰).app I.val).hom := by
  intro x y hxy
  have hTypePresheaf : Presheaf.IsSheaf S.topology
      (I.val ⋙ forget AddCommGrpCat.{u + 1}) :=
    (Presheaf.isSheaf_iff_isSheaf_forget
      (J := S.topology) (P' := I.val)
      (forget AddCommGrpCat.{u + 1})).mp I.cond
  have hType : Presieve.IsSheaf S.topology
      (I.val ⋙ forget AddCommGrpCat.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type S.topology
      (I.val ⋙ forget AddCommGrpCat.{u + 1})).mp hTypePresheaf
  have hgen := hType (Sieve.generate 𝒰.presieve) 𝒰.mem_topology
  have hcover : Presieve.IsSheafFor
      (I.val ⋙ forget AddCommGrpCat.{u + 1}) 𝒰.presieve :=
    (Presieve.isSheafFor_iff_generate 𝒰.presieve).mpr hgen
  have harrows := (Presieve.isSheafFor_arrows_iff
    (I.val ⋙ forget AddCommGrpCat.{u + 1})
    (fun i => homOfLE (𝒰.inclusion i))).mp hcover
  let sections := fun i => I.val.map (homOfLE (𝒰.inclusion i)).op x
  have hcompat : Presieve.Arrows.Compatible
      (I.val ⋙ forget AddCommGrpCat.{u + 1})
      (fun i => homOfLE (𝒰.inclusion i)) sections :=
    (Presieve.Arrows.toCompatible
      (I.val ⋙ forget AddCommGrpCat.{u + 1})
      (fun i => homOfLE (𝒰.inclusion i)) x).property
  obtain ⟨_, _, hunique⟩ := harrows sections hcompat
  have hx := hunique x (by intro i; rfl)
  have hy := hunique y (by
    intro i
    have hi := congrFun hxy (fun _ => i)
    change I.val.map (homOfLE (𝒰.inclusion i)).op y =
      I.val.map (homOfLE (𝒰.inclusion i)).op x
    simpa only [baseToSelectedCechZero_app_apply] using hi.symm)
  exact hx.trans hy.symm

private def SelectedCechResolutionTotalCechSupportedAtMost
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n m : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n) : Prop :=
  ∀ q p : ℕ, ∀ h : q + p = n, m < p →
    (selectedCechResolutionTotalProjection 𝒰 F q p n h).hom x = 0

private theorem selectedCechResolutionTotal_cechSupportedAtMost_top
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n) :
    SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F n n x := by
  intro q p hqp hp
  omega

private noncomputable def selectedCechResolutionTotalCechDiagonalProjection
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) (p : Fin (n + 1)) :
    (selectedCechResolutionTotalComplex 𝒰 F).X n ⟶
      ((selectedCechResolutionBicomplex 𝒰 F).X (n - p)).X p :=
  selectedCechResolutionTotalProjection 𝒰 F (n - p) p n (by omega)

private noncomputable def selectedCechResolutionTotalCechDiagonalInclusion
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) (p : Fin (n + 1)) :
    ((selectedCechResolutionBicomplex 𝒰 F).X (n - p)).X p ⟶
      (selectedCechResolutionTotalComplex 𝒰 F).X n :=
  (selectedCechResolutionBicomplex 𝒰 F).ιTotal
    (ComplexShape.up ℕ) (n - p) p n (by
      change (n - (p : ℕ)) + (p : ℕ) = n
      omega)

private theorem selectedCechResolutionTotal_cechDecomposition
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    ∑ p : Fin (n + 1),
        selectedCechResolutionTotalCechDiagonalProjection 𝒰 F n p ≫
          selectedCechResolutionTotalCechDiagonalInclusion 𝒰 F n p =
      𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro q' p' h
  change q' + p' = n at h
  let p : Fin (n + 1) := ⟨p', by omega⟩
  rw [Preadditive.comp_sum]
  rw [Finset.sum_eq_single p]
  · rw [← Category.assoc]
    simp only [selectedCechResolutionTotalCechDiagonalProjection,
      selectedCechResolutionTotalCechDiagonalInclusion,
      selectedCechResolutionTotal_ι_projection_general]
    have hq : q' = n - (p : ℕ) := by
      dsimp only [p]
      omega
    simp [p, hq]
    exact (Category.comp_id _).symm
  · intro r _ hr
    rw [← Category.assoc]
    simp only [selectedCechResolutionTotalCechDiagonalProjection,
      selectedCechResolutionTotalCechDiagonalInclusion,
      selectedCechResolutionTotal_ι_projection_general]
    have hpne : p' ≠ (r : ℕ) := by
      intro eq
      apply hr
      apply Fin.ext
      exact eq.symm
    by_cases hq : q' = n - (r : ℕ)
    · simp [hq, hpne]
    · simp [hq]
  · simp

private theorem selectedCechResolutionTotal_eq_cechZero_of_supportedAtMost
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hsupp : SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F n 0 x) :
    x = ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) n 0 n (by simp)).hom
        ((selectedCechResolutionTotalProjection 𝒰 F n 0 n (by simp)).hom x) := by
  let p0 : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  let ev :
      (((selectedCechResolutionTotalComplex 𝒰 F).X n ⟶
          (selectedCechResolutionTotalComplex 𝒰 F).X n)) →+
        ((selectedCechResolutionTotalComplex 𝒰 F).X n : Type (u + 1)) :=
    { toFun := fun f => f.hom x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hdec := ConcreteCategory.congr_hom
    (selectedCechResolutionTotal_cechDecomposition 𝒰 F n) x
  change ev (∑ q : Fin (n + 1),
      selectedCechResolutionTotalCechDiagonalProjection 𝒰 F n q ≫
        selectedCechResolutionTotalCechDiagonalInclusion 𝒰 F n q) = ev (𝟙 _) at hdec
  rw [map_sum] at hdec
  change
    (∑ q : Fin (n + 1),
      (selectedCechResolutionTotalCechDiagonalInclusion 𝒰 F n q).hom
        ((selectedCechResolutionTotalCechDiagonalProjection 𝒰 F n q).hom x)) = x at hdec
  have hsum :
      (∑ q : Fin (n + 1),
        (selectedCechResolutionTotalCechDiagonalInclusion 𝒰 F n q).hom
          ((selectedCechResolutionTotalCechDiagonalProjection 𝒰 F n q).hom x)) =
        (selectedCechResolutionTotalCechDiagonalInclusion 𝒰 F n p0).hom
          ((selectedCechResolutionTotalCechDiagonalProjection 𝒰 F n p0).hom x) := by
    apply Finset.sum_eq_single p0
    · intro q _ hq
      have hp : 0 < (q : ℕ) := by
        by_contra hn
        apply hq
        apply Fin.ext
        simpa only [p0] using Nat.eq_zero_of_not_pos hn
      have hz := hsupp (n - q) q (by omega) hp
      rw [selectedCechResolutionTotalCechDiagonalProjection, hz, map_zero]
    · simp
  simpa only [p0, selectedCechResolutionTotalCechDiagonalInclusion,
    selectedCechResolutionTotalCechDiagonalProjection, Nat.cast_zero,
    Nat.sub_zero] using hdec.symm.trans hsum

private theorem selectedCechResolutionTotal_d_projection_succ_succ_commuted
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (q p : ℕ) :
    (selectedCechResolutionTotalComplex 𝒰 F).d
          (p + q + 1) (p + q + 2) ≫
        selectedCechResolutionTotalProjection 𝒰 F (q + 1) (p + 1)
          (p + q + 2) (by omega) =
      selectedCechResolutionTotalProjection 𝒰 F q (p + 1)
          (p + q + 1) (by omega) ≫
          ((selectedCechResolutionBicomplex 𝒰 F).d q (q + 1)).f (p + 1) +
        selectedCechResolutionTotalProjection 𝒰 F (q + 1) p
          (p + q + 1) (by omega) ≫
          (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (q + 1, p) •
            ((selectedCechResolutionBicomplex 𝒰 F).X (q + 1)).d p (p + 1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change a + b = p + q + 1 at h
  simp only [← Category.assoc, Preadditive.comp_add]
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    (i₁ := a) (i₁' := a + 1) (by simp) b (p + q + 2) (by
      change a + 1 + b = p + q + 2
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 F) (ComplexShape.up ℕ)
    a (i₂ := b) (i₂' := b + 1) (by simp) (p + q + 2) (by
      change a + (b + 1) = p + q + 2
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  by_cases haq : a = q
  · have hb : b = p + 1 := by omega
    subst a
    subst b
    simp
  · by_cases haqs : a = q + 1
    · have hb : b = p := by omega
      subst a
      subst b
      simp
    · simp [haq, haqs]

private theorem selectedCechResolutionTotal_eliminateCechOfDifferentialSupported
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (q m : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X ((m + 1) + q))
    (hsupp : SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F
      ((m + 1) + q) (m + 1) x)
    (hdiff : SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F
      ((m + 1) + q + 1) 0
      (((selectedCechResolutionTotalComplex 𝒰 F).d
        ((m + 1) + q) ((m + 1) + q + 1)).hom x)) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (m + q),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d
          (m + q) ((m + 1) + q)).hom y
      SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F
          ((m + 1) + q) m x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d
          ((m + 1) + q) ((m + 1) + q + 1)).hom x' =
        ((selectedCechResolutionTotalComplex 𝒰 F).d
          ((m + 1) + q) ((m + 1) + q + 1)).hom x := by
  let xcomp : ((selectedCechResolutionBicomplex 𝒰 F).X q).X (m + 1) :=
    (selectedCechResolutionTotalProjection 𝒰 F q (m + 1)
      ((m + 1) + q) (by omega)).hom x
  have hxcycle :
      (((selectedCechResolutionBicomplex 𝒰 F).X q).d
        (m + 1) (m + 2)).hom xcomp = 0 := by
    rcases q with _ | q
    · have hleft :
          (((selectedCechResolutionTotalComplex 𝒰 F).d
              (m + 1) (m + 2) ≫
            selectedCechResolutionTotalProjection 𝒰 F 0 (m + 2)
              (m + 2) (by omega)).hom x) = 0 :=
        hdiff 0 (m + 2) (by omega) (by omega)
      have hformula := ConcreteCategory.congr_hom
        (selectedCechResolutionTotal_d_projection_zero_succ 𝒰 F (m + 1)) x
      have hsigned :
          (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (0, m + 1) •
            ((selectedCechResolutionBicomplex 𝒰 F).X 0).d
              (m + 1) (m + 2)).hom xcomp = 0 := by
        have hsigned' := hformula.symm.trans hleft
        simpa only [xcomp, ConcreteCategory.comp_apply, Nat.add_assoc] using hsigned'
      simpa using hsigned
    · have hrzero :
          (selectedCechResolutionTotalProjection 𝒰 F q (m + 2)
            ((m + 1) + (q + 1)) (by omega)).hom x = 0 :=
        hsupp q (m + 2) (by omega) (by omega)
      have hleft :
          (((selectedCechResolutionTotalComplex 𝒰 F).d
              ((m + 1) + (q + 1)) ((m + 1) + (q + 1) + 1) ≫
            selectedCechResolutionTotalProjection 𝒰 F (q + 1) (m + 2)
              ((m + 1) + (q + 1) + 1) (by omega)).hom x) = 0 :=
        hdiff (q + 1) (m + 2) (by omega) (by omega)
      have hformula := ConcreteCategory.congr_hom
        (selectedCechResolutionTotal_d_projection_succ_succ_commuted
          𝒰 F q (m + 1)) x
      have hformula' :
          (((selectedCechResolutionTotalComplex 𝒰 F).d
              ((m + 1) + (q + 1)) ((m + 1) + (q + 1) + 1) ≫
            selectedCechResolutionTotalProjection 𝒰 F (q + 1) (m + 2)
              ((m + 1) + (q + 1) + 1) (by omega)).hom x) =
            (((selectedCechResolutionBicomplex 𝒰 F).d q (q + 1)).f
                (m + 2)).hom
              ((selectedCechResolutionTotalProjection 𝒰 F q (m + 2)
                ((m + 1) + (q + 1)) (by omega)).hom x) +
              (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
                  (ComplexShape.up ℕ) (q + 1, m + 1) •
                ((selectedCechResolutionBicomplex 𝒰 F).X (q + 1)).d
                  (m + 1) (m + 2)).hom xcomp := by
        simpa only [Nat.add_assoc] using hformula
      have hsum :
          (((selectedCechResolutionBicomplex 𝒰 F).d q (q + 1)).f
              (m + 2)).hom
              ((selectedCechResolutionTotalProjection 𝒰 F q (m + 2)
                ((m + 1) + (q + 1)) (by omega)).hom x) +
            (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
                (ComplexShape.up ℕ) (q + 1, m + 1) •
              ((selectedCechResolutionBicomplex 𝒰 F).X (q + 1)).d
                (m + 1) (m + 2)).hom xcomp = 0 := by
        exact hformula'.symm.trans hleft
      rw [hrzero, map_zero, zero_add] at hsum
      change
        ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
            (ComplexShape.up ℕ) (q + 1, m + 1) •
          (((selectedCechResolutionBicomplex 𝒰 F).X (q + 1)).d
            (m + 1) (m + 2)).hom xcomp = 0 at hsum
      exact (smul_eq_zero_iff_eq _).mp hsum
  let I := (largeSheafInjectiveResolution F).cocomplex.X q
  letI : Injective I := (largeSheafInjectiveResolution F).injective q
  let C := (selectedCechResolutionBicomplex 𝒰 F).X q
  have hexact : C.ExactAt (m + 1) := by
    change ((selectedCechComplexFunctor 𝒰).obj I.val).ExactAt (m + 1)
    exact injectiveSheaf_selectedCech_exactAt 𝒰 I (m + 1) (by omega)
  rw [C.exactAt_iff' m (m + 1) (m + 2) (by simp) (by simp)] at hexact
  rw [ShortComplex.ab_exact_iff_ker_le_range] at hexact
  have hxmem : xcomp ∈ ((C.d (m + 1) (m + 2)).hom).ker := by
    change (C.d (m + 1) (m + 2)).hom xcomp = 0
    exact hxcycle
  rcases hexact hxmem with ⟨ycomp, hycomp⟩
  change (C.d m (m + 1)).hom ycomp = xcomp at hycomp
  let ε := ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
    (ComplexShape.up ℕ) (q, m)
  let ycomp' : C.X m := ε⁻¹ • ycomp
  have hycomp' : (ε • C.d m (m + 1)).hom ycomp' = xcomp := by
    change (ε : ℤ) • (C.d m (m + 1)).hom (((ε⁻¹ : ℤˣ) : ℤ) • ycomp) = xcomp
    rw [map_zsmul, hycomp, smul_smul, ← Units.val_mul]
    have hunit : ε * ε⁻¹ = 1 := mul_inv_cancel ε
    have hval : ((ε * ε⁻¹ : ℤˣ) : ℤ) = 1 := congrArg Units.val hunit
    rw [hval, one_zsmul]
  let y : (selectedCechResolutionTotalComplex 𝒰 F).X (m + q) :=
    ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
      (ComplexShape.up ℕ) q m (m + q) (by
        change q + m = m + q
        omega)).hom ycomp'
  refine ⟨y, ?_, ?_⟩
  · intro r s hrs hms
    change (selectedCechResolutionTotalProjection 𝒰 F r s
      ((m + 1) + q) hrs).hom
      (x - ((selectedCechResolutionTotalComplex 𝒰 F).d
        (m + q) ((m + 1) + q)).hom y) = 0
    rw [map_sub]
    by_cases hs : s = m + 1
    · subst s
      have hr : r = q := by omega
      subst r
      have himage := ConcreteCategory.congr_hom
          (selectedCechResolutionTotal_ι_d_projection_cech_explicit
          𝒰 F q m (m + q) ((m + 1) + q) (by omega) (by omega)) ycomp'
      have himage' :
          (selectedCechResolutionTotalProjection 𝒰 F q (m + 1)
            ((m + 1) + q) (by omega)).hom
            (((selectedCechResolutionTotalComplex 𝒰 F).d
              (m + q) ((m + 1) + q)).hom y) =
            (ε • C.d m (m + 1)).hom ycomp' := by
        simpa only [y, ε, C, Nat.add_assoc] using himage
      change xcomp -
        (selectedCechResolutionTotalProjection 𝒰 F q (m + 1)
          ((m + 1) + q) (by omega)).hom
          (((selectedCechResolutionTotalComplex 𝒰 F).d
            (m + q) ((m + 1) + q)).hom y) = 0
      rw [himage', hycomp']
      simp
    · have hxzero := hsupp r s hrs (by omega)
      rw [hxzero, zero_sub]
      have hzero := ConcreteCategory.congr_hom
        (selectedCechResolutionTotal_ι_d_projection_zero_explicit
          𝒰 F q m (m + q) ((m + 1) + q) r s
          (by omega) (by omega) hrs
          (Or.inr (by omega)) (Or.inr (Ne.symm hs))) ycomp'
      have hzero' :
          (selectedCechResolutionTotalProjection 𝒰 F r s
            ((m + 1) + q) hrs).hom
            (((selectedCechResolutionTotalComplex 𝒰 F).d
              (m + q) ((m + 1) + q)).hom y) = 0 := by
        simpa only [y, Nat.add_assoc, map_zero] using hzero
      rw [hzero']
      simp
  · rw [map_sub]
    change
      ((selectedCechResolutionTotalComplex 𝒰 F).d
          ((m + 1) + q) ((m + 1) + q + 1)).hom x -
        (((selectedCechResolutionTotalComplex 𝒰 F).d
            (m + q) ((m + 1) + q) ≫
          (selectedCechResolutionTotalComplex 𝒰 F).d
            ((m + 1) + q) ((m + 1) + q + 1)).hom y) =
      ((selectedCechResolutionTotalComplex 𝒰 F).d
          ((m + 1) + q) ((m + 1) + q + 1)).hom x
    rw [HomologicalComplex.d_comp_d]
    simp

private theorem selectedCechResolutionTotal_eliminateCechOfDifferentialSupportedAt
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (n m q : ℕ) (hdegree : (m + 1) + q = n)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hsupp : SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F
      n (m + 1) x)
    (hdiff : SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F
      (n + 1) 0
      (((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x)) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (n - 1),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y
      SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F n m x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' =
          ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x := by
  subst n
  rcases selectedCechResolutionTotal_eliminateCechOfDifferentialSupported
      q m x hsupp hdiff with ⟨y, hsupp', hdiff'⟩
  have hprev : m + q = (m + 1) + q - 1 := by omega
  let y' : (selectedCechResolutionTotalComplex 𝒰 F).X ((m + 1) + q - 1) :=
    selectedCechResolutionTotalDegreeAddEquiv 𝒰 F hprev y
  refine ⟨y', ?_⟩
  have hd := selectedCechResolutionTotal_d_transport_source
    𝒰 F (k := (m + 1) + q) hprev y
  change
    SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F ((m + 1) + q) m
        (x - ((selectedCechResolutionTotalComplex 𝒰 F).d
          ((m + 1) + q - 1) ((m + 1) + q)).hom y') ∧
      ((selectedCechResolutionTotalComplex 𝒰 F).d
        ((m + 1) + q) ((m + 1) + q + 1)).hom
        (x - ((selectedCechResolutionTotalComplex 𝒰 F).d
          ((m + 1) + q - 1) ((m + 1) + q)).hom y') =
      ((selectedCechResolutionTotalComplex 𝒰 F).d
        ((m + 1) + q) ((m + 1) + q + 1)).hom x
  rw [← hd]
  exact ⟨hsupp', hdiff'⟩

private theorem selectedCechResolutionTotal_normalizeCechPreimageAux
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (n k : ℕ) (hk : k ≤ n)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hsupp : SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F n k x)
    (hdiff : SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F (n + 1) 0
      (((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x)) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (n - 1),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y
      SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F n 0 x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' =
          ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x := by
  induction k generalizing x with
  | zero =>
      refine ⟨0, ?_⟩
      simp only [map_zero, sub_zero]
      exact ⟨hsupp, trivial⟩
  | succ k ih =>
      let q := n - (k + 1)
      have hdegree : (k + 1) + q = n := by
        dsimp [q]
        omega
      rcases selectedCechResolutionTotal_eliminateCechOfDifferentialSupportedAt
          n k q hdegree x hsupp hdiff with ⟨y₁, hsupp₁, hdiff₁⟩
      let x₁ := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y₁
      have hdiffForX₁ : SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F
          (n + 1) 0
          (((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x₁) := by
        rw [hdiff₁]
        exact hdiff
      rcases ih (by omega) x₁ hsupp₁ hdiffForX₁ with
        ⟨y₂, hsupp₂, hdiff₂⟩
      refine ⟨y₁ + y₂, ?_⟩
      have hmap :
          ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom
              (y₁ + y₂) =
            ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y₁ +
              ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y₂ :=
        map_add _ y₁ y₂
      rw [hmap]
      dsimp only
      have hx :
          x - (((selectedCechResolutionTotalComplex 𝒰 F).d
              (n - 1) n).hom y₁ +
            ((selectedCechResolutionTotalComplex 𝒰 F).d
              (n - 1) n).hom y₂) =
          x₁ - ((selectedCechResolutionTotalComplex 𝒰 F).d
            (n - 1) n).hom y₂ := by
        dsimp [x₁]
        abel
      rw [hx]
      exact ⟨hsupp₂, hdiff₂.trans hdiff₁⟩

private theorem selectedCechResolutionTotal_normalizeCechPreimage
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (n : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hdiff : SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F (n + 1) 0
      (((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x)) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (n - 1),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y
      SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F n 0 x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' =
          ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x :=
  selectedCechResolutionTotal_normalizeCechPreimageAux n n (by rfl) x
    (selectedCechResolutionTotal_cechSupportedAtMost_top 𝒰 F n x) hdiff

private theorem selectedCechResolutionTotal_normalizeCechCycle
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (n : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 F).X n)
    (hcycle : ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x = 0) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 F).X (n - 1),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 F).d (n - 1) n).hom y
      SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F n 0 x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' = 0 := by
  have hdiff : SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F (n + 1) 0
      (((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x) := by
    rw [hcycle]
    intro q p hqp hp
    rw [map_zero]
  rcases selectedCechResolutionTotal_normalizeCechPreimage n x hdiff with
    ⟨y, hsupp, hdiffEq⟩
  refine ⟨y, hsupp, ?_⟩
  exact hdiffEq.trans hcycle

private theorem baseResolutionToSelectedCechTotal_f_cechSupportedAtMost_zero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (a : (baseResolutionComplex (base := base) F).X n) :
    SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F n 0
      (((baseResolutionToSelectedCechTotal 𝒰 F).f n).hom a) := by
  intro q p hqp hp
  rw [baseResolutionToSelectedCechTotal_f, ConcreteCategory.comp_apply]
  have hformula := ConcreteCategory.congr_hom
    (selectedCechResolutionTotal_ι_projection_general 𝒰 F
      q p n hqp n 0 (by simp))
    (((baseResolutionToSelectedCechZero 𝒰 F).f n).hom a)
  rw [ConcreteCategory.comp_apply] at hformula
  have h0p : (0 : ℕ) ≠ p := by omega
  by_cases hnq : n = q
  · simpa only [dif_pos hnq, dif_neg h0p, map_zero] using hformula
  · simpa only [dif_neg hnq, map_zero] using hformula

private theorem baseResolutionToSelectedCechTotal_f_injective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Injective ((baseResolutionToSelectedCechTotal 𝒰 F).f n).hom := by
  intro a b hab
  let I := (largeSheafInjectiveResolution F).cocomplex.X n
  apply baseToSelectedCechZero_app_injective 𝒰 I
  have hp := congrArg
    (selectedCechResolutionTotalProjection 𝒰 F n 0 n (by simp)).hom hab
  rw [baseResolutionToSelectedCechTotal_f, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply] at hp
  have hself := selectedCechResolutionTotal_ι_projection_self 𝒰 F n 0 n (by simp)
  have hselfa := ConcreteCategory.congr_hom hself
    (((baseResolutionToSelectedCechZero 𝒰 F).f n).hom a)
  have hselfb := ConcreteCategory.congr_hom hself
    (((baseResolutionToSelectedCechZero 𝒰 F).f n).hom b)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hselfa hselfb
  exact hselfa.symm.trans (hp.trans hselfb)

private theorem baseResolutionToSelectedCechTotal_f_projection_zero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (a : (baseResolutionComplex (base := base) F).X n) :
    (selectedCechResolutionTotalProjection 𝒰 F n 0 n (by simp)).hom
        (((baseResolutionToSelectedCechTotal 𝒰 F).f n).hom a) =
      ((baseResolutionToSelectedCechZero 𝒰 F).f n).hom a := by
  rw [baseResolutionToSelectedCechTotal_f, ConcreteCategory.comp_apply]
  have hself := selectedCechResolutionTotal_ι_projection_self 𝒰 F n 0 n (by simp)
  have h := ConcreteCategory.congr_hom hself
    (((baseResolutionToSelectedCechZero 𝒰 F).f n).hom a)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
  exact h

private theorem baseResolutionToSelectedCechTotal_homologyMap_surjective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Surjective
      (HomologicalComplex.homologyMap
        (baseResolutionToSelectedCechTotal 𝒰 F) n).hom := by
  let K := baseResolutionComplex (base := base) F
  let T := selectedCechResolutionTotalComplex 𝒰 F
  let e := baseResolutionToSelectedCechTotal 𝒰 F
  intro α
  have hπsurj : Function.Surjective (T.homologyπ n).hom :=
    (AddCommGrpCat.epi_iff_surjective (T.homologyπ n)).mp inferInstance
  rcases hπsurj α with ⟨z, rfl⟩
  let x : T.X n := (T.iCycles n).hom z
  have hxcycle : (T.d n (n + 1)).hom x = 0 := by
    have h := ConcreteCategory.congr_hom (T.iCycles_d n (n + 1)) z
    simpa only [x, ConcreteCategory.comp_apply, map_zero] using h
  rcases selectedCechResolutionTotal_normalizeCechCycle n x hxcycle with
    ⟨y, hsupp, hx'cycle⟩
  let x' : T.X n := x - (T.d (n - 1) n).hom y
  have hx'cycle' :
      ((selectedCechResolutionTotalComplex 𝒰 F).d n (n + 1)).hom x' = 0 := by
    simpa only [x'] using hx'cycle
  let b0 := (selectedCechResolutionTotalProjection 𝒰 F n 0 n (by simp)).hom x'
  have hx'eq :
      x' = ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
          (ComplexShape.up ℕ) n 0 n (by simp)).hom b0 :=
    selectedCechResolutionTotal_eq_cechZero_of_supportedAtMost
      𝒰 F n x' hsupp
  have hb0res :
      (((selectedCechResolutionBicomplex 𝒰 F).d n (n + 1)).f 0).hom b0 = 0 := by
    have hformula := ConcreteCategory.congr_hom
      (selectedCechResolutionTotal_ι_d_projection_resolution_explicit
        𝒰 F n 0 n (n + 1) (by omega) (by omega)) b0
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hformula
    rw [← hformula]
    rw [← hx'eq]
    have hp := congrArg
      (selectedCechResolutionTotalProjection 𝒰 F (n + 1) 0 (n + 1)
        (by omega)).hom hx'cycle'
    simpa only [map_zero] using hp
  have hb0cech :
      (((selectedCechResolutionBicomplex 𝒰 F).X n).d 0 1).hom b0 = 0 := by
    have hformula := ConcreteCategory.congr_hom
      (selectedCechResolutionTotal_ι_d_projection_cech_explicit
        𝒰 F n 0 n (n + 1) (by omega) (by omega)) b0
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hformula
    have hsigned :
        (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (n, 0) •
            ((selectedCechResolutionBicomplex 𝒰 F).X n).d 0 1).hom b0 = 0 := by
      rw [← hformula]
      rw [← hx'eq]
      have hp := congrArg
        (selectedCechResolutionTotalProjection 𝒰 F n 1 (n + 1)
          (by omega)).hom hx'cycle'
      simpa only [map_zero] using hp
    change
      ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
          (ComplexShape.up ℕ) (n, 0) •
        (((selectedCechResolutionBicomplex 𝒰 F).X n).d 0 1).hom b0 = 0 at hsigned
    exact (smul_eq_zero_iff_eq _).mp hsigned
  let I := (largeSheafInjectiveResolution F).cocomplex.X n
  rcases (sheaf_selectedCechAugmentation_exactAtZero 𝒰 I b0).mp hb0cech with
    ⟨a, ha⟩
  change ((baseResolutionToSelectedCechZero 𝒰 F).f n).hom a = b0 at ha
  have hacycle : (K.d n (n + 1)).hom a = 0 := by
    let I' := (largeSheafInjectiveResolution F).cocomplex.X (n + 1)
    apply baseToSelectedCechZero_app_injective 𝒰 I'
    have hcomm := ConcreteCategory.congr_hom
      ((baseResolutionToSelectedCechZero 𝒰 F).comm n (n + 1)) a
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomm
    calc
      ((baseResolutionToSelectedCechZero 𝒰 F).f (n + 1)).hom
          ((K.d n (n + 1)).hom a) =
        (((selectedCechResolutionBicomplex 𝒰 F).d n (n + 1)).f 0).hom
          (((baseResolutionToSelectedCechZero 𝒰 F).f n).hom a) := hcomm.symm
      _ = (((selectedCechResolutionBicomplex 𝒰 F).d n (n + 1)).f 0).hom b0 := by
        rw [ha]
      _ = 0 := hb0res
      _ = ((baseResolutionToSelectedCechZero 𝒰 F).f (n + 1)).hom 0 := by
        rw [map_zero]
  have hacycleSc : (K.sc n).g.hom a = 0 := by
    change (K.d n ((ComplexShape.up ℕ).next n)).hom a = 0
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp]
    exact hacycle
  let za : K.cycles n := ((K.sc n).abCyclesIso.inv).hom ⟨a, hacycleSc⟩
  have hza_i : (K.iCycles n).hom za = a := by
    simpa only [za] using (K.sc n).abCyclesIso_inv_apply_iCycles ⟨a, hacycleSc⟩
  have hx'cycleSc : (T.sc n).g.hom x' = 0 := by
    change (T.d n ((ComplexShape.up ℕ).next n)).hom x' = 0
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp]
    simpa only [x'] using hx'cycle
  let z' : T.cycles n := ((T.sc n).abCyclesIso.inv).hom ⟨x', hx'cycleSc⟩
  have hz'_i : (T.iCycles n).hom z' = x' := by
    simpa only [z'] using (T.sc n).abCyclesIso_inv_apply_iCycles ⟨x', hx'cycleSc⟩
  have hdiffcycle : (T.homologyπ n).hom (z - z') = 0 := by
    apply (cochainHomologyπ_eq_zero_iff_boundary T n (z - z')).mpr
    refine ⟨y, ?_⟩
    rw [map_sub, hz'_i]
    change (T.d (n - 1) n).hom y = x - x'
    dsimp [x']
    abel
  have hclasses : (T.homologyπ n).hom z' = (T.homologyπ n).hom z := by
    rw [map_sub, sub_eq_zero] at hdiffcycle
    exact hdiffcycle.symm
  have hcycles :
      (HomologicalComplex.cyclesMap e n).hom za = z' := by
    apply (AddCommGrpCat.mono_iff_injective (T.iCycles n)).mp inferInstance
    have hmap := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i e n) za
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap
    rw [hmap, hza_i, hz'_i, hx'eq]
    dsimp only [e]
    rw [baseResolutionToSelectedCechTotal_f, ConcreteCategory.comp_apply, ha]
    rfl
  refine ⟨(K.homologyπ n).hom za, ?_⟩
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality e n) za
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [hnat, hcycles, hclasses]

private theorem baseResolutionToSelectedCechTotal_homologyMap_injective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Injective
      (HomologicalComplex.homologyMap
        (baseResolutionToSelectedCechTotal 𝒰 F) n).hom := by
  let K := baseResolutionComplex (base := base) F
  let T := selectedCechResolutionTotalComplex 𝒰 F
  let e := baseResolutionToSelectedCechTotal 𝒰 F
  intro α β hαβ
  have hmapzero :
      (HomologicalComplex.homologyMap e n).hom (α - β) = 0 := by
    rw [map_sub, hαβ, sub_self]
  have hπsurj : Function.Surjective (K.homologyπ n).hom :=
    (AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance
  rcases hπsurj (α - β) with ⟨z, hz⟩
  have hzmapzero :
      (HomologicalComplex.homologyMap e n).hom ((K.homologyπ n).hom z) = 0 := by
    rw [hz]
    exact hmapzero
  let zt : T.cycles n := (HomologicalComplex.cyclesMap e n).hom z
  have hztclass : (T.homologyπ n).hom zt = 0 := by
    have hnat := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality e n) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
    rw [← hnat]
    exact hzmapzero
  rcases (cochainHomologyπ_eq_zero_iff_boundary T n zt).mp hztclass with
    ⟨w, hw⟩
  let a : K.X n := (K.iCycles n).hom z
  have hzt_i :
      (T.iCycles n).hom zt = (e.f n).hom a := by
    have hmap := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i e n) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap
    exact hmap
  have hzclasszero : (K.homologyπ n).hom z = 0 := by
    rcases n with _ | k
    · have hztzero : (T.iCycles 0).hom zt = 0 := by
        rw [← hw]
        rw [T.shape 0 0 (by simp)]
        rfl
      have hedgezero : (e.f 0).hom a = 0 := hzt_i.symm.trans hztzero
      have hazero : a = 0 := by
        apply baseResolutionToSelectedCechTotal_f_injective 𝒰 F 0
        simpa only [map_zero] using hedgezero
      have hzzero : z = 0 := by
        apply (AddCommGrpCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
        simpa only [a, map_zero] using hazero
      rw [hzzero, map_zero]
    · have hedgeSupp := baseResolutionToSelectedCechTotal_f_cechSupportedAtMost_zero
          𝒰 F (k + 1) a
      have hprev : k + 1 - 1 = k := by omega
      let w0 : T.X k := selectedCechResolutionTotalDegreeAddEquiv 𝒰 F hprev w
      have hdw0 := selectedCechResolutionTotal_d_transport_source
        𝒰 F (k := k + 1) hprev w
      have hw0 : (T.d k (k + 1)).hom w0 = (T.iCycles (k + 1)).hom zt := by
        exact hdw0.symm.trans hw
      have hdiff : SelectedCechResolutionTotalCechSupportedAtMost 𝒰 F (k + 1) 0
          ((T.d k (k + 1)).hom w0) := by
        rw [hw0, hzt_i]
        exact hedgeSupp
      rcases selectedCechResolutionTotal_normalizeCechPreimage k w0 hdiff with
        ⟨v, hw'supp, hw'diff⟩
      let w' : T.X k := w0 - (T.d (k - 1) k).hom v
      have hw'diff' : (T.d k (k + 1)).hom w' = (T.d k (k + 1)).hom w0 := by
        simpa only [w'] using hw'diff
      let b0 := (selectedCechResolutionTotalProjection 𝒰 F k 0 k (by simp)).hom w'
      have hw'eq :
          w' = ((selectedCechResolutionBicomplex 𝒰 F).ιTotal
            (ComplexShape.up ℕ) k 0 k (by simp)).hom b0 :=
        selectedCechResolutionTotal_eq_cechZero_of_supportedAtMost
          𝒰 F k w' hw'supp
      have hb0cech :
          (((selectedCechResolutionBicomplex 𝒰 F).X k).d 0 1).hom b0 = 0 := by
        have hformula := ConcreteCategory.congr_hom
          (selectedCechResolutionTotal_ι_d_projection_cech_explicit
            𝒰 F k 0 k (k + 1) (by omega) (by omega)) b0
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hformula
        have hsigned :
            (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
                (ComplexShape.up ℕ) (k, 0) •
              ((selectedCechResolutionBicomplex 𝒰 F).X k).d 0 1).hom b0 = 0 := by
          rw [← hformula]
          rw [← hw'eq]
          have hp₁ := congrArg
            (selectedCechResolutionTotalProjection 𝒰 F k 1 (k + 1)
              (by omega)).hom hw'diff'
          have hp₂ := congrArg
            (selectedCechResolutionTotalProjection 𝒰 F k 1 (k + 1)
              (by omega)).hom hw0
          have hp₃ := congrArg
            (selectedCechResolutionTotalProjection 𝒰 F k 1 (k + 1)
              (by omega)).hom hzt_i
          exact hp₁.trans (hp₂.trans (hp₃.trans
            (hedgeSupp k 1 (by omega) (by omega))))
        change
          ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (k, 0) •
            (((selectedCechResolutionBicomplex 𝒰 F).X k).d 0 1).hom b0 = 0
          at hsigned
        exact (smul_eq_zero_iff_eq _).mp hsigned
      let I := (largeSheafInjectiveResolution F).cocomplex.X k
      rcases (sheaf_selectedCechAugmentation_exactAtZero 𝒰 I b0).mp hb0cech with
        ⟨b, hb⟩
      change ((baseResolutionToSelectedCechZero 𝒰 F).f k).hom b = b0 at hb
      have hb0res :
          (((selectedCechResolutionBicomplex 𝒰 F).d k (k + 1)).f 0).hom b0 =
            ((baseResolutionToSelectedCechZero 𝒰 F).f (k + 1)).hom a := by
        have hformula := ConcreteCategory.congr_hom
          (selectedCechResolutionTotal_ι_d_projection_resolution_explicit
            𝒰 F k 0 k (k + 1) (by omega) (by omega)) b0
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hformula
        rw [← hformula]
        rw [← hw'eq]
        have hp₁ := congrArg
          (selectedCechResolutionTotalProjection 𝒰 F (k + 1) 0 (k + 1)
            (by omega)).hom hw'diff'
        have hp₂ := congrArg
          (selectedCechResolutionTotalProjection 𝒰 F (k + 1) 0 (k + 1)
            (by omega)).hom hw0
        exact hp₁.trans (hp₂.trans
          ((congrArg
            (selectedCechResolutionTotalProjection 𝒰 F (k + 1) 0 (k + 1)
              (by omega)).hom hzt_i).trans
            (baseResolutionToSelectedCechTotal_f_projection_zero
              𝒰 F (k + 1) a)))
      have hba : (K.d k (k + 1)).hom b = a := by
        let I' := (largeSheafInjectiveResolution F).cocomplex.X (k + 1)
        apply baseToSelectedCechZero_app_injective 𝒰 I'
        have hcomm := ConcreteCategory.congr_hom
          ((baseResolutionToSelectedCechZero 𝒰 F).comm k (k + 1)) b
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomm
        calc
          ((baseResolutionToSelectedCechZero 𝒰 F).f (k + 1)).hom
              ((K.d k (k + 1)).hom b) =
            (((selectedCechResolutionBicomplex 𝒰 F).d k (k + 1)).f 0).hom
              (((baseResolutionToSelectedCechZero 𝒰 F).f k).hom b) := hcomm.symm
          _ = (((selectedCechResolutionBicomplex 𝒰 F).d k (k + 1)).f 0).hom b0 := by
            rw [hb]
          _ = ((baseResolutionToSelectedCechZero 𝒰 F).f (k + 1)).hom a := hb0res
      apply (cochainHomologyπ_eq_zero_iff_boundary K (k + 1) z).mpr
      refine ⟨b, ?_⟩
      simpa only [Nat.add_sub_cancel_right, a] using hba
  have hsubzero : α - β = 0 := by
    rw [← hz]
    exact hzclasszero
  exact sub_eq_zero.mp hsubzero

/-- Actual sheaf gluing and injective-row exactness make the base edge a quasi-isomorphism. -/
theorem baseResolutionToSelectedCechTotal_quasiIso
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    QuasiIso (baseResolutionToSelectedCechTotal 𝒰 F) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨baseResolutionToSelectedCechTotal_homologyMap_injective 𝒰 F n,
    baseResolutionToSelectedCechTotal_homologyMap_surjective 𝒰 F n⟩

/-- Homology equivalence induced by the base-resolution edge quasi-isomorphism. -/
noncomputable def baseResolutionToSelectedCechTotalHomologyEquiv
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    ((baseResolutionComplex (base := base) F).homology n : Type (u + 1)) ≃+
      ((selectedCechResolutionTotalComplex 𝒰 F).homology n : Type (u + 1)) := by
  letI : QuasiIso (baseResolutionToSelectedCechTotal 𝒰 F) :=
    baseResolutionToSelectedCechTotal_quasiIso 𝒰 F
  exact (isoOfQuasiIsoAt
    (baseResolutionToSelectedCechTotal 𝒰 F) n).addCommGroupIsoToAddEquiv



/-- Canonical equivalence from selected Čech homology to actual local sheaf cohomology. -/
noncomputable def selectedCechToSheafHAtBaseEquiv
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (hLeray : IsLerayFor 𝒰 F)
    (n : Nat) :
    (((selectedCechComplexFunctor 𝒰).obj F.val).homology n : Type (u + 1)) ≃+
      (F.H' n base : Type (u + 2)) :=
  (selectedCechToResolutionTotalHomologyEquiv 𝒰 F hLeray n).trans
    ((baseResolutionToSelectedCechTotalHomologyEquiv 𝒰 F n).symm.trans
      (baseResolutionHomologyEquivHPrime F n))

end LargeLeray

/-- Positive-degree local vanishing for an arbitrary additive sheaf. -/
def IsLerayForSheaf
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})] :
    Prop :=
  LargeLeray.IsLerayFor 𝒰 F

/-- The existing zero obstruction sheaf supplies the satisfying instance. -/
theorem zeroObstructionSheaf_isLerayForSheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {base : S.category}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    IsLerayForSheaf 𝒰 (zeroObstructionSheaf S).toAddCommGrpSheaf :=
  by
    intro q hq p σ
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    letI : Injective (zeroObstructionSheaf S).toAddCommGrpSheaf :=
      zeroObstructionSheaf_toAddCommGrpSheaf_isZero.injective
    exact CategoryTheory.Abelian.Ext.subsingleton_of_injective _ _ n

/-- A nontrivial positive-degree local `H'` rejects the Leray predicate. -/
theorem not_isLerayForSheaf_of_nontrivialHPrime
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {base : S.category}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {F : Sheaf S.topology AddCommGrpCat.{u + 1}}
    {q p : ℕ} (hq : 0 < q)
    (σ : (canonicalCoverRelative 𝒰).simplex p)
    [Nontrivial (F.H' q ((canonicalCoverRelative 𝒰).overlap p σ))] :
    ¬ IsLerayForSheaf 𝒰 F := by
  intro hLeray
  exact not_subsingleton _ (hLeray q hq p σ)

/-- Generic selected Čech comparison for an arbitrary large additive sheaf. -/
noncomputable def selectedCechToSheafHAtBaseEquivForSheaf
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (hLeray : IsLerayForSheaf 𝒰 F)
    (n : Nat) :
    (((selectedCechComplexFunctor 𝒰).obj F.val).homology n : Type (u + 1)) ≃+
      (F.H' n base : Type (u + 2)) :=
  LargeLeray.selectedCechToSheafHAtBaseEquiv 𝒰 F hLeray n

end AAT.AG.Cohomology
