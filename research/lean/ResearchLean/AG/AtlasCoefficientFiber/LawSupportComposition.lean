import ResearchLean.AG.AtlasCoefficientFiber.LawSupportFamilies

/-!
# G-135 D：原Lawラベル別部分台族の入れ子と恒等

## Implementation notes

各台の原P・細cochain・Q・literal R射の既存合成則を全族へ持ち上げる。
元ラベル台を取る場合は元Law canonical族同型そのものを回復する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory HomologicalComplex CanonicalResolution ResolutionInvariance
open FaceRelationSubdivision AtlasDefectComposition
universe u

/-- 同じshort complex族の恒等射を集めた射は恒等射。 -/
theorem coefficientShortComplexFamily_map_id {J : Type u}
    (S : J → ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)) :
    coefficientShortComplexFamily_map (fun j => 𝟙 (S j)) = 𝟙 _ := by
  apply ShortComplex.Hom.ext
  · exact FiniteComplexFamily.map_id _
  · exact FiniteComplexFamily.map_id _
  · exact FiniteComplexFamily.map_id _

/-- 元short complex族射の合成を全三成分で保つ。 -/
theorem coefficientShortComplexFamily_map_comp {J : Type u}
    {S T U : J → ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)}
    (φ : ∀ j, S j ⟶ T j) (ψ : ∀ j, T j ⟶ U j) :
    coefficientShortComplexFamily_map φ ≫ coefficientShortComplexFamily_map ψ =
      coefficientShortComplexFamily_map (fun j => φ j ≫ ψ j) := by
  apply ShortComplex.Hom.ext
  · exact (FiniteComplexFamily.map_comp _ _ (fun j => (φ j).τ₁) (fun j => (ψ j).τ₁)).symm
  · exact (FiniteComplexFamily.map_comp _ _ (fun j => (φ j).τ₂) (fun j => (ψ j).τ₂)).symm
  · exact (FiniteComplexFamily.map_comp _ _ (fun j => (φ j).τ₃) (fun j => (ψ j).τ₃)).symm

variable {Source : Type u} [finiteSource : Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)

omit finiteSource in
/-- 同じ原SES支持制限の恒等を全三射で述べる。 -/
theorem supportEvaluationRestrictionMorphism_refl (A : Set qc.Target) :
    supportEvaluationRestrictionMorphism M (Set.Subset.refl A) = 𝟙 _ := by
  apply ShortComplex.Hom.ext
  · rw [supportEvaluationRestrictionMorphism_τ1, supportPushforwardHom_refl, zeroExtensionMap_id]
    rfl
  · rw [supportEvaluationRestrictionMorphism_τ2, subsetRestrictHom_refl, zeroExtensionMap_id]
    rfl
  · rw [supportEvaluationRestrictionMorphism_τ3, supportQHom_refl, zeroExtensionMap_id]
    rfl

omit finiteSource in
/-- 同じ原SESの入れ子支持制限を全三射で述べる。 -/
theorem supportEvaluationRestrictionMorphism_comp {A B C : Set qc.Target}
    (hab : A ⊆ B) (hbc : B ⊆ C) :
    supportEvaluationRestrictionMorphism M hbc ≫ supportEvaluationRestrictionMorphism M hab =
      supportEvaluationRestrictionMorphism M (hab.trans hbc) := by
  apply ShortComplex.Hom.ext
  · rw [ShortComplex.comp_τ₁, supportEvaluationRestrictionMorphism_τ1,
      supportEvaluationRestrictionMorphism_τ1, supportEvaluationRestrictionMorphism_τ1,
      ← zeroExtensionMap_comp, supportPushforwardHom_comp]
  · rw [ShortComplex.comp_τ₂, supportEvaluationRestrictionMorphism_τ2,
      supportEvaluationRestrictionMorphism_τ2, supportEvaluationRestrictionMorphism_τ2,
      ← zeroExtensionMap_comp]
    rw [← subsetRestrictHom_comp Nf
      (A := comparisonFactor qc qf h ⁻¹' A) (B := comparisonFactor qc qf h ⁻¹' B)
      (C := comparisonFactor qc qf h ⁻¹' C) (fun _ ht => hab ht) (fun _ ht => hbc ht)]
  · rw [ShortComplex.comp_τ₃, supportEvaluationRestrictionMorphism_τ3,
      supportEvaluationRestrictionMorphism_τ3, supportEvaluationRestrictionMorphism_τ3,
      ← zeroExtensionMap_comp, supportQHom_comp]

variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
variable {A B : LawValueLabel laws → Set qc.Target}
variable (hab : ∀ l, A l ⊆ B l) (hb : ∀ l, B l ⊆ labelValueFiber laws qc ha l)

/-- 原Law全族SES射は任意ラベル別入れ子台制限と合成する。 -/
theorem lawSupportFamilyMorphism_comp :
    lawSupportFamilyMorphism M laws ha hb ≫
      coefficientShortComplexFamily_map (fun l => supportEvaluationRestrictionMorphism M (hab l)) =
    lawSupportFamilyMorphism M laws ha (fun l => (hab l).trans (hb l)) := by
  dsimp only [lawSupportFamilyMorphism]
  rw [Category.assoc, coefficientShortComplexFamily_map_comp]
  congr 2
  funext l
  exact supportEvaluationRestrictionMorphism_comp M (hab l) (hb l)

/-- 原Law全族P射は同じ入れ子primitive P台制限と合成する。 -/
theorem lawSupportFamilyP_comp : lawSupportFamilyP M laws ha hb ≫
    FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (supportPushforwardHom M (hab l))) =
      lawSupportFamilyP M laws ha (fun l => (hab l).trans (hb l)) :=
  congrArg ShortComplex.Hom.τ₁ (lawSupportFamilyMorphism_comp M laws ha hab hb)
/-- 原Law全族細射は同じ入れ子細台制限と合成する。 -/
theorem lawSupportFamilyFine_comp : lawSupportFamilyFine M laws ha hb ≫
    FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab l ht))) =
      lawSupportFamilyFine M laws ha (fun l => (hab l).trans (hb l)) :=
  congrArg ShortComplex.Hom.τ₂ (lawSupportFamilyMorphism_comp M laws ha hab hb)
/-- 原Law全族Q射は同じ入れ子原L双対台制限と合成する。 -/
theorem lawSupportFamilyQ_comp : lawSupportFamilyQ M laws ha hb ≫
    FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (supportQHom M (hab l))) =
      lawSupportFamilyQ M laws ha (fun l => (hab l).trans (hb l)) :=
  congrArg ShortComplex.Hom.τ₃ (lawSupportFamilyMorphism_comp M laws ha hab hb)
/-- 原Law全族粗射は同じ入れ子原粗台制限と合成する。 -/
theorem lawSupportFamilyCoarse_comp : lawSupportFamilyCoarse (Nc := Nc) laws ha hb ≫
    FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (subsetRestrictHom Nc (hab l))) =
      lawSupportFamilyCoarse (Nc := Nc) laws ha (fun l => (hab l).trans (hb l)) := by
  rw [lawSupportFamilyCoarse_eq, lawSupportFamilyCoarse_eq, Category.assoc,
    ← FiniteComplexFamily.map_comp]
  congr 2
  funext l
  rw [← zeroExtensionMap_comp, ← subsetRestrictHom_comp Nc (hab l) (hb l)]

omit finiteSource in
/-- 原Law直接Phi R族射は同じ入れ子literal R台制限と合成する。 -/
theorem lawSupportFamilyR_comp :
    (FiniteLinearFamily.map (fun l => supportFiberR M (hab l))).comp
      (lawSupportFamilyR M laws ha hb) =
    lawSupportFamilyR M laws ha (fun l => (hab l).trans (hb l)) := by
  apply LinearMap.ext
  intro z
  funext l
  rw [LinearMap.comp_apply, FiniteLinearFamily.map_apply, lawSupportFamilyR_apply,
    lawSupportFamilyR_apply, lawSupportR_apply, lawSupportR_apply]
  exact LinearMap.congr_fun (supportFiberR_comp M (hab l) (hb l)) (lawRFamilyEquiv M laws ha z l)

/-- 原ラベル台のままなら全族SES射は元canonical族同型の順射。 -/
theorem lawSupportFamilyMorphism_refl :
    lawSupportFamilyMorphism M laws ha (fun l => Set.Subset.refl (labelValueFiber laws qc ha l)) =
      (lawEvaluationRestrictionFamilyIso M laws ha).hom := by
  dsimp only [lawSupportFamilyMorphism]
  simp only [supportEvaluationRestrictionMorphism_refl, coefficientShortComplexFamily_map_id,
    Category.comp_id]
/-- 原ラベル台でのP族射は元Law P座標同型。 -/
theorem lawSupportFamilyP_refl :
    lawSupportFamilyP M laws ha (fun l => Set.Subset.refl (labelValueFiber laws qc ha l)) =
      (lawPushforwardStandardIso M laws ha).hom :=
  congrArg ShortComplex.Hom.τ₁ (lawSupportFamilyMorphism_refl M laws ha)
/-- 原ラベル台での細族射は元Law細座標同型。 -/
theorem lawSupportFamilyFine_refl :
    lawSupportFamilyFine M laws ha (fun l => Set.Subset.refl (labelValueFiber laws qc ha l)) =
      (lawFineStandardIso (Nf := Nf) (h := h) laws ha).hom :=
  congrArg ShortComplex.Hom.τ₂ (lawSupportFamilyMorphism_refl M laws ha)
/-- 原ラベル台でのQ族射は元Law Q座標同型。 -/
theorem lawSupportFamilyQ_refl :
    lawSupportFamilyQ M laws ha (fun l => Set.Subset.refl (labelValueFiber laws qc ha l)) =
      (lawRestrictionStandardIso M laws ha).hom :=
  congrArg ShortComplex.Hom.τ₃ (lawSupportFamilyMorphism_refl M laws ha)
/-- 原ラベル台での粗族射は元Law粗座標同型。 -/
theorem lawSupportFamilyCoarse_refl :
    lawSupportFamilyCoarse (Nc := Nc) laws ha (fun l => Set.Subset.refl (labelValueFiber laws qc ha l)) =
      (lawCoarseStandardIso (Nc := Nc) laws ha).hom := by
  rw [lawSupportFamilyCoarse_eq]
  simp only [subsetRestrictHom_refl, zeroExtensionMap_id, FiniteComplexFamily.map_id, Category.comp_id]
omit finiteSource in
/-- 原ラベル台での直接Phi R族射は元literal核族同型。 -/
theorem lawSupportFamilyR_refl :
    lawSupportFamilyR M laws ha (fun l => Set.Subset.refl (labelValueFiber laws qc ha l)) =
      (lawRFamilyEquiv M laws ha).toLinearMap := by
  apply LinearMap.ext
  intro z
  funext l
  rw [lawSupportFamilyR_apply, lawSupportR_apply, supportFiberR_refl]
  rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientShortComplexFamily_map_id
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientShortComplexFamily_map_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationRestrictionMorphism_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationRestrictionMorphism_comp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyMorphism_comp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyP_comp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyFine_comp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyQ_comp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyCoarse_comp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyR_comp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyMorphism_refl
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyP_refl
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyFine_refl
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyQ_refl
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyCoarse_refl
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyR_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationRestrictionMorphism.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
