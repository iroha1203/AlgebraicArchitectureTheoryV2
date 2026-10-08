import ResearchLean.AG.AtlasCoefficientFiber.LawHomologyCoordinates
import ResearchLean.AG.AtlasCoefficientFiber.SupportCones

/-!
# G-135 D：原Law全射から同じラベルの部分台への射

## Implementation notes

実Lawのcanonical族座標への射影を、原始セルから生成した支持制限へ合成する。
終域は同じ元P・細cochain・Qであり、別の中間複体を選ばない。
全整数次数のHomを先に作り、同じ三次数値と原η・独立uの正方形へ読む。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision AtlasDefectComposition
open HomologicalComplex
universe u
variable {Source : Type u} [Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
variable (l : LawValueLabel laws) {A : Set qc.Target}
variable (hA : A ⊆ labelValueFiber laws qc ha l)

/-- 原Law SESの同じラベル射影を原A台の実SES制限へ合成する。 -/
def lawSupportMorphism : lawEvaluationRestrictionShortComplex M laws ha ⟶
    evaluationRestrictionShortComplex M A :=
  lawEvaluationRestrictionProjection M laws ha l ≫ supportEvaluationRestrictionMorphism M hA

/-- 原Law部分台SES射の元projectionとprimitive制限による生成式。 -/
theorem lawSupportMorphism_eq : lawSupportMorphism M laws ha l hA =
    lawEvaluationRestrictionProjection M laws ha l ≫ supportEvaluationRestrictionMorphism M hA := rfl

/-- 原Lawから原P_Aへの全次数射は同じ実SES射の左成分。 -/
def lawSupportP : zeroExtension (lawPushforwardComplex M laws ha) ⟶
    zeroExtension (pushforwardComplex M A) := (lawSupportMorphism M laws ha l hA).τ₁

/-- 原Lawから細側canonical逆像Aへの全次数射。 -/
def lawSupportFine : zeroExtension
    (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha)) ⟶
      zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)) :=
  (lawSupportMorphism M laws ha l hA).τ₂

/-- 原Lawから同じ原L双対Q_Aへの全次数射。 -/
def lawSupportQ : zeroExtension (lawRestrictionComplex M laws ha) ⟶
    zeroExtension (restrictionComplex M A) := (lawSupportMorphism M laws ha l hA).τ₃

/-- 原粗Lawの同じラベル座標を原粗A cochainへ制限する全次数射。 -/
def lawSupportCoarse : zeroExtension (Nc.lawGeneratedComplex laws ha) ⟶
    zeroExtension (Nc.targetSubsetComplex A) :=
  (lawCoarseStandardIso (Nc := Nc) laws ha).hom ≫ FiniteComplexFamily.projection _ l ≫
    zeroExtensionMap (subsetRestrictHom Nc hA)

/-- 原Law P射は同じラベルSESの左射に原P台制限を合成する。 -/
theorem lawSupportP_projection : lawSupportP M laws ha l hA =
    (lawEvaluationRestrictionProjection M laws ha l).τ₁ ≫
      zeroExtensionMap (supportPushforwardHom M hA) := rfl

/-- 原Law細射は同じラベルSESの中射に元細台制限を合成する。 -/
theorem lawSupportFine_projection : lawSupportFine M laws ha l hA =
    (lawEvaluationRestrictionProjection M laws ha l).τ₂ ≫
      zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hA ht)) := rfl

/-- 原Law Q射は同じラベルSESの右射に原Q台制限を合成する。 -/
theorem lawSupportQ_projection : lawSupportQ M laws ha l hA =
    (lawEvaluationRestrictionProjection M laws ha l).τ₃ ≫
      zeroExtensionMap (supportQHom M hA) := rfl

/-- 原Law P射の全体等号は元canonical射影とprimitive支持制限。 -/
theorem lawSupportP_eq : lawSupportP M laws ha l hA =
    (lawPushforwardStandardIso M laws ha).hom ≫ FiniteComplexFamily.projection _ l ≫
      zeroExtensionMap (supportPushforwardHom M hA) := by
  dsimp only [lawSupportP, lawSupportMorphism]
  rw [ShortComplex.comp_τ₁, lawEvaluationRestrictionProjection_τ1,
    supportEvaluationRestrictionMorphism_τ1]
  rfl

/-- 原Law細射の全体等号は元細canonical射影とprimitive支持制限。 -/
theorem lawSupportFine_eq : lawSupportFine M laws ha l hA =
    (lawFineStandardIso (Nf := Nf) (h := h) laws ha).hom ≫ FiniteComplexFamily.projection _ l ≫
      zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hA ht)) := by
  dsimp only [lawSupportFine, lawSupportMorphism]
  rw [ShortComplex.comp_τ₂, lawEvaluationRestrictionProjection_τ2,
    supportEvaluationRestrictionMorphism_τ2]
  rfl

/-- 原Law Q射の全体等号は元Q canonical射影と原L双対支持制限。 -/
theorem lawSupportQ_eq : lawSupportQ M laws ha l hA =
    (lawRestrictionStandardIso M laws ha).hom ≫ FiniteComplexFamily.projection _ l ≫
      zeroExtensionMap (supportQHom M hA) := by
  dsimp only [lawSupportQ, lawSupportMorphism]
  rw [ShortComplex.comp_τ₃, lawEvaluationRestrictionProjection_τ3,
    supportEvaluationRestrictionMorphism_τ3]
  rfl

/-- 原粗Law射の生成式を下流へ公開する。 -/
theorem lawSupportCoarse_eq : lawSupportCoarse (Nc := Nc) laws ha l hA =
    (lawCoarseStandardIso (Nc := Nc) laws ha).hom ≫ FiniteComplexFamily.projection _ l ≫
      zeroExtensionMap (subsetRestrictHom Nc hA) := rfl

/-- 原Law P射の全整数次数値は同じ原ラベル射影と支持制限。 -/
theorem lawSupportP_apply (n : ℤ) (x : (zeroExtension (lawPushforwardComplex M laws ha)).X n) :
    (lawSupportP M laws ha l hA).f n x =
      (zeroExtensionMap (supportPushforwardHom M hA)).f n
        ((lawEvaluationRestrictionProjection M laws ha l).τ₁.f n x) := rfl

/-- 原Law細射の全整数次数値は同じ原ラベル射影と支持制限。 -/
theorem lawSupportFine_apply (n : ℤ)
    (x : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).X n) :
    (lawSupportFine M laws ha l hA).f n x =
      (zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hA ht))).f n
        ((lawEvaluationRestrictionProjection M laws ha l).τ₂.f n x) := rfl

/-- 原Law Q射の全整数次数値は同じ原ラベル射影と原L双対制限。 -/
theorem lawSupportQ_apply (n : ℤ) (x : (zeroExtension (lawRestrictionComplex M laws ha)).X n) :
    (lawSupportQ M laws ha l hA).f n x =
      (zeroExtensionMap (supportQHom M hA)).f n
        ((lawEvaluationRestrictionProjection M laws ha l).τ₃.f n x) := rfl

/-- 原粗Law射の全整数次数値を同じ原粗座標で読む。 -/
theorem lawSupportCoarse_apply (n : ℤ) (x : (zeroExtension (Nc.lawGeneratedComplex laws ha)).X n) :
    (lawSupportCoarse (Nc := Nc) laws ha l hA).f n x =
      (zeroExtensionMap (subsetRestrictHom Nc hA)).f n
        (((lawCoarseStandardIso (Nc := Nc) laws ha).hom ≫
          FiniteComplexFamily.projection _ l).f n x) := rfl

/-- 原LawP台射の値は同じ元canonicalラベル値のprimitive制限。 -/
theorem lawSupportP_component_apply (n : ℤ)
    (x : (zeroExtension (lawPushforwardComplex M laws ha)).X n) :
    (lawSupportP M laws ha l hA).f n x =
      (zeroExtensionMap (supportPushforwardHom M hA)).f n ((lawPushforwardStandardIso M laws ha).hom.f n x l) := by
  simp only [lawSupportP_eq, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    FiniteComplexFamily.projection_apply]

/-- 原LawFine台射の値は同じ元canonicalラベル値のprimitive制限。 -/
theorem lawSupportFine_component_apply (n : ℤ)
    (x : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).X n) :
    (lawSupportFine M laws ha l hA).f n x =
      (zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hA ht))).f n ((lawFineStandardIso (Nf := Nf) (h := h) laws ha).hom.f n x l) := by
  simp only [lawSupportFine_eq, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    FiniteComplexFamily.projection_apply]
  rfl

/-- 原LawQ台射の値は同じ元canonicalラベル値のprimitive制限。 -/
theorem lawSupportQ_component_apply (n : ℤ)
    (x : (zeroExtension (lawRestrictionComplex M laws ha)).X n) :
    (lawSupportQ M laws ha l hA).f n x =
      (zeroExtensionMap (supportQHom M hA)).f n ((lawRestrictionStandardIso M laws ha).hom.f n x l) := by
  simp only [lawSupportQ_eq, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    FiniteComplexFamily.projection_apply]

/-- 原LawCoarse台射の値は同じ元canonicalラベル値のprimitive制限。 -/
theorem lawSupportCoarse_component_apply (n : ℤ)
    (x : (zeroExtension (Nc.lawGeneratedComplex laws ha)).X n) :
    (lawSupportCoarse (Nc := Nc) laws ha l hA).f n x =
      (zeroExtensionMap (subsetRestrictHom Nc hA)).f n ((lawCoarseStandardIso (Nc := Nc) laws ha).hom.f n x l) := by
  simp only [lawSupportCoarse_eq, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    FiniteComplexFamily.projection_apply]

/-- 原Law unitと同じ原A unitの全Hom正方形。 -/
theorem lawSupportUnit : zeroExtensionMap (lawUnitHom M laws ha) ≫ lawSupportP M laws ha l hA =
    lawSupportCoarse (Nc := Nc) laws ha l hA ≫ zeroExtensionMap (unitHom M A) := by
  rw [lawSupportP_eq, lawSupportCoarse_eq]
  rw [← Category.assoc, ← Category.assoc, lawUnitStandard_square]
  simp only [Category.assoc]
  rw [← Category.assoc (FiniteComplexFamily.map _ _
    (fun j => zeroExtensionMap (unitHom M (labelValueFiber laws qc ha j))))
    (FiniteComplexFamily.projection _ l), FiniteComplexFamily.map_projection]
  simp only [Category.assoc]
  rw [supportStandardUnit]

/-- 原Law evaluationと同じ原A evaluationの全Hom正方形。 -/
theorem lawSupportEvaluation : zeroExtensionMap (lawEvaluationHom M laws ha) ≫
    lawSupportFine M laws ha l hA = lawSupportP M laws ha l hA ≫
      zeroExtensionMap (evaluationHom M A) :=
  (lawSupportMorphism M laws ha l hA).comm₁₂.symm

/-- 原Law restrictionと同じ原Q restrictionの全Hom正方形。 -/
theorem lawSupportRestriction : zeroExtensionMap (lawRestrictionHom M laws ha) ≫
    lawSupportQ M laws ha l hA = lawSupportFine M laws ha l hA ≫
      zeroExtensionMap (restrictionHom M A) :=
  (lawSupportMorphism M laws ha l hA).comm₂₃.symm

/-- 独立生成した原Law uと同じ原A uの全Hom正方形。 -/
theorem lawSupportDirect :
    zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha)) ≫
      lawSupportFine M laws ha l hA =
    lawSupportCoarse (Nc := Nc) laws ha l hA ≫ zeroExtensionMap (M.aSubnerveComparisonHom A) := by
  rw [lawStandardComparison_factorization, Category.assoc, lawSupportEvaluation,
    ← Category.assoc, lawSupportUnit, Category.assoc]
  rw [aSubnerveComparisonHom_factorization, zeroExtensionMap_comp]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportMorphism
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportMorphism_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportP
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFine
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportQ
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoarse
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportP_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFine_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportQ_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportP_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFine_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportQ_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoarse_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportP_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFine_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportQ_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoarse_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportP_component_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFine_component_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportQ_component_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoarse_component_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportUnit
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportEvaluation
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportRestriction
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportDirect
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoarse.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFine.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportP.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportQ.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
