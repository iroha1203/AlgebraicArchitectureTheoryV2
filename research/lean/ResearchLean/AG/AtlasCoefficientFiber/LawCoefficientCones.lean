import ResearchLean.AG.AtlasCoefficientFiber.LawHomologyCoordinates
import ResearchLean.AG.AtlasCoefficientFiber.FiberCone
import ResearchLean.AG.AtlasDefectComposition.FiniteConeFamily
import ResearchLean.AG.AtlasDefectComposition.ConeEquivalence

/-!
# G-135 D：同じLaw三錐とラベル族

## Implementation notes

実Law射の標準錐を実可換正方形で同じ原ラベル錐族へ送る。
Q評価と連結射は入力生成Law短完全列の標準descとδを使う。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CochainComplex HomologicalComplex Pretriangulated
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u
/-- 同じ標準複体の有限積から有限直和を生成する。 -/
local instance lawCoefficientFiniteBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- 実射の同型正方形から同じ成分錐の族への複体同型。 -/
def coefficientFamilyConeIso {J : Type u}
    {X Y : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    {F G : J → CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (φ : X ⟶ Y) (ψ : ∀ j, F j ⟶ G j)
    (eX : X ≅ FiniteComplexFamily.complex F) (eY : Y ≅ FiniteComplexFamily.complex G)
    (comm : φ ≫ eY.hom = eX.hom ≫ FiniteComplexFamily.map F G ψ) :
    mappingCone φ ≅ FiniteComplexFamily.complex (fun j => mappingCone (ψ j)) :=
  coneMapIso φ (FiniteComplexFamily.map F G ψ) eX eY comm ≪≫ FiniteConeFamily.iso ψ

/-- 族錐同型は全次数・全元の同じtarget/source二座標を保持する。 -/
theorem coefficientFamilyConeIso_component {J : Type u}
    {X Y : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    {F G : J → CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (φ : X ⟶ Y) (ψ : ∀ j, F j ⟶ G j)
    (eX : X ≅ FiniteComplexFamily.complex F) (eY : Y ≅ FiniteComplexFamily.complex G)
    (comm : φ ≫ eY.hom = eX.hom ≫ FiniteComplexFamily.map F G ψ)
    (n : ℤ) (z : (mappingCone φ).X n) (j : J) :
    coneCoordinateEquiv (ψ j) n ((coefficientFamilyConeIso φ ψ eX eY comm).hom.f n z j) =
      (eY.hom.f n (coneCoordinateEquiv φ n z).1 j,
        eX.hom.f (n+1) (coneCoordinateEquiv φ n z).2 j) := by
  change coneCoordinateEquiv (ψ j) n
    ((FiniteConeFamily.iso ψ).hom.f n
      ((coneMapIso φ (FiniteComplexFamily.map F G ψ) eX eY comm).hom.f n z) j) = _
  rw [FiniteConeFamily.iso_apply, FiniteConeFamily.degreeEquiv_component,
    coneMapIso_hom, coneCoordinateEquiv_map]

variable {Source : Type u} [Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 同じ原Law ηの実標準錐。 -/
abbrev lawCoefficientCone := mappingCone (zeroExtensionMap (lawUnitHom M laws ha))
/-- 同じ原Law εの実標準錐。 -/
abbrev lawFiberCone := mappingCone (zeroExtensionMap (lawEvaluationHom M laws ha))
/-- 独立生成した同じ原Law uの実標準錐。 -/
abbrev lawTotalCone := mappingCone
  (zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha)))

/-- 実Law η錐を重複を保持する原η錐族へ送る全複体同型。 -/
def lawCoefficientConeFamilyIso : lawCoefficientCone M laws ha ≅
    FiniteComplexFamily.complex (fun l => coefficientCone M (labelValueFiber laws qc ha l)) :=
  coefficientFamilyConeIso _ _ (lawCoarseStandardIso (Nc := Nc) laws ha)
    (lawPushforwardStandardIso M laws ha) (lawUnitStandard_square M laws ha)

/-- 実Law ε錐を同じ原ε錐族へ送る全複体同型。 -/
def lawFiberConeFamilyIso : lawFiberCone M laws ha ≅
    FiniteComplexFamily.complex (fun l => fiberCone M (labelValueFiber laws qc ha l)) :=
  coefficientFamilyConeIso _ _ (lawPushforwardStandardIso M laws ha)
    (lawFineStandardIso (Nf := Nf) (h := h) laws ha) (lawEvaluationStandard_square M laws ha)

/-- 独立生成Law u錐を同じ原u錐族へ送る全複体同型。 -/
def lawTotalConeFamilyIso : lawTotalCone M laws ha ≅
    FiniteComplexFamily.complex (fun l => totalCone M (labelValueFiber laws qc ha l)) :=
  coefficientFamilyConeIso _ _ (lawCoarseStandardIso (Nc := Nc) laws ha)
    (lawFineStandardIso (Nf := Nf) (h := h) laws ha) (lawGeneratedStandard_square M laws ha)

/-- 同じLaw三射から独立uを中間対象とする実合成triangleを生成する。 -/
def lawCoefficientCompositionTriangle : Triangle (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  compositionTriangle (zeroExtensionMap (lawUnitHom M laws ha))
    (zeroExtensionMap (lawEvaluationHom M laws ha))
    (zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha)))
    (lawStandardComparison_factorization M laws ha)

/-- 同じ実Law合成triangleは標準homotopy圏でdistinguishedとなる。 -/
theorem lawCoefficientCompositionTriangle_distinguished :
    (HomotopyCategory.quotient (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)).mapTriangle.obj
      (lawCoefficientCompositionTriangle M laws ha) ∈
        distTriang (HomotopyCategory (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)) :=
  compositionTriangle_distinguished _ _ _ (lawStandardComparison_factorization M laws ha)

/-- Law合成triangleの第一射は同じε作用とsource保持である。 -/
theorem lawCoefficientCompositionTriangle_first (n : ℤ) (z : (lawCoefficientCone M laws ha).X n) :
    coneCoordinateEquiv
      (zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) n
      ((lawCoefficientCompositionTriangle M laws ha).mor₁.f n z) =
      ((zeroExtensionMap (lawEvaluationHom M laws ha)).f n
        (coneCoordinateEquiv (zeroExtensionMap (lawUnitHom M laws ha)) n z).1,
        (coneCoordinateEquiv (zeroExtensionMap (lawUnitHom M laws ha)) n z).2) :=
  compositionTriangle_first _ _ _ (lawStandardComparison_factorization M laws ha) n z

/-- Law合成triangleの第二射はtarget保持と同じη作用である。 -/
theorem lawCoefficientCompositionTriangle_second (n : ℤ) (z : (lawTotalCone M laws ha).X n) :
    coneCoordinateEquiv (zeroExtensionMap (lawEvaluationHom M laws ha)) n
      ((lawCoefficientCompositionTriangle M laws ha).mor₂.f n z) =
      ((coneCoordinateEquiv
        (zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) n z).1,
        (zeroExtensionMap (lawUnitHom M laws ha)).f (n+1)
          (coneCoordinateEquiv
            (zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) n z).2) :=
  compositionTriangle_second _ _ _ (lawStandardComparison_factorization M laws ha) n z

/-- Law合成triangleの第三射は同じshift負号を含む。 -/
theorem lawCoefficientCompositionTriangle_third (n : ℤ) (z : (lawFiberCone M laws ha).X n) :
    coneCoordinateEquiv (zeroExtensionMap (lawUnitHom M laws ha)) (n+1)
      (((lawCoefficientCone M laws ha).shiftFunctorObjXIso 1 n (n+1) rfl).hom
        ((lawCoefficientCompositionTriangle M laws ha).mor₃.f n z)) =
      (-(coneCoordinateEquiv (zeroExtensionMap (lawEvaluationHom M laws ha)) n z).2, 0) :=
  compositionTriangle_third _ _ _ (lawStandardComparison_factorization M laws ha) n z

/-- 同じ実Law ε錐から同じ原L双対族Qへの標準評価。 -/
def lawFiberConeDesc : lawFiberCone M laws ha ⟶ zeroExtension (lawRestrictionComplex M laws ha) :=
  mappingCone.descShortComplex (lawEvaluationRestrictionShortComplex M laws ha)

/-- 原Qへの評価を標準short complexのdescとして読む所有API。 -/
theorem lawFiberConeDesc_eq : lawFiberConeDesc M laws ha =
    mappingCone.descShortComplex (lawEvaluationRestrictionShortComplex M laws ha) := rfl

/-- 原ε錐のtarget包含を原Q評価へ送る次数別公開式。 -/
theorem lawFiberConeDesc_inr_apply (n : ℤ)
    (y : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).X n) :
    (lawFiberConeDesc M laws ha).f n
      ((mappingCone.inr (zeroExtensionMap (lawEvaluationHom M laws ha))).f n y) =
      (zeroExtensionMap (lawRestrictionHom M laws ha)).f n y := by
  have hz := congrArg (fun t : ((zeroExtension
      (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).X n ⟶
        (zeroExtension (lawRestrictionComplex M laws ha)).X n) => t y)
    (mappingCone.inr_f_descShortComplex_f (lawEvaluationRestrictionShortComplex M laws ha) n)
  simpa only [ModuleCat.comp_apply] using hz

/-- 原ε錐のshifted source包含は原Q評価で零となる。 -/
theorem lawFiberConeDesc_inl_apply (n : ℤ)
    (x : (zeroExtension (lawPushforwardComplex M laws ha)).X (n+1)) :
    (lawFiberConeDesc M laws ha).f n
      ((mappingCone.inl (zeroExtensionMap (lawEvaluationHom M laws ha))).v (n+1) n (by simp) x) = 0 := by
  have hz := congrArg (fun t : ((zeroExtension (lawPushforwardComplex M laws ha)).X (n+1) ⟶
      (zeroExtension (lawRestrictionComplex M laws ha)).X n) => t x)
    (mappingCone.inl_v_descShortComplex_f (lawEvaluationRestrictionShortComplex M laws ha)
      (n+1) n (by simp))
  simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using hz

/-- 全次数で実錐座標(y,x)を同じ原Lの制限yへ送る。 -/
theorem lawFiberConeDesc_symm_apply (n : ℤ)
    (p : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).X n ×
      (zeroExtension (lawPushforwardComplex M laws ha)).X (n+1)) :
    (lawFiberConeDesc M laws ha).f n
      ((coneCoordinateEquiv (zeroExtensionMap (lawEvaluationHom M laws ha)) n).symm p) =
        (zeroExtensionMap (lawRestrictionHom M laws ha)).f n p.1 := by
  rw [coneCoordinateEquiv_symm_eq, map_add, lawFiberConeDesc_inr_apply,
    lawFiberConeDesc_inl_apply, add_zero]

/-- 実錐の全元に対する原L制限評価式。 -/
theorem lawFiberConeDesc_apply (n : ℤ) (z : (lawFiberCone M laws ha).X n) :
    (lawFiberConeDesc M laws ha).f n z = (zeroExtensionMap (lawRestrictionHom M laws ha)).f n
      (coneCoordinateEquiv (zeroExtensionMap (lawEvaluationHom M laws ha)) n z).1 := by
  simpa only [LinearEquiv.symm_apply_apply] using
    lawFiberConeDesc_symm_apply M laws ha n (coneCoordinateEquiv _ n z)

/-- 原ε錐への包含の後に評価すると、原L制限そのものになる。 -/
theorem lawFiberCone_inr_desc : mappingCone.inr (zeroExtensionMap (lawEvaluationHom M laws ha)) ≫
    lawFiberConeDesc M laws ha = zeroExtensionMap (lawRestrictionHom M laws ha) :=
  mappingCone.inr_descShortComplex (lawEvaluationRestrictionShortComplex M laws ha)

/-- 原Law短完全性から同じ実評価の擬同型性を生成する。 -/
instance lawFiberConeDesc_quasiIso : QuasiIso (lawFiberConeDesc M laws ha) :=
  mappingCone.quasiIso_descShortComplex (lawEvaluationRestriction_shortExact M laws ha)

/-- 同じLaw Q評価の全次数homology射は標準圏で可逆である。 -/
instance lawFiberConeDesc_homology_isIso (n : ℤ) :
    IsIso (homologyMap (lawFiberConeDesc M laws ha) n) :=
  (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

/-- 同じ実Law ε錐と同じQの全homology両方向同型。 -/
def lawFiberConeHomologyEquiv (n : ℤ) : (lawFiberCone M laws ha).homology n ≃ₗ[ℚ]
    (zeroExtension (lawRestrictionComplex M laws ha)).homology n :=
  (asIso (homologyMap (lawFiberConeDesc M laws ha) n)).toLinearEquiv

/-- 全次数の順射は同じQ評価のhomology射である。 -/
theorem lawFiberConeHomologyEquiv_apply (n : ℤ) (z : (lawFiberCone M laws ha).homology n) :
    lawFiberConeHomologyEquiv M laws ha n z = homologyMap (lawFiberConeDesc M laws ha) n z := rfl

/-- 同じ実Law錐の連結射は同じ原Law SESδと全次数で一致する。 -/
theorem lawFiberCone_connecting (n : ℤ) : coneConnecting (zeroExtensionMap (lawEvaluationHom M laws ha)) n =
    homologyMap (lawFiberConeDesc M laws ha) n ≫
      (lawEvaluationRestriction_shortExact M laws ha).δ n (n+1) rfl :=
  coneConnecting_shortExact (lawEvaluationRestrictionShortComplex M laws ha)
    (lawEvaluationRestriction_shortExact M laws ha) n

/-- 同じ実Law錐H¹をliteral Law κ*核へ送る両方向同型。 -/
def lawFiberConeH1REquiv : (lawFiberCone M laws ha).homology (1 : ℤ) ≃ₗ[ℚ] lawR M laws ha :=
  (lawFiberConeHomologyEquiv M laws ha 1).trans (lawRestrictionHomologyREquiv M laws ha)

/-- Law錐R座標への順射は同じ実Q評価を使う。 -/
theorem lawFiberConeH1REquiv_apply (z : (lawFiberCone M laws ha).homology (1 : ℤ)) :
    lawFiberConeH1REquiv M laws ha z = lawRestrictionHomologyREquiv M laws ha
      (lawFiberConeHomologyEquiv M laws ha 1 z) := rfl

/-- 原Law τは同じLaw錐連結射とshift符号まで一致する。 -/
theorem lawFiberConeH1REquiv_tau (z : (lawFiberCone M laws ha).homology (1 : ℤ)) :
    lawConnectingTau M laws ha (lawFiberConeH1REquiv M laws ha z) =
      coneConnecting (zeroExtensionMap (lawEvaluationHom M laws ha)) 1 z := by
  rw [lawFiberConeH1REquiv_apply, lawConnectingTau_apply, LinearEquiv.symm_apply_apply,
    lawFiberCone_connecting, ModuleCat.comp_apply, lawFiberConeHomologyEquiv_apply]
  rfl

/-- Law係数錐族同型は全次数で原Pと原粗Cの同じ値を読む。 -/
theorem lawCoefficientConeFamilyIso_component (n : ℤ) (z : (lawCoefficientCone M laws ha).X n)
    (l : LawValueLabel laws) :
    coneCoordinateEquiv (zeroExtensionMap (unitHom M (labelValueFiber laws qc ha l))) n
      ((lawCoefficientConeFamilyIso M laws ha).hom.f n z l) =
    ((lawPushforwardStandardIso M laws ha).hom.f n
      (coneCoordinateEquiv (zeroExtensionMap (lawUnitHom M laws ha)) n z).1 l,
      (lawCoarseStandardIso (Nc := Nc) laws ha).hom.f (n+1)
        (coneCoordinateEquiv (zeroExtensionMap (lawUnitHom M laws ha)) n z).2 l) :=
  coefficientFamilyConeIso_component _ _ _ _ (lawUnitStandard_square M laws ha) n z l

/-- Law fiber錐族同型は全次数で原細Cと原Pの同じ値を読む。 -/
theorem lawFiberConeFamilyIso_component (n : ℤ) (z : (lawFiberCone M laws ha).X n)
    (l : LawValueLabel laws) :
    coneCoordinateEquiv (zeroExtensionMap (evaluationHom M (labelValueFiber laws qc ha l))) n
      ((lawFiberConeFamilyIso M laws ha).hom.f n z l) =
    ((lawFineStandardIso (Nf := Nf) (h := h) laws ha).hom.f n
      (coneCoordinateEquiv (zeroExtensionMap (lawEvaluationHom M laws ha)) n z).1 l,
      (lawPushforwardStandardIso M laws ha).hom.f (n+1)
        (coneCoordinateEquiv (zeroExtensionMap (lawEvaluationHom M laws ha)) n z).2 l) :=
  coefficientFamilyConeIso_component _ _ _ _ (lawEvaluationStandard_square M laws ha) n z l

/-- 独立Law全体錐族同型は全次数で原細Cと原粗Cの同じ値を読む。 -/
theorem lawTotalConeFamilyIso_component (n : ℤ) (z : (lawTotalCone M laws ha).X n)
    (l : LawValueLabel laws) :
    coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom (labelValueFiber laws qc ha l))) n
      ((lawTotalConeFamilyIso M laws ha).hom.f n z l) =
    ((lawFineStandardIso (Nf := Nf) (h := h) laws ha).hom.f n
      (coneCoordinateEquiv (zeroExtensionMap
        (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) n z).1 l,
      (lawCoarseStandardIso (Nc := Nc) laws ha).hom.f (n+1)
        (coneCoordinateEquiv (zeroExtensionMap
          (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) n z).2 l) :=
  coefficientFamilyConeIso_component _ _ _ _ (lawGeneratedStandard_square M laws ha) n z l

/-- 同じLaw係数錐から原ラベル係数錐の有限直和への同型。 -/
def lawCoefficientConeDirectSumIso : lawCoefficientCone M laws ha ≅
    biproduct (fun l => coefficientCone M (labelValueFiber laws qc ha l)) :=
  lawCoefficientConeFamilyIso M laws ha ≪≫ FiniteComplexFamily.directSumIso _

/-- 同じLaw fiber錐から原ラベルfiber錐の有限直和への同型。 -/
def lawFiberConeDirectSumIso : lawFiberCone M laws ha ≅
    biproduct (fun l => fiberCone M (labelValueFiber laws qc ha l)) :=
  lawFiberConeFamilyIso M laws ha ≪≫ FiniteComplexFamily.directSumIso _

/-- 独立Law全体錐から原ラベル全体錐の有限直和への同型。 -/
def lawTotalConeDirectSumIso : lawTotalCone M laws ha ≅
    biproduct (fun l => totalCone M (labelValueFiber laws qc ha l)) :=
  lawTotalConeFamilyIso M laws ha ≪≫ FiniteComplexFamily.directSumIso _

/-- 第一triangle射は同じ原ラベル第一射と全次数で可換。 -/
theorem lawCoefficientCompositionTriangle_first_component (n : ℤ)
    (z : (lawCoefficientCone M laws ha).X n) (l : LawValueLabel laws) :
    (lawTotalConeFamilyIso M laws ha).hom.f n
      ((lawCoefficientCompositionTriangle M laws ha).mor₁.f n z) l =
    (coefficientCompositionTriangle M (labelValueFiber laws qc ha l)).mor₁.f n
      ((lawCoefficientConeFamilyIso M laws ha).hom.f n z l) := by
  apply (coneCoordinateEquiv (zeroExtensionMap
    (M.aSubnerveComparisonHom (labelValueFiber laws qc ha l))) n).injective
  rw [lawTotalConeFamilyIso_component, lawCoefficientCompositionTriangle_first,
    coefficientCompositionTriangle_first, lawCoefficientConeFamilyIso_component]
  apply Prod.ext
  · exact congrArg (fun f => f.f n
      (coneCoordinateEquiv (zeroExtensionMap (lawUnitHom M laws ha)) n z).1 l)
      (lawEvaluationStandard_square M laws ha)
  · rfl

/-- 第二triangle射は同じ原ラベル第二射と全次数で可換。 -/
theorem lawCoefficientCompositionTriangle_second_component (n : ℤ)
    (z : (lawTotalCone M laws ha).X n) (l : LawValueLabel laws) :
    (lawFiberConeFamilyIso M laws ha).hom.f n
      ((lawCoefficientCompositionTriangle M laws ha).mor₂.f n z) l =
    (coefficientCompositionTriangle M (labelValueFiber laws qc ha l)).mor₂.f n
      ((lawTotalConeFamilyIso M laws ha).hom.f n z l) := by
  apply (coneCoordinateEquiv (zeroExtensionMap
    (evaluationHom M (labelValueFiber laws qc ha l))) n).injective
  rw [lawFiberConeFamilyIso_component, lawCoefficientCompositionTriangle_second,
    coefficientCompositionTriangle_second, lawTotalConeFamilyIso_component]
  apply Prod.ext
  · rfl
  · exact congrArg (fun f => f.f (n+1)
      (coneCoordinateEquiv (zeroExtensionMap
        (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) n z).2 l)
      (lawUnitStandard_square M laws ha)

/-- 第三triangle射は同じ原ラベル第三射とshift負号まで全次数で可換。 -/
theorem lawCoefficientCompositionTriangle_third_component (n : ℤ)
    (z : (lawFiberCone M laws ha).X n) (l : LawValueLabel laws) :
    (lawCoefficientConeFamilyIso M laws ha).hom.f (n+1)
      (((lawCoefficientCone M laws ha).shiftFunctorObjXIso 1 n (n+1) rfl).hom
        ((lawCoefficientCompositionTriangle M laws ha).mor₃.f n z)) l =
    ((coefficientCone M (labelValueFiber laws qc ha l)).shiftFunctorObjXIso 1 n (n+1) rfl).hom
      ((coefficientCompositionTriangle M (labelValueFiber laws qc ha l)).mor₃.f n
        ((lawFiberConeFamilyIso M laws ha).hom.f n z l)) := by
  apply (coneCoordinateEquiv (zeroExtensionMap
    (unitHom M (labelValueFiber laws qc ha l))) (n+1)).injective
  rw [lawCoefficientConeFamilyIso_component, lawCoefficientCompositionTriangle_third,
    coefficientCompositionTriangle_third, lawFiberConeFamilyIso_component]
  simp only [map_neg, map_zero]
  rfl

/-- 同じLaw Q評価は原ラベルQ評価族と全次数・全元で可換。 -/
theorem lawFiberConeDesc_family_square : lawFiberConeDesc M laws ha ≫
    (lawRestrictionStandardIso M laws ha).hom =
    (lawFiberConeFamilyIso M laws ha).hom ≫
      FiniteComplexFamily.map _ _ (fun l => fiberConeDesc M (labelValueFiber laws qc ha l)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext l
  change (lawRestrictionStandardIso M laws ha).hom.f n ((lawFiberConeDesc M laws ha).f n z) l =
    (fiberConeDesc M (labelValueFiber laws qc ha l)).f n
      ((lawFiberConeFamilyIso M laws ha).hom.f n z l)
  rw [lawFiberConeDesc_apply, fiberConeDesc_apply, lawFiberConeFamilyIso_component]
  exact congrArg (fun f => f.f n
    (coneCoordinateEquiv (zeroExtensionMap (lawEvaluationHom M laws ha)) n z).1 l)
    (lawRestrictionStandard_square M laws ha)

/-- 同じ実Law fiber錐homologyを原各fiber錐homology族へ送る。 -/
def lawFiberConeFamilyHomologyEquiv (n : ℤ) : (lawFiberCone M laws ha).homology n ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → (fiberCone M (labelValueFiber laws qc ha l)).homology n) :=
  coefficientFamilyHomologyEquiv (lawFiberConeFamilyIso M laws ha) n

/-- 実Law Q評価のhomologyは全次数・全元で原ラベルQ評価と可換。 -/
theorem lawFiberConeHomologyEquiv_family (n : ℤ) (z : (lawFiberCone M laws ha).homology n)
    (l : LawValueLabel laws) :
    lawRestrictionHomologyEquiv M laws ha n (lawFiberConeHomologyEquiv M laws ha n z) l =
      fiberConeHomologyEquiv M (labelValueFiber laws qc ha l) n
        (lawFiberConeFamilyHomologyEquiv M laws ha n z l) := by
  rw [lawFiberConeHomologyEquiv_apply, fiberConeHomologyEquiv_apply, lawRestrictionHomologyEquiv_eq]
  exact coefficientFamilyHomologyEquiv_natural _ _ _ _ (lawFiberConeDesc_family_square M laws ha) n z l

/-- 実Law錐R同定は全ラベルで同じ原錐R同定と可換。 -/
theorem lawFiberConeH1REquiv_family (z : (lawFiberCone M laws ha).homology (1 : ℤ))
    (l : LawValueLabel laws) :
    lawRFamilyEquiv M laws ha (lawFiberConeH1REquiv M laws ha z) l =
      fiberConeH1REquiv M (labelValueFiber laws qc ha l)
        (lawFiberConeFamilyHomologyEquiv M laws ha 1 z l) := by
  rw [lawFiberConeH1REquiv_apply, lawRestrictionHomologyREquiv_component,
    lawFiberConeHomologyEquiv_family, fiberConeH1REquiv_apply]

/-- 同じLaw錐連結射は各原錐連結射とshift符号まで一致する。 -/
theorem lawFiberCone_connecting_component (z : (lawFiberCone M laws ha).homology (1 : ℤ))
    (l : LawValueLabel laws) :
    lawPushforwardHomologyEquiv M laws ha 2
      (coneConnecting (zeroExtensionMap (lawEvaluationHom M laws ha)) 1 z) l =
    coneConnecting (zeroExtensionMap (evaluationHom M (labelValueFiber laws qc ha l))) 1
      (lawFiberConeFamilyHomologyEquiv M laws ha 1 z l) := by
  rw [← lawFiberConeH1REquiv_tau, lawConnectingTau_component,
    lawFiberConeH1REquiv_family, fiberConeH1REquiv_tau]

/-- 同じLaw錐核射影の値はliteral Law R上の同じτである。 -/
theorem lawFiberConeKernelProjection_tau (z : (lawFiberCone M laws ha).homology (1 : ℤ)) :
    (coneKernelProjection (zeroExtensionMap (lawEvaluationHom M laws ha)) 1 z).val =
      lawConnectingTau M laws ha (lawFiberConeH1REquiv M laws ha z) := by
  rw [coneKernelProjection_val, lawFiberConeH1REquiv_tau]

/-- 元入力で生成したLaw H⁰Q零性は同じ実Law fiber錐へ移る。 -/
theorem lawFiberCone_H0_isZero : IsZero ((lawFiberCone M laws ha).homology (0 : ℤ)) := by
  letI : Subsingleton ((zeroExtension (lawRestrictionComplex M laws ha)).homology (0 : ℤ)) :=
    ModuleCat.subsingleton_of_isZero (lawRestriction_H0_isZero M laws ha)
  letI : Subsingleton ((lawFiberCone M laws ha).homology (0 : ℤ)) :=
    (lawFiberConeHomologyEquiv M laws ha 0).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- 同じLaw Q homology同型の逆元を同じ実評価で読む。 -/
theorem lawFiberConeHomologyEquiv_symm_evaluation (n : ℤ)
    (z : (zeroExtension (lawRestrictionComplex M laws ha)).homology n) :
    homologyMap (lawFiberConeDesc M laws ha) n ((lawFiberConeHomologyEquiv M laws ha n).symm z) = z :=
  (lawFiberConeHomologyEquiv M laws ha n).apply_symm_apply z

/-- 同じLaw錐包含は全次数で同じ原Law L制限homologyへ送られる。 -/
theorem lawFiberConeHomologyEquiv_inr (n : ℤ)
    (z : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology n) :
    lawFiberConeHomologyEquiv M laws ha n
      (homologyMap (mappingCone.inr (zeroExtensionMap (lawEvaluationHom M laws ha))) n z) =
      homologyMap (zeroExtensionMap (lawRestrictionHom M laws ha)) n z := by
  rw [lawFiberConeHomologyEquiv_apply, ← ModuleCat.comp_apply,
    ← homologyMap_comp, lawFiberCone_inr_desc]

/-- 同じLaw錐H¹包含はliteral Rへの原Law fiber制限である。 -/
theorem lawFiberConeH1REquiv_inr
    (z : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ)) :
    lawFiberConeH1REquiv M laws ha
      (homologyMap (mappingCone.inr (zeroExtensionMap (lawEvaluationHom M laws ha))) 1 z) =
      lawFiberRestrictionH1 M laws ha z := by
  rw [lawFiberConeH1REquiv_apply, lawFiberConeHomologyEquiv_inr, lawFiberRestrictionH1_apply]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientFiniteBiproducts
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientFamilyConeIso
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientFamilyConeIso_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCone
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberCone
#print axioms AAT.AG.AtlasCoefficientFiber.lawTotalCone
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientConeFamilyIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeFamilyIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawTotalConeFamilyIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCompositionTriangle
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCompositionTriangle_distinguished
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCompositionTriangle_first
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCompositionTriangle_second
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCompositionTriangle_third
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeDesc
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeDesc_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeDesc_inr_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeDesc_inl_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeDesc_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeDesc_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberCone_inr_desc
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeDesc_quasiIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeDesc_homology_isIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeHomologyEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberCone_connecting
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeH1REquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeH1REquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeH1REquiv_tau
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientConeFamilyIso_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeFamilyIso_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawTotalConeFamilyIso_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientConeDirectSumIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeDirectSumIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawTotalConeDirectSumIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCompositionTriangle_first_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCompositionTriangle_second_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCompositionTriangle_third_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeDesc_family_square
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeFamilyHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeHomologyEquiv_family
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeH1REquiv_family
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberCone_connecting_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeKernelProjection_tau
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberCone_H0_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeHomologyEquiv_symm_evaluation
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeHomologyEquiv_inr
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberConeH1REquiv_inr
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
