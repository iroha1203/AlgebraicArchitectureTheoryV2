import ResearchLean.AG.AtlasCoefficientFiber.FaceCloneHomology
import ResearchLean.AG.AtlasCoefficientFiber.LawCoefficientCones
import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationLaw

/-!
# G-135 D：面複製の同じ実Lawと選択ラベルのH²

## Implementation notes

全ラベルの原ε同型から実Law ε同型を生成する。
H²は面を選択する発生ラベルだけにℚを置くが、ラベル名を同じ台で商にしない。
選択しない成分の零性は原始非選択表から導く。全Lawが面を選ぶ条件を加えない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits HomologicalComplex CochainComplex
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u

/-- 選択成分の可逆座標と非選択成分の零性から、元添字を保つ全族同型を作る。 -/
def selectedFamilyEquiv {J : Type u} {X : J → Type u}
    [∀ j, AddCommGroup (X j)] [∀ j, Module ℚ (X j)]
    (p : J → Prop) (e : ∀ j, p j → X j ≃ₗ[ℚ] ℚ)
    (hz : ∀ j, ¬ p j → Subsingleton (X j)) :
    ((j : J) → X j) ≃ₗ[ℚ] ({j // p j} → ℚ) := by
  classical
  exact
    { toFun := fun x j => e j.1 j.2 (x j.1)
      invFun := fun y j => if hj : p j then (e j hj).symm (y ⟨j, hj⟩) else 0
      left_inv := by
        intro x
        funext j
        by_cases hj : p j
        · simp only [dif_pos hj, LinearEquiv.symm_apply_apply]
        · simpa only [dif_neg hj] using (hz j hj).elim (0 : X j) (x j)
      right_inv := by
        intro y
        funext j
        simp only [dif_pos j.2, LinearEquiv.apply_symm_apply]
      map_add' := by
        intro x y
        funext j
        exact map_add (e j.1 j.2) _ _
      map_smul' := by
        intro r x
        funext j
        exact map_smul (e j.1 j.2) r _ }
/-- 全族同型は各選択ラベルで同じ元成分の座標を読む。 -/
@[simp] theorem selectedFamilyEquiv_apply {J : Type u} {X : J → Type u}
    [∀ j, AddCommGroup (X j)] [∀ j, Module ℚ (X j)]
    (p : J → Prop) (e : ∀ j, p j → X j ≃ₗ[ℚ] ℚ)
    (hz : ∀ j, ¬ p j → Subsingleton (X j)) (x) (j : {j // p j}) :
    selectedFamilyEquiv p e hz x j = e j.1 j.2 (x j.1) := rfl

namespace FaceClone
variable {Source : Type u} [Fintype Source] {q : Reading Source}
variable (N : TargetSupportedNerve.{u,u} q) (F : N.nerve.FaceComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 原ラベルε同型を実Lawの全三次数複体へ移す。 -/
def lawEvaluationIso : zeroExtension (lawPushforwardComplex (FaceDuplication.comparison N F) laws ha) ≅
    zeroExtension ((FaceDuplication.supported N F).lawGeneratedComplex laws
      (lawFineAdequate (h := Reading.coarserThan_refl q) laws ha)) :=
  lawPushforwardStandardIso _ laws ha ≪≫
    FiniteComplexFamily.iso _ _ (fun l => evaluationIso N F (labelValueFiber laws q ha l)) ≪≫
      (lawFineStandardIso (Nf := FaceDuplication.supported N F)
        (h := Reading.coarserThan_refl q) laws ha).symm
/-- 実Law同型の順射は同じ原Law ε。 -/
theorem lawEvaluationIso_hom : (lawEvaluationIso N F laws ha).hom =
    zeroExtensionMap (lawEvaluationHom (FaceDuplication.comparison N F) laws ha) := by
  dsimp only [lawEvaluationIso, Iso.trans_hom, Iso.symm_hom]
  rw [FiniteComplexFamily.iso_hom]
  simp only [evaluationIso_hom]
  rw [← Category.assoc, ← lawEvaluationStandard_square, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
/-- 同じ実Law εを全次数・全元で保持する。 -/
theorem lawEvaluationIso_apply (n : ℤ) (z) :
    (lawEvaluationIso N F laws ha).hom.f n z =
      (zeroExtensionMap (lawEvaluationHom (FaceDuplication.comparison N F) laws ha)).f n z := by
  rw [lawEvaluationIso_hom]

/-- 同じ原Law aの両方向同型、同台ラベルも個別に保つ。 -/
def lawUnitEquiv : (zeroExtension (N.lawGeneratedComplex laws ha)).homology (1 : ℤ) ≃ₗ[ℚ]
    (zeroExtension (lawPushforwardComplex (FaceDuplication.comparison N F) laws ha)).homology (1 : ℤ) :=
  (lawCoarseHomologyEquiv (Nc := N) laws ha 1).trans
    ((LinearEquiv.piCongrRight (fun l => unitEquiv N F (labelValueFiber laws q ha l))).trans
      (lawPushforwardHomologyEquiv (FaceDuplication.comparison N F) laws ha 1).symm)
/-- 実Law a同型の順射は同じ元ηのH¹射。 -/
theorem lawUnitEquiv_apply (x) : lawUnitEquiv N F laws ha x =
    lawUnitH1 (FaceDuplication.comparison N F) laws ha x := by
  apply (lawPushforwardHomologyEquiv (FaceDuplication.comparison N F) laws ha 1).injective
  funext l
  dsimp only [lawUnitEquiv, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
  rw [LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.piCongrRight_apply, unitEquiv_apply, unitH1_eq_standard]
  exact (lawUnit_homology_component (FaceDuplication.comparison N F) laws ha 1 x l).symm
/-- 実Law aの逆座標は同じLaw元へ戻る。 -/
theorem lawUnitEquiv_symm_apply (y) :
    lawUnitH1 (FaceDuplication.comparison N F) laws ha ((lawUnitEquiv N F laws ha).symm y) = y := by
  rw [← lawUnitEquiv_apply, LinearEquiv.apply_symm_apply]
/-- 同じLaw aから逆に戻すと元の粗Law元を回復する。 -/
theorem lawUnitEquiv_apply_symm (x) :
    (lawUnitEquiv N F laws ha).symm (lawUnitH1 (FaceDuplication.comparison N F) laws ha x) = x := by
  rw [← lawUnitEquiv_apply, LinearEquiv.symm_apply_apply]
/-- 原実Law H¹比較は元G-134の両逆と同じ全単射。 -/
theorem lawH1_bijective : Function.Bijective
    ((FaceDuplication.comparison N F).generatedComparisonHom laws ha
      (lawFineAdequate (h := Reading.coarserThan_refl q) laws ha)).h1Map := by
  have he : (FaceDuplication.lawH1Equiv N F laws ha).toLinearMap =
      ((FaceDuplication.comparison N F).generatedComparisonHom laws ha
        (lawFineAdequate (h := Reading.coarserThan_refl q) laws ha)).h1Map :=
    FaceDuplication.lawH1Equiv_toLinearMap N F laws ha
  rw [← he]
  exact (FaceDuplication.lawH1Equiv N F laws ha).bijective
/-- 同じ原実Law旧診断の二成分は零。 -/
theorem lawDefect_zero : blockDefect
    ((FaceDuplication.comparison N F).generatedComparisonHom laws ha
      (lawFineAdequate (h := Reading.coarserThan_refl q) laws ha)).h1Map = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (lawH1_bijective N F laws ha)
omit [Fintype Source] in
/-- 同じliteral Law Rは各原始ラベルRが零なので零空間。 -/
theorem lawR_zero : Subsingleton (lawR (FaceDuplication.comparison N F) laws ha) := by
  letI : ∀ l : LawValueLabel laws, Subsingleton
    (R (FaceDuplication.comparison N F) (labelValueFiber laws q ha l)) :=
    fun l => R_zero N F (labelValueFiber laws q ha l)
  exact ⟨fun x y => (lawRFamilyEquiv (FaceDuplication.comparison N F) laws ha).injective
    (Subsingleton.elim _ _)⟩
/-- 同じ原Law τはliteral Law Rから出る零射。 -/
theorem lawTau_zero : lawConnectingTau (FaceDuplication.comparison N F) laws ha = 0 := by
  letI := lawR_zero N F laws ha
  ext z
  rw [Subsingleton.elim z 0, map_zero, LinearMap.zero_apply]
/-- 原Law ε錐は全整数次数で零homology。 -/
theorem lawFiberCone_zero (n : ℤ) :
    IsZero ((lawFiberCone (FaceDuplication.comparison N F) laws ha).homology n) := by
  apply cone_homology_isZero_of_bijective
  intro m
  have he : Function.Bijective (homologyMapIso (lawEvaluationIso N F laws ha) m).hom.hom :=
    (homologyMapIso (lawEvaluationIso N F laws ha) m).toLinearEquiv.bijective
  simpa only [homologyMapIso_hom, lawEvaluationIso_hom] using he

/-- 同じ原η錐と原u錐は原実Law ε同型の正方形で両方向同型。 -/
def lawCoefficientConeIso : lawCoefficientCone (FaceDuplication.comparison N F) laws ha ≅
    lawTotalCone (FaceDuplication.comparison N F) laws ha :=
  coneMapIso _ _ (Iso.refl _) (lawEvaluationIso N F laws ha) (by
    rw [lawEvaluationIso_hom, Iso.refl_hom, Category.id_comp]
    exact (lawStandardComparison_factorization (FaceDuplication.comparison N F) laws ha).symm)
/-- Law η錐同型の順射は同じ元標準正方形射。 -/
theorem lawCoefficientConeIso_hom : (lawCoefficientConeIso N F laws ha).hom =
    mappingCone.map (zeroExtensionMap (lawUnitHom (FaceDuplication.comparison N F) laws ha))
      (zeroExtensionMap ((FaceDuplication.comparison N F).generatedComparisonHom laws ha
        (lawFineAdequate (h := Reading.coarserThan_refl q) laws ha))) (𝟙 _)
      (zeroExtensionMap (lawEvaluationHom (FaceDuplication.comparison N F) laws ha))
        (by simpa only [Category.id_comp] using
          (lawStandardComparison_factorization (FaceDuplication.comparison N F) laws ha).symm) := by
  simp only [lawCoefficientConeIso, coneMapIso_hom, Iso.refl_hom, lawEvaluationIso_hom]
/-- 原Law η錐同型は同じ元三錐triangleの第一射である。 -/
theorem lawCoefficientConeIso_first : (lawCoefficientConeIso N F laws ha).hom =
    (lawCoefficientCompositionTriangle (FaceDuplication.comparison N F) laws ha).mor₁ := by
  ext n z
  apply (coneCoordinateEquiv
    (zeroExtensionMap ((FaceDuplication.comparison N F).generatedComparisonHom laws ha
      (lawFineAdequate (h := Reading.coarserThan_refl q) laws ha))) n).injective
  rw [lawCoefficientConeIso_hom, coneCoordinateEquiv_map]
  exact (lawCoefficientCompositionTriangle_first (FaceDuplication.comparison N F) laws ha n z).symm

/-- 同じ原Law total錐のhomologyを全発生ラベルの原total錐族へ送る。 -/
def lawTotalFamilyHomologyEquiv (n : ℤ) :
    (lawTotalCone (FaceDuplication.comparison N F) laws ha).homology n ≃ₗ[ℚ]
      ((l : LawValueLabel laws) →
        (totalCone (FaceDuplication.comparison N F) (labelValueFiber laws q ha l)).homology n) :=
  coefficientFamilyHomologyEquiv (lawTotalConeFamilyIso (FaceDuplication.comparison N F) laws ha) n
/-- 元面を選択する発生ラベル。台一致によるラベル同定は行わない。 -/
abbrev SelectedLabel := {l : LawValueLabel laws //
  ∃ t, t ∈ N.faceSupport F ∧ t ∈ labelValueFiber laws q ha l}
/-- 任意Lawの同じ原total錐H²は面を選ぶ元ラベルのℚ族。 -/
def lawTotalH2Equiv : (lawTotalCone (FaceDuplication.comparison N F) laws ha).homology (2 : ℤ) ≃ₗ[ℚ]
    (SelectedLabel N F laws ha → ℚ) :=
  (lawTotalFamilyHomologyEquiv N F laws ha 2).trans
    (selectedFamilyEquiv _ (fun l hl => totalConeH2Equiv N F (labelValueFiber laws q ha l) hl)
      (fun l hl => ModuleCat.isZero_iff_subsingleton.mp
        (absent_totalCone_zero N F (labelValueFiber laws q ha l) hl 2)))
/-- Law H²座標は各選択ラベルで同じ元total錐H²を読む。 -/
theorem lawTotalH2Equiv_apply (x) (l : SelectedLabel N F laws ha) :
    lawTotalH2Equiv N F laws ha x l = totalConeH2Equiv N F (labelValueFiber laws q ha l.1) l.2
      (lawTotalFamilyHomologyEquiv N F laws ha 2 x l.1) := rfl
/-- 同じ実Law η錐H²も原ラベル名を保つ選択族となる。 -/
def lawCoefficientH2Equiv :
    (lawCoefficientCone (FaceDuplication.comparison N F) laws ha).homology (2 : ℤ) ≃ₗ[ℚ]
      (SelectedLabel N F laws ha → ℚ) :=
  (homologyMapIso (lawCoefficientConeIso N F laws ha) 2).toLinearEquiv.trans
    (lawTotalH2Equiv N F laws ha)
/-- 同じ実Law比較の標準H²余核も選択された元ラベルのℚ族。 -/
def lawH2CokernelEquiv :
    ((zeroExtension ((FaceDuplication.supported N F).lawGeneratedComplex laws
      (lawFineAdequate (h := Reading.coarserThan_refl q) laws ha))).homology (2 : ℤ) ⧸
      LinearMap.range (homologyMap (zeroExtensionMap
        ((FaceDuplication.comparison N F).generatedComparisonHom laws ha
          (lawFineAdequate (h := Reading.coarserThan_refl q) laws ha))) 2).hom) ≃ₗ[ℚ]
      (SelectedLabel N F laws ha → ℚ) :=
  (comparisonConeHTwoEquiv _).symm.trans (lawTotalH2Equiv N F laws ha)
/-- 同じ原Law ηの標準H²余核も同じ選択ラベル族。 -/
def lawCoefficientH2CokernelEquiv :
    ((zeroExtension (lawPushforwardComplex (FaceDuplication.comparison N F) laws ha)).homology (2 : ℤ) ⧸
      LinearMap.range (homologyMap
        (zeroExtensionMap (lawUnitHom (FaceDuplication.comparison N F) laws ha)) 2).hom) ≃ₗ[ℚ]
      (SelectedLabel N F laws ha → ℚ) :=
  (comparisonConeHTwoEquiv _).symm.trans (lawCoefficientH2Equiv N F laws ha)

end FaceClone
end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.selectedFamilyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.selectedFamilyEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawEvaluationIso
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawEvaluationIso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawEvaluationIso_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawUnitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawUnitEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawUnitEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawUnitEquiv_apply_symm
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawH1_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawDefect_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawR_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawTau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawFiberCone_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawCoefficientConeIso
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawCoefficientConeIso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawCoefficientConeIso_first
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawTotalFamilyHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.SelectedLabel
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawTotalH2Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawTotalH2Equiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawCoefficientH2Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawH2CokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.lawCoefficientH2CokernelEquiv
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
