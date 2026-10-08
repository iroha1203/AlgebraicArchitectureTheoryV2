import ResearchLean.AG.AtlasCoefficientFiber.LawCoefficientInput

/-!
# G-135 D：同じ実Law比較の順像因子化

## Implementation notes

各ラベルの原Pを成分ごとに集める。独立なgeneratedComparisonHomは定義し直さず、
既存block正方形とcanonical逆像等号から、別に作った二射の合成へ同定する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 各原Law block比較は同じ粗A・細canonical逆像比較と三次数で可換。 -/
theorem lawBlockCanonical_square (l : LawValueLabel laws) :
    cochainComp (M.generatedBlockComparisonHom laws ha (lawFineAdequate (h := h) laws ha) l)
      (lawFineBlockCanonicalEquiv (Nf := Nf) (h := h) laws ha l).toHom =
      cochainComp (Nc.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom
        (M.aSubnerveComparisonHom (labelValueFiber laws qc ha l)) := by
  rw [lawFineBlockCanonicalEquiv_toHom, ← coefficientCochain_comp_assoc]
  rw [AAT.AG.FaceRelationSubdivision.lawBlockFiber_comparison_square]
  rw [coefficientCochain_comp_assoc, coefficientCochainEquivOfEq_comp]
  rw [AAT.AG.FaceRelationSubdivision.lawFiberComparison_canonical]

/-- 元の実Law比較とcanonical台族の同じ比較の全Hom正方形。 -/
theorem lawGeneratedCanonical_square :
    cochainComp (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))
      (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).toHom =
      cochainComp (lawCoarseCanonicalEquiv (Nc := Nc) laws ha).toHom
        (ThreeComplexFamily.map
          (fun l => Nc.targetSubsetComplex (labelValueFiber laws qc ha l))
          (fun l => Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' labelValueFiber laws qc ha l))
          (fun l => M.aSubnerveComparisonHom (labelValueFiber laws qc ha l))) := by
  rw [lawFineCanonicalEquiv_toHom, ← coefficientCochain_comp_assoc]
  rw [M.lawFamily_square]
  rw [coefficientCochain_comp_assoc]
  rw [coefficientFamilyEquiv_natural
    (fun l => Nc.lawValueBlockTargetSubsetComplexEquiv laws ha l)
    (lawFineBlockCanonicalEquiv (Nf := Nf) (h := h) laws ha)
    (fun l => M.generatedBlockComparisonHom laws ha (lawFineAdequate (h := h) laws ha) l)
    (fun l => M.aSubnerveComparisonHom (labelValueFiber laws qc ha l))
    (lawBlockCanonical_square M laws ha)]
  rw [← coefficientCochain_comp_assoc, ← lawCoarseCanonicalEquiv_toHom]

/-- Law順像は同じ発生ラベルの原Pの有限族複体である。 -/
def lawPushforwardComplex : ThreeCochainComplex.{0,u} ℚ :=
  ThreeComplexFamily.complex (fun l => pushforwardComplex M (labelValueFiber laws qc ha l))

/-- 実粗Law座標から、各原ηへのunit。 -/
def lawUnitHom : ThreeCochainComplex.Hom (Nc.lawGeneratedComplex laws ha)
    (lawPushforwardComplex M laws ha) :=
  cochainComp (lawCoarseCanonicalEquiv (Nc := Nc) laws ha).toHom
    (ThreeComplexFamily.map _ _ (fun l => unitHom M (labelValueFiber laws qc ha l)))

/-- 各原εのセル評価を元の実細Law座標へ戻す。 -/
def lawEvaluationHom : ThreeCochainComplex.Hom (lawPushforwardComplex M laws ha)
    (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha)) :=
  cochainComp (ThreeComplexFamily.map _ _ (fun l => evaluationHom M (labelValueFiber laws qc ha l)))
    (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).symm.toHom

/-- Law unitの実次数0は同じ原ηの成分値である。 -/
theorem lawUnitHom_f0 (x : (Nc.lawGeneratedComplex laws ha).C0) (l : LawValueLabel laws) :
    (lawUnitHom M laws ha).f0 x l = (unitHom M (labelValueFiber laws qc ha l)).f0
      ((lawCoarseCanonicalEquiv (Nc := Nc) laws ha).e0 x l) := rfl

/-- Law unitの実次数1は同じ原ηの成分値である。 -/
theorem lawUnitHom_f1 (x : (Nc.lawGeneratedComplex laws ha).C1) (l : LawValueLabel laws) :
    (lawUnitHom M laws ha).f1 x l = (unitHom M (labelValueFiber laws qc ha l)).f1
      ((lawCoarseCanonicalEquiv (Nc := Nc) laws ha).e1 x l) := rfl

/-- Law unitの実次数2は同じ原ηの成分値である。 -/
theorem lawUnitHom_f2 (x : (Nc.lawGeneratedComplex laws ha).C2) (l : LawValueLabel laws) :
    (lawUnitHom M laws ha).f2 x l = (unitHom M (labelValueFiber laws qc ha l)).f2
      ((lawCoarseCanonicalEquiv (Nc := Nc) laws ha).e2 x l) := rfl

/-- 同じ実Law評価の後に細同値を適用すると、原ε族の全Homになる。 -/
theorem lawEvaluationCanonical_square :
    cochainComp (lawEvaluationHom M laws ha)
      (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).toHom =
      ThreeComplexFamily.map _ _ (fun l => evaluationHom M (labelValueFiber laws qc ha l)) := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro x
  · exact (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e0.apply_symm_apply _
  · exact (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e1.apply_symm_apply _
  · exact (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e2.apply_symm_apply _

/-- 独立生成済み実Law比較は、別に生成したunitと評価の全Hom合成である。 -/
theorem lawGeneratedComparison_factorization :
    M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha) =
      cochainComp (lawUnitHom M laws ha) (lawEvaluationHom M laws ha) := by
  have hs := lawGeneratedCanonical_square M laws ha
  have hp : cochainComp
      (ThreeComplexFamily.map _ _ (fun l => unitHom M (labelValueFiber laws qc ha l)))
      (ThreeComplexFamily.map _ _ (fun l => evaluationHom M (labelValueFiber laws qc ha l))) =
      ThreeComplexFamily.map _ _ (fun l => M.aSubnerveComparisonHom (labelValueFiber laws qc ha l)) := by
    rw [coefficientFamily_map_comp]
    congr 1
    funext l
    exact (aSubnerveComparisonHom_factorization M _).symm
  have he : cochainComp (cochainComp (lawUnitHom M laws ha) (lawEvaluationHom M laws ha))
      (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).toHom =
      cochainComp (lawCoarseCanonicalEquiv (Nc := Nc) laws ha).toHom
        (ThreeComplexFamily.map _ _ (fun l => M.aSubnerveComparisonHom (labelValueFiber laws qc ha l))) := by
    rw [coefficientCochain_comp_assoc, lawEvaluationCanonical_square]
    change cochainComp (cochainComp _ _) _ = _
    rw [coefficientCochain_comp_assoc, hp]
  have hx := hs.trans he.symm
  apply cochain_ext <;> apply LinearMap.ext <;> intro x
  · exact (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e0.injective
      (congrArg (fun f => f.f0 x) hx)
  · exact (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e1.injective
      (congrArg (fun f => f.f1 x) hx)
  · exact (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e2.injective
      (congrArg (fun f => f.f2 x) hx)

/-- 同じ実Law因子化は標準零延長の全整数次数でも成立する。 -/
theorem lawStandardComparison_factorization :
    zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha)) =
      zeroExtensionMap (lawUnitHom M laws ha) ≫ zeroExtensionMap (lawEvaluationHom M laws ha) := by
  rw [lawGeneratedComparison_factorization, zeroExtensionMap_comp]


/-- Law unitの全Hom生成式。 -/
theorem lawUnitHom_eq : lawUnitHom M laws ha =
    cochainComp (lawCoarseCanonicalEquiv (Nc := Nc) laws ha).toHom
      (ThreeComplexFamily.map _ _ (fun l => unitHom M (labelValueFiber laws qc ha l))) := rfl

/-- Law評価の全Hom生成式。 -/
theorem lawEvaluationHom_eq : lawEvaluationHom M laws ha =
    cochainComp (ThreeComplexFamily.map _ _ (fun l => evaluationHom M (labelValueFiber laws qc ha l)))
      (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).symm.toHom := rfl

/-- 元の細Law次数0座標を戻すと、原εの同じ成分値になる。 -/
theorem lawEvaluationHom_f0 (x : (lawPushforwardComplex M laws ha).C0) (l : LawValueLabel laws) :
    (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e0 ((lawEvaluationHom M laws ha).f0 x) l =
      (evaluationHom M (labelValueFiber laws qc ha l)).f0 (x l) :=
  congrFun (congrArg (fun f => f.f0 x) (lawEvaluationCanonical_square M laws ha)) l

/-- 元の細Law次数1座標を戻すと、原εの同じ成分値になる。 -/
theorem lawEvaluationHom_f1 (x : (lawPushforwardComplex M laws ha).C1) (l : LawValueLabel laws) :
    (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e1 ((lawEvaluationHom M laws ha).f1 x) l =
      (evaluationHom M (labelValueFiber laws qc ha l)).f1 (x l) :=
  congrFun (congrArg (fun f => f.f1 x) (lawEvaluationCanonical_square M laws ha)) l

/-- 元の細Law次数2座標を戻すと、原εの同じ成分値になる。 -/
theorem lawEvaluationHom_f2 (x : (lawPushforwardComplex M laws ha).C2) (l : LawValueLabel laws) :
    (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e2 ((lawEvaluationHom M laws ha).f2 x) l =
      (evaluationHom M (labelValueFiber laws qc ha l)).f2 (x l) :=
  congrFun (congrArg (fun f => f.f2 x) (lawEvaluationCanonical_square M laws ha)) l

/-- 原P族の零延長を全整数次数の同じ原P零延長族へ同定する。 -/
def lawPushforwardStandardIso : zeroExtension (lawPushforwardComplex M laws ha) ≅
    FiniteComplexFamily.complex (fun l => zeroExtension (pushforwardComplex M (labelValueFiber laws qc ha l))) :=
  ThreeComplexFamily.zeroExtensionIso _

/-- 実粗Law零延長と同じ原粗台族への全次数同型。 -/
def lawCoarseStandardIso : zeroExtension (Nc.lawGeneratedComplex laws ha) ≅
    FiniteComplexFamily.complex (fun l => zeroExtension (Nc.targetSubsetComplex (labelValueFiber laws qc ha l))) :=
  cochainEquivZeroExtensionIso (lawCoarseCanonicalEquiv (Nc := Nc) laws ha) ≪≫
    ThreeComplexFamily.zeroExtensionIso _

/-- 実細Law零延長と同じcanonical逆像族への全次数同型。 -/
def lawFineStandardIso : zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha)) ≅
    FiniteComplexFamily.complex (fun l => zeroExtension
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' labelValueFiber laws qc ha l))) :=
  cochainEquivZeroExtensionIso (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha) ≪≫
    ThreeComplexFamily.zeroExtensionIso _

/-- 細Law標準同型の射は、可逆座標と同じ原複体族への同型の合成。 -/
theorem lawFineStandardIso_hom :
    (lawFineStandardIso (Nf := Nf) (h := h) laws ha).hom =
      (cochainEquivZeroExtensionIso
        (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha)).hom ≫
        (ThreeComplexFamily.zeroExtensionIso _).hom := rfl

/-- 元のLaw unitは全整数次数で同じ原η族の射と可換。 -/
theorem lawUnitStandard_square : zeroExtensionMap (lawUnitHom M laws ha) ≫
    (lawPushforwardStandardIso M laws ha).hom = (lawCoarseStandardIso (Nc := Nc) laws ha).hom ≫
      FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (unitHom M (labelValueFiber laws qc ha l))) := by
  rw [lawUnitHom_eq, zeroExtensionMap_comp]
  dsimp only [lawPushforwardStandardIso, lawCoarseStandardIso, Iso.trans_hom]
  rw [Category.assoc, ThreeComplexFamily.zeroExtensionIso_natural]
  rw [cochainEquivZeroExtensionIso_hom, Category.assoc]

/-- 元のLaw評価は全整数次数で同じ原ε族の射と可換。 -/
theorem lawEvaluationStandard_square : zeroExtensionMap (lawEvaluationHom M laws ha) ≫
    (lawFineStandardIso (Nf := Nf) (h := h) laws ha).hom = (lawPushforwardStandardIso M laws ha).hom ≫
      FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (evaluationHom M (labelValueFiber laws qc ha l))) := by
  have hs := congrArg zeroExtensionMap (lawEvaluationCanonical_square M laws ha)
  rw [zeroExtensionMap_comp] at hs
  dsimp only [lawFineStandardIso, lawPushforwardStandardIso, Iso.trans_hom]
  rw [cochainEquivZeroExtensionIso_hom, ← Category.assoc, hs,
    ThreeComplexFamily.zeroExtensionIso_natural]

/-- 独立生成実Law比較は全整数次数で同じ原u族の射と可換。 -/
theorem lawGeneratedStandard_square :
    zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha)) ≫
      (lawFineStandardIso (Nf := Nf) (h := h) laws ha).hom =
      (lawCoarseStandardIso (Nc := Nc) laws ha).hom ≫
        FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap
          (M.aSubnerveComparisonHom (labelValueFiber laws qc ha l))) := by
  have hs := congrArg zeroExtensionMap (lawGeneratedCanonical_square M laws ha)
  rw [zeroExtensionMap_comp, zeroExtensionMap_comp] at hs
  dsimp only [lawFineStandardIso, lawCoarseStandardIso, Iso.trans_hom]
  rw [cochainEquivZeroExtensionIso_hom, cochainEquivZeroExtensionIso_hom]
  rw [← Category.assoc, hs, Category.assoc, ThreeComplexFamily.zeroExtensionIso_natural,
    ← Category.assoc]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawBlockCanonical_square
#print axioms AAT.AG.AtlasCoefficientFiber.lawGeneratedCanonical_square
#print axioms AAT.AG.AtlasCoefficientFiber.lawPushforwardComplex
#print axioms AAT.AG.AtlasCoefficientFiber.lawUnitHom
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationHom
#print axioms AAT.AG.AtlasCoefficientFiber.lawUnitHom_f0
#print axioms AAT.AG.AtlasCoefficientFiber.lawUnitHom_f1
#print axioms AAT.AG.AtlasCoefficientFiber.lawUnitHom_f2
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationCanonical_square
#print axioms AAT.AG.AtlasCoefficientFiber.lawGeneratedComparison_factorization
#print axioms AAT.AG.AtlasCoefficientFiber.lawStandardComparison_factorization
#print axioms AAT.AG.AtlasCoefficientFiber.lawUnitHom_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationHom_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationHom_f0
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationHom_f1
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationHom_f2
#print axioms AAT.AG.AtlasCoefficientFiber.lawPushforwardStandardIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoarseStandardIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawFineStandardIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawFineStandardIso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.lawUnitStandard_square
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationStandard_square
#print axioms AAT.AG.AtlasCoefficientFiber.lawGeneratedStandard_square
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
