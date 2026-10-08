import ResearchLean.AG.AtlasCoefficientFiber.LawSupportConnecting
import ResearchLean.AG.AtlasCoefficientFiber.LawCoefficientCones

/-!
# G-135 D：原Law三錐と同じ部分台の合成triangle

## Implementation notes

原Lawのη・ε・独立uから標準mappingCone.mapを生成する。
全整数次数の二座標、三射、shift負号、同じQ評価とnative連結射を保つ。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition CochainComplex
universe u
variable {Source : Type u} [Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
variable (l : LawValueLabel laws) {A : Set qc.Target}
variable (hA : A ⊆ labelValueFiber laws qc ha l)

/-- 元coefficient錐を同じ原正方形から台制限する。 -/
def lawSupportCoefficientCone : lawCoefficientCone M laws ha ⟶ coefficientCone M A :=
  mappingCone.map (zeroExtensionMap (lawUnitHom M laws ha)) (zeroExtensionMap (unitHom M A))
    (lawSupportCoarse (Nc := Nc) laws ha l hA) (lawSupportP M laws ha l hA) (lawSupportUnit M laws ha l hA)

/-- 同じ元coefficient錐制限は全次数で元二座標の台制限として作用する。 -/
theorem lawSupportCoefficientCone_apply (n : ℤ) (z : (lawCoefficientCone M laws ha).X n) :
    coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) n ((lawSupportCoefficientCone M laws ha l hA).f n z) =
      ((lawSupportP M laws ha l hA).f n (coneCoordinateEquiv (zeroExtensionMap (lawUnitHom M laws ha)) n z).1,
       (lawSupportCoarse (Nc := Nc) laws ha l hA).f (n+1) (coneCoordinateEquiv (zeroExtensionMap (lawUnitHom M laws ha)) n z).2) :=
  coneCoordinateEquiv_map _ _ _ _ (lawSupportUnit M laws ha l hA) n z

/-- 元fiber錐を同じ原正方形から台制限する。 -/
def lawSupportFiberCone : lawFiberCone M laws ha ⟶ fiberCone M A :=
  mappingCone.map (zeroExtensionMap (lawEvaluationHom M laws ha)) (zeroExtensionMap (evaluationHom M A))
    (lawSupportP M laws ha l hA) (lawSupportFine M laws ha l hA) (lawSupportEvaluation M laws ha l hA)

/-- 同じ元fiber錐制限は全次数で元二座標の台制限として作用する。 -/
theorem lawSupportFiberCone_apply (n : ℤ) (z : (lawFiberCone M laws ha).X n) :
    coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) n ((lawSupportFiberCone M laws ha l hA).f n z) =
      ((lawSupportFine M laws ha l hA).f n (coneCoordinateEquiv (zeroExtensionMap (lawEvaluationHom M laws ha)) n z).1,
       (lawSupportP M laws ha l hA).f (n+1) (coneCoordinateEquiv (zeroExtensionMap (lawEvaluationHom M laws ha)) n z).2) :=
  coneCoordinateEquiv_map _ _ _ _ (lawSupportEvaluation M laws ha l hA) n z

/-- 元total錐を同じ原正方形から台制限する。 -/
def lawSupportTotalCone : lawTotalCone M laws ha ⟶ totalCone M A :=
  mappingCone.map (zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) (zeroExtensionMap (M.aSubnerveComparisonHom A))
    (lawSupportCoarse (Nc := Nc) laws ha l hA) (lawSupportFine M laws ha l hA) (lawSupportDirect M laws ha l hA)

/-- 同じ元total錐制限は全次数で元二座標の台制限として作用する。 -/
theorem lawSupportTotalCone_apply (n : ℤ) (z : (lawTotalCone M laws ha).X n) :
    coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) n ((lawSupportTotalCone M laws ha l hA).f n z) =
      ((lawSupportFine M laws ha l hA).f n (coneCoordinateEquiv (zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) n z).1,
       (lawSupportCoarse (Nc := Nc) laws ha l hA).f (n+1) (coneCoordinateEquiv (zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) n z).2) :=
  coneCoordinateEquiv_map _ _ _ _ (lawSupportDirect M laws ha l hA) n z

/-- 元合成triangleの第一射は同じ三錐台制限と全次数で可換。 -/
theorem lawSupportConeTriangle_first :
    (lawCoefficientCompositionTriangle M laws ha).mor₁ ≫ lawSupportTotalCone M laws ha l hA =
      lawSupportCoefficientCone M laws ha l hA ≫ (coefficientCompositionTriangle M A).mor₁ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (lawSupportTotalCone M laws ha l hA).f n ((lawCoefficientCompositionTriangle M laws ha).mor₁.f n z) =
    (coefficientCompositionTriangle M A).mor₁.f n ((lawSupportCoefficientCone M laws ha l hA).f n z)
  apply (coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) n).injective
  rw [lawSupportTotalCone_apply, lawCoefficientCompositionTriangle_first,
    coefficientCompositionTriangle_first, lawSupportCoefficientCone_apply]
  apply Prod.ext
  · exact congrArg (fun f => f.f n (coneCoordinateEquiv (zeroExtensionMap (lawUnitHom M laws ha)) n z).1)
      (lawSupportEvaluation M laws ha l hA)
  · rfl

/-- 元合成triangleの第二射も原η正方形から全次数で可換。 -/
theorem lawSupportConeTriangle_second :
    (lawCoefficientCompositionTriangle M laws ha).mor₂ ≫ lawSupportFiberCone M laws ha l hA =
      lawSupportTotalCone M laws ha l hA ≫ (coefficientCompositionTriangle M A).mor₂ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (lawSupportFiberCone M laws ha l hA).f n ((lawCoefficientCompositionTriangle M laws ha).mor₂.f n z) =
    (coefficientCompositionTriangle M A).mor₂.f n ((lawSupportTotalCone M laws ha l hA).f n z)
  apply (coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) n).injective
  rw [lawSupportFiberCone_apply, lawCoefficientCompositionTriangle_second,
    coefficientCompositionTriangle_second, lawSupportTotalCone_apply]
  apply Prod.ext
  · rfl
  · exact congrArg (fun f => f.f (n+1)
      (coneCoordinateEquiv (zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))) n z).2)
      (lawSupportUnit M laws ha l hA)

/-- 標準shiftの錐台射は同じ次数加算同型の下で元の次数射である。 -/
theorem lawSupportConeShift_apply (n : ℤ) (z : ((lawCoefficientCone M laws ha)⟦(1 : ℤ)⟧).X n) :
    ((coefficientCone M A).shiftFunctorObjXIso 1 n (n+1) rfl).hom
      ((lawSupportCoefficientCone M laws ha l hA)⟦(1 : ℤ)⟧'.f n z) =
      (lawSupportCoefficientCone M laws ha l hA).f (n+1)
        (((lawCoefficientCone M laws ha).shiftFunctorObjXIso 1 n (n+1) rfl).hom z) := rfl

/-- 元合成triangleの第三射は同じ標準shift負号まで保って全次数で可換。 -/
theorem lawSupportConeTriangle_third :
    (lawCoefficientCompositionTriangle M laws ha).mor₃ ≫ (lawSupportCoefficientCone M laws ha l hA)⟦(1 : ℤ)⟧' =
      lawSupportFiberCone M laws ha l hA ≫ (coefficientCompositionTriangle M A).mor₃ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (lawSupportCoefficientCone M laws ha l hA)⟦(1 : ℤ)⟧'.f n
      ((lawCoefficientCompositionTriangle M laws ha).mor₃.f n z) =
    (coefficientCompositionTriangle M A).mor₃.f n ((lawSupportFiberCone M laws ha l hA).f n z)
  apply (((coefficientCone M A).shiftFunctorObjXIso 1 n (n+1) rfl).toLinearEquiv).injective
  apply (coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) (n+1)).injective
  change coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) (n+1)
    (((coefficientCone M A).shiftFunctorObjXIso 1 n (n+1) rfl).hom
      ((lawSupportCoefficientCone M laws ha l hA)⟦(1 : ℤ)⟧'.f n
        ((lawCoefficientCompositionTriangle M laws ha).mor₃.f n z))) =
    coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) (n+1)
      (((coefficientCone M A).shiftFunctorObjXIso 1 n (n+1) rfl).hom
        ((coefficientCompositionTriangle M A).mor₃.f n ((lawSupportFiberCone M laws ha l hA).f n z)))
  rw [lawSupportConeShift_apply, lawSupportCoefficientCone_apply, lawCoefficientCompositionTriangle_third,
    coefficientCompositionTriangle_third, lawSupportFiberCone_apply]
  apply Prod.ext
  · exact map_neg ((lawSupportP M laws ha l hA).f (n+1)).hom _
  · exact map_zero ((lawSupportCoarse (Nc := Nc) laws ha l hA).f (n+1+1)).hom

/-- 元三錐の全三射から同じ実合成triangle間の台射を生成する。 -/
def lawSupportConeTriangle : lawCoefficientCompositionTriangle M laws ha ⟶ coefficientCompositionTriangle M A where
  hom₁ := lawSupportCoefficientCone M laws ha l hA
  hom₂ := lawSupportTotalCone M laws ha l hA
  hom₃ := lawSupportFiberCone M laws ha l hA
  comm₁ := lawSupportConeTriangle_first M laws ha l hA
  comm₂ := lawSupportConeTriangle_second M laws ha l hA
  comm₃ := lawSupportConeTriangle_third M laws ha l hA

/-- 原fiber錐からQへの評価は全次数で同じ台制限と可換。 -/
theorem lawSupportFiberConeDesc : lawFiberConeDesc M laws ha ≫ lawSupportQ M laws ha l hA =
    lawSupportFiberCone M laws ha l hA ≫ fiberConeDesc M A := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (lawSupportQ M laws ha l hA).f n ((lawFiberConeDesc M laws ha).f n z) =
    (fiberConeDesc M A).f n ((lawSupportFiberCone M laws ha l hA).f n z)
  rw [lawFiberConeDesc_apply, fiberConeDesc_apply, lawSupportFiberCone_apply]
  exact congrArg (fun f => f.f n (coneCoordinateEquiv (zeroExtensionMap (lawEvaluationHom M laws ha)) n z).1) (lawSupportRestriction M laws ha l hA)

/-- 原fiber錐からQへの全homology同型も同じ台射と自然。 -/
theorem lawSupportFiberConeHomologyEquiv (n : ℤ) (z : (lawFiberCone M laws ha).homology n) :
    HomologicalComplex.homologyMap (lawSupportQ M laws ha l hA) n
      (lawFiberConeHomologyEquiv M laws ha n z) =
    fiberConeHomologyEquiv M A n (HomologicalComplex.homologyMap (lawSupportFiberCone M laws ha l hA) n z) := by
  rw [lawFiberConeHomologyEquiv_apply, fiberConeHomologyEquiv_apply,
    ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    lawSupportFiberConeDesc]

/-- 原Qから錐へ戻る同じ両方向同型も全次数で部分台射と可換。 -/
theorem lawSupportFiberConeHomologyEquiv_symm (n : ℤ)
    (z : (zeroExtension (lawRestrictionComplex M laws ha)).homology n) :
    HomologicalComplex.homologyMap (lawSupportFiberCone M laws ha l hA) n
      ((lawFiberConeHomologyEquiv M laws ha n).symm z) =
    (fiberConeHomologyEquiv M A n).symm
      (HomologicalComplex.homologyMap (lawSupportQ M laws ha l hA) n z) := by
  apply (fiberConeHomologyEquiv M A n).injective
  rw [← lawSupportFiberConeHomologyEquiv, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- 原fiber錐の標準連結射は原Q評価と同じδを介して全整数次数で自然。 -/
theorem lawSupportFiberConeConnecting (n : ℤ) (z : (lawFiberCone M laws ha).homology n) :
    HomologicalComplex.homologyMap (lawSupportP M laws ha l hA) (n+1)
      (coneConnecting (zeroExtensionMap (lawEvaluationHom M laws ha)) n z) =
    coneConnecting (zeroExtensionMap (evaluationHom M A)) n
      (HomologicalComplex.homologyMap (lawSupportFiberCone M laws ha l hA) n z) := by
  rw [lawFiberCone_connecting, fiberCone_connecting, ModuleCat.comp_apply, ModuleCat.comp_apply]
  have hh := lawSupport_delta M laws ha l hA n
    (lawFiberConeHomologyEquiv M laws ha n z)
  rw [lawSupportFiberConeHomologyEquiv, lawFiberConeHomologyEquiv_apply,
    fiberConeHomologyEquiv_apply] at hh
  exact hh

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoefficientCone
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoefficientCone_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberCone
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberCone_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportTotalCone
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportTotalCone_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportConeTriangle_first
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportConeTriangle_second
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportConeShift_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportConeTriangle_third
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportConeTriangle
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeDesc
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeHomologyEquiv_symm
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeConnecting
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
