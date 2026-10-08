import ResearchLean.AG.AtlasCoefficientFiber.PushforwardEvaluation
import ResearchLean.AG.AtlasDefectComposition.ConeCompositionTriangle

/-!
# G-135 C：原η・原ε・独立uの三錐と合成triangle

## Implementation notes

原三項複体の全Hom因子化を標準零延長へ移す。中間対象は独立uの錐であり、
三射の成分とshift負号はG133の同じ標準mappingCone APIから読む。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition CochainComplex Pretriangulated
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原ηの係数差を読む実標準錐。 -/
abbrev coefficientCone := mappingCone (zeroExtensionMap (unitHom M A))

/-- 原εのfiber差を読む実標準錐。 -/
abbrev fiberCone := mappingCone (zeroExtensionMap (evaluationHom M A))

/-- 独立に生成済みの原uを保持する実全体錐。 -/
abbrev totalCone := mappingCone (zeroExtensionMap (M.aSubnerveComparisonHom A))

/-- 原全Hom因子化を全整数次数の標準complex射へ移す。 -/
theorem standardComparison_factorization :
    zeroExtensionMap (M.aSubnerveComparisonHom A) =
      zeroExtensionMap (unitHom M A) ≫ zeroExtensionMap (evaluationHom M A) := by
  rw [aSubnerveComparisonHom_factorization, zeroExtensionMap_comp]

/-- 同じ二射と独立uの錐から生成する合成triangle。 -/
def coefficientCompositionTriangle : Triangle (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  compositionTriangle (zeroExtensionMap (unitHom M A))
    (zeroExtensionMap (evaluationHom M A)) (zeroExtensionMap (M.aSubnerveComparisonHom A))
    (standardComparison_factorization M A)

/-- 合成triangleの始対象は原ηの錐。 -/
@[simp] theorem coefficientCompositionTriangle_obj₁ :
    (coefficientCompositionTriangle M A).obj₁ = coefficientCone M A := rfl

/-- 合成triangleの中間対象は独立uの錐。 -/
@[simp] theorem coefficientCompositionTriangle_obj₂ :
    (coefficientCompositionTriangle M A).obj₂ = totalCone M A := rfl

/-- 合成triangleの終対象は原εの錐。 -/
@[simp] theorem coefficientCompositionTriangle_obj₃ :
    (coefficientCompositionTriangle M A).obj₃ = fiberCone M A := rfl

/-- 同じ三錐の合成triangleは標準homotopy圏でdistinguishedとなる。 -/
theorem coefficientCompositionTriangle_distinguished :
    (HomotopyCategory.quotient (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)).mapTriangle.obj
      (coefficientCompositionTriangle M A) ∈
        distTriang (HomotopyCategory (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)) :=
  compositionTriangle_distinguished _ _ _ (standardComparison_factorization M A)

/-- 第一射は原εをtargetへ作用させ、原Cのshifted sourceを保つ。 -/
theorem coefficientCompositionTriangle_first (n : ℤ) (z : (coefficientCone M A).X n) :
    coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) n
      ((coefficientCompositionTriangle M A).mor₁.f n z) =
      ((zeroExtensionMap (evaluationHom M A)).f n
        (coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) n z).1,
        (coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) n z).2) :=
  compositionTriangle_first _ _ _ (standardComparison_factorization M A) n z

/-- 第二射は原C′のtargetを保ち、shifted sourceへ原ηを作用させる。 -/
theorem coefficientCompositionTriangle_second (n : ℤ) (z : (totalCone M A).X n) :
    coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) n
      ((coefficientCompositionTriangle M A).mor₂.f n z) =
      ((coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) n z).1,
        (zeroExtensionMap (unitHom M A)).f (n+1)
          (coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) n z).2) :=
  compositionTriangle_second _ _ _ (standardComparison_factorization M A) n z

/-- 第三射は標準shift負号を伴う原P包含である。 -/
theorem coefficientCompositionTriangle_third (n : ℤ) (z : (fiberCone M A).X n) :
    coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) (n+1)
      (((coefficientCone M A).shiftFunctorObjXIso 1 n (n+1) rfl).hom
        ((coefficientCompositionTriangle M A).mor₃.f n z)) =
      (-(coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) n z).2, 0) :=
  compositionTriangle_third _ _ _ (standardComparison_factorization M A) n z

/-- 原η錐の微分は全整数次数で(dP y+ηx,-dC x)となる。 -/
theorem coefficientCone_d (n : ℤ) (z : (coefficientCone M A).X n) :
    coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) (n+1)
      ((coefficientCone M A).d n (n+1) z) =
      ((zeroExtension (pushforwardComplex M A)).d n (n+1)
          (coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) n z).1 +
        (zeroExtensionMap (unitHom M A)).f (n+1)
          (coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) n z).2,
        -(zeroExtension (Nc.targetSubsetComplex A)).d (n+1) (n+1+1)
          (coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) n z).2) :=
  coneCoordinateEquiv_d_apply _ n z

/-- 原ε錐の微分は全整数次数で(dC′ y+εx,-dP x)となる。 -/
theorem fiberCone_d (n : ℤ) (z : (fiberCone M A).X n) :
    coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) (n+1)
      ((fiberCone M A).d n (n+1) z) =
      ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).d n (n+1)
          (coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) n z).1 +
        (zeroExtensionMap (evaluationHom M A)).f (n+1)
          (coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) n z).2,
        -(zeroExtension (pushforwardComplex M A)).d (n+1) (n+1+1)
          (coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) n z).2) :=
  coneCoordinateEquiv_d_apply _ n z

/-- 独立u錐の微分は全整数次数で(dC′ y+ux,-dC x)となる。 -/
theorem totalCone_d (n : ℤ) (z : (totalCone M A).X n) :
    coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) (n+1)
      ((totalCone M A).d n (n+1) z) =
      ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).d n (n+1)
          (coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) n z).1 +
        (zeroExtensionMap (M.aSubnerveComparisonHom A)).f (n+1)
          (coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) n z).2,
        -(zeroExtension (Nc.targetSubsetComplex A)).d (n+1) (n+1+1)
          (coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) n z).2) :=
  coneCoordinateEquiv_d_apply _ n z

/-- 原η錐の次数外対象は零であり、低次数寄与を消去しない。 -/
theorem coefficientCone_isZero (n : ℤ) (hm : n ≠ -1) (h0 : n ≠ 0)
    (h1 : n ≠ 1) (h2 : n ≠ 2) : IsZero ((coefficientCone M A).X n) :=
  comparisonCone_isZero _ n hm h0 h1 h2

/-- 原ε錐の次数外対象は零である。 -/
theorem fiberCone_isZero (n : ℤ) (hm : n ≠ -1) (h0 : n ≠ 0)
    (h1 : n ≠ 1) (h2 : n ≠ 2) : IsZero ((fiberCone M A).X n) :=
  comparisonCone_isZero _ n hm h0 h1 h2

/-- 独立u錐の次数外対象は零である。 -/
theorem totalCone_isZero (n : ℤ) (hm : n ≠ -1) (h0 : n ≠ 0)
    (h1 : n ≠ 1) (h2 : n ≠ 2) : IsZero ((totalCone M A).X n) :=
  comparisonCone_isZero _ n hm h0 h1 h2

/-- 原有限cellから全次数の係数錐有限次元性を得る。 -/
instance coefficientCone_finiteDimensional (n : ℤ) :
    FiniteDimensional ℚ ((coefficientCone M A).X n) := coneDegreeFiniteDimensional _ n

/-- 原有限cellから全次数のfiber錐有限次元性を得る。 -/
instance fiberCone_finiteDimensional (n : ℤ) :
    FiniteDimensional ℚ ((fiberCone M A).X n) := coneDegreeFiniteDimensional _ n

/-- 原有限cellから全次数の独立全体錐有限次元性を得る。 -/
instance totalCone_finiteDimensional (n : ℤ) :
    FiniteDimensional ℚ ((totalCone M A).X n) := coneDegreeFiniteDimensional _ n

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCone
#print axioms AAT.AG.AtlasCoefficientFiber.fiberCone
#print axioms AAT.AG.AtlasCoefficientFiber.totalCone
#print axioms AAT.AG.AtlasCoefficientFiber.standardComparison_factorization
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCompositionTriangle
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCompositionTriangle_obj₁
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCompositionTriangle_obj₂
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCompositionTriangle_obj₃
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCompositionTriangle_distinguished
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCompositionTriangle_first
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCompositionTriangle_second
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCompositionTriangle_third
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCone_d
#print axioms AAT.AG.AtlasCoefficientFiber.fiberCone_d
#print axioms AAT.AG.AtlasCoefficientFiber.totalCone_d
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCone_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.fiberCone_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.totalCone_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCone_finiteDimensional
#print axioms AAT.AG.AtlasCoefficientFiber.fiberCone_finiteDimensional
#print axioms AAT.AG.AtlasCoefficientFiber.totalCone_finiteDimensional
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
