import ResearchLean.AG.AtlasCoefficientFiber.LawSupportConeFamilies
import ResearchLean.AG.AtlasCoefficientFiber.LawSupportFamilyHomology
import ResearchLean.AG.AtlasCoefficientFiber.LawSupportEmpty

/-!
# G-135 D：原Law部分台錐族の全次数shiftと連結射

## Implementation notes

元native錐射の各射影から、同じ全族射のshift負号と標準homology値を読む。
Q評価、literal R、tauは元Law短完全列の同じdeltaへ接続する。
H¹だけから全整数次数の自然性を推定する経路を使わない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CochainComplex HomologicalComplex
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
variable {A : LawValueLabel laws → Set qc.Target}
variable (hA : ∀ l, A l ⊆ labelValueFiber laws qc ha l)

/-- 元Law第三triangle射は同じ標準shiftの下で全次数の原部分台族値を保つ。 -/
theorem lawSupportConeFamilyTriangle_third (n : ℤ) (z : (lawFiberCone M laws ha).X n) :
    (lawSupportCoefficientConeFamily M laws ha hA).f (n+1)
      (((lawCoefficientCone M laws ha).shiftFunctorObjXIso 1 n (n+1) rfl).hom
        ((lawCoefficientCompositionTriangle M laws ha).mor₃.f n z)) =
    fun l => ((coefficientCone M (A l)).shiftFunctorObjXIso 1 n (n+1) rfl).hom
      ((coefficientCompositionTriangle M (A l)).mor₃.f n
        ((lawSupportFiberConeFamily M laws ha hA).f n z l)) := by
  funext l
  rw [lawSupportCoefficientConeFamily_value, lawSupportFiberConeFamily_value]
  have hh := congrArg (fun f => ((coefficientCone M (A l)).shiftFunctorObjXIso 1 n (n+1) rfl).hom
    (f.f n z)) (lawSupportConeTriangle_third M laws ha l (hA l))
  change ((coefficientCone M (A l)).shiftFunctorObjXIso 1 n (n+1) rfl).hom
    (((lawSupportCoefficientCone M laws ha l (hA l))⟦(1 : ℤ)⟧').f n
      ((lawCoefficientCompositionTriangle M laws ha).mor₃.f n z)) =
    ((coefficientCone M (A l)).shiftFunctorObjXIso 1 n (n+1) rfl).hom
      ((coefficientCompositionTriangle M (A l)).mor₃.f n
        ((lawSupportFiberCone M laws ha l (hA l)).f n z)) at hh
  rw [lawSupportConeShift_apply] at hh
  exact hh

/-- 同じ全族fiber錐射の標準homologyを原部分台の全錐homologyへ読む。 -/
def lawSupportFiberConeFamilyHomology (n : ℤ) : (lawFiberCone M laws ha).homology n →ₗ[ℚ]
    ((l : LawValueLabel laws) → (fiberCone M (A l)).homology n) :=
  (FiniteComplexFamily.homologyEquiv _ n).toLinearMap.comp
    (homologyMap (lawSupportFiberConeFamily M laws ha hA) n).hom
/-- 全族fiber錐標準homology射の各値は同じnative部分台錐射。 -/
theorem lawSupportFiberConeFamilyHomology_apply (n : ℤ) (z : (lawFiberCone M laws ha).homology n)
    (l : LawValueLabel laws) : lawSupportFiberConeFamilyHomology M laws ha hA n z l =
    homologyMap (lawSupportFiberCone M laws ha l (hA l)) n z := by
  change FiniteComplexFamily.homologyEquiv _ n
    (homologyMap (lawSupportFiberConeFamily M laws ha hA) n z) l = _
  rw [FiniteComplexFamily.homologyEquiv_component]
  have hh := congrArg (fun f => homologyMap f n) (lawSupportFiberConeFamily_projection M laws ha hA l)
  dsimp only at hh
  rw [homologyMap_comp] at hh
  exact congrArg (fun f => f z) hh

/-- 元Law Q評価は同じnative全族Q評価の標準homologyと全次数で可換。 -/
theorem lawSupportFiberConeFamilyDesc_homology (n : ℤ) (z : (lawFiberCone M laws ha).homology n) :
    homologyMap (lawSupportFamilyQ M laws ha hA) n (lawFiberConeHomologyEquiv M laws ha n z) =
    homologyMap (FiniteComplexFamily.map _ _ (fun l => fiberConeDesc M (A l))) n
      (homologyMap (lawSupportFiberConeFamily M laws ha hA) n z) := by
  rw [lawFiberConeHomologyEquiv_apply]
  have hh := congrArg (fun f => homologyMap f n) (lawSupportFiberConeFamilyDesc M laws ha hA)
  dsimp only at hh
  rw [homologyMap_comp, homologyMap_comp] at hh
  exact congrArg (fun f => f z) hh

/-- 元Law Q評価の全原部分台族homology値は同じ各Q両方向同型。 -/
theorem lawSupportFiberConeFamilyQ (n : ℤ) (z : (lawFiberCone M laws ha).homology n) :
    lawSupportFamilyQHomology M laws ha hA n (lawFiberConeHomologyEquiv M laws ha n z) =
      fun l => fiberConeHomologyEquiv M (A l) n (lawSupportFiberConeFamilyHomology M laws ha hA n z l) := by
  funext l
  rw [lawSupportFamilyQHomology_apply, lawSupportFiberConeFamilyHomology_apply]
  exact lawSupportFiberConeHomologyEquiv M laws ha l (hA l) n z

/-- 原Law錐のliteral R両方向同型は同じ直接Phi R台制限族と可換。 -/
theorem lawSupportFiberConeFamilyR (z : (lawFiberCone M laws ha).homology (1 : ℤ)) :
    lawSupportFamilyR M laws ha hA (lawFiberConeH1REquiv M laws ha z) =
      fun l => fiberConeH1REquiv M (A l) (lawSupportFiberConeFamilyHomology M laws ha hA 1 z l) := by
  funext l
  rw [lawSupportFamilyR_apply, lawFiberConeH1REquiv_apply, lawSupportR_viaQ,
    lawSupportFiberConeHomologyEquiv, fiberConeH1REquiv_apply, lawSupportFiberConeFamilyHomology_apply]

/-- 原Law錐標準連結射は同じ全原部分台族の連結射と全整数次数で可換。 -/
theorem lawSupportFiberConeFamilyConnecting (n : ℤ) (z : (lawFiberCone M laws ha).homology n) :
    lawSupportFamilyPHomology M laws ha hA (n+1)
      (coneConnecting (zeroExtensionMap (lawEvaluationHom M laws ha)) n z) =
      fun l => coneConnecting (zeroExtensionMap (evaluationHom M (A l))) n
        (lawSupportFiberConeFamilyHomology M laws ha hA n z l) := by
  funext l
  rw [lawSupportFamilyPHomology_apply, lawSupportFiberConeFamilyHomology_apply]
  exact lawSupportFiberConeConnecting M laws ha l (hA l) n z

variable [IsEmpty laws.Law]

/-- 空Lawの同じ原coefficient錐は全整数次数で零対象。 -/
theorem lawSupportEmptyCoefficientCone (n : ℤ) : IsZero ((lawCoefficientCone M laws ha).X n) := by
  letI := lawSupportEmptyP M laws ha n
  letI := lawSupportEmptyCoarse (Nc := Nc) laws ha (n+1)
  exact (mappingCone.isZero_X_iff _ n).mpr
    ⟨ModuleCat.isZero_of_subsingleton _, ModuleCat.isZero_of_subsingleton _⟩
/-- 空Lawの同じ原fiber錐は全整数次数で零対象。 -/
theorem lawSupportEmptyFiberCone (n : ℤ) : IsZero ((lawFiberCone M laws ha).X n) := by
  letI := lawSupportEmptyFine (Nf := Nf) (h := h) laws ha n
  letI := lawSupportEmptyP M laws ha (n+1)
  exact (mappingCone.isZero_X_iff _ n).mpr
    ⟨ModuleCat.isZero_of_subsingleton _, ModuleCat.isZero_of_subsingleton _⟩
/-- 空Lawの独立生成原total錐も全整数次数で零対象。 -/
theorem lawSupportEmptyTotalCone (n : ℤ) : IsZero ((lawTotalCone M laws ha).X n) := by
  letI := lawSupportEmptyFine (Nf := Nf) (h := h) laws ha n
  letI := lawSupportEmptyCoarse (Nc := Nc) laws ha (n+1)
  exact (mappingCone.isZero_X_iff _ n).mpr
    ⟨ModuleCat.isZero_of_subsingleton _, ModuleCat.isZero_of_subsingleton _⟩

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportConeFamilyTriangle_third
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamilyHomology
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamilyHomology_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamilyDesc_homology
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamilyQ
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamilyR
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamilyConnecting
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportEmptyCoefficientCone
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportEmptyFiberCone
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportEmptyTotalCone
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
