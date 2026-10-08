import ResearchLean.AG.AtlasCoefficientFiber.LawSupportFamilies

/-!
# G-135 D：原Law適合写像の全部分台族

## Implementation notes

全ラベル混在閉路の同じprimitive包含と、原Phi H₁包含・H¹制限を集める。
全κ・全κ*の実写像等号から、literal R族射の直接Phi値を照合する。
ラベル別自然性を追加入力として受け取らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
variable {A : LawValueLabel laws → Set qc.Target}
variable (hA : ∀ l, A l ⊆ labelValueFiber laws qc ha l)

/-- 原部分台族の混在閉路を同じ元Lawラベル族へ含める。 -/
def lawSupportFamilyMixed :
    ((l : LawValueLabel laws) → mixedCycles M (A l)) →ₗ[ℚ]
      ((l : LawValueLabel laws) → mixedCycles M (labelValueFiber laws qc ha l)) :=
  FiniteLinearFamily.map (fun l => supportMixedCyclesInclude M (hA l))
/-- 全族混在閉路包含の同じ原ラベル値。 -/
theorem lawSupportFamilyMixed_apply (x : (l : LawValueLabel laws) → mixedCycles M (A l))
    (l : LawValueLabel laws) :
    lawSupportFamilyMixed M laws ha hA x l = supportMixedCyclesInclude M (hA l) (x l) := rfl

/-- 原部分台族の全Phi H₁を同じ原Lawラベル族へ含める。 -/
def lawSupportFamilyPhiHomology :
    ((l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (A l)) → PhiHomology M (A l) c) →ₗ[ℚ]
      ((l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc ha l)) →
        PhiHomology M (labelValueFiber laws qc ha l) c) :=
  LinearMap.pi (fun l => (supportAllPhiHomology M (hA l)).comp (LinearMap.proj l))
/-- 全族Phi H₁包含の同じ原ラベル値。 -/
theorem lawSupportFamilyPhiHomology_apply
    (x : (l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (A l)) → PhiHomology M (A l) c)
    (l : LawValueLabel laws) :
    lawSupportFamilyPhiHomology M laws ha hA x l = supportAllPhiHomology M (hA l) (x l) := rfl

/-- 各原部分台のprimitiveκを同じラベル族へ集める。 -/
def supportFamilyKappa : ((l : LawValueLabel laws) → mixedCycles M (A l)) →ₗ[ℚ]
    ((l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (A l)) → PhiHomology M (A l) c) :=
  LinearMap.pi (fun l => (kappa M (A l)).comp (LinearMap.proj l))
/-- 原部分台κ族の同じラベル値。 -/
theorem supportFamilyKappa_apply (x : (l : LawValueLabel laws) → mixedCycles M (A l))
    (l : LawValueLabel laws) : supportFamilyKappa M laws (A := A) x l = kappa M (A l) (x l) := rfl

/-- 同じ原Law κの全写像等号はprimitive部分台族κと可換。 -/
theorem lawSupportFamilyKappa :
    (lawKappa M laws ha).comp (lawSupportFamilyMixed M laws ha hA) =
      (lawSupportFamilyPhiHomology M laws ha hA).comp (supportFamilyKappa M laws (A := A)) := by
  apply LinearMap.ext
  intro x
  funext l
  simp only [LinearMap.comp_apply, lawKappa_apply, lawSupportFamilyMixed_apply,
    lawSupportFamilyPhiHomology_apply, supportFamilyKappa_apply]
  exact (supportKappa M (hA l) (x l)).symm

/-- 同じ原Law全Phi H¹を原部分台族へ直接cochain制限する。 -/
def lawSupportFamilyPhiH1 :
    ((l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc ha l)) →
      (phiComplex M (labelValueFiber laws qc ha l) c).H1) →ₗ[ℚ]
        ((l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (A l)) → (phiComplex M (A l) c).H1) :=
  FiniteLinearFamily.map (fun l => supportAllPhiH1 M (hA l))
/-- 全族Phi H¹制限の同じ原ラベル値。 -/
theorem lawSupportFamilyPhiH1_apply
    (z : (l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc ha l)) →
      (phiComplex M (labelValueFiber laws qc ha l) c).H1) (l : LawValueLabel laws) :
    lawSupportFamilyPhiH1 M laws ha hA z l = supportAllPhiH1 M (hA l) (z l) := rfl

/-- 全族κ*は同じprimitive混在閉路包含の双対と実写像全体で可換。 -/
theorem lawSupportFamilyKappaStar :
    (FiniteLinearFamily.map (fun l => kappaStar M (A l))).comp
      (lawSupportFamilyPhiH1 M laws ha hA) =
    (FiniteLinearFamily.map (fun l => (supportMixedCyclesInclude M (hA l)).dualMap)).comp
      (lawKappaStar M laws ha) := by
  apply LinearMap.ext
  intro z
  funext l
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, FiniteLinearFamily.map_apply,
    lawSupportFamilyPhiH1_apply, LinearMap.dualMap_apply, lawKappaStar_apply]
  exact supportKappaStar M (hA l) (z l) x

/-- literal原Law R族射の全Phi値は同じ直接cochain制限族。 -/
theorem lawSupportFamilyR_val (z : lawR M laws ha) :
    (fun l => (lawSupportFamilyR M laws ha hA z l).1) = lawSupportFamilyPhiH1 M laws ha hA z.1 := by
  funext l
  rw [lawSupportFamilyR_apply, lawSupportR_val, lawSupportPhiH1_apply, lawSupportFamilyPhiH1_apply]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyMixed
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyMixed_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyPhiHomology
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyPhiHomology_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportFamilyKappa
#print axioms AAT.AG.AtlasCoefficientFiber.supportFamilyKappa_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyKappa
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyPhiH1
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyPhiH1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyKappaStar
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyR_val
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyMixed.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyPhiH1.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyPhiHomology.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportAllPhiH1.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportAllPhiHomology.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportMixedCyclesInclude.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
