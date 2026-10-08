import ResearchLean.AG.AtlasCoefficientFiber.LawSupportProjection
import ResearchLean.AG.AtlasCoefficientFiber.SupportFiber

/-!
# G-135 D：原Lawの混在適合とliteral Rの部分台値

## Implementation notes

原Lawのラベルを保持した単一成分包含と、原Phi cochain制限を対にする。
R射は既存literal核への直接Phi制限から生成し、Q座標由来の射と全元で照合する。
RをQから定義して支持自然性を自明化する案はこの照合義務を失うため採らない。
-/
noncomputable section
open scoped Classical
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision AtlasDefectComposition
open HomologicalComplex
universe u
variable {Source : Type u} [finiteSource : Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
variable (l : LawValueLabel laws) {A : Set qc.Target}
variable (hA : A ⊆ labelValueFiber laws qc ha l)
omit finiteSource

/-- 原A混在閉路を同じ原Lawラベル成分へ含める。 -/
def lawSupportMixedInsert : mixedCycles M A →ₗ[ℚ]
    ((j : LawValueLabel laws) → mixedCycles M (labelValueFiber laws qc ha j)) :=
  (LinearMap.single ℚ _ l).comp (supportMixedCyclesInclude M hA)

/-- 原Law混在閉路包含の全ラベル値。 -/
theorem lawSupportMixedInsert_apply (x : mixedCycles M A) :
    lawSupportMixedInsert M laws ha l hA x = Pi.single l (supportMixedCyclesInclude M hA x) := rfl

/-- 原A全Phi H₁を同じ原Lawラベル成分へ含める。 -/
def lawSupportPhiHomologyInsert :
    ((c : Nc.ChartInTargetSubset A) → PhiHomology M A c) →ₗ[ℚ]
      ((j : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc ha j)) →
        PhiHomology M (labelValueFiber laws qc ha j) c) :=
  (LinearMap.single ℚ _ l).comp (supportAllPhiHomology M hA)

/-- 原Law全Phi H₁包含の全ラベル値。 -/
theorem lawSupportPhiHomologyInsert_apply
    (x : (c : Nc.ChartInTargetSubset A) → PhiHomology M A c) :
    lawSupportPhiHomologyInsert M laws ha l hA x = Pi.single l (supportAllPhiHomology M hA x) := rfl

/-- 原Law κの全ラベル写像は同じ原A κと全混在閉路で可換。 -/
theorem lawSupportKappa :
    (lawKappa M laws ha).comp (lawSupportMixedInsert M laws ha l hA) =
      (lawSupportPhiHomologyInsert M laws ha l hA).comp (kappa M A) := by
  apply LinearMap.ext
  intro x
  funext j
  change lawKappa M laws ha (lawSupportMixedInsert M laws ha l hA x) j =
    lawSupportPhiHomologyInsert M laws ha l hA (kappa M A x) j
  rw [lawKappa_apply, lawSupportMixedInsert_apply, lawSupportPhiHomologyInsert_apply]
  by_cases hj : j = l
  · subst j
    rw [Pi.single_eq_same, Pi.single_eq_same, supportKappa]
  · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]

/-- 原Law全Phi H¹の同じラベル値を原A台へ制限する。 -/
def lawSupportPhiH1 :
    ((j : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc ha j)) →
      (phiComplex M (labelValueFiber laws qc ha j) c).H1) →ₗ[ℚ]
        ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) :=
  (supportAllPhiH1 M hA).comp (LinearMap.proj l)

/-- 原Law Phi台射の全値は同じ原Phi cochain制限。 -/
theorem lawSupportPhiH1_apply
    (x : (j : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc ha j)) →
      (phiComplex M (labelValueFiber laws qc ha j) c).H1) :
    lawSupportPhiH1 M laws ha l hA x = supportAllPhiH1 M hA (x l) := rfl

/-- 原Law κ*と原Phi台制限は同じ混在閉路への評価で可換。 -/
theorem lawSupportKappaStar
    (z : (j : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc ha j)) →
      (phiComplex M (labelValueFiber laws qc ha j) c).H1) (x : mixedCycles M A) :
    kappaStar M A (lawSupportPhiH1 M laws ha l hA z) x =
      lawKappaStar M laws ha z l (supportMixedCyclesInclude M hA x) := by
  rw [lawSupportPhiH1_apply, lawKappaStar_apply, supportKappaStar]

/-- literal原Law Rを同じ直接Phi制限で原Aのliteral Rへ送る。 -/
def lawSupportR : lawR M laws ha →ₗ[ℚ] R M A :=
  (supportFiberR M hA).comp ((LinearMap.proj l).comp (lawRFamilyEquiv M laws ha).toLinearMap)

/-- 原Law R台射の全値は同じ原ラベルRの直接制限。 -/
theorem lawSupportR_apply (z : lawR M laws ha) :
    lawSupportR M laws ha l hA z = supportFiberR M hA (lawRFamilyEquiv M laws ha z l) := rfl

/-- literal原Law R台射の原Phi値は同じ直接cochain H¹制限。 -/
theorem lawSupportR_val (z : lawR M laws ha) :
    (lawSupportR M laws ha l hA z).1 = lawSupportPhiH1 M laws ha l hA z.1 := by
  rw [lawSupportR_apply, supportFiberR_val, lawRFamilyEquiv_val, lawSupportPhiH1_apply]

include finiteSource

/-- 原Law Q-H¹-Rの両方向座標は同じ直接Phi R台射と可換。 -/
theorem lawSupportR_viaQ (z : (zeroExtension (lawRestrictionComplex M laws ha)).homology (1 : ℤ)) :
    lawSupportR M laws ha l hA (lawRestrictionHomologyREquiv M laws ha z) =
      restrictionStandardHomologyREquiv M A (homologyMap (lawSupportQ M laws ha l hA) 1 z) := by
  rw [lawSupportR_apply, lawRestrictionHomologyREquiv_component,
    supportFiberR_eq_supportRRestriction, supportRRestriction_viaQ,
    lawRestrictionHomologyEquiv_component, lawSupportQ_projection,
    homologyMap_comp, ModuleCat.comp_apply]
  rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportMixedInsert
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportMixedInsert_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportPhiHomologyInsert
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportPhiHomologyInsert_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportKappa
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportPhiH1
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportPhiH1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportKappaStar
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportR
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportR_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportR_val
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportR_viaQ
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
