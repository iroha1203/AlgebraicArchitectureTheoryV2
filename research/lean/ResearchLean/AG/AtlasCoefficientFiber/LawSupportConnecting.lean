import ResearchLean.AG.AtlasCoefficientFiber.LawSupportFiber

/-!
# G-135 D：同じ原Law SESの連結射と部分台

## Implementation notes

生成済み実Law SES射へnative delta_naturalityを適用し、原Q-R両方向座標でtauへ戻す。
H¹だけの可換式から全次数の連結射を推測する経路は採らない。
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

/-- 実Law標準deltaは全整数次数・全元で同じ原Aへの射と可換。 -/
theorem lawSupport_delta (n : ℤ)
    (z : (zeroExtension (lawRestrictionComplex M laws ha)).homology n) :
    homologyMap (lawSupportP M laws ha l hA) (n+1)
      ((lawEvaluationRestriction_shortExact M laws ha).δ n (n+1) rfl z) =
    (evaluationRestriction_shortExact M A).δ n (n+1) rfl
      (homologyMap (lawSupportQ M laws ha l hA) n z) :=
  congrArg (fun f => f z) (HomologicalComplex.HomologySequence.δ_naturality
    (lawSupportMorphism M laws ha l hA) (lawEvaluationRestriction_shortExact M laws ha)
    (evaluationRestriction_shortExact M A) n (n+1) rfl)

/-- literal原Law Rの同じtauは原Aのtauと全R元で可換。 -/
theorem lawSupport_tau (z : lawR M laws ha) :
    homologyMap (lawSupportP M laws ha l hA) (2 : ℤ) (lawConnectingTau M laws ha z) =
      connectingTau M A (lawSupportR M laws ha l hA z) := by
  have hr := lawSupportR_viaQ M laws ha l hA ((lawRestrictionHomologyREquiv M laws ha).symm z)
  rw [LinearEquiv.apply_symm_apply] at hr
  rw [lawConnectingTau_apply, connectingTau_apply, hr, LinearEquiv.symm_apply_apply]
  exact lawSupport_delta M laws ha l hA 1 ((lawRestrictionHomologyREquiv M laws ha).symm z)

/-- 同じ原Law五項列のH¹Pから細H¹への射は原A射と可換。 -/
theorem lawSupportEvaluationH1 (z : (zeroExtension (lawPushforwardComplex M laws ha)).homology (1 : ℤ)) :
    homologyMap (lawSupportFine M laws ha l hA) 1 (lawEvaluationH1 M laws ha z) =
      evaluationH1 M A (homologyMap (lawSupportP M laws ha l hA) 1 z) := by
  rw [lawEvaluationH1_apply, evaluationH1_apply]
  have hh := congrArg (fun f => homologyMap f (1 : ℤ)) (lawSupportEvaluation M laws ha l hA)
  dsimp only at hh
  rw [homologyMap_comp, homologyMap_comp] at hh
  exact congrArg (fun f => f z) hh

/-- 同じ原Law五項列の細H¹からliteral Rへの射は直接Phi制限と可換。 -/
theorem lawSupportFiberRestrictionH1
    (z : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ)) :
    lawSupportR M laws ha l hA (lawFiberRestrictionH1 M laws ha z) =
      fiberRestrictionH1 M A (homologyMap (lawSupportFine M laws ha l hA) 1 z) := by
  rw [lawFiberRestrictionH1_apply, lawSupportR_viaQ, fiberRestrictionH1_apply]
  have hh := congrArg (fun f => homologyMap f (1 : ℤ)) (lawSupportRestriction M laws ha l hA)
  dsimp only at hh
  rw [homologyMap_comp, homologyMap_comp] at hh
  exact congrArg (restrictionStandardHomologyREquiv M A) (congrArg (fun f => f z) hh)

/-- 同じ原Law五項列のH²Pから細H²への射も原A射と可換。 -/
theorem lawSupportEvaluationH2 (z : (zeroExtension (lawPushforwardComplex M laws ha)).homology (2 : ℤ)) :
    homologyMap (lawSupportFine M laws ha l hA) 2 (lawEvaluationH2 M laws ha z) =
      evaluationH2 M A (homologyMap (lawSupportP M laws ha l hA) 2 z) := by
  rw [lawEvaluationH2_eq_standard, evaluationH2_apply]
  have hh := congrArg (fun f => homologyMap f (2 : ℤ)) (lawSupportEvaluation M laws ha l hA)
  dsimp only at hh
  rw [homologyMap_comp, homologyMap_comp] at hh
  exact congrArg (fun f => f z) hh

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupport_delta
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupport_tau
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportEvaluationH1
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberRestrictionH1
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportEvaluationH2
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
