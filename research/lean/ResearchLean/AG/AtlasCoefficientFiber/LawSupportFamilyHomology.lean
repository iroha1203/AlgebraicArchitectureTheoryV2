import ResearchLean.AG.AtlasCoefficientFiber.LawSupportFamilies

/-!
# G-135 D：原Law部分台族のnative homologyとliteral R

## Implementation notes

全族の実射を標準homologyへ送り、元射影から成分値を照合する。
原R族からのtauも同じ実族SESのdeltaと原Q両方向同型で生成する。
成分rank和や供給された自然性を全族射の代わりに使わない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory HomologicalComplex CanonicalResolution ResolutionInvariance
open FaceRelationSubdivision AtlasDefectComposition
universe u
/-- 原短完全列族のnative deltaは全整数次数で同じ各成分deltaとなる。 -/
theorem coefficientShortComplexFamily_delta_component {J : Type u} [Fintype J]
    (S : J → ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ))
    (hs : ∀ j, (S j).ShortExact) (n : ℤ)
    (z : (coefficientShortComplexFamily S).X₃.homology n) (j : J) :
    FiniteComplexFamily.homologyEquiv (fun j => (S j).X₁) (n+1)
      ((coefficientShortComplexFamily_shortExact S hs).δ n (n+1) rfl z) j =
    (hs j).δ n (n+1) rfl
      (FiniteComplexFamily.homologyEquiv (fun j => (S j).X₃) n z j) := by
  rw [FiniteComplexFamily.homologyEquiv_component, FiniteComplexFamily.homologyEquiv_component]
  have hh := congrArg (fun f => f z) (HomologicalComplex.HomologySequence.δ_naturality
    (coefficientShortComplexFamily_projection S j) (coefficientShortComplexFamily_shortExact S hs)
    (hs j) n (n+1) rfl)
  dsimp only at hh
  rw [coefficientShortComplexFamily_projection_τ1, coefficientShortComplexFamily_projection_τ3] at hh
  exact hh

variable {Source : Type u} [Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
variable {A : LawValueLabel laws → Set qc.Target}
variable (hA : ∀ l, A l ⊆ labelValueFiber laws qc ha l)

/-- 全族P射の標準homologyを同じ各原部分台homologyへ読む。 -/
def lawSupportFamilyPHomology (n : ℤ) :
    (zeroExtension (lawPushforwardComplex M laws ha)).homology n →ₗ[ℚ]
      ((l : LawValueLabel laws) → (zeroExtension (pushforwardComplex M (A l))).homology n) :=
  (FiniteComplexFamily.homologyEquiv _ n).toLinearMap.comp
    (homologyMap (lawSupportFamilyP M laws ha hA) n).hom

/-- 全族P標準homology射の各値は同じ実部分台射。 -/
theorem lawSupportFamilyPHomology_apply (n : ℤ)
    (z : (zeroExtension (lawPushforwardComplex M laws ha)).homology n) (l : LawValueLabel laws) :
    lawSupportFamilyPHomology M laws ha hA n z l = homologyMap (lawSupportP M laws ha l (hA l)) n z := by
  change FiniteComplexFamily.homologyEquiv _ n
    (homologyMap (lawSupportFamilyP M laws ha hA) n z) l = _
  rw [FiniteComplexFamily.homologyEquiv_component]
  have hh := congrArg (fun f => homologyMap f n) (lawSupportFamilyP_projection M laws ha hA l)
  dsimp only at hh
  rw [homologyMap_comp] at hh
  exact congrArg (fun f => f z) hh

/-- 全族Fine射の標準homologyを同じ各原部分台homologyへ読む。 -/
def lawSupportFamilyFineHomology (n : ℤ) :
    (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology n →ₗ[ℚ]
      ((l : LawValueLabel laws) → (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A l))).homology n) :=
  (FiniteComplexFamily.homologyEquiv _ n).toLinearMap.comp
    (homologyMap (lawSupportFamilyFine M laws ha hA) n).hom

/-- 全族Fine標準homology射の各値は同じ実部分台射。 -/
theorem lawSupportFamilyFineHomology_apply (n : ℤ)
    (z : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology n) (l : LawValueLabel laws) :
    lawSupportFamilyFineHomology M laws ha hA n z l = homologyMap (lawSupportFine M laws ha l (hA l)) n z := by
  change FiniteComplexFamily.homologyEquiv _ n
    (homologyMap (lawSupportFamilyFine M laws ha hA) n z) l = _
  rw [FiniteComplexFamily.homologyEquiv_component]
  have hh := congrArg (fun f => homologyMap f n) (lawSupportFamilyFine_projection M laws ha hA l)
  dsimp only at hh
  rw [homologyMap_comp] at hh
  exact congrArg (fun f => f z) hh

/-- 全族Q射の標準homologyを同じ各原部分台homologyへ読む。 -/
def lawSupportFamilyQHomology (n : ℤ) :
    (zeroExtension (lawRestrictionComplex M laws ha)).homology n →ₗ[ℚ]
      ((l : LawValueLabel laws) → (zeroExtension (restrictionComplex M (A l))).homology n) :=
  (FiniteComplexFamily.homologyEquiv _ n).toLinearMap.comp
    (homologyMap (lawSupportFamilyQ M laws ha hA) n).hom

/-- 全族Q標準homology射の各値は同じ実部分台射。 -/
theorem lawSupportFamilyQHomology_apply (n : ℤ)
    (z : (zeroExtension (lawRestrictionComplex M laws ha)).homology n) (l : LawValueLabel laws) :
    lawSupportFamilyQHomology M laws ha hA n z l = homologyMap (lawSupportQ M laws ha l (hA l)) n z := by
  change FiniteComplexFamily.homologyEquiv _ n
    (homologyMap (lawSupportFamilyQ M laws ha hA) n z) l = _
  rw [FiniteComplexFamily.homologyEquiv_component]
  have hh := congrArg (fun f => homologyMap f n) (lawSupportFamilyQ_projection M laws ha hA l)
  dsimp only at hh
  rw [homologyMap_comp] at hh
  exact congrArg (fun f => f z) hh

/-- 全族Coarse射の標準homologyを同じ各原部分台homologyへ読む。 -/
def lawSupportFamilyCoarseHomology (n : ℤ) :
    (zeroExtension (Nc.lawGeneratedComplex laws ha)).homology n →ₗ[ℚ]
      ((l : LawValueLabel laws) → (zeroExtension (Nc.targetSubsetComplex (A l))).homology n) :=
  (FiniteComplexFamily.homologyEquiv _ n).toLinearMap.comp
    (homologyMap (lawSupportFamilyCoarse (Nc := Nc) laws ha hA) n).hom

/-- 全族Coarse標準homology射の各値は同じ実部分台射。 -/
theorem lawSupportFamilyCoarseHomology_apply (n : ℤ)
    (z : (zeroExtension (Nc.lawGeneratedComplex laws ha)).homology n) (l : LawValueLabel laws) :
    lawSupportFamilyCoarseHomology (Nc := Nc) laws ha hA n z l = homologyMap (lawSupportCoarse (Nc := Nc) laws ha l (hA l)) n z := by
  change FiniteComplexFamily.homologyEquiv _ n
    (homologyMap (lawSupportFamilyCoarse (Nc := Nc) laws ha hA) n z) l = _
  rw [FiniteComplexFamily.homologyEquiv_component]
  have hh := congrArg (fun f => homologyMap f n) (lawSupportFamilyCoarse_projection (Nc := Nc) laws ha hA l)
  dsimp only at hh
  rw [homologyMap_comp] at hh
  exact congrArg (fun f => f z) hh

/-- 原Q部分台族のnative H¹を同じliteral R族へ両方向に読む。 -/
def supportFamilyQREquiv :
    (FiniteComplexFamily.complex (fun l => zeroExtension (restrictionComplex M (A l)))).homology (1 : ℤ) ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → R M (A l)) :=
  (FiniteComplexFamily.homologyEquiv _ 1).trans
    (LinearEquiv.piCongrRight (fun l => restrictionStandardHomologyREquiv M (A l)))

/-- 同じR族座標の全値は元Qの標準H¹座標。 -/
theorem supportFamilyQREquiv_apply
    (z : (FiniteComplexFamily.complex (fun l => zeroExtension (restrictionComplex M (A l)))).homology (1 : ℤ))
    (l : LawValueLabel laws) :
    supportFamilyQREquiv M laws (A := A) z l = restrictionStandardHomologyREquiv M (A l)
      (FiniteComplexFamily.homologyEquiv _ 1 z l) := rfl

/-- 元R族からQへ戻る両方向座標も同じ各ラベルのQ逆座標。 -/
theorem supportFamilyQREquiv_symm_component (z : (l : LawValueLabel laws) → R M (A l))
    (l : LawValueLabel laws) :
    FiniteComplexFamily.homologyEquiv _ 1 ((supportFamilyQREquiv M laws (A := A)).symm z) l =
      (restrictionStandardHomologyREquiv M (A l)).symm (z l) := by
  apply (restrictionStandardHomologyREquiv M (A l)).injective
  rw [← supportFamilyQREquiv_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- 原Law直接Phi R族制限は同じnative Q族射の両方向座標と一致。 -/
theorem lawSupportFamilyR_viaQ
    (z : (zeroExtension (lawRestrictionComplex M laws ha)).homology (1 : ℤ)) :
    lawSupportFamilyR M laws ha hA (lawRestrictionHomologyREquiv M laws ha z) =
      supportFamilyQREquiv M laws (A := A) (homologyMap (lawSupportFamilyQ M laws ha hA) 1 z) := by
  funext l
  rw [lawSupportFamilyR_apply, lawSupportR_viaQ, supportFamilyQREquiv_apply,
    FiniteComplexFamily.homologyEquiv_component]
  have hh := congrArg (fun f => homologyMap f (1 : ℤ)) (lawSupportFamilyQ_projection M laws ha hA l)
  dsimp only at hh
  rw [homologyMap_comp] at hh
  exact congrArg (restrictionStandardHomologyREquiv M (A l)) (congrArg (fun f => f z) hh).symm

/-- 原部分台literal R族から同じ実族SES deltaで作るtau。 -/
def supportFamilyTau : ((l : LawValueLabel laws) → R M (A l)) →ₗ[ℚ]
    (FiniteComplexFamily.complex (fun l => zeroExtension (pushforwardComplex M (A l)))).homology (2 : ℤ) :=
  ((lawSupportFamily_shortExact M (A := A)).δ 1 2 rfl).hom.comp
    (supportFamilyQREquiv M laws (A := A)).symm.toLinearMap

/-- 原部分台族tauの全値は同じnative deltaの可逆Q座標。 -/
theorem supportFamilyTau_apply (z : (l : LawValueLabel laws) → R M (A l)) :
    supportFamilyTau M laws (A := A) z = (lawSupportFamily_shortExact M (A := A)).δ 1 2 rfl
      ((supportFamilyQREquiv M laws (A := A)).symm z) := rfl

/-- 元部分台族のnative tauは全R族・全ラベルで同じ元tauになる。 -/
theorem supportFamilyTau_component (z : (l : LawValueLabel laws) → R M (A l))
    (l : LawValueLabel laws) :
    FiniteComplexFamily.homologyEquiv _ 2 (supportFamilyTau M laws (A := A) z) l =
      connectingTau M (A l) (z l) := by
  rw [supportFamilyTau_apply, connectingTau_apply]
  have hh := coefficientShortComplexFamily_delta_component
    (fun l => evaluationRestrictionShortComplex M (A l))
    (fun l => evaluationRestriction_shortExact M (A l)) 1
    ((supportFamilyQREquiv M laws (A := A)).symm z) l
  have hh' : FiniteComplexFamily.homologyEquiv
      (fun j => zeroExtension (pushforwardComplex M (A j))) 2
      ((lawSupportFamily_shortExact M (A := A)).δ 1 2 rfl
        ((supportFamilyQREquiv M laws (A := A)).symm z)) l =
    (evaluationRestriction_shortExact M (A l)).δ 1 2 rfl
      (FiniteComplexFamily.homologyEquiv
        (fun j => zeroExtension (restrictionComplex M (A j))) 1
        ((supportFamilyQREquiv M laws (A := A)).symm z) l) := hh
  rw [supportFamilyQREquiv_symm_component] at hh'
  exact hh'

/-- 原Law tauと直接Phi R族射は同じnative全族SESのtauと可換。 -/
theorem lawSupportFamily_tau_native (z : lawR M laws ha) :
    homologyMap (lawSupportFamilyP M laws ha hA) (2 : ℤ) (lawConnectingTau M laws ha z) =
      supportFamilyTau M laws (A := A) (lawSupportFamilyR M laws ha hA z) := by
  have hr := lawSupportFamilyR_viaQ M laws ha hA ((lawRestrictionHomologyREquiv M laws ha).symm z)
  rw [LinearEquiv.apply_symm_apply] at hr
  rw [lawConnectingTau_apply, supportFamilyTau_apply, hr, LinearEquiv.symm_apply_apply]
  exact lawSupportFamily_delta M laws ha hA 1 ((lawRestrictionHomologyREquiv M laws ha).symm z)

/-- 同じ原Law tauの全部分台族値。 -/
theorem lawSupportFamily_tau (z : lawR M laws ha) :
    lawSupportFamilyPHomology M laws ha hA 2 (lawConnectingTau M laws ha z) =
      fun l => connectingTau M (A l) (lawSupportFamilyR M laws ha hA z l) := by
  funext l
  rw [lawSupportFamilyPHomology_apply, lawSupportFamilyR_apply]
  exact lawSupport_tau M laws ha l (hA l) z

/-- 原五項列のH¹Pから細H¹への射を全族で保持。 -/
theorem lawSupportFamilyEvaluationH1
    (z : (zeroExtension (lawPushforwardComplex M laws ha)).homology (1 : ℤ)) :
    lawSupportFamilyFineHomology M laws ha hA 1 (lawEvaluationH1 M laws ha z) =
      fun l => evaluationH1 M (A l) (lawSupportFamilyPHomology M laws ha hA 1 z l) := by
  funext l
  rw [lawSupportFamilyFineHomology_apply, lawSupportFamilyPHomology_apply]
  exact lawSupportEvaluationH1 M laws ha l (hA l) z
/-- 原五項列の細H¹からliteral Rへの射を直接Phi制限の全族で保持。 -/
theorem lawSupportFamilyFiberRestrictionH1
    (z : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ)) :
    lawSupportFamilyR M laws ha hA (lawFiberRestrictionH1 M laws ha z) =
      fun l => fiberRestrictionH1 M (A l) (lawSupportFamilyFineHomology M laws ha hA 1 z l) := by
  funext l
  rw [lawSupportFamilyR_apply, lawSupportFamilyFineHomology_apply]
  exact lawSupportFiberRestrictionH1 M laws ha l (hA l) z
/-- 原五項列のH²Pから細H²への射も全族で保持。 -/
theorem lawSupportFamilyEvaluationH2
    (z : (zeroExtension (lawPushforwardComplex M laws ha)).homology (2 : ℤ)) :
    lawSupportFamilyFineHomology M laws ha hA 2 (lawEvaluationH2 M laws ha z) =
      fun l => evaluationH2 M (A l) (lawSupportFamilyPHomology M laws ha hA 2 z l) := by
  funext l
  rw [lawSupportFamilyFineHomology_apply, lawSupportFamilyPHomology_apply]
  exact lawSupportEvaluationH2 M laws ha l (hA l) z

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientShortComplexFamily_delta_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyPHomology
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyPHomology_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyFineHomology
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyFineHomology_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyQHomology
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyQHomology_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyCoarseHomology
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyCoarseHomology_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportFamilyQREquiv
#print axioms AAT.AG.AtlasCoefficientFiber.supportFamilyQREquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportFamilyQREquiv_symm_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyR_viaQ
#print axioms AAT.AG.AtlasCoefficientFiber.supportFamilyTau
#print axioms AAT.AG.AtlasCoefficientFiber.supportFamilyTau_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportFamilyTau_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamily_tau_native
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamily_tau
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyEvaluationH1
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyFiberRestrictionH1
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyEvaluationH2
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
