import ResearchLean.AG.AtlasCoefficientFiber.SupportPushforward
import ResearchLean.AG.AtlasCoefficientFiber.SupportQRestriction
import ResearchLean.AG.AtlasCoefficientFiber.FiveTermSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# G-135 D：原短完全列と標準連結射の全次数台自然性

## Implementation notes

同じ原P・細cochain・Qの台制限正方形から実ShortComplex射を作る。
mathlibの標準δ自然性を全整数次数へ適用し、元のH¹Q≃Rで同じτへ戻す。
連結射を台ごとに新しく選ぶ案は元の標準短完全列との一致を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 元の実短完全列への同じ台制限射。全三対象を原入力から生成する。 -/
def supportEvaluationRestrictionMorphism :
    evaluationRestrictionShortComplex M B ⟶ evaluationRestrictionShortComplex M A where
  τ₁ := zeroExtensionMap (supportPushforwardHom M hab)
  τ₂ := zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab ht))
  τ₃ := zeroExtensionMap (supportQHom M hab)
  comm₁₂ := by
    rw [evaluationRestrictionShortComplex_f, evaluationRestrictionShortComplex_f]
    have hh := congrArg zeroExtensionMap (supportEvaluationHom M hab)
    rw [zeroExtensionMap_comp, zeroExtensionMap_comp] at hh
    exact hh
  comm₂₃ := by
    rw [evaluationRestrictionShortComplex_g, evaluationRestrictionShortComplex_g]
    have hh := congrArg zeroExtensionMap (supportRestrictionHom M hab)
    rw [zeroExtensionMap_comp, zeroExtensionMap_comp] at hh
    exact hh.symm

/-- 実短完全列の左台射は同じP制限。 -/
theorem supportEvaluationRestrictionMorphism_τ1 :
    (supportEvaluationRestrictionMorphism M hab).τ₁ = zeroExtensionMap (supportPushforwardHom M hab) := rfl
/-- 実短完全列の中台射は同じ元細cochain制限。 -/
theorem supportEvaluationRestrictionMorphism_τ2 :
    (supportEvaluationRestrictionMorphism M hab).τ₂ =
      zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab ht)) := rfl
/-- 実短完全列の右台射は同じQ=L*制限。 -/
theorem supportEvaluationRestrictionMorphism_τ3 :
    (supportEvaluationRestrictionMorphism M hab).τ₃ = zeroExtensionMap (supportQHom M hab) := rfl

/-- 原標準δは全整数次数・全元で元の台制限と自然。 -/
theorem supportConnecting_delta (n : ℤ)
    (z : (zeroExtension (restrictionComplex M B)).homology n) :
    HomologicalComplex.homologyMap (zeroExtensionMap (supportPushforwardHom M hab)) (n+1)
      ((evaluationRestriction_shortExact M B).δ n (n+1) rfl z) =
    (evaluationRestriction_shortExact M A).δ n (n+1) rfl
      (HomologicalComplex.homologyMap (zeroExtensionMap (supportQHom M hab)) n z) :=
  congrArg (fun f => f z) (HomologicalComplex.HomologySequence.δ_naturality
    (supportEvaluationRestrictionMorphism M hab) (evaluationRestriction_shortExact M B)
    (evaluationRestriction_shortExact M A) n (n+1) rfl)

/-- 元H¹Q≃R座標に戻した同じ実Q台制限。直接Φ制限との照合に使う。 -/
def supportRRestriction : R M B →ₗ[ℚ] R M A :=
  (restrictionStandardHomologyREquiv M A).toLinearMap.comp
    ((HomologicalComplex.homologyMap (zeroExtensionMap (supportQHom M hab)) (1 : ℤ)).hom.comp
      (restrictionStandardHomologyREquiv M B).symm.toLinearMap)

/-- 原R台制限の全値は同じ標準Q射の元の可逆座標。 -/
theorem supportRRestriction_apply (z : R M B) :
    supportRRestriction M hab z = restrictionStandardHomologyREquiv M A
      (HomologicalComplex.homologyMap (zeroExtensionMap (supportQHom M hab)) (1 : ℤ)
        ((restrictionStandardHomologyREquiv M B).symm z)) := rfl

/-- H¹Qから原Rへの両方向座標は同じQ台射と可換。 -/
theorem supportRRestriction_viaQ (z : (zeroExtension (restrictionComplex M B)).homology (1 : ℤ)) :
    supportRRestriction M hab (restrictionStandardHomologyREquiv M B z) =
      restrictionStandardHomologyREquiv M A
        (HomologicalComplex.homologyMap (zeroExtensionMap (supportQHom M hab)) (1 : ℤ) z) := by
  rw [supportRRestriction_apply, LinearEquiv.symm_apply_apply]

/-- 原R台制限の恒等則は同じ標準Q射の恒等から従う。 -/
theorem supportRRestriction_refl (A : Set qc.Target) :
    supportRRestriction M (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  rw [supportRRestriction_apply, supportQHom_refl, zeroExtensionMap_id,
    HomologicalComplex.homologyMap_id]
  change restrictionStandardHomologyREquiv M A ((restrictionStandardHomologyREquiv M A).symm z) = z
  exact LinearEquiv.apply_symm_apply _ z

/-- 原R台制限の合成則は同じ標準Q射の合成から従う。 -/
theorem supportRRestriction_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportRRestriction M hab).comp (supportRRestriction M hbc) =
      supportRRestriction M (hab.trans hbc) := by
  apply LinearMap.ext
  intro z
  change supportRRestriction M hab (supportRRestriction M hbc z) = _
  rw [supportRRestriction_apply, supportRRestriction_apply, supportRRestriction_apply,
    LinearEquiv.symm_apply_apply]
  have hh := congrArg (fun f => HomologicalComplex.homologyMap (zeroExtensionMap f) (1 : ℤ))
    (supportQHom_comp M hab hbc)
  dsimp only at hh
  rw [zeroExtensionMap_comp, HomologicalComplex.homologyMap_comp] at hh
  exact congrArg (restrictionStandardHomologyREquiv M A)
    (congrArg (fun f => f ((restrictionStandardHomologyREquiv M C).symm z)) hh)

/-- 原τの全R元での台自然性。定義済み標準δの次数1を同じ座標へ戻す。 -/
theorem supportConnecting_tau (z : R M B) :
    HomologicalComplex.homologyMap (zeroExtensionMap (supportPushforwardHom M hab)) (2 : ℤ)
      (connectingTau M B z) = connectingTau M A (supportRRestriction M hab z) := by
  rw [connectingTau_apply, connectingTau_apply, supportRRestriction_apply,
    LinearEquiv.symm_apply_apply]
  exact supportConnecting_delta M hab 1 ((restrictionStandardHomologyREquiv M B).symm z)

/-- 五項列のH¹P→H¹細の同じ射は台制限と自然。 -/
theorem supportEvaluationH1
    (z : (zeroExtension (pushforwardComplex M B)).homology (1 : ℤ)) :
    HomologicalComplex.homologyMap (zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab ht))) 1
      (evaluationH1 M B z) =
    evaluationH1 M A
      (HomologicalComplex.homologyMap (zeroExtensionMap (supportPushforwardHom M hab)) 1 z) := by
  rw [evaluationH1_apply, evaluationH1_apply]
  have hh := congrArg (fun f => HomologicalComplex.homologyMap (zeroExtensionMap f) (1 : ℤ))
    (supportEvaluationHom M hab)
  dsimp only at hh
  rw [zeroExtensionMap_comp, zeroExtensionMap_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hh
  exact (congrArg (fun f => f z) hh).symm

/-- 五項列のH¹細→Rの同じ射は原Q台正方形により自然。 -/
theorem supportFiberRestrictionH1
    (z : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' B))).homology (1 : ℤ)) :
    supportRRestriction M hab (fiberRestrictionH1 M B z) =
      fiberRestrictionH1 M A
        (HomologicalComplex.homologyMap (zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab ht))) 1 z) := by
  rw [fiberRestrictionH1_apply, fiberRestrictionH1_apply, supportRRestriction_viaQ]
  have hh := congrArg (fun f => HomologicalComplex.homologyMap (zeroExtensionMap f) (1 : ℤ))
    (supportRestrictionHom M hab)
  dsimp only at hh
  rw [zeroExtensionMap_comp, zeroExtensionMap_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hh
  exact congrArg (restrictionStandardHomologyREquiv M A) (congrArg (fun f => f z) hh)

/-- 五項列のH²P→H²細も同じ射を保って台制限と自然。 -/
theorem supportEvaluationH2
    (z : (zeroExtension (pushforwardComplex M B)).homology (2 : ℤ)) :
    HomologicalComplex.homologyMap (zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab ht))) 2
      (evaluationH2 M B z) =
    evaluationH2 M A
      (HomologicalComplex.homologyMap (zeroExtensionMap (supportPushforwardHom M hab)) 2 z) := by
  rw [evaluationH2_apply, evaluationH2_apply]
  have hh := congrArg (fun f => HomologicalComplex.homologyMap (zeroExtensionMap f) (2 : ℤ))
    (supportEvaluationHom M hab)
  dsimp only at hh
  rw [zeroExtensionMap_comp, zeroExtensionMap_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hh
  exact (congrArg (fun f => f z) hh).symm

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationRestrictionMorphism
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationRestrictionMorphism_τ1
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationRestrictionMorphism_τ2
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationRestrictionMorphism_τ3
#print axioms AAT.AG.AtlasCoefficientFiber.supportConnecting_delta
#print axioms AAT.AG.AtlasCoefficientFiber.supportRRestriction
#print axioms AAT.AG.AtlasCoefficientFiber.supportRRestriction_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportRRestriction_viaQ
#print axioms AAT.AG.AtlasCoefficientFiber.supportRRestriction_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportRRestriction_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportConnecting_tau
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationH1
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberRestrictionH1
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationH2
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
