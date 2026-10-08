import ResearchLean.AG.AtlasCoefficientFiber.SupportPhiEmbedding
import ResearchLean.AG.AtlasCoefficientFiber.SupportConnecting

/-!
# G-135 D：原κ双対とliteral Rの同じ台制限

## Implementation notes

同じ全Φ H¹制限と原κの自然性からliteral kernelへの制限を生成する。
全Φ双対は単一fiber類に対する実評価で照合し、全Q代表で元のR座標と接続する。
Rの自然性を追加入力にする案はκ*核の保存を放電しないため採らない。
-/
noncomputable section
open scoped Classical
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision AtlasDefectComposition TwoPhase
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 全Φ双対は同じ原Φ cochain制限と原Φ H₁包含に対して自然。 -/
theorem supportAllPhiHomologyDual
    (z : (c : Nc.ChartInTargetSubset B) → (phiComplex M B c).H1)
    (x : (c : Nc.ChartInTargetSubset A) → PhiHomology M A c) :
    allPhiHomologyDualEquiv M A (supportAllPhiH1 M hab z) x =
      allPhiHomologyDualEquiv M B z (supportAllPhiHomology M hab x) := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  have hh : (allPhiHomologyDualEquiv M A (supportAllPhiH1 M hab z)) =
      (allPhiHomologyDualEquiv M B z).comp (supportAllPhiHomology M hab) := by
    apply LinearMap.pi_ext
    intro c y
    change allPhiHomologyDualEquiv M A (supportAllPhiH1 M hab z) (Pi.single c y) =
      allPhiHomologyDualEquiv M B z (supportAllPhiHomology M hab (Pi.single c y))
    rw [allPhiHomologyDualEquiv_single, supportAllPhiHomology_single,
      allPhiHomologyDualEquiv_single, supportAllPhiH1_apply]
    exact supportPhiHomologyDual M hab c _ y
  exact LinearMap.congr_fun hh x

/-- 原κ*の台制限は同じ原混在閉路包含への前合成。 -/
theorem supportKappaStar
    (z : (c : Nc.ChartInTargetSubset B) → (phiComplex M B c).H1) (x : mixedCycles M A) :
    kappaStar M A (supportAllPhiH1 M hab z) x =
      kappaStar M B z (supportMixedCyclesInclude M hab x) := by
  rw [kappaStar_apply, kappaStar_apply, supportAllPhiHomologyDual, supportKappa]

/-- 同じ直接Φ H¹制限は独立に生成したκ*のliteral kernelを保つ。 -/
def supportFiberR : R M B →ₗ[ℚ] R M A :=
  ((supportAllPhiH1 M hab).comp (R M B).subtype).codRestrict _ (fun z => by
    apply LinearMap.ext
    intro x
    change kappaStar M A (supportAllPhiH1 M hab z.1) x = 0
    rw [supportKappaStar]
    exact LinearMap.congr_fun z.2 (supportMixedCyclesInclude M hab x))

/-- literal R台制限の元Φ座標は同じ直接H¹制限。 -/
@[simp] theorem supportFiberR_val (z : R M B) :
    (supportFiberR M hab z).1 = supportAllPhiH1 M hab z.1 := rfl

/-- 原垂直双対座標も同じ垂直H₁包含への前合成に対して自然。 -/
theorem supportPhiVerticalDual
    (z : (c : Nc.ChartInTargetSubset B) → (phiComplex M B c).H1) (x : VerticalHomology M A) :
    phiCohomologyVerticalDualEquiv M A (supportAllPhiH1 M hab z) x =
      phiCohomologyVerticalDualEquiv M B z (supportVerticalHomology M hab x) := by
  rw [phiCohomologyVerticalDualEquiv_apply, phiCohomologyVerticalDualEquiv_apply,
    supportAllPhiHomologyDual]
  rw [supportAllPhiHomology_apply, LinearEquiv.symm_apply_apply]

/-- 原垂直閉路のL内代表は同じ台包含と可換。 -/
theorem supportVerticalCycleInclusion (x : verticalCycles M A) :
    supportL1Include M hab (verticalCycleInclusion M A x).1 =
      (verticalCycleInclusion M B (supportVerticalCyclesInclude M hab x)).1 := by
  apply Subtype.ext
  rw [supportL1Include_val, verticalCycleInclusion_val, verticalCycleInclusion_val,
    supportVerticalCyclesInclude_val, supportVerticalEdgeChainInclude_inclusion]

/-- 標準H¹Qから原垂直双対核への座標は全原Q代表で台制限と可換。 -/
theorem supportQRawR
    (z : (zeroExtension (restrictionComplex M B)).homology (1 : ℤ)) (x : VerticalHomology M A) :
    (restrictionStandardHomologyRawREquiv M A
      (HomologicalComplex.homologyMap (zeroExtensionMap (supportQHom M hab)) 1 z)).1 x =
      (restrictionStandardHomologyRawREquiv M B z).1 (supportVerticalHomology M hab x) := by
  obtain ⟨z, rfl⟩ := (oldH1Equiv (restrictionComplex M B)).surjective z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      have hm : (supportQHom M hab).h1Map (Submodule.Quotient.mk z) =
          Submodule.Quotient.mk ((supportQHom M hab).cyclesMap z) :=
        (supportQHom M hab).h1Map_mk z
      rw [← oldH1Equiv_natural, hm,
        restrictionStandardHomologyRawREquiv_mk, supportVerticalHomology_mk,
        restrictionStandardHomologyRawREquiv_mk]
      rw [TwoPhase.ThreeCochainComplex.Hom.cyclesMap_apply, supportQHom_f1]
      change supportQ1 M hab z.1 (verticalCycleInclusion M A x).1 =
        z.1 (verticalCycleInclusion M B (supportVerticalCyclesInclude M hab x)).1
      rw [supportQ1_apply, supportVerticalCycleInclusion]

/-- 直接Φで生成したliteral R制限は元H¹Q座標からの制限と同じ実写像。 -/
theorem supportFiberR_eq_supportRRestriction : supportFiberR M hab = supportRRestriction M hab := by
  apply LinearMap.ext
  intro z
  apply (fiberRRawEquiv M A).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rw [fiberRRawEquiv_val, supportFiberR_val, supportPhiVerticalDual, supportRRestriction_apply,
    restrictionStandardHomologyREquiv_raw]
  rw [supportQRawR]
  have hh := (restrictionStandardHomologyREquiv M B).apply_symm_apply z
  have hr := restrictionStandardHomologyREquiv_raw M B
    ((restrictionStandardHomologyREquiv M B).symm z)
  rw [hh] at hr
  rw [← hr, fiberRRawEquiv_val]

/-- 原τの自然性は直接Φから生成した同じliteral R制限で成り立つ。 -/
theorem supportFiberR_tau (z : R M B) :
    HomologicalComplex.homologyMap (zeroExtensionMap (supportPushforwardHom M hab)) 2
      (connectingTau M B z) = connectingTau M A (supportFiberR M hab z) := by
  rw [supportFiberR_eq_supportRRestriction]
  exact supportConnecting_tau M hab z

/-- 直接Φから生成したliteral R台制限の恒等則。 -/
theorem supportFiberR_refl (A : Set qc.Target) :
    supportFiberR M (Set.Subset.refl A) = LinearMap.id := by
  rw [supportFiberR_eq_supportRRestriction, supportRRestriction_refl]

/-- 直接Φから生成したliteral R台制限の合成則。 -/
theorem supportFiberR_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportFiberR M hab).comp (supportFiberR M hbc) = supportFiberR M (hab.trans hbc) := by
  rw [supportFiberR_eq_supportRRestriction, supportFiberR_eq_supportRRestriction,
    supportFiberR_eq_supportRRestriction, supportRRestriction_comp]

/-- 元五項列のfine H¹からliteral Rへの射も直接Φ制限に対して自然。 -/
theorem supportFiberR_fiveTerm
    (z : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' B))).homology (1 : ℤ)) :
    supportFiberR M hab (fiberRestrictionH1 M B z) = fiberRestrictionH1 M A
      (HomologicalComplex.homologyMap (zeroExtensionMap
        (subsetRestrictHom Nf (fun _ ht => hab ht))) 1 z) := by
  rw [supportFiberR_eq_supportRRestriction]
  exact supportFiberRestrictionH1 M hab z

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportAllPhiHomologyDual
#print axioms AAT.AG.AtlasCoefficientFiber.supportKappaStar
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberR
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberR_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiVerticalDual
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalCycleInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.supportQRawR
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberR_eq_supportRRestriction
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberR_tau
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberR_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberR_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberR_fiveTerm
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
