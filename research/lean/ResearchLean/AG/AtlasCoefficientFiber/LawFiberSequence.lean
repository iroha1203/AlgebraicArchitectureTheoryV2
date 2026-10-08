import ResearchLean.AG.AtlasCoefficientFiber.LawCoefficientComparison
import ResearchLean.AG.AtlasCoefficientFiber.FiveTermSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# G-135 D：同じLaw評価と原fiber完全列

## Implementation notes

Qとκの成分は同じ各ラベルの原L双対・原混在関係から取る。
実細Law座標への可逆移送で短完全列を作り、標準δの自然性を使う。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits HomologicalComplex CanonicalResolution ResolutionInvariance
open FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u

/-- 同じ複体short complex族を成分ごとの実二射で集める。 -/
def coefficientShortComplexFamily {J : Type u}
    (S : J → ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)) :
    ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  ShortComplex.mk (FiniteComplexFamily.map _ _ (fun j => (S j).f))
    (FiniteComplexFamily.map _ _ (fun j => (S j).g)) (by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext j
      exact congrArg (fun f => f.f n (x j)) (S j).zero)

/-- 元の各short exact列から、同じ成分族のshort exact性を生成する。 -/
theorem coefficientShortComplexFamily_shortExact {J : Type u}
    (S : J → ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ))
    (hs : ∀ j, (S j).ShortExact) : (coefficientShortComplexFamily S).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hn (j : J) := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp (hs j) n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    have hpre (j : J) : ∃ y, (S j).f.f n y = x j :=
      (ShortComplex.moduleCat_exact_iff _).mp (hn j).exact (x j) (congrFun hx j)
    choose y hy using hpre
    exact ⟨y, funext hy⟩
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro x y hxy
    funext j
    exact (hn j).moduleCat_injective_f (congrFun hxy j)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    have hpre (j : J) : ∃ y, (S j).g.f n y = x j := (hn j).moduleCat_surjective_g (x j)
    choose y hy using hpre
    exact ⟨y, funext hy⟩

variable {Source : Type u} [Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 同じ発生ラベルの原L双対Qを集める三項複体。 -/
def lawRestrictionComplex : ThreeCochainComplex.{0,u} ℚ :=
  ThreeComplexFamily.complex (fun l => restrictionComplex M (labelValueFiber laws qc ha l))

/-- 元の細Law座標を原制限の同じ全ラベル成分へ送る。 -/
def lawRestrictionHom : ThreeCochainComplex.Hom
    (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha)) (lawRestrictionComplex M laws ha) :=
  cochainComp (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).toHom
    (ThreeComplexFamily.map _ _ (fun l => restrictionHom M (labelValueFiber laws qc ha l)))

/-- Law制限の全Hom生成式。 -/
theorem lawRestrictionHom_eq : lawRestrictionHom M laws ha =
    cochainComp (lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).toHom
      (ThreeComplexFamily.map _ _ (fun l => restrictionHom M (labelValueFiber laws qc ha l))) := rfl

/-- 同じLaw評価と原制限は全三次数で合成零。 -/
theorem lawEvaluation_restriction_zero0 (x : (lawPushforwardComplex M laws ha).C0) :
    (lawRestrictionHom M laws ha).f0 ((lawEvaluationHom M laws ha).f0 x) = 0 := by
  funext l
  rw [lawRestrictionHom_eq, cochainComp_f0]
  change (restrictionHom M (labelValueFiber laws qc ha l)).f0
    ((lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e0 ((lawEvaluationHom M laws ha).f0 x) l) = 0
  rw [lawEvaluationHom_f0, evaluationHom_f0, restrictionHom_f0]
  exact restriction0_evaluation0 M _ _

/-- 同じLaw評価と原制限の実次数1合成零。 -/
theorem lawEvaluation_restriction_zero1 (x : (lawPushforwardComplex M laws ha).C1) :
    (lawRestrictionHom M laws ha).f1 ((lawEvaluationHom M laws ha).f1 x) = 0 := by
  funext l
  rw [lawRestrictionHom_eq, cochainComp_f1]
  change (restrictionHom M (labelValueFiber laws qc ha l)).f1
    ((lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e1 ((lawEvaluationHom M laws ha).f1 x) l) = 0
  rw [lawEvaluationHom_f1, evaluationHom_f1, restrictionHom_f1]
  exact restriction1_evaluation1 M _ _

/-- 同じLaw評価と原制限の実次数2合成零。 -/
theorem lawEvaluation_restriction_zero2 (x : (lawPushforwardComplex M laws ha).C2) :
    (lawRestrictionHom M laws ha).f2 ((lawEvaluationHom M laws ha).f2 x) = 0 := by
  funext l
  rw [lawRestrictionHom_eq, cochainComp_f2]
  change (restrictionHom M (labelValueFiber laws qc ha l)).f2
    ((lawFineCanonicalEquiv (Nf := Nf) (h := h) laws ha).e2 ((lawEvaluationHom M laws ha).f2 x) l) = 0
  rw [lawEvaluationHom_f2, evaluationHom_f2, restrictionHom_f2]
  exact restriction2_evaluation2 M _ _

/-- 同じLaw評価と原制限は標準零延長の全次数で合成零。 -/
theorem lawEvaluation_restriction_standard_zero :
    zeroExtensionMap (lawEvaluationHom M laws ha) ≫ zeroExtensionMap (lawRestrictionHom M laws ha) = 0 := by
  ext n x
  by_cases h0 : n = 0
  · subst n; exact lawEvaluation_restriction_zero0 M laws ha x
  by_cases h1 : n = 1
  · subst n; exact lawEvaluation_restriction_zero1 M laws ha x
  by_cases h2 : n = 2
  · subst n; exact lawEvaluation_restriction_zero2 M laws ha x
  have hz := degreeMap_out (lawEvaluationHom M laws ha) n h0 h1 h2
  change (degreeMap (lawRestrictionHom M laws ha) n) ((degreeMap (lawEvaluationHom M laws ha) n) x) = 0
  rw [hz]
  simp

/-- 同じ実Law評価と原L制限の全次数short complex。 -/
def lawEvaluationRestrictionShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  ShortComplex.mk (zeroExtensionMap (lawEvaluationHom M laws ha))
    (zeroExtensionMap (lawRestrictionHom M laws ha)) (lawEvaluation_restriction_standard_zero M laws ha)

/-- 元のQ族を零延長して同じ原Q標準複体族へ移す。 -/
def lawRestrictionStandardIso : zeroExtension (lawRestrictionComplex M laws ha) ≅
    FiniteComplexFamily.complex (fun l => zeroExtension (restrictionComplex M (labelValueFiber laws qc ha l))) :=
  ThreeComplexFamily.zeroExtensionIso _

/-- 実Law制限は全整数次数で同じ原制限族と可換。 -/
theorem lawRestrictionStandard_square : zeroExtensionMap (lawRestrictionHom M laws ha) ≫
    (lawRestrictionStandardIso M laws ha).hom = (lawFineStandardIso (Nf := Nf) (h := h) laws ha).hom ≫
      FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (restrictionHom M (labelValueFiber laws qc ha l))) := by
  rw [lawRestrictionHom_eq, zeroExtensionMap_comp]
  dsimp only [lawRestrictionStandardIso, lawFineStandardIso, Iso.trans_hom]
  rw [Category.assoc, ThreeComplexFamily.zeroExtensionIso_natural,
    cochainEquivZeroExtensionIso_hom, Category.assoc]

/-- 同じ実Law short complexは原各ラベルSESの族と全射を保って同型。 -/
def lawEvaluationRestrictionFamilyIso : lawEvaluationRestrictionShortComplex M laws ha ≅
    coefficientShortComplexFamily (fun l => evaluationRestrictionShortComplex M (labelValueFiber laws qc ha l)) :=
  ShortComplex.isoMk (lawPushforwardStandardIso M laws ha)
    (lawFineStandardIso (Nf := Nf) (h := h) laws ha) (lawRestrictionStandardIso M laws ha)
    (lawEvaluationStandard_square M laws ha).symm (lawRestrictionStandard_square M laws ha).symm

/-- 実Law評価と同じ原L制限は入力生成の短完全列である。 -/
theorem lawEvaluationRestriction_shortExact : (lawEvaluationRestrictionShortComplex M laws ha).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso (lawEvaluationRestrictionFamilyIso M laws ha)).mpr
    (coefficientShortComplexFamily_shortExact _ (fun l => evaluationRestriction_shortExact M (labelValueFiber laws qc ha l)))


/-- 元SES族の同じ一ラベルへの全三射projection。 -/
def coefficientShortComplexFamily_projection {J : Type u}
    (S : J → ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)) (j : J) :
    coefficientShortComplexFamily S ⟶ S j where
  τ₁ := FiniteComplexFamily.projection _ j
  τ₂ := FiniteComplexFamily.projection _ j
  τ₃ := FiniteComplexFamily.projection _ j
  comm₁₂ := (FiniteComplexFamily.map_projection _ _ (fun j => (S j).f) j).symm
  comm₂₃ := (FiniteComplexFamily.map_projection _ _ (fun j => (S j).g) j).symm

/-- 実Law SESから同じ原ラベルSESへの全三射projection。 -/
def lawEvaluationRestrictionProjection (l : LawValueLabel laws) :
    lawEvaluationRestrictionShortComplex M laws ha ⟶
      evaluationRestrictionShortComplex M (labelValueFiber laws qc ha l) :=
  (lawEvaluationRestrictionFamilyIso M laws ha).hom ≫
    coefficientShortComplexFamily_projection _ l

/-- 実Law SESの左projectionは同じ原P族座標である。 -/
theorem lawEvaluationRestrictionProjection_τ1 (l : LawValueLabel laws) :
    (lawEvaluationRestrictionProjection M laws ha l).τ₁ =
      (lawPushforwardStandardIso M laws ha).hom ≫ FiniteComplexFamily.projection _ l := rfl

/-- 実Law SESの右projectionは同じ原Q族座標である。 -/
theorem lawEvaluationRestrictionProjection_τ3 (l : LawValueLabel laws) :
    (lawEvaluationRestrictionProjection M laws ha l).τ₃ =
      (lawRestrictionStandardIso M laws ha).hom ≫ FiniteComplexFamily.projection _ l := rfl

/-- 実Law P homologyを全整数次数で同じ原P homology族へ読む。 -/
def lawPushforwardHomologyEquiv (n : ℤ) : (zeroExtension (lawPushforwardComplex M laws ha)).homology n ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → (zeroExtension (pushforwardComplex M (labelValueFiber laws qc ha l))).homology n) :=
  (homologyMapIso (lawPushforwardStandardIso M laws ha) n).toLinearEquiv.trans
    (FiniteComplexFamily.homologyEquiv _ n)

/-- 実Law Q homologyを全整数次数で同じ原Q homology族へ読む。 -/
def lawRestrictionHomologyEquiv (n : ℤ) : (zeroExtension (lawRestrictionComplex M laws ha)).homology n ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → (zeroExtension (restrictionComplex M (labelValueFiber laws qc ha l))).homology n) :=
  (homologyMapIso (lawRestrictionStandardIso M laws ha) n).toLinearEquiv.trans
    (FiniteComplexFamily.homologyEquiv _ n)

/-- 同じP homology座標は実SES projectionのhomology射である。 -/
theorem lawPushforwardHomologyEquiv_component (n : ℤ)
    (x : (zeroExtension (lawPushforwardComplex M laws ha)).homology n) (l : LawValueLabel laws) :
    lawPushforwardHomologyEquiv M laws ha n x l =
      homologyMap (lawEvaluationRestrictionProjection M laws ha l).τ₁ n x := by
  dsimp only [lawPushforwardHomologyEquiv, LinearEquiv.trans_apply]
  rw [FiniteComplexFamily.homologyEquiv_component, lawEvaluationRestrictionProjection_τ1,
    homologyMap_comp]
  rfl

/-- 同じQ homology座標は実SES projectionのhomology射である。 -/
theorem lawRestrictionHomologyEquiv_component (n : ℤ)
    (x : (zeroExtension (lawRestrictionComplex M laws ha)).homology n) (l : LawValueLabel laws) :
    lawRestrictionHomologyEquiv M laws ha n x l =
      homologyMap (lawEvaluationRestrictionProjection M laws ha l).τ₃ n x := by
  dsimp only [lawRestrictionHomologyEquiv, LinearEquiv.trans_apply]
  rw [FiniteComplexFamily.homologyEquiv_component, lawEvaluationRestrictionProjection_τ3,
    homologyMap_comp]
  rfl

/-- Law実標準δは全整数次数・全元で原各ラベルの同じδになる。 -/
theorem lawConnecting_delta_component (n : ℤ)
    (x : (zeroExtension (lawRestrictionComplex M laws ha)).homology n) (l : LawValueLabel laws) :
    lawPushforwardHomologyEquiv M laws ha (n+1)
      ((lawEvaluationRestriction_shortExact M laws ha).δ n (n+1) rfl x) l =
      (evaluationRestriction_shortExact M (labelValueFiber laws qc ha l)).δ n (n+1) rfl
        (lawRestrictionHomologyEquiv M laws ha n x l) := by
  rw [lawPushforwardHomologyEquiv_component, lawRestrictionHomologyEquiv_component]
  exact congrArg (fun f => f x) (HomologicalComplex.HomologySequence.δ_naturality
    (lawEvaluationRestrictionProjection M laws ha l) (lawEvaluationRestriction_shortExact M laws ha)
    (evaluationRestriction_shortExact M (labelValueFiber laws qc ha l)) n (n+1) rfl)

/-- 全ラベルの同じ原混在関係κ。 -/
def lawKappa : ((l : LawValueLabel laws) → mixedCycles M (labelValueFiber laws qc ha l)) →ₗ[ℚ]
    ((l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc ha l)) →
      PhiHomology M (labelValueFiber laws qc ha l) c) :=
  LinearMap.pi fun l => (kappa M (labelValueFiber laws qc ha l)).comp (LinearMap.proj l)

/-- 全ラベルの同じ原Φ cohomology上の適合κ*。 -/
def lawKappaStar := FiniteLinearFamily.map (fun l : LawValueLabel laws => kappaStar M (labelValueFiber laws qc ha l))

/-- LawのRは同じ全ラベルκ*のliteral核。 -/
abbrev lawR := LinearMap.ker (lawKappaStar M laws ha)

/-- literal Law Rと同じ各原R族の両方向同型。 -/
def lawRFamilyEquiv : lawR M laws ha ≃ₗ[ℚ] ((l : LawValueLabel laws) → R M (labelValueFiber laws qc ha l)) :=
  FiniteLinearFamily.kernelEquiv _

omit [Fintype Source] in
/-- Law R同型は同じ原Φクラスの各ラベル値を保つ。 -/
theorem lawRFamilyEquiv_val (x : lawR M laws ha) (l : LawValueLabel laws) :
    (lawRFamilyEquiv M laws ha x l).val = x.val l := rfl

/-- 同じLaw Qの一次homologyと同じliteral Law Rの両方向同型。 -/
def lawRestrictionHomologyREquiv : (zeroExtension (lawRestrictionComplex M laws ha)).homology (1 : ℤ) ≃ₗ[ℚ]
    lawR M laws ha :=
  (lawRestrictionHomologyEquiv M laws ha 1).trans
    ((LinearEquiv.piCongrRight fun l => restrictionStandardHomologyREquiv M (labelValueFiber laws qc ha l)).trans
      (lawRFamilyEquiv M laws ha).symm)

/-- Q-R同定の全ラベル値は同じ原Q-R同定を使う。 -/
theorem lawRestrictionHomologyREquiv_component
    (x : (zeroExtension (lawRestrictionComplex M laws ha)).homology (1 : ℤ)) (l : LawValueLabel laws) :
    lawRFamilyEquiv M laws ha (lawRestrictionHomologyREquiv M laws ha x) l =
      restrictionStandardHomologyREquiv M (labelValueFiber laws qc ha l)
        (lawRestrictionHomologyEquiv M laws ha 1 x l) := by
  exact congrFun ((lawRFamilyEquiv M laws ha).apply_symm_apply _) l

/-- Lawの連結射は同じ実SESδをliteral Law Rへ移したもの。 -/
def lawConnectingTau : lawR M laws ha →ₗ[ℚ] (zeroExtension (lawPushforwardComplex M laws ha)).homology (2 : ℤ) :=
  ((lawEvaluationRestriction_shortExact M laws ha).δ (1 : ℤ) 2 rfl).hom.comp
    (lawRestrictionHomologyREquiv M laws ha).symm.toLinearMap

/-- Law τの同じ標準δへの評価。 -/
theorem lawConnectingTau_apply (x : lawR M laws ha) :
    lawConnectingTau M laws ha x = (lawEvaluationRestriction_shortExact M laws ha).δ (1 : ℤ) 2 rfl
      ((lawRestrictionHomologyREquiv M laws ha).symm x) := rfl

/-- 同じLaw τは全R元・全ラベルで原τそのものになる。 -/
theorem lawConnectingTau_component (x : lawR M laws ha) (l : LawValueLabel laws) :
    lawPushforwardHomologyEquiv M laws ha 2 (lawConnectingTau M laws ha x) l =
      connectingTau M (labelValueFiber laws qc ha l) (lawRFamilyEquiv M laws ha x l) := by
  rw [lawConnectingTau_apply]
  change lawPushforwardHomologyEquiv M laws ha (1+1)
    ((lawEvaluationRestriction_shortExact M laws ha).δ 1 (1+1) rfl
      ((lawRestrictionHomologyREquiv M laws ha).symm x)) l = _
  rw [lawConnecting_delta_component]
  have hq := lawRestrictionHomologyREquiv_component M laws ha
    ((lawRestrictionHomologyREquiv M laws ha).symm x) l
  rw [LinearEquiv.apply_symm_apply] at hq
  rw [hq, connectingTau_restrictionStandardHomologyREquiv]
  rfl

/-- 各原H⁰Q零性から同じLaw QのH⁰零性を生成する。 -/
theorem lawRestriction_H0_isZero : IsZero ((zeroExtension (lawRestrictionComplex M laws ha)).homology (0 : ℤ)) := by
  letI (l : LawValueLabel laws) : Subsingleton ((zeroExtension (restrictionComplex M (labelValueFiber laws qc ha l))).homology (0 : ℤ)) :=
    ModuleCat.subsingleton_of_isZero (restrictionComplex_H0_isZero M _)
  letI : Subsingleton ((zeroExtension (lawRestrictionComplex M laws ha)).homology (0 : ℤ)) :=
    ⟨fun x y => (lawRestrictionHomologyEquiv M laws ha 0).injective (Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- 同じ実Law評価の標準H¹射。 -/
def lawEvaluationH1 := (homologyMap (zeroExtensionMap (lawEvaluationHom M laws ha)) (1 : ℤ)).hom

/-- 同じ実Law制限の標準H¹射をliteral Law Rへ送る。 -/
def lawFiberRestrictionH1 := (lawRestrictionHomologyREquiv M laws ha).toLinearMap.comp
  (homologyMap (zeroExtensionMap (lawRestrictionHom M laws ha)) (1 : ℤ)).hom

/-- 同じ実Law評価の標準H²射。 -/
def lawEvaluationH2 := (homologyMap (zeroExtensionMap (lawEvaluationHom M laws ha)) (2 : ℤ)).hom

/-- 同じLaw H⁰Q零性から原Law評価H¹射の単射性を得る。 -/
theorem lawEvaluationH1_injective : Function.Injective (lawEvaluationH1 M laws ha) := by
  have he := (lawEvaluationRestriction_shortExact M laws ha).homology_exact₁ (0 : ℤ) 1 rfl
  have hz : (lawEvaluationRestriction_shortExact M laws ha).δ (0 : ℤ) 1 rfl = 0 :=
    (lawRestriction_H0_isZero M laws ha).eq_of_src _ _
  exact (ModuleCat.mono_iff_injective _).mp (he.mono_g hz)

/-- 同じ実Law五項列は細H¹で完全。 -/
theorem lawFiveTerm_exact_at_fineH1 : Function.Exact (lawEvaluationH1 M laws ha) (lawFiberRestrictionH1 M laws ha) := by
  have he := (lawEvaluationRestriction_shortExact M laws ha).homology_exact₂ (1 : ℤ)
  have hn := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
  intro x
  change lawRestrictionHomologyREquiv M laws ha
    (homologyMap (zeroExtensionMap (lawRestrictionHom M laws ha)) 1 x) = 0 ↔ _
  rw [← (lawRestrictionHomologyREquiv M laws ha).map_zero,
    (lawRestrictionHomologyREquiv M laws ha).injective.eq_iff]
  exact hn x

set_option maxRecDepth 4096 in
/-- 同じ実Law五項列はliteral Rで完全。 -/
theorem lawFiveTerm_exact_at_fiber : Function.Exact (lawFiberRestrictionH1 M laws ha) (lawConnectingTau M laws ha) := by
  have he := (lawEvaluationRestriction_shortExact M laws ha).homology_exact₃ (1 : ℤ) 2 rfl
  have hn : Function.Exact
      (homologyMap (zeroExtensionMap (lawRestrictionHom M laws ha)) (1 : ℤ)).hom
      ((lawEvaluationRestriction_shortExact M laws ha).δ (1 : ℤ) 2 rfl).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
  intro x
  rw [lawConnectingTau_apply]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hn ((lawRestrictionHomologyREquiv M laws ha).symm x)).mp hx
    refine ⟨y, ?_⟩
    change lawRestrictionHomologyREquiv M laws ha
      (homologyMap (zeroExtensionMap (lawRestrictionHom M laws ha)) 1 y) = x
    rw [hy, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, hy⟩
    rw [← hy]
    change (lawEvaluationRestriction_shortExact M laws ha).δ 1 2 rfl
      ((lawRestrictionHomologyREquiv M laws ha).symm
        (lawRestrictionHomologyREquiv M laws ha
          (homologyMap (zeroExtensionMap (lawRestrictionHom M laws ha)) 1 y))) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact (hn _).mpr ⟨y, rfl⟩

/-- 同じ実Law五項列はPのH²で完全。 -/
theorem lawFiveTerm_exact_at_pushforwardH2 : Function.Exact (lawConnectingTau M laws ha) (lawEvaluationH2 M laws ha) := by
  have he := (lawEvaluationRestriction_shortExact M laws ha).homology_exact₁ (1 : ℤ) 2 rfl
  have hn := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hn x).mp hx
    refine ⟨lawRestrictionHomologyREquiv M laws ha y, ?_⟩
    rw [lawConnectingTau_apply, LinearEquiv.symm_apply_apply]
    exact hy
  · rintro ⟨y, hy⟩
    apply (hn x).mpr
    exact ⟨(lawRestrictionHomologyREquiv M laws ha).symm y, hy⟩

omit [Fintype Source] in
/-- Law原κの所有API：同じラベルの原混在サイクルを同じ原κへ送る。 -/
theorem lawKappa_apply
    (x : (l : LawValueLabel laws) → mixedCycles M (labelValueFiber laws qc ha l)) (l : LawValueLabel laws) :
    lawKappa M laws ha x l = kappa M (labelValueFiber laws qc ha l) (x l) := rfl

omit [Fintype Source] in
/-- Law原κ*の所有API：同じラベルの原Φクラス族を同じ原κ*へ送る。 -/
theorem lawKappaStar_apply
    (x : (l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc ha l)) →
      (phiComplex M (labelValueFiber laws qc ha l) c).H1) (l : LawValueLabel laws) :
    lawKappaStar M laws ha x l = kappaStar M (labelValueFiber laws qc ha l) (x l) := rfl

omit [Fintype Source] in
/-- Law R族同型の所有API：逆射も同じ原Φ値を読む。 -/
theorem lawRFamilyEquiv_symm_val
    (x : (l : LawValueLabel laws) → R M (labelValueFiber laws qc ha l)) (l : LawValueLabel laws) :
    ((lawRFamilyEquiv M laws ha).symm x).val l = (x l).val := rfl

/-- Law実εH¹の所有API：同じ標準homology射への全体等号。 -/
theorem lawEvaluationH1_eq_standard : lawEvaluationH1 M laws ha =
    (homologyMap (zeroExtensionMap (lawEvaluationHom M laws ha)) (1 : ℤ)).hom := rfl

/-- Law実εH¹の所有API：全元の同じ標準homology値。 -/
theorem lawEvaluationH1_apply (x : (zeroExtension (lawPushforwardComplex M laws ha)).homology (1 : ℤ)) :
    lawEvaluationH1 M laws ha x = homologyMap (zeroExtensionMap (lawEvaluationHom M laws ha)) 1 x := rfl

/-- Law実fiber制限H¹の所有API：同じQ射の後にliteral R座標を読む。 -/
theorem lawFiberRestrictionH1_apply
    (x : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ)) :
    lawFiberRestrictionH1 M laws ha x = lawRestrictionHomologyREquiv M laws ha
      (homologyMap (zeroExtensionMap (lawRestrictionHom M laws ha)) 1 x) := rfl

/-- Law実εH²の所有API：同じ標準homology射への全体等号。 -/
theorem lawEvaluationH2_eq_standard : lawEvaluationH2 M laws ha =
    (homologyMap (zeroExtensionMap (lawEvaluationHom M laws ha)) (2 : ℤ)).hom := rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientShortComplexFamily
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientShortComplexFamily_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestrictionComplex
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestrictionHom
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestrictionHom_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluation_restriction_zero0
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluation_restriction_zero1
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluation_restriction_zero2
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluation_restriction_standard_zero
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationRestrictionShortComplex
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestrictionStandardIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestrictionStandard_square
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationRestrictionFamilyIso
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationRestriction_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientShortComplexFamily_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationRestrictionProjection
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationRestrictionProjection_τ1
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationRestrictionProjection_τ3
#print axioms AAT.AG.AtlasCoefficientFiber.lawPushforwardHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestrictionHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawPushforwardHomologyEquiv_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestrictionHomologyEquiv_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawConnecting_delta_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawKappa
#print axioms AAT.AG.AtlasCoefficientFiber.lawKappaStar
#print axioms AAT.AG.AtlasCoefficientFiber.lawR
#print axioms AAT.AG.AtlasCoefficientFiber.lawRFamilyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawRFamilyEquiv_val
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestrictionHomologyREquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestrictionHomologyREquiv_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawConnectingTau
#print axioms AAT.AG.AtlasCoefficientFiber.lawConnectingTau_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawConnectingTau_component
#print axioms AAT.AG.AtlasCoefficientFiber.lawRestriction_H0_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationH1
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberRestrictionH1
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationH2
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationH1_injective
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiveTerm_exact_at_fineH1
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiveTerm_exact_at_fiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiveTerm_exact_at_pushforwardH2
#print axioms AAT.AG.AtlasCoefficientFiber.lawKappa_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawKappaStar_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawRFamilyEquiv_symm_val
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationH1_eq_standard
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationH1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberRestrictionH1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationH2_eq_standard
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
