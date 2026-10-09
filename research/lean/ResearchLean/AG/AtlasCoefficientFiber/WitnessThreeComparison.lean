import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeInput
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFullSupport
import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneDiagnostics
import ResearchLean.AG.FaceRelationSubdivision.IncidenceNamedComparison

/-!
# G-135 W3：原H¹d0像商と二比較のperiod

## Implementation notes

原cyclesのperiod核を原boundary rangeへ両方向同定して全商座標を生成する。
零微分への置換は三角形の頂点d0像を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 元cycles上の写像から、元d0像商全体を同定する一般両逆。 -/
def periodQuotientEquiv (C : ThreeCochainComplex ℚ) {V : Type*}
    [AddCommGroup V] [Module ℚ V] (f : LinearMap.ker C.d1 →ₗ[ℚ] V)
    (hk : LinearMap.ker f = LinearMap.range C.boundaryToCycles)
    (hs : Function.Surjective f) : C.H1 ≃ₗ[ℚ] V :=
  (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs)
/-- この同型は全原cocycleのperiodを読む。 -/
theorem periodQuotientEquiv_mk (C : ThreeCochainComplex ℚ) {V : Type*}
    [AddCommGroup V] [Module ℚ V] (f : LinearMap.ker C.d1 →ₗ[ℚ] V)
    (hk : LinearMap.ker f = LinearMap.range C.boundaryToCycles)
    (hs : Function.Surjective f) (z : LinearMap.ker C.d1) :
    periodQuotientEquiv C f hk hs ((LinearMap.range C.boundaryToCycles).mkQ z) = f z := rfl

/-- 粗原cycleのh period。 -/
def coarsePeriod : LinearMap.ker (namedComplex Nc).d1 →ₗ[ℚ] ℚ where
  toFun z := z.1 3
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 粗h period核は元頂点d0像の全range。 -/
theorem coarsePeriod_kernel : LinearMap.ker coarsePeriod =
    LinearMap.range (namedComplex Nc).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    change z.1 3 = 0 at hz
    have hf := congrFun z.2 0
    change (namedComplex Nc).d1 z.1 0 = 0 at hf
    rw [namedComplex_d1_apply] at hf
    change z.1 0 - z.1 1 + z.1 2 = 0 at hf
    refine ⟨![0,z.1 0,z.1 1], ?_⟩
    apply Subtype.ext
    funext e
    change (namedComplex Nc).d0 ![0,z.1 0,z.1 1] e = z.1 e
    rw [namedComplex_d0_apply]
    fin_cases e <;> simp [Nc,coarseNerve] <;> linarith
  · rintro ⟨z,rfl⟩
    change (namedComplex Nc).d0 z 3 = 0
    rw [namedComplex_d0_apply]
    exact sub_self _
/-- 任意有理h periodは同原cycleから生成する。 -/
theorem coarsePeriod_surjective : Function.Surjective coarsePeriod := by
  intro q
  refine ⟨⟨![0,0,0,q], ?_⟩,rfl⟩
  rw [LinearMap.mem_ker]
  funext f
  change (namedComplex Nc).d1 ![0,0,0,q] f = (0 : ℚ)
  simp [namedComplex_d1_apply,Nc,coarseNerve]
/-- 全粗H¹商の両逆h座標。 -/
def coarseNamedCoordinates : (namedComplex Nc).H1 ≃ₗ[ℚ] ℚ :=
  periodQuotientEquiv _ coarsePeriod coarsePeriod_kernel coarsePeriod_surjective

/-- 面あり細原cycleのh period。 -/
def finePeriod : LinearMap.ker (namedComplex Nf).d1 →ₗ[ℚ] ℚ where
  toFun z := z.1 4
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- f0/f1/mの実cycle式を使用してh核を原d0像rangeへ戻す。 -/
theorem finePeriod_kernel : LinearMap.ker finePeriod =
    LinearMap.range (namedComplex Nf).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    change z.1 4 = 0 at hz
    have h0 := congrFun z.2 0
    have h1 := congrFun z.2 1
    have hm := congrFun z.2 2
    change (namedComplex Nf).d1 z.1 0 = 0 at h0
    change (namedComplex Nf).d1 z.1 1 = 0 at h1
    change (namedComplex Nf).d1 z.1 2 = 0 at hm
    rw [namedComplex_d1_apply] at h0 h1 hm
    change z.1 0 - z.1 2 + z.1 3 = 0 at h0
    change z.1 1 - z.1 2 + z.1 3 = 0 at h1
    change z.1 5 - z.1 1 + z.1 0 = 0 at hm
    refine ⟨![0,z.1 0,z.1 2], ?_⟩
    apply Subtype.ext
    funext e
    change (namedComplex Nf).d0 ![0,z.1 0,z.1 2] e = z.1 e
    rw [namedComplex_d0_apply]
    fin_cases e <;> simp [Nf,fineNerve] <;> linarith
  · rintro ⟨z,rfl⟩
    change (namedComplex Nf).d0 z 4 = 0
    rw [namedComplex_d0_apply]
    exact sub_self _
/-- 同原h単独cycleが全有理periodを与える。 -/
theorem finePeriod_surjective : Function.Surjective finePeriod := by
  intro q
  refine ⟨⟨![0,0,0,0,q,0], ?_⟩,rfl⟩
  rw [LinearMap.mem_ker]
  funext f
  change (namedComplex Nf).d1 ![0,0,0,0,q,0] f = (0 : ℚ)
  fin_cases f <;> simp [namedComplex_d1_apply,Nf,fineNerve]
/-- 面あり全細H¹商のh座標。 -/
def fineNamedCoordinates : (namedComplex Nf).H1 ≃ₗ[ℚ] ℚ :=
  periodQuotientEquiv _ finePeriod finePeriod_kernel finePeriod_surjective

/-- mなし原cycleのh/k全period。 -/
def pairedPeriod : LinearMap.ker (namedComplex pairedNf).d1 →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun z := ![z.1 4,z.1 5]
  map_add' _ _ := by funext i; fin_cases i <;> rfl
  map_smul' _ _ := by funext i; fin_cases i <;> rfl
/-- 二period核はmなしでも元頂点d0像の全range。 -/
theorem pairedPeriod_kernel : LinearMap.ker pairedPeriod =
    LinearMap.range (namedComplex pairedNf).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    change ![z.1 4,z.1 5] = 0 at hz
    have hh : z.1 4 = 0 := congrFun hz 0
    have hk : z.1 5 = 0 := congrFun hz 1
    have h0 := congrFun z.2 0
    have h1 := congrFun z.2 1
    change (namedComplex pairedNf).d1 z.1 0 = 0 at h0
    change (namedComplex pairedNf).d1 z.1 1 = 0 at h1
    rw [namedComplex_d1_apply] at h0 h1
    change z.1 0 - z.1 2 + z.1 3 = 0 at h0
    change z.1 1 - z.1 2 + z.1 3 = 0 at h1
    refine ⟨![0,z.1 0,z.1 2], ?_⟩
    apply Subtype.ext
    funext e
    change (namedComplex pairedNf).d0 ![0,z.1 0,z.1 2] e = z.1 e
    rw [namedComplex_d0_apply]
    fin_cases e <;> simp [pairedNf,pairedNerve] <;> linarith
  · rintro ⟨z,rfl⟩
    change ![(namedComplex pairedNf).d0 z 4,(namedComplex pairedNf).d0 z 5] = 0
    funext i
    fin_cases i <;> simp [namedComplex_d0_apply,pairedNf,pairedNerve]
/-- 全h/k periodを同原paired cycleから構成する。 -/
theorem pairedPeriod_surjective : Function.Surjective pairedPeriod := by
  intro q
  refine ⟨⟨![0,0,0,0,q 0,q 1], ?_⟩,?_⟩
  · rw [LinearMap.mem_ker]
    funext f
    change (namedComplex pairedNf).d1 ![0,0,0,0,q 0,q 1] f = (0 : ℚ)
    fin_cases f <;> simp [namedComplex_d1_apply,pairedNf,pairedNerve]
  · funext i; fin_cases i <;> rfl
/-- mなし全細H¹商の二period両逆。 -/
def pairedNamedCoordinates : (namedComplex pairedNf).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  periodQuotientEquiv _ pairedPeriod pairedPeriod_kernel pairedPeriod_surjective

/-- 原面ありH¹比較は全元でh恒等。 -/
theorem named_map (x : (namedComplex Nc).H1) :
    fineNamedCoordinates ((incidenceNamedHom M).h1Map x) = coarseNamedCoordinates x := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (namedComplex Nc).boundaryToCycles).mkQ_surjective x
  rw [ThreeCochainComplex.Hom.h1Map_mk]
  rfl
/-- 原mなしH¹比較はhを保存しkへ零を送る。 -/
theorem paired_named_map (x : (namedComplex Nc).H1) :
    pairedNamedCoordinates ((incidenceNamedHom pairedM).h1Map x) = ![coarseNamedCoordinates x,0] := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (namedComplex Nc).boundaryToCycles).mkQ_surjective x
  rw [ThreeCochainComplex.Hom.h1Map_mk]
  funext i; fin_cases i <;> rfl

/-- 元coarse subset全H¹商のh period座標。 -/
def coarseCoordinates (A : Set Bool) (hA : A.Nonempty) : (Nc.targetSubsetComplex A).H1 ≃ₗ[ℚ] ℚ :=
  (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).h1Equiv.trans coarseNamedCoordinates
/-- 元面ありfine subset全H¹商のh period座標。 -/
def fineCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1 ≃ₗ[ℚ] ℚ :=
  (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).h1Equiv.trans fineNamedCoordinates
/-- 元mなしsubset全H¹商のh/k座標。 -/
def pairedCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (pairedNf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (fullSubsetNamedEquiv pairedNf (fun _ => rfl) _ (fine_nonempty A hA)).h1Equiv.trans pairedNamedCoordinates
/-- 面ありの独立元u全三成分を原named比較へ接続。 -/
theorem subset_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (M.aSubnerveComparisonHom A)
      (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).toHom =
    cochainComp (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).toHom (incidenceNamedHom M) :=
  fullSubsetNamed_square M (fun _ => rfl) (fun _ => rfl) A _ hA
    (fine_nonempty A hA) (fun _ ht => ht)
/-- mなしの独立元u全三成分も原named比較へ接続。 -/
theorem paired_subset_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (pairedM.aSubnerveComparisonHom A)
      (fullSubsetNamedEquiv pairedNf (fun _ => rfl) _ (fine_nonempty A hA)).toHom =
    cochainComp (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).toHom (incidenceNamedHom pairedM) :=
  fullSubsetNamed_square pairedM (fun _ => rfl) (fun _ => rfl) A _ hA
    (fine_nonempty A hA) (fun _ ht => ht)
/-- 同原subset比較は全H¹元でh恒等。 -/
theorem subset_map (A : Set Bool) (hA : A.Nonempty) (x : (Nc.targetSubsetComplex A).H1) :
    fineCoordinates A hA ((M.aSubnerveComparisonHom A).h1Map x) = coarseCoordinates A hA x := by
  have hn := fun z => congrArg (fun f => f.f1 z) (subset_square A hA)
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA)
    (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA))
    (M.aSubnerveComparisonHom A) (incidenceNamedHom M) hn x
  exact (congrArg fineNamedCoordinates hh).trans (named_map _)
/-- mなし同原subset比較はhを保存しkへ零。 -/
theorem paired_subset_map (A : Set Bool) (hA : A.Nonempty) (x : (Nc.targetSubsetComplex A).H1) :
    pairedCoordinates A hA ((pairedM.aSubnerveComparisonHom A).h1Map x) = ![coarseCoordinates A hA x,0] := by
  have hn := fun z => congrArg (fun f => f.f1 z) (paired_subset_square A hA)
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA)
    (fullSubsetNamedEquiv pairedNf (fun _ => rfl) _ (fine_nonempty A hA))
    (pairedM.aSubnerveComparisonHom A) (incidenceNamedHom pairedM) hn x
  exact (congrArg pairedNamedCoordinates hh).trans (paired_named_map _)
/-- 面あり同元Tは全H¹で単射・全射。 -/
theorem comparison_bijective (A : Set Bool) (hA : A.Nonempty) :
    Function.Bijective (M.aSubnerveComparisonHom A).h1Map := by
  constructor
  · intro x y h
    apply (coarseCoordinates A hA).injective
    exact (subset_map A hA x).symm.trans ((congrArg (fineCoordinates A hA) h).trans (subset_map A hA y))
  · intro y
    refine ⟨(coarseCoordinates A hA).symm (fineCoordinates A hA y), ?_⟩
    apply (fineCoordinates A hA).injective
    rw [subset_map,LinearEquiv.apply_symm_apply]
/-- 原Tの実欠損は面あり00。 -/
theorem defect (A : Set Bool) (hA : A.Nonempty) :
    blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (comparison_bijective A hA)
/-- mなし実Tの全座標表示。 -/
def pairedCoordinateMap : ℚ →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun x := ![x,0]
  map_add' _ _ := by funext i; fin_cases i <;> simp
  map_smul' _ _ := by funext i; fin_cases i <;> simp
/-- mなし表示射の全元単射性。 -/
theorem pairedCoordinateMap_injective : Function.Injective pairedCoordinateMap := by
  intro x y he
  exact congrFun he 0
/-- mなしk periodは実余核を読む。 -/
def kPeriod : (Fin 2 → ℚ) →ₗ[ℚ] ℚ where
  toFun z := z 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 全k period核は元mなし表示射の全range。 -/
theorem kPeriod_kernel : LinearMap.ker kPeriod = LinearMap.range pairedCoordinateMap := by
  ext z
  constructor
  · intro hz
    change z 1 = 0 at hz
    refine ⟨z 0, ?_⟩
    funext i; fin_cases i
    · rfl
    · exact hz.symm
  · rintro ⟨x,rfl⟩
    rfl
/-- k periodは全有理値を同座標から読む。 -/
theorem kPeriod_surjective : Function.Surjective kPeriod := fun q => ⟨![0,q],rfl⟩
/-- 全mなし表示射余核の両逆。 -/
def coordinateCokernelEquiv : ((Fin 2 → ℚ) ⧸ LinearMap.range pairedCoordinateMap) ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ kPeriod_kernel.symm).trans (kPeriod.quotKerEquivOfSurjective kPeriod_surjective)
/-- 同原mなし実余核商全体をk periodへ戻す両逆。 -/
def pairedCokernelEquiv (A : Set Bool) (hA : A.Nonempty) :
    ((pairedNf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1 ⧸
      LinearMap.range (pairedM.aSubnerveComparisonHom A).h1Map) ≃ₗ[ℚ] ℚ :=
  (LinearConjugation.cokernelEquiv (pairedM.aSubnerveComparisonHom A).h1Map pairedCoordinateMap
    (coarseCoordinates A hA) (pairedCoordinates A hA) (paired_subset_map A hA)).trans coordinateCokernelEquiv
/-- 同実余核の全代表をk値で読む。 -/
theorem pairedCokernelEquiv_mk (A : Set Bool) (hA : A.Nonempty)
    (x : (pairedNf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1) :
    pairedCokernelEquiv A hA ((LinearMap.range (pairedM.aSubnerveComparisonHom A).h1Map).mkQ x) =
      pairedCoordinates A hA x 1 := rfl
/-- mなし同実Tも全元単射。 -/
theorem paired_comparison_injective (A : Set Bool) (hA : A.Nonempty) :
    Function.Injective (pairedM.aSubnerveComparisonHom A).h1Map := by
  intro x y he
  apply (coarseCoordinates A hA).injective
  apply pairedCoordinateMap_injective
  exact (paired_subset_map A hA x).symm.trans ((congrArg (pairedCoordinates A hA) he).trans (paired_subset_map A hA y))
/-- mなし同実Tの欠損は01。 -/
theorem paired_defect (A : Set Bool) (hA : A.Nonempty) :
    blockDefect (pairedM.aSubnerveComparisonHom A).h1Map = (0,1) := by
  apply Prod.ext
  · rw [blockDefect_kernel_dimension,LinearMap.ker_eq_bot.mpr (paired_comparison_injective A hA)]
    exact Module.finrank_zero_of_subsingleton
  · exact (pairedCokernelEquiv A hA).finrank_eq.trans (Module.finrank_self ℚ)
/-- 面あり原producerのJも同実00。 -/
theorem primitive_J (A : Set Bool) (hA : A.Nonempty) : primitiveDiagnostic M A = (0,0) :=
  (primitiveDiagnostic_eq_blockDefect M A).trans (defect A hA)
/-- mなし原producerのJも同実01。 -/
theorem paired_primitive_J (A : Set Bool) (hA : A.Nonempty) : primitiveDiagnostic pairedM A = (0,1) :=
  (primitiveDiagnostic_eq_blockDefect pairedM A).trans (paired_defect A hA)
/-- 面あり空Aも実零商から欠損00。 -/
theorem empty_defect : blockDefect (M.aSubnerveComparisonHom ∅).h1Map = (0,0) := by
  letI := WitnessOne.empty_H1_subsingleton qc Nc
  letI : Subsingleton (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' ∅)).H1 := by
    simpa only [Set.preimage_empty] using WitnessOne.empty_H1_subsingleton qf Nf
  exact (blockDefect_eq_zero_iff_bijective _).mpr
    ⟨fun _ _ _ => Subsingleton.elim _ _,fun y => ⟨0,Subsingleton.elim _ _⟩⟩
/-- paired空Aも実零商から欠損00。 -/
theorem paired_empty_defect : blockDefect (pairedM.aSubnerveComparisonHom ∅).h1Map = (0,0) := by
  letI := WitnessOne.empty_H1_subsingleton qc Nc
  letI : Subsingleton (pairedNf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' ∅)).H1 := by
    simpa only [Set.preimage_empty] using WitnessOne.empty_H1_subsingleton qf pairedNf
  exact (blockDefect_eq_zero_iff_bijective _).mpr
    ⟨fun _ _ _ => Subsingleton.elim _ _,fun y => ⟨0,Subsingleton.elim _ _⟩⟩
/-- 同面ありproducerは全Aで欠損零。 -/
theorem allA_primitive_J (A : Set Bool) : primitiveDiagnostic M A = (0,0) := by
  by_cases hA : A.Nonempty
  · exact primitive_J A hA
  · have ha := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [primitiveDiagnostic_eq_blockDefect]
    exact empty_defect
/-- 同paired producerの全A分類は空Aを含む。 -/
theorem allA_paired_primitive_J (A : Set Bool) :
    primitiveDiagnostic pairedM A = @ite (ℕ × ℕ) A.Nonempty (Classical.propDecidable _) (0,1) (0,0) := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_pos hA]; exact paired_primitive_J A hA
  · have ha := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [if_neg Set.not_nonempty_empty,primitiveDiagnostic_eq_blockDefect]
    exact paired_empty_defect

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.periodQuotientEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.periodQuotientEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarsePeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarsePeriod_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarsePeriod_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarseNamedCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.finePeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.finePeriod_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.finePeriod_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fineNamedCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPeriod_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPeriod_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedNamedCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.named_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_named_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarseCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fineCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.subset_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_subset_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.subset_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_subset_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.comparison_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedCoordinateMap
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedCoordinateMap_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.kPeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.kPeriod_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.kPeriod_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coordinateCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedCokernelEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_comparison_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.empty_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_empty_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.allA_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.allA_paired_primitive_J
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
