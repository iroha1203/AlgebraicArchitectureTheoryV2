import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeGeneration
import ResearchLean.AG.AtlasDefectComposition.EndpointNaturality
import ResearchLean.AG.AtlasDefectComposition.CochainEquivalence

/-!
# G-135 W3：原H²と非零h代表

## Implementation notes

原d1の全像とperiod核を両方向に同定する。H²の商を期待値へ交換する方法は採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- 全三次数原同型から標準homologyへ移す両逆。 -/
def standardCoordinates {C D : ThreeCochainComplex ℚ}
    (e : ThreeCochainComplex.CochainEquiv C D) (n : ℤ) :
    (zeroExtension C).homology n ≃ₗ[ℚ] (zeroExtension D).homology n :=
  (HomologicalComplex.homologyMapIso (cochainEquivZeroExtensionIso e) n).toLinearEquiv
/-- 粗原二面periodはF1−F0。 -/
def secondPeriod : (namedComplex Nc).C2 →ₗ[ℚ] ℚ where
  toFun z := z 1 - z 0
  map_add' z w := by change (z 1 + w 1) - (z 0 + w 0) = (z 1-z 0)+(w 1-w 0); ring
  map_smul' r z := by change r*z 1-r*z 0=r*(z 1-z 0); ring
/-- 原二面periodの核は同じ原d1全像。 -/
theorem secondPeriod_kernel : LinearMap.ker secondPeriod = LinearMap.range (namedComplex Nc).d1 := by
  ext z
  constructor
  · intro hz
    change z 1 - z 0 = 0 at hz
    refine ⟨![z 0,0,0,0],?_⟩
    funext f
    rw [namedComplex_d1_apply]
    change z 0 - 0 + 0 = z f
    fin_cases f <;> dsimp <;> linarith
  · rintro ⟨z,rfl⟩
    change (namedComplex Nc).d1 z 1 - (namedComplex Nc).d1 z 0 = 0
    rw [namedComplex_d1_apply,namedComplex_d1_apply]
    exact sub_self _
/-- 全有理periodは同じ二面値(0,q)で生成。 -/
theorem secondPeriod_surjective : Function.Surjective secondPeriod := by
  intro q; exact ⟨![0,q],by change q-0=q; exact sub_zero _⟩
/-- 全原粗H²商と有理periodの両逆。 -/
def coarseNamedH2Coordinates : ((namedComplex Nc).C2 ⧸ LinearMap.range (namedComplex Nc).d1) ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ secondPeriod_kernel.symm).trans (secondPeriod.quotKerEquivOfSurjective secondPeriod_surjective)
/-- 同商両逆は元代表のF1−F0を読む。 -/
theorem coarseNamedH2Coordinates_mk (z : (namedComplex Nc).C2) :
    coarseNamedH2Coordinates ((LinearMap.range (namedComplex Nc).d1).mkQ z) = z 1 - z 0 := rfl
/-- 原細d1の全射性、f0/f1/mの全値を同時に実現。 -/
theorem fine_d1_surjective : Function.Surjective (namedComplex Nf).d1 := by
  intro z
  refine ⟨![z 0,z 1,0,0,0,z 2 + z 1 - z 0],?_⟩
  funext f
  rw [namedComplex_d1_apply]
  change ![z 0,z 1,0,0,0,z 2+z 1-z 0] (![0,1,5] f) -
    ![z 0,z 1,0,0,0,z 2+z 1-z 0] (![2,2,1] f) +
    ![z 0,z 1,0,0,0,z 2+z 1-z 0] (![3,3,0] f) = z f
  fin_cases f <;> dsimp <;> ring
/-- mだけを除いた同原二面d1も全射。 -/
theorem paired_d1_surjective : Function.Surjective (namedComplex pairedNf).d1 := by
  intro z
  refine ⟨![z 0,z 1,0,0,0,0],?_⟩
  funext f
  rw [namedComplex_d1_apply]
  change ![z 0,z 1,0,0,0,0] (![0,1] f) -
    ![z 0,z 1,0,0,0,0] 2 + ![z 0,z 1,0,0,0,0] 3 = z f
  fin_cases f <;> dsimp <;> ring
/-- 原d1全射から標準H²零を生成する一般API。 -/
theorem standardH2_subsingleton_of_surjective (C : ThreeCochainComplex ℚ) (hs : Function.Surjective C.d1) :
    Subsingleton ((zeroExtension C).homology (2 : ℤ)) := by
  have hr : LinearMap.range C.d1 = ⊤ := LinearMap.range_eq_top.mpr hs
  letI : Subsingleton (C.C2 ⧸ LinearMap.range C.d1) := by rw [hr]; infer_instance
  exact (oldH2Equiv C).toEquiv.subsingleton_congr.mp inferInstance
/-- 非空Aの元粗標準H²と元二面periodの両逆。 -/
def coarseH2Coordinates (A : Set Bool) (hA : A.Nonempty) :
    (zeroExtension (Nc.targetSubsetComplex A)).homology (2 : ℤ) ≃ₗ[ℚ] ℚ :=
  (standardCoordinates (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA) 2).trans
    ((oldH2Equiv (namedComplex Nc)).symm.trans coarseNamedH2Coordinates)
/-- 非空Aの独立P標準H²と元二面periodの両逆。 -/
def pH2Coordinates (A : Set Bool) (hA : A.Nonempty) :
    (zeroExtension (pushforwardComplex M A)).homology (2 : ℤ) ≃ₗ[ℚ] ℚ :=
  (standardCoordinates (pNamedEquiv A hA) 2).trans
    ((oldH2Equiv (namedComplex Nc)).symm.trans coarseNamedH2Coordinates)
/-- 同P原代表は元座標のF1−F0。 -/
theorem pH2Coordinates_mk (A : Set Bool) (hA : A.Nonempty) (z : (pushforwardComplex M A).C2) :
    pH2Coordinates A hA (oldH2Equiv _ ((LinearMap.range (pushforwardComplex M A).d1).mkQ z)) =
      (pNamedEquiv A hA).e2 z 1 - (pNamedEquiv A hA).e2 z 0 := by
  change coarseNamedH2Coordinates ((oldH2Equiv (namedComplex Nc)).symm
    (HomologicalComplex.homologyMap (zeroExtensionMap (pNamedEquiv A hA).toHom) 2
      (oldH2Equiv _ ((LinearMap.range (pushforwardComplex M A).d1).mkQ z)))) = _
  rw [← oldH2Equiv_natural,LinearEquiv.symm_apply_apply,oldH2Map_mk]
  rfl
/-- 元細側標準H²は零、元fine三面の全像を使用。 -/
theorem fineH2_subsingleton (A : Set Bool) (hA : A.Nonempty) :
    Subsingleton ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A))).homology (2 : ℤ)) := by
  letI := standardH2_subsingleton_of_surjective (namedComplex Nf) fine_d1_surjective
  exact (standardCoordinates (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)) 2).toEquiv.subsingleton_congr.mpr inferInstance
/-- mなしfine標準H²も零、同二面の全像を使用。 -/
theorem pairedFineH2_subsingleton (A : Set Bool) (hA : A.Nonempty) :
    Subsingleton ((zeroExtension (pairedNf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A))).homology (2 : ℤ)) := by
  letI := standardH2_subsingleton_of_surjective (namedComplex pairedNf) paired_d1_surjective
  exact (standardCoordinates (fullSubsetNamedEquiv pairedNf (fun _ => rfl) _ (fine_nonempty A hA)) 2).toEquiv.subsingleton_congr.mpr inferInstance
/-- 原P H²次元1。 -/
theorem pH2_dimension (A : Set Bool) (hA : A.Nonempty) : Module.finrank ℚ ((zeroExtension (pushforwardComplex M A)).homology (2 : ℤ)) = 1 :=
  (pH2Coordinates A hA).finrank_eq.trans (Module.finrank_self ℚ)

/-- 粗原h代表は他辺零、hのみ1。 -/
def coarseHCycle (A : Set Bool) : LinearMap.ker (Nc.targetSubsetComplex A).d1 :=
  ⟨fun e => (![0,0,0,1] : Fin 4 → ℚ) e.1,by
    funext f; change (Nc.targetSubsetComplex A).d1 _ f = (0 : ℚ)
    rw [TargetSupportedNerve.targetSubsetComplex_d1_apply]; change (0:ℚ)-0+0=0; ring⟩
/-- 同粗hの全原商類。 -/
def coarseHClass (A : Set Bool) : (Nc.targetSubsetComplex A).H1 :=
  (LinearMap.range (Nc.targetSubsetComplex A).boundaryToCycles).mkQ (coarseHCycle A)
/-- 同原h periodは1。 -/
theorem coarse_h_period (A : Set Bool) (hA : A.Nonempty) : coarseCoordinates A hA (coarseHClass A) = 1 := rfl
/-- 保存に残る粗hは非零。 -/
theorem coarse_h_nonzero (A : Set Bool) (hA : A.Nonempty) : coarseHClass A ≠ 0 := by
  intro hh; have he := congrArg (coarseCoordinates A hA) hh
  rw [coarse_h_period,map_zero] at he; exact one_ne_zero he
/-- 面あり細hは同じ実uで生成、全period1を保つ。 -/
def fineHClass (A : Set Bool) := (M.aSubnerveComparisonHom A).h1Map (coarseHClass A)
/-- 元比較の保存する同h period1。 -/
theorem fine_h_period (A : Set Bool) (hA : A.Nonempty) : fineCoordinates A hA (fineHClass A) = 1 := by
  rw [fineHClass,subset_map,coarse_h_period]
/-- 同じ細hも非零。 -/
theorem fine_h_nonzero (A : Set Bool) (hA : A.Nonempty) : fineHClass A ≠ 0 := by
  intro hh; have he := congrArg (fineCoordinates A hA) hh
  rw [fine_h_period,map_zero] at he; exact one_ne_zero he
/-- mなし実uが送るhは全二座標(1,0)。 -/
theorem paired_h_period (A : Set Bool) (hA : A.Nonempty) : pairedCoordinates A hA
    ((pairedM.aSubnerveComparisonHom A).h1Map (coarseHClass A)) = ![1,0] := by
  rw [paired_subset_map,coarse_h_period]
/-- mなしでも同hは非零。 -/
theorem paired_h_nonzero (A : Set Bool) (hA : A.Nonempty) :
    (pairedM.aSubnerveComparisonHom A).h1Map (coarseHClass A) ≠ 0 := by
  intro hh
  have he := congrArg (fun z => pairedCoordinates A hA z 0) hh
  change pairedCoordinates A hA ((pairedM.aSubnerveComparisonHom A).h1Map (coarseHClass A)) 0 = (pairedCoordinates A hA 0) 0 at he
  rw [paired_h_period,map_zero] at he
  exact one_ne_zero he

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.standardCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.secondPeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.secondPeriod_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.secondPeriod_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarseNamedH2Coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarseNamedH2Coordinates_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fine_d1_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_d1_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.standardH2_subsingleton_of_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarseH2Coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pH2Coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pH2Coordinates_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fineH2_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedFineH2_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pH2_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarseHCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarseHClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarse_h_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarse_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fineHClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fine_h_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fine_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_h_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_h_nonzero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
