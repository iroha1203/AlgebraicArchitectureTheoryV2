import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeFiber
import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreePairedGeneration
import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeDiagnostics

/-!
# G-135 W3 paired：同じ原Phiとliteral R

## Implementation notes

原Phiの同名chart/辺と両方の空面型から全三次数同型を生成する。
原fine複体のmを残してpairedに使用する方法は採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- m削除後の原Phiを同じchart/k名で全三次数に比較する。 -/
def pairedPhiEquiv (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    ThreeCochainComplex.CochainEquiv (phiComplex pairedM A c) (phiComplex M A c) where
  e0 := LinearEquiv.refl ℚ _
  e1 := LinearEquiv.refl ℚ _
  e2 := by
    letI := pairedPhiFace_empty A c
    letI := phiFace_empty A c
    change (PhiFace pairedM A c → ℚ) ≃ₗ[ℚ] (PhiFace M A c → ℚ)
    exact LinearEquiv.ofBijective 0 ⟨Function.injective_of_subsingleton _,fun z => ⟨0,Subsingleton.elim _ _⟩⟩
  comm0 _ := rfl
  comm1 _ := by funext f; exact False.elim ((phiFace_empty A c).false f)
/-- 同原paired Rの全商両逆k period。 -/
def pairedRCoordinates (A : Set Bool) (hA : A.Nonempty) : R pairedM A ≃ₗ[ℚ] ℚ :=
  (pairedRFamilyEquiv A).trans ((LinearEquiv.piCongrRight fun c => (pairedPhiEquiv A c).h1Equiv).trans
    (LinearEquiv.ofBijective (phiFamilyPeriod A hA) (phiFamilyPeriod_bijective A hA)))
/-- 同原paired R次元1。 -/
theorem paired_R_dimension (A : Set Bool) (hA : A.Nonempty) : Module.finrank ℚ (R pairedM A) = 1 :=
  (pairedRCoordinates A hA).finrank_eq.trans (Module.finrank_self ℚ)
/-- 同原paired H¹Qもliteral R経由で元k値と全両逆。 -/
def pairedQCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (zeroExtension (restrictionComplex pairedM A)).homology (1 : ℤ) ≃ₗ[ℚ] ℚ :=
  (restrictionStandardHomologyREquiv pairedM A).trans (pairedRCoordinates A hA)
/-- 原paired P標準H²は零、五辺の実微分全射性を使用。 -/
theorem pairedPH2_subsingleton (A : Set Bool) (hA : A.Nonempty) :
    Subsingleton ((zeroExtension (pushforwardComplex pairedM A)).homology (2 : ℤ)) := by
  letI := standardH2_subsingleton_of_surjective pairedPNamedComplex pairedP_d1_surjective
  exact (standardCoordinates (pairedPNamedEquiv A hA) 2).toEquiv.subsingleton_congr.mpr inferInstance
/-- 元paired ε全H¹で(h,0)、Pの元cycleから直接評価。 -/
theorem paired_evaluation_coordinates (A : Set Bool) (hA : A.Nonempty) (z : (pushforwardComplex pairedM A).H1) :
    pairedCoordinates A hA ((evaluationHom pairedM A).h1Map z) = ![pairedPH1Coordinates A hA z,0] := by
  induction z using Submodule.Quotient.induction_on with | _ z =>
    change pairedCoordinates A hA ((evaluationHom pairedM A).h1Map
      ((LinearMap.range (pushforwardComplex pairedM A).boundaryToCycles).mkQ z)) = _
    rw [ThreeCochainComplex.Hom.h1Map_mk]
    funext i
    fin_cases i
    · rfl
    · change evaluation1 pairedM A z.1 (pairedFineEdge A hA 5) = 0
      exact paired_evaluation_k A hA z.1
/-- 空A元P H¹も、原ε単射と元fine空H¹から零。 -/
theorem emptyP_standardH1_subsingleton (N : TargetSupportedNerve qf)
    (M' : IncidenceSupportedComparison qc qf coarser Nc N) :
    Subsingleton ((zeroExtension (pushforwardComplex M' ∅)).homology (1 : ℤ)) := by
  letI : Subsingleton (N.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' (∅ : Set Bool))).H1 := by
    rw [Set.preimage_empty]
    exact WitnessOne.empty_H1_subsingleton qf N
  letI : Subsingleton ((zeroExtension (N.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' (∅ : Set Bool)))).homology (1 : ℤ)) :=
    (oldH1Equiv _).toEquiv.subsingleton_congr.mp inferInstance
  exact Function.Injective.subsingleton (evaluationH1_injective M' ∅)
/-- 同paired η標準H¹は空Aも含め全Aで全単射。 -/
theorem allA_paired_unit_bijective (A : Set Bool) : Function.Bijective (unitH1 pairedM A) := by
  classical
  by_cases hA : A.Nonempty
  · exact paired_unit_bijective A hA
  · have he := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    letI := WitnessOne.empty_H1_subsingleton qc Nc
    letI := emptyP_standardH1_subsingleton pairedNf pairedM
    letI : Subsingleton ((zeroExtension (Nc.targetSubsetComplex ∅)).homology (1 : ℤ)) :=
      (oldH1Equiv _).toEquiv.subsingleton_congr.mp inferInstance
    exact ⟨Function.injective_of_subsingleton _,fun z => ⟨0,Subsingleton.elim _ _⟩⟩
/-- 原空A Rもchart添字空から零。 -/
theorem empty_R_subsingleton : Subsingleton (R M ∅) := by
  letI : IsEmpty (Nc.ChartInTargetSubset ∅) := ⟨fun c => by obtain ⟨t,ht,ha⟩ := c.2; exact ha⟩
  infer_instance
/-- paired原空A Rも零。 -/
theorem paired_empty_R_subsingleton : Subsingleton (R pairedM ∅) := by
  letI : IsEmpty (Nc.ChartInTargetSubset ∅) := ⟨fun c => by obtain ⟨t,ht,ha⟩ := c.2; exact ha⟩
  infer_instance
/-- 原R全A次元、空支持を保持。 -/
theorem allA_R_dimension (A : Set Bool) : Module.finrank ℚ (R M A) = @ite ℕ A.Nonempty (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_pos hA]; exact r_dimension A hA
  · have he := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [if_neg Set.not_nonempty_empty]
    letI := empty_R_subsingleton
    exact Module.finrank_zero_of_subsingleton
/-- paired原R全A次元、空支持を保持。 -/
theorem allA_paired_R_dimension (A : Set Bool) : Module.finrank ℚ (R pairedM A) = @ite ℕ A.Nonempty (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_pos hA]; exact paired_R_dimension A hA
  · have he := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [if_neg Set.not_nonempty_empty]
    letI := paired_empty_R_subsingleton
    exact Module.finrank_zero_of_subsingleton

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPhiEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedRCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_R_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedQCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPH2_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_evaluation_coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.emptyP_standardH1_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.allA_paired_unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.empty_R_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_empty_R_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.allA_R_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.allA_paired_R_dimension
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
