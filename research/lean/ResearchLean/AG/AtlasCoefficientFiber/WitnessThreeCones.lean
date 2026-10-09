import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeDiagnostics
import ResearchLean.AG.AtlasCoefficientFiber.ConeSequences
import ResearchLean.AG.AtlasCoefficientFiber.DefectShortExact
import ResearchLean.AG.AtlasDefectComposition.ConeConditional

/-!
# G-135 W3：原総錐とH²比較核

## Implementation notes

原H¹比較の全射性を同じG133錐の指定核射影へ使用する。
τとG133相殺の種類を保ち、相殺をτの代用にする経路は採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- 原u標準H¹の全単射、元H¹商の同じ比較を移す。 -/
theorem standard_comparison_bijective (A : Set Bool) (hA : A.Nonempty) :
    Function.Bijective (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) (1 : ℤ)).hom :=
  (LinearConjugation.bijective_iff _ _ (oldH1Equiv _) (oldH1Equiv _)
    (oldH1Equiv_natural (M.aSubnerveComparisonHom A))).mp (comparison_bijective A hA)
/-- 同原uのH²射は細側H²零により零。 -/
theorem standard_comparison2_zero (A : Set Bool) (hA : A.Nonempty) :
    (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) (2 : ℤ)).hom = 0 := by
  letI := fineH2_subsingleton A hA
  exact Subsingleton.elim _ _
/-- 同原H²比較核は元粗二面periodと両逆。 -/
def comparisonH2KernelCoordinates (A : Set Bool) (hA : A.Nonempty) :
    LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) (2 : ℤ)).hom ≃ₗ[ℚ] ℚ :=
  (LinearEquiv.ofBijective (LinearMap.ker (HomologicalComplex.homologyMap
    (zeroExtensionMap (M.aSubnerveComparisonHom A)) (2 : ℤ)).hom).subtype
      ⟨Submodule.injective_subtype _,fun z => ⟨⟨z,by rw [LinearMap.mem_ker,standard_comparison2_zero A hA]; rfl⟩,rfl⟩⟩).trans
    (coarseH2Coordinates A hA)
/-- 同原総錐標準H¹は指定G133射影を通じ元二面periodと両逆。 -/
def totalConeH1Coordinates (A : Set Bool) (hA : A.Nonempty) : (totalCone M A).homology (1 : ℤ) ≃ₗ[ℚ] ℚ :=
  (coneKernelProjectionEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) 1
    (standard_comparison_bijective A hA).2).trans (comparisonH2KernelCoordinates A hA)
/-- 原総錐H¹次元1、uのH¹欠損零と区別する。 -/
theorem totalConeH1_dimension (A : Set Bool) (hA : A.Nonempty) : Module.finrank ℚ ((totalCone M A).homology (1 : ℤ)) = 1 :=
  (totalConeH1Coordinates A hA).finrank_eq.trans (Module.finrank_self ℚ)
/-- 同じ原η/εのG133相殺は全Aで零。 -/
theorem cancellation_zero (A : Set Bool) : DefectSequence.cancellation (unitH1 M A) (evaluationH1 M A) = 0 :=
  coefficientCancellation_zero M A
/-- mなしでも同じ原G133相殺は零。 -/
theorem paired_cancellation_zero (A : Set Bool) : DefectSequence.cancellation (unitH1 pairedM A) (evaluationH1 pairedM A) = 0 :=
  coefficientCancellation_zero pairedM A

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.standard_comparison_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.standard_comparison2_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.comparisonH2KernelCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.totalConeH1Coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.totalConeH1_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.cancellation_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_cancellation_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
