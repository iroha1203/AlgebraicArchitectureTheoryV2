import ResearchLean.AG.AtlasCoefficientFiber.WitnessFourLaw
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFourSubdivision
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFourDuplication
import ResearchLean.AG.AtlasCoefficientFiber.FinitePreservationDecision

/-!
# W4：全原入力・全A・二発生Lawの階数表

Implementation notes: Φ商、κ*実像、literal R、標準τ実像と原aの欠損を
同じ入力から計算する。primitive Jは元d0/d1/独立uの有限有理rankに接続する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
open CategoryTheory HomologicalComplex CochainComplex

/-- 元Φの全商零から、同じ全Betti和・κ*像・literal R・τ像を同時に零とする。 -/
theorem fiber_zero_ranks {Source : Type} {qc qf : Reading Source} {h : qc.CoarserThan qf}
    {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
    (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)
    (hp : ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1) :
    (letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
      ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 = 0) ∧
    Module.finrank ℚ (LinearMap.range (kappaStar M A)) = 0 ∧
    Module.finrank ℚ (R M A) = 0 ∧
    Module.finrank ℚ (LinearMap.range (connectingTau M A)) = 0 := by
  letI (c : Nc.ChartInTargetSubset A) := hp c
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  have hk : kappaStar M A = 0 := LinearMap.ext fun x => by
    rw [Subsingleton.elim x 0, map_zero]; rfl
  letI : Subsingleton (R M A) := inferInstance
  have ht : connectingTau M A = 0 := LinearMap.ext fun x => by
    rw [Subsingleton.elim x 0, map_zero]; rfl
  refine ⟨?_,?_,Module.finrank_zero_of_subsingleton,?_⟩
  · have hd (c : Nc.ChartInTargetSubset A) : Module.finrank ℚ (phiComplex M A c).H1 = 0 := Module.finrank_zero_of_subsingleton
    simp only [hd, Finset.sum_const_zero]
  · rw [hk, LinearMap.range_zero]; exact Module.finrank_zero_of_subsingleton
  · rw [ht, LinearMap.range_zero]; exact Module.finrank_zero_of_subsingleton

/-- 元Lawのκ*像・literal R・τ像は、同じ元射の零性と商零から零。 -/
theorem law_zero_ranks {Source : Type} [Fintype Source] {qc qf : Reading Source} {h : qc.CoarserThan qf}
    {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
    (M : IncidenceSupportedComparison qc qf h Nc Nf) (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
    (hk : lawKappaStar M laws ha = 0) (hr : Subsingleton (lawR M laws ha))
    (ht : lawConnectingTau M laws ha = 0) :
    Module.finrank ℚ (LinearMap.range (lawKappaStar M laws ha)) = 0 ∧
    Module.finrank ℚ (lawR M laws ha) = 0 ∧
    Module.finrank ℚ (LinearMap.range (lawConnectingTau M laws ha)) = 0 := by
  letI := hr
  refine ⟨?_, Module.finrank_zero_of_subsingleton, ?_⟩
  · rw [hk, LinearMap.range_zero]; exact Module.finrank_zero_of_subsingleton
  · rw [ht, LinearMap.range_zero]; exact Module.finrank_zero_of_subsingleton

/-- 同じ原plusの全AのΦ/κ*/R/τ階数。 -/
theorem plus_fiber_ranks (A : Set Bool) :
    (letI := Fintype.ofFinite (FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A)
      ∑ c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A, Module.finrank ℚ (phiComplex FaceRelationSubdivision.WitnessOne.rPlus A c).H1 = 0) ∧
    Module.finrank ℚ (LinearMap.range (kappaStar FaceRelationSubdivision.WitnessOne.rPlus A)) = 0 ∧
    Module.finrank ℚ (R FaceRelationSubdivision.WitnessOne.rPlus A) = 0 ∧
    Module.finrank ℚ (LinearMap.range (connectingTau FaceRelationSubdivision.WitnessOne.rPlus A)) = 0 :=
  fiber_zero_ranks FaceRelationSubdivision.WitnessOne.rPlus A (WitnessFourTriangle.plus_phiH1_zero A)

/-- 同じ原minusの全AのΦ/κ*/R/τ階数。 -/
theorem minus_fiber_ranks (A : Set Bool) :
    (letI := Fintype.ofFinite (FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A)
      ∑ c : FaceRelationSubdivision.WitnessOne.N.ChartInTargetSubset A, Module.finrank ℚ (phiComplex FaceRelationSubdivision.WitnessOne.rMinus A c).H1 = 0) ∧
    Module.finrank ℚ (LinearMap.range (kappaStar FaceRelationSubdivision.WitnessOne.rMinus A)) = 0 ∧
    Module.finrank ℚ (R FaceRelationSubdivision.WitnessOne.rMinus A) = 0 ∧
    Module.finrank ℚ (LinearMap.range (connectingTau FaceRelationSubdivision.WitnessOne.rMinus A)) = 0 :=
  fiber_zero_ranks FaceRelationSubdivision.WitnessOne.rMinus A (WitnessFourTriangle.minus_phiH1_zero A)

/-- 同じG134三原入力の全A階数。 -/
theorem subdivision_fiber_ranks (i : FaceRelationSubdivision.WitnessTwo.Case) (A : Set Bool) :
    (letI := Fintype.ofFinite ((FaceRelationSubdivision.WitnessTwo.old i).ChartInTargetSubset A)
      ∑ c : (FaceRelationSubdivision.WitnessTwo.old i).ChartInTargetSubset A, Module.finrank ℚ (phiComplex (FaceRelationSubdivision.WitnessTwo.comparison i) A c).H1 = 0) ∧
    Module.finrank ℚ (LinearMap.range (kappaStar (FaceRelationSubdivision.WitnessTwo.comparison i) A)) = 0 ∧
    Module.finrank ℚ (R (FaceRelationSubdivision.WitnessTwo.comparison i) A) = 0 ∧
    Module.finrank ℚ (LinearMap.range (connectingTau (FaceRelationSubdivision.WitnessTwo.comparison i) A)) = 0 :=
  fiber_zero_ranks (FaceRelationSubdivision.WitnessTwo.comparison i) A (WitnessFourSubdivision.phiH1_zero i A)

/-- 同じG134面複製の全A階数。 -/
theorem duplication_fiber_ranks (A : Set Bool) :
    (letI := Fintype.ofFinite (FaceRelationSubdivision.WitnessThree.N.ChartInTargetSubset A)
      ∑ c : FaceRelationSubdivision.WitnessThree.N.ChartInTargetSubset A, Module.finrank ℚ (phiComplex FaceRelationSubdivision.WitnessThree.comparison A c).H1 = 0) ∧
    Module.finrank ℚ (LinearMap.range (kappaStar FaceRelationSubdivision.WitnessThree.comparison A)) = 0 ∧
    Module.finrank ℚ (R FaceRelationSubdivision.WitnessThree.comparison A) = 0 ∧
    Module.finrank ℚ (LinearMap.range (connectingTau FaceRelationSubdivision.WitnessThree.comparison A)) = 0 :=
  fiber_zero_ranks FaceRelationSubdivision.WitnessThree.comparison A (WitnessFourDuplication.phiH1_zero A)

/-- 同じ原plusの二発生Law階数。 -/
theorem plus_law_fiber_ranks :
    Module.finrank ℚ (LinearMap.range (lawKappaStar FaceRelationSubdivision.WitnessOne.rPlus FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate)) = 0 ∧
    Module.finrank ℚ (lawR FaceRelationSubdivision.WitnessOne.rPlus FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate) = 0 ∧
    Module.finrank ℚ (LinearMap.range (lawConnectingTau FaceRelationSubdivision.WitnessOne.rPlus FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate)) = 0 := law_zero_ranks FaceRelationSubdivision.WitnessOne.rPlus
  FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate
  WitnessFourLaw.plus_kappaStar_zero WitnessFourLaw.plus_R_zero WitnessFourLaw.plus_tau_zero

/-- 同じ原minusの二発生Law階数。 -/
theorem minus_law_fiber_ranks :
    Module.finrank ℚ (LinearMap.range (lawKappaStar FaceRelationSubdivision.WitnessOne.rMinus FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate)) = 0 ∧
    Module.finrank ℚ (lawR FaceRelationSubdivision.WitnessOne.rMinus FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate) = 0 ∧
    Module.finrank ℚ (LinearMap.range (lawConnectingTau FaceRelationSubdivision.WitnessOne.rMinus FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate)) = 0 := law_zero_ranks FaceRelationSubdivision.WitnessOne.rMinus
  FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate
  WitnessFourLaw.minus_kappaStar_zero WitnessFourLaw.minus_R_zero WitnessFourLaw.minus_tau_zero

/-- 同じ原三細分の二発生Law階数。 -/
theorem subdivision_law_fiber_ranks (i : FaceRelationSubdivision.WitnessTwo.Case) :
    Module.finrank ℚ (LinearMap.range (lawKappaStar (FaceRelationSubdivision.WitnessTwo.comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate)) = 0 ∧
    Module.finrank ℚ (lawR (FaceRelationSubdivision.WitnessTwo.comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate) = 0 ∧
    Module.finrank ℚ (LinearMap.range (lawConnectingTau (FaceRelationSubdivision.WitnessTwo.comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate)) = 0 :=
  law_zero_ranks (FaceRelationSubdivision.WitnessTwo.comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate
    (WitnessFourSubdivision.law_kappaStar_zero i) (WitnessFourSubdivision.law_R_zero i) (WitnessFourSubdivision.law_tau_zero i)

/-- 同じ原面複製の二発生Law階数。 -/
theorem duplication_law_fiber_ranks :
    Module.finrank ℚ (LinearMap.range (lawKappaStar FaceRelationSubdivision.WitnessThree.comparison ConnectedFaceWitness.laws ConnectedFaceWitness.adequate)) = 0 ∧
    Module.finrank ℚ (lawR FaceRelationSubdivision.WitnessThree.comparison ConnectedFaceWitness.laws ConnectedFaceWitness.adequate) = 0 ∧
    Module.finrank ℚ (LinearMap.range (lawConnectingTau FaceRelationSubdivision.WitnessThree.comparison ConnectedFaceWitness.laws ConnectedFaceWitness.adequate)) = 0 := law_zero_ranks FaceRelationSubdivision.WitnessThree.comparison
  ConnectedFaceWitness.laws ConnectedFaceWitness.adequate WitnessFourDuplication.law_kappaStar_zero
  WitnessFourDuplication.law_R_zero WitnessFourDuplication.law_tau_zero

/-- 同じ原minus aも空Aを含めた全A。 -/
theorem allA_minus_unit_defect (A : Set Bool) : blockDefect (unitH1 FaceRelationSubdivision.WitnessOne.rMinus A) =
    @ite (ℕ × ℕ) (A = ∅) (Classical.propDecidable _) (0,0) (0,1) :=
  (WitnessFourDiagnostics.defect_eq_unit_of_R_zero FaceRelationSubdivision.WitnessOne.rMinus A (WitnessFourTriangle.minus_R_zero A)).symm.trans
    (WitnessFourDiagnostics.allA_minus_defect A)

/-- 同じ面複製の原a欠損は全Aで零。 -/
theorem duplication_unit_defect (A : Set Bool) :
    blockDefect (unitH1 FaceRelationSubdivision.WitnessThree.comparison A) = (0,0) :=
  (WitnessFourDiagnostics.defect_eq_unit_of_R_zero FaceRelationSubdivision.WitnessThree.comparison A (WitnessFourDuplication.R_zero A)).symm.trans
    (WitnessFourDuplication.defect_zero A)

/-- 同じ面複製の原Law a欠損は零。 -/
theorem duplication_law_unit_defect : blockDefect (lawUnitH1 FaceRelationSubdivision.WitnessThree.comparison
    ConnectedFaceWitness.laws ConnectedFaceWitness.adequate) = (0,0) := by
  apply (blockDefect_eq_zero_iff_bijective _).mpr
  have hh : WitnessFourDuplication.lawUnitEquiv.toLinearMap = lawUnitH1 FaceRelationSubdivision.WitnessThree.comparison
      ConnectedFaceWitness.laws ConnectedFaceWitness.adequate :=
    LinearMap.ext (FaceClone.lawUnitEquiv_apply FaceRelationSubdivision.WitnessThree.N () ConnectedFaceWitness.laws ConnectedFaceWitness.adequate)
  rw [← hh]
  exact WitnessFourDuplication.lawUnitEquiv.bijective

/-- 同じ原plusのd0/d1/独立u有限rank生成J。 -/
theorem plus_primitive_J (A : Set Bool) : primitiveDiagnostic FaceRelationSubdivision.WitnessOne.rPlus A = (0,0) :=
  (primitiveDiagnostic_eq_blockDefect FaceRelationSubdivision.WitnessOne.rPlus A).trans (WitnessFourDiagnostics.plus_defect A)

/-- 同じ原minusのd0/d1/独立u有限rank生成J。 -/
theorem minus_primitive_J (A : Set Bool) : primitiveDiagnostic FaceRelationSubdivision.WitnessOne.rMinus A = @ite (ℕ × ℕ) (A = ∅) (Classical.propDecidable _) (0,0) (0,1) :=
  (primitiveDiagnostic_eq_blockDefect FaceRelationSubdivision.WitnessOne.rMinus A).trans (WitnessFourDiagnostics.allA_minus_defect A)

/-- 同じ原duplicationのd0/d1/独立u有限rank生成J。 -/
theorem duplication_primitive_J (A : Set Bool) : primitiveDiagnostic FaceRelationSubdivision.WitnessThree.comparison A = (0,0) :=
  (primitiveDiagnostic_eq_blockDefect FaceRelationSubdivision.WitnessThree.comparison A).trans (WitnessFourDuplication.defect_zero A)

/-- 同じ原三細分・全Aの有限rank生成J。 -/
theorem subdivision_primitive_J (i : FaceRelationSubdivision.WitnessTwo.Case) (A : Set Bool) :
    primitiveDiagnostic (FaceRelationSubdivision.WitnessTwo.comparison i) A = (0,0) :=
  (primitiveDiagnostic_eq_blockDefect (FaceRelationSubdivision.WitnessTwo.comparison i) A).trans (WitnessFourSubdivision.defect_zero i A)

/-- 同じ原plusの二発生Law有限rank生成J。 -/
theorem plus_primitive_LawJ : primitiveLawDiagnostic FaceRelationSubdivision.WitnessOne.rPlus FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate = (0,0) :=
  (primitiveLawDiagnostic_eq_blockDefect FaceRelationSubdivision.WitnessOne.rPlus FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate).trans WitnessFourLaw.plus_defect

/-- 同じ原minusの二発生Law有限rank生成J。 -/
theorem minus_primitive_LawJ : primitiveLawDiagnostic FaceRelationSubdivision.WitnessOne.rMinus FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate = (0,2) :=
  (primitiveLawDiagnostic_eq_blockDefect FaceRelationSubdivision.WitnessOne.rMinus FaceRelationSubdivision.WitnessOne.laws FaceRelationSubdivision.WitnessOne.coarseAdequate).trans WitnessFourLaw.minus_defect

/-- 同じ原duplicationの二発生Law有限rank生成J。 -/
theorem duplication_primitive_LawJ : primitiveLawDiagnostic FaceRelationSubdivision.WitnessThree.comparison ConnectedFaceWitness.laws ConnectedFaceWitness.adequate = (0,0) :=
  (primitiveLawDiagnostic_eq_blockDefect FaceRelationSubdivision.WitnessThree.comparison ConnectedFaceWitness.laws ConnectedFaceWitness.adequate).trans WitnessFourDuplication.law_defect_zero

/-- 同じ原三細分の二発生Law有限rank生成J。 -/
theorem subdivision_primitive_LawJ (i : FaceRelationSubdivision.WitnessTwo.Case) :
    primitiveLawDiagnostic (FaceRelationSubdivision.WitnessTwo.comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate = (0,0) := by
  rw [primitiveLawDiagnostic_eq_blockDefect]
  change blockDefect ((FaceRelationSubdivision.WitnessTwo.comparison i).generatedComparisonHom ConnectedFaceWitness.laws ConnectedFaceWitness.adequate _).h1Map = (0,0)
  simpa only [← FaceRelationSubdivision.WitnessTwo.law_comparison] using FaceRelationSubdivision.WitnessTwo.law_defect_zero i

end AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable

#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.fiber_zero_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.law_zero_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.plus_fiber_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.minus_fiber_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.subdivision_fiber_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.duplication_fiber_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.plus_law_fiber_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.minus_law_fiber_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.subdivision_law_fiber_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.duplication_law_fiber_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.allA_minus_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.duplication_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.duplication_law_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.plus_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.minus_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.duplication_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.subdivision_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.plus_primitive_LawJ
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.minus_primitive_LawJ
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.duplication_primitive_LawJ
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable.subdivision_primitive_LawJ
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFourRankTable
