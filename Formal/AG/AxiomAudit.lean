import Formal.AG
import Formal.AG.LawAlgebra.FiniteExamples

/-!
Kernel axiom audit entrypoint for PRD-R R1.

This file is intended to be run in CI with:

```bash
lake env lean Formal/AG/AxiomAudit.lean
```

The target list starts with declarations touched by the R1 reduction-compiler
tactic removal. Later PRD-R hardening PRs can extend this list additively.
-/

namespace AAT.AG.AxiomAudit

open CategoryTheory

theorem boundaryCocycleNonzero :
    Cohomology.FiniteExamples.PseudoCircleGolden.boundaryCocycle
        Cohomology.FiniteExamples.PseudoCircleGolden.BoundaryEdge.AB ≠ 0 :=
  Cohomology.FiniteExamples.PseudoCircleGolden.boundaryCocycle_AB_nonzero

theorem derivedG5AllDegree :
    ∀ n,
      (FiniteModel.DerivedPart5.sharedWitnessQuotientHilbertSeries *
        FiniteModel.DerivedPart5.sharedWitnessQuotientHilbertSeries).coeff n =
      (FiniteModel.DerivedPart5.sharedWitnessAmbientHilbertSeries *
        FiniteModel.DerivedPart5.sharedWitnessConflictAlternatingSeries).coeff n :=
  FiniteModel.DerivedPart5.sharedWitnessG5_all_degree_coefficient_identity

theorem temporalPseudoCircleNonzero :
    Examples.EvolutionPart9.pseudoCircleMismatch
        Examples.EvolutionPart9.PseudoCircleEdge.ab ≠ 0 :=
  Examples.EvolutionPart9.pseudoCircleMismatch_ab_nonzero

theorem forceCandidateConcreteNonzero :
    Examples.EvolutionPart9.forceCandidateFixture.concreteObstructionValue ≠ 0 :=
  Examples.EvolutionPart9.forceCandidateFixture.concreteObstruction_nonzero

theorem concreteThreeReadingAgreementRequiredLaw {U : AtomCarrier}
    (A : ArchitectureObject U) (LU : LawUniverse U) :
    (SemanticLawful A LU ↔
        NoRequiredObstruction A (requiredLawWitnessFamily LU)) ∧
      (NoRequiredObstruction A (requiredLawWitnessFamily LU) ↔
        RequiredSignatureAxesZero A (requiredLawSignatureAxes LU)) ∧
        (SemanticLawful A LU ↔
          RequiredSignatureAxesZero A (requiredLawSignatureAxes LU)) :=
  AAT.AG.concreteThreeReadingAgreement A LU

theorem finiteAcyclicConcreteThreeReadingAgreement :
    (SemanticLawful FiniteModel.acyclicObject FiniteModel.lawUniverse ↔
        NoRequiredObstruction FiniteModel.acyclicObject
          FiniteModel.concreteNoCycleWitnessFamily) ∧
      (NoRequiredObstruction FiniteModel.acyclicObject
          FiniteModel.concreteNoCycleWitnessFamily ↔
        RequiredSignatureAxesZero FiniteModel.acyclicObject
          FiniteModel.concreteNoCycleSignatureAxes) ∧
        (SemanticLawful FiniteModel.acyclicObject FiniteModel.lawUniverse ↔
          RequiredSignatureAxesZero FiniteModel.acyclicObject
            FiniteModel.concreteNoCycleSignatureAxes) :=
  FiniteModel.acyclic_concreteThreeReadingAgreement

theorem finiteCyclicConcreteThreeReadingFires :
    (¬ SemanticLawful FiniteModel.object FiniteModel.lawUniverse) ∧
      (∃ witness : FiniteModel.concreteNoCycleWitnessFamily.Witness,
        FiniteModel.concreteNoCycleWitnessFamily.badWitness FiniteModel.object
          witness) ∧
        ¬ RequiredSignatureAxesZero FiniteModel.object
          FiniteModel.concreteNoCycleSignatureAxes :=
  FiniteModel.object_concreteThreeReadingAgreement_fires

theorem finiteCorePackageFromAxiomRealizationNoHEq :
    ∃ core : AATCorePackage FiniteModel.carrier,
      core.axioms = FiniteModel.axiomSystem ∧
        core.family = FiniteModel.allFamily ∧
          core.configuration = FiniteModel.configuration ∧
            core.object = FiniteModel.object ∧
              core.configuration.family = core.family ∧
                core.object.configuration = core.configuration ∧
                  core.lawUniverse = FiniteModel.lawUniverse ∧
                    core.obstructionLaw = FiniteModel.noCycleLaw ∧
                      core.signature = FiniteModel.signature :=
  FiniteModel.corePackageFromAxiomRealization_exists_noHEq

theorem finiteSeedWitnessClosureAdmissible :
    Site.AdmissibleCover FiniteModel.siteCoverageRequirements FiniteModel.siteOverlap
      FiniteModel.siteSeedWitnessClosureCover.toAATCoverageFamily.toCoverageFamily :=
  FiniteModel.siteSeedWitnessClosureCover_admissible

theorem finiteSeedWitnessClosureUAdequate :
    Site.UAdequateCover FiniteModel.siteAdequacyRequirements
      FiniteModel.siteSeedWitnessClosureCover.toAATCoverageFamily :=
  FiniteModel.siteSeedWitnessClosureCover_uAdequate

theorem finiteRestrictionQuotientFiniteMeetPoset :
    ∃ site : Site.QuotientFiniteMeetPosetCategory
        (Site.contextMorphismPreorderCategory FiniteModel.object),
      site =
        Site.quotientFiniteMeetPosetCategoryOf
          (Site.contextMorphismPreorderCategory FiniteModel.object)
          (Site.productContextFiniteMeet (A := FiniteModel.object)) :=
  FiniteModel.siteRestrictionQuotientFiniteMeetPosetCategory_fromFiniteMeet

theorem finiteContextMorphismRolesConcrete :
    (FiniteModel.siteContextIdentityMorphism FiniteModel.siteContext).IsRestriction ∧
      (FiniteModel.siteContextIdentityMorphism FiniteModel.siteContext).IsProjection ∧
        (FiniteModel.siteContextIdentityMorphism FiniteModel.siteContext).IsRefinement ∧
          (FiniteModel.siteContextIdentityMorphism FiniteModel.siteContext).IsBaseChange :=
  FiniteModel.siteContextIdentityMorphism_rolesConcrete

theorem finiteTwoPatchCoverUAdequate :
    Site.UAdequateCover FiniteModel.twoPatchAdequacyRequirements
      FiniteModel.twoPatchCover :=
  FiniteModel.twoPatchCover_uAdequate

theorem finiteTwoPatchUnitDescent :
    Site.AATDescent FiniteModel.twoPatchSite FiniteModel.twoPatchUnitPresheaf
      (CategoryTheory.Sieve.generate FiniteModel.twoPatchCover.presieve) :=
  FiniteModel.twoPatchUnit_descent

theorem finiteTwoPatchSheafificationGap :
    Site.AATSheafificationGap FiniteModel.twoPatchSheafificationComparison :=
  FiniteModel.twoPatchSheafificationGap

theorem finiteTwoPatchCechDifferentialNonzero :
    FiniteModel.twoPatchCechComplex.differential 0
      FiniteModel.twoPatchSeparatedCochain PUnit.unit = true :=
  FiniteModel.twoPatchSeparatedCochain_differential_nonzero

theorem finiteSiteTopologyEqCoverageToGrothendieck :
    FiniteModel.site.topology =
      (Site.admissiblePrecoverage
        FiniteModel.siteCoverageRequirements FiniteModel.siteOverlap).toCoverage.toGrothendieck :=
  FiniteModel.siteTopology_eq_coverage_toGrothendieck

theorem finiteAcyclicLocalSectionLawfulFromWitnessIdeals :
    AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicLocalSectionData.Lawful :=
  AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicLocalSection_lawful_from_witnessIdeals

theorem finiteAcyclicSectionPrimeMapMemLocalLawfulLocus
    (p : PrimeSpectrum Int) :
    AAT.AG.LawAlgebra.LawfulLocus.localSectionPrimeMap
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.CycleRing
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cycleWitnessIdealFamily
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicLocalSectionData p ∈
      AAT.AG.LawAlgebra.LawfulLocus.localLawfulLocus
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.CycleRing
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cycleWitnessIdealFamily :=
  AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclic_sectionPrimeMap_mem_localLawfulLocus p

theorem structureSheafMathlibSheafificationLiftUnique
    {U : AtomCarrier} {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type} [CommRing k]
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (raw : LawAlgebra.AlgebraValuedAATPresheaf S k)
    (F : LawAlgebra.LawAlgebraSheaf S k) (η : raw ⟶ F.val) :
    ∃! lift : (sheafify S.topology raw ⟶ F.val),
      toSheafify S.topology raw ≫ lift = η :=
  LawAlgebra.LawAlgebraSheafificationBridge.mathlib_sheafification_lift_unique raw F η

theorem schemeSingleAffineSpecCompatibilityAllConditions
    {U : AtomCarrier} {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type} [CommRing k]
    (T : LawAlgebra.Scheme.RingedAATTopos S k)
    (C : LawAlgebra.AffineChart.AffineAATChart k)
    (hT :
      T.forgetfulLocallyRingedSpace =
        LawAlgebra.Scheme.affineChartMathlibSpecLocallyRingedSpace k C)
    (i j : (LawAlgebra.Scheme.ArchitectureScheme.singleAffineSpec S k T C hT).ChartIndex) :
    LawAlgebra.Scheme.ChartCompatibility.allConditions k
      ((LawAlgebra.Scheme.ArchitectureScheme.singleAffineSpec S k T C hT).compatibility i j) :=
  LawAlgebra.Scheme.ArchitectureScheme.singleAffineSpec_compatibility_allConditions
    S k T C hT i j

theorem canonicalTupleStandardFinitePosetCechComplexDComp
    {U : AtomCarrier} {A : ArchitectureObject U} {S : Site.AATSite A}
    {geometry : Site.FinitePosetCoverGeometry S}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry)
    (Ob : Cohomology.ObstructionSheaf S) :
    ∀ (n : Nat)
      (cochain :
        Site.FinitePosetCechCochain
          (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime Ob) n),
      (Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex
          tupleGeometry Ob).differential (n + 1)
          ((Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex
            tupleGeometry Ob).differential n cochain) =
        Site.FinitePosetCechZeroCochain
          (Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex
            tupleGeometry Ob).additive (n + 2) :=
  Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex_differential_comp
    tupleGeometry Ob

/--
info: 'AAT.AG.AxiomAudit.boundaryCocycleNonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms boundaryCocycleNonzero

/--
info: 'AAT.AG.AxiomAudit.derivedG5AllDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms derivedG5AllDegree

/--
info: 'AAT.AG.AxiomAudit.temporalPseudoCircleNonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms temporalPseudoCircleNonzero

/--
info: 'AAT.AG.AxiomAudit.forceCandidateConcreteNonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms forceCandidateConcreteNonzero

/--
info: 'AAT.AG.AxiomAudit.concreteThreeReadingAgreementRequiredLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms concreteThreeReadingAgreementRequiredLaw

/--
info: 'AAT.AG.AxiomAudit.finiteAcyclicConcreteThreeReadingAgreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms finiteAcyclicConcreteThreeReadingAgreement

/--
info: 'AAT.AG.AxiomAudit.finiteCyclicConcreteThreeReadingFires' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms finiteCyclicConcreteThreeReadingFires

/--
info: 'AAT.AG.AxiomAudit.finiteCorePackageFromAxiomRealizationNoHEq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms finiteCorePackageFromAxiomRealizationNoHEq

/--
info: 'AAT.AG.AxiomAudit.finiteSeedWitnessClosureAdmissible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms finiteSeedWitnessClosureAdmissible

/--
info: 'AAT.AG.AxiomAudit.finiteSeedWitnessClosureUAdequate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms finiteSeedWitnessClosureUAdequate

/--
info: 'AAT.AG.AxiomAudit.finiteRestrictionQuotientFiniteMeetPoset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms finiteRestrictionQuotientFiniteMeetPoset

/--
info: 'AAT.AG.AxiomAudit.finiteContextMorphismRolesConcrete' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms finiteContextMorphismRolesConcrete

/--
info: 'AAT.AG.AxiomAudit.finiteTwoPatchCoverUAdequate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms finiteTwoPatchCoverUAdequate

/--
info: 'AAT.AG.AxiomAudit.finiteTwoPatchUnitDescent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms finiteTwoPatchUnitDescent

/--
info: 'AAT.AG.AxiomAudit.finiteTwoPatchSheafificationGap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms finiteTwoPatchSheafificationGap

/--
info: 'AAT.AG.AxiomAudit.finiteTwoPatchCechDifferentialNonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms finiteTwoPatchCechDifferentialNonzero

/--
info: 'AAT.AG.AxiomAudit.finiteSiteTopologyEqCoverageToGrothendieck' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms finiteSiteTopologyEqCoverageToGrothendieck

/--
info: 'AAT.AG.AxiomAudit.finiteAcyclicLocalSectionLawfulFromWitnessIdeals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms finiteAcyclicLocalSectionLawfulFromWitnessIdeals

/--
info: 'AAT.AG.AxiomAudit.finiteAcyclicSectionPrimeMapMemLocalLawfulLocus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms finiteAcyclicSectionPrimeMapMemLocalLawfulLocus

/--
info: 'AAT.AG.AxiomAudit.structureSheafMathlibSheafificationLiftUnique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms structureSheafMathlibSheafificationLiftUnique

/--
info: 'AAT.AG.AxiomAudit.schemeSingleAffineSpecCompatibilityAllConditions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms schemeSingleAffineSpecCompatibilityAllConditions

/--
info: 'AAT.AG.AxiomAudit.canonicalTupleStandardFinitePosetCechComplexDComp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canonicalTupleStandardFinitePosetCechComplexDComp

end AAT.AG.AxiomAudit
