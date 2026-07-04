import Formal.AG

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

end AAT.AG.AxiomAudit
