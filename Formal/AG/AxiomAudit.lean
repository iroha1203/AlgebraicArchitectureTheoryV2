import Formal.AG
import Formal.AG.Examples.DerivedPart5
import Formal.AG.LawAlgebra.FiniteExamples
import Formal.Util.AssertStandardAxioms

/-!
Kernel axiom audit entrypoint for PRD-R R1.

This file is intended to be run in CI with:

```bash
lake env lean Formal/AG/AxiomAudit.lean
```

Every declaration in the `AAT.AG.AxiomAudit` namespace is audited by the
`#assert_standard_axioms_only` command at the end of this file: adding an
entry to the namespace is sufficient to place it under the kernel axiom
allowlist check (standard mathlib axioms only). Per-entry `#guard_msgs in
#print axioms` blocks are no longer needed.

The command must remain the last non-empty line of this file; declarations
added after it would escape the audit, and CI checks the tail position
textually.
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

theorem example56LawConflictPackageFiringLawConflict1Nonzero
    {k : Type} [CommRing k]
    (E : FiniteModel.DerivedPart5.Example56LawConflictPackageFiring k) :
    ∃ x : E.lawConflictPackage.LawConflict 1, x ≠ 0 :=
  FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.lawConflict1_nonzero E

theorem example56LawConflictPackageFiringTor1Nonzero
    {k : Type} [CommRing k]
    (E : FiniteModel.DerivedPart5.Example56LawConflictPackageFiring k) :
    ∃ x : Derived.Intersection.mathlibTor
        (Derived.Counterexample.SharedWitnessCoord.ChartRing k)
        (Derived.Counterexample.SharedWitnessCoord.idealU k)
        (Derived.Counterexample.SharedWitnessCoord.idealV k) 1,
      x ≠ 0 :=
  FiniteModel.DerivedPart5.Example56LawConflictPackageFiring.tor1_nonzero E

theorem temporalPseudoCircleNonzero :
    Examples.EvolutionPart9.pseudoCircleMismatch
        Examples.EvolutionPart9.PseudoCircleEdge.ab ≠ 0 :=
  Examples.EvolutionPart9.pseudoCircleMismatch_ab_nonzero

theorem forceCandidateConcreteNonzero :
    Examples.EvolutionPart9.forceCandidateFixture.concreteObstructionValue ≠ 0 :=
  Examples.EvolutionPart9.forceCandidateFixture.concreteObstruction_nonzero

theorem presentedArchitectureFundamentalGroupRelatorMapsToIdentity
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    {G : SingularityMonodromyStack.OperationCategoryData X}
    {R : SingularityMonodromyStack.RefactorEndpointReading G}
    {H : SingularityMonodromyStack.HomotopyGeneratorFamily R}
    {base : G.State}
    (Pi : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup H base)
    {w : Pi.FreeWord} (h : Pi.Relator w) :
    SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedQuotientMap
      Pi w = 1 :=
  SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedRelator_maps_to_identity
    Pi h

theorem presentedArchitectureFundamentalGroupLiftOf
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    {G : SingularityMonodromyStack.OperationCategoryData X}
    {R : SingularityMonodromyStack.RefactorEndpointReading G}
    {H : SingularityMonodromyStack.HomotopyGeneratorFamily R}
    {base : G.State}
    (Pi : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup H base)
    {Y : Type*} [Group Y]
    (f : SingularityMonodromyStack.FormalEdgeStep G -> Y)
    (hrels : ∀ r ∈
      SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedRelators Pi,
        FreeGroup.lift f r = 1)
    (step : SingularityMonodromyStack.FormalEdgeStep G) :
    SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift
      Pi f hrels (PresentedGroup.of step) = f step :=
  SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift_of
    Pi f hrels step

theorem presentedArchitectureFundamentalGroupLiftUnique
    {U : AtomCarrier} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum P k}
    {G : SingularityMonodromyStack.OperationCategoryData X}
    {R : SingularityMonodromyStack.RefactorEndpointReading G}
    {H : SingularityMonodromyStack.HomotopyGeneratorFamily R}
    {base : G.State}
    (Pi : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup H base)
    {Y : Type*} [Group Y]
    (f : SingularityMonodromyStack.FormalEdgeStep G -> Y)
    (hrels : ∀ r ∈
      SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedRelators Pi,
        FreeGroup.lift f r = 1)
    (g :
      (SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.pi1AAT Pi) →* Y)
    (hg : ∀ step : SingularityMonodromyStack.FormalEdgeStep G,
      g (PresentedGroup.of step) = f step)
    (x : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.pi1AAT Pi) :
    g x =
      SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift
        Pi f hrels x :=
  SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.presentedGroupLift_unique
    Pi f hrels g hg x

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

theorem finiteConcreteGeneratorUnitCertificateOneMemSpan :
    (1 :
      MvPolynomial
        LawAlgebra.FiniteExamples.NSdepthExample.Coord Int) ∈
      Ideal.span
        (Set.range LawAlgebra.FiniteExamples.NSdepthExample.unitGenerator) :=
  LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorUnitCertificate_one_mem_span

theorem finiteConcreteGeneratorNSdepthEqOne :
    LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorNSdepthProfile.toNSdepthProfile.NSdepth =
      1 :=
  LawAlgebra.FiniteExamples.NSdepthExample.concreteGeneratorNSdepth_eq_one

theorem coverRelativeCohomologyClassSuccEqIffAdditiveH1ClassEq
    {U : AtomCarrier} {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (x y : K.CechCocycle 1) :
    K.cohomologyClassSucc 0 x = K.cohomologyClassSucc 0 y ↔
      K.additiveH1Class x = K.additiveH1Class y :=
  Cohomology.CoverRelativeCechComplex.cohomologyClassSucc_eq_iff_additiveH1Class_eq
    K x y

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

theorem coverNerveTopologicalDebtCapacityFromComplex
    {N : Cohomology.CoverNerve}
    (D : Cohomology.FiniteNerveCochainComplex N) :
    Module.finrank D.k D.C1 <=
      Module.finrank D.k D.H1 + Module.finrank D.k D.C0 +
        Module.finrank D.k D.C2 :=
  Cohomology.FiniteNerveCochainComplex.topologicalDebtCapacity_fromComplex D

theorem finiteForestEdgeAbsorptionVanishing
    {N : Cohomology.CoverNerve}
    (F : Cohomology.FiniteForestEdgeAbsorptionData N) :
    ∀ x : F.H1, x = 0 :=
  Cohomology.FiniteForestEdgeAbsorptionData.forestVanishing F

theorem derObUOfConDefCoefficientConDefClass
    {A : Type} [CommRing A]
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily A)
    {M : Type} [AddCommGroup M] [Module A M]
    (c : Cohomology.StandardObstruction.ConDef_U A F) (m : M) :
    (Cohomology.StandardObstruction.DerOb_U.ofConDefCoefficient
      (A := A) c m).conDefClass = c :=
  Cohomology.StandardObstruction.DerOb_U.ofConDefCoefficient_conDefClass c m

theorem derObUOfConDefCoefficientCoefficient
    {A : Type} [CommRing A]
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily A)
    {M : Type} [AddCommGroup M] [Module A M]
    (c : Cohomology.StandardObstruction.ConDef_U A F) (m : M) :
    (Cohomology.StandardObstruction.DerOb_U.ofConDefCoefficient
      (A := A) c m).coefficient = m :=
  Cohomology.StandardObstruction.DerOb_U.ofConDefCoefficient_coefficient c m

def finiteSynthesisAATSynthesisPackageEqToPackage :=
  FiniteModel.RepresentationAnalysisPart7.finiteSynthesisAATSynthesisPackage_eq_toPackage

def finiteSynthesisFires :=
  FiniteModel.RepresentationAnalysisPart7.finiteSynthesis_algebraicGeometricAATSynthesis_fires

def lowDegreeRealKernelEquivHarmonic :=
  Measurement.lowDegreeRealComplex_kernel_equiv_harmonicCohomology

def nonzeroBoundaryRealComplexDPrevNonzero :=
  Measurement.nonzeroBoundaryRealComplex_dPrev_nonzero

def nonzeroBoundaryRealHodgeDecompositionFires :=
  Measurement.nonzeroBoundaryRealHodgeDecomposition_fires

def squareFreeRepairSupportNotMemAlexanderDualIffHitsForbidden :=
  Measurement.squareFree_repairSupport_notMemAlexanderDual_iff_hitsForbidden

def squareFreeSingletonQMinimalRepairHittingSet :=
  Measurement.squareFree_singletonQ_minimalRepairHittingSet

def replayZeroTheorem42GlobalTransitionExists :=
  Examples.EvolutionPart9.replay_zero_theorem42_global_transition_exists

def toyForceIntegrable :=
  Examples.EvolutionPart9.toy_force_integrable

def forceCandidateSelectedNonzeroBackedByConcrete :=
  Examples.EvolutionPart9.force_candidate_selected_nonzero_backed_by_concrete

def forceCandidatePackageInhabited :=
  Examples.EvolutionPart9.force_candidate_package_inhabited

def transportDescentZeroToyModelNonempty :=
  @FiniteModel.SingularityMonodromyStackPart6.TransportDescentZeroToyModel.nonempty_of_relationBoundaryZero

def transportDescentNonzeroToyModelNonempty :=
  @FiniteModel.SingularityMonodromyStackPart6.TransportDescentNonzeroToyModel.nonempty_of_not_relationBoundaryZero

end AAT.AG.AxiomAudit

#assert_standard_axioms_only AAT.AG.AxiomAudit
