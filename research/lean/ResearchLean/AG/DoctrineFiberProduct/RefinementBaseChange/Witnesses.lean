import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Supply
import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChangeSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.ExactBottomCoverageClassification

/-! # Support-stratified G-114 witnesses -/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-- The strict finite G-101 refinement over an unpointed identity cospan. -/
noncomputable def activeForwardOnlyConfiguration :
    RefinementBCConfiguration FiniteModel.carrier where
  sOnePrime := FiniteModel.extractionDoctrine
  sOne := refinementTargetDoctrine
  sTwo := refinementTargetDoctrine
  bottom := refinementTargetDoctrine
  fst := (𝟙 refinementTargetPoint :
    refinementTargetPoint ⟶ refinementTargetPoint).doctrineHom
  snd := (𝟙 refinementTargetPoint :
    refinementTargetPoint ⟶ refinementTargetPoint).doctrineHom
  refinement := finiteExtractionRefinement

/-- The selected strict source and matching second source. -/
noncomputable def activeForwardOnlySource :
    activeForwardOnlyConfiguration.CompatibleSource where
  sourcePrime := FiniteModel.ExtractionSource.withoutComponentC
  sourceTwo := FiniteModel.ExtractionSource.withoutComponentC
  bottom_eq := rfl

/-- The target package makes the strict forward-only example active. -/
theorem activeForwardOnly_active : Active activeForwardOnlyConfiguration := by
  exact ⟨⟨activeForwardOnlySource,
    ⟨refinementTargetPackage, refinementTargetPackage_point⟩⟩⟩

/-- The selected component-C extraction explicitly violates the fixed condition. -/
theorem activeForwardOnly_not_condition :
    ¬ ConfigurationRealizedLocusExtractionReflecting
      activeForwardOnlyConfiguration := by
  intro condition
  have obstruction := finiteExtractionRefinement_not_reflecting
  exact obstruction.2 <| condition activeForwardOnlySource
    ⟨⟨refinementTargetPackage, refinementTargetPackage_point⟩⟩
    FiniteModel.FiniteAtom.componentC obstruction.1

/-- Hence the active strict example admits no refinement base-change regime. -/
theorem activeForwardOnly_no_regime :
    ¬ Nonempty (RefinementBCRegime activeForwardOnlyConfiguration) := by
  intro regime
  exact activeForwardOnly_not_condition
    ((refinementBCRegime_iff_configurationCondition
      activeForwardOnlyConfiguration).mp regime)

/-- The explicit component-C extraction difference underlying the negative witness. -/
theorem activeForwardOnly_extraction_difference :
    (activeForwardOnlyConfiguration.targetPointAt activeForwardOnlySource).doctrine.extracts
        (activeForwardOnlyConfiguration.targetPointAt activeForwardOnlySource).source
        ((activeForwardOnlyConfiguration.baseRefinementAt
          activeForwardOnlySource).doctrineHom.atomMap
            FiniteModel.FiniteAtom.componentC) ∧
      ¬ (activeForwardOnlyConfiguration.sourcePointAt
          activeForwardOnlySource).doctrine.extracts
        (activeForwardOnlyConfiguration.sourcePointAt
          activeForwardOnlySource).source
        FiniteModel.FiniteAtom.componentC := by
  simpa [activeForwardOnlyConfiguration, activeForwardOnlySource,
    RefinementBCConfiguration.targetPointAt,
    RefinementBCConfiguration.sourcePointAt,
    RefinementBCConfiguration.baseRefinementAt] using
      finiteExtractionRefinement_not_reflecting

/-- The strict forward-only witness has genuinely different base doctrines. -/
theorem activeForwardOnly_base_doctrines_ne :
    activeForwardOnlyConfiguration.sOnePrime ≠
      activeForwardOnlyConfiguration.sOne := by
  intro hdoctrine
  let HasFailure := fun D : ExtractionDoctrine FiniteModel.carrier =>
    ∃ source : D.Source,
      ¬ D.extracts source FiniteModel.FiniteAtom.componentC
  have sourceFailure : HasFailure activeForwardOnlyConfiguration.sOnePrime :=
    ⟨activeForwardOnlySource.sourcePrime,
      activeForwardOnly_extraction_difference.2⟩
  have targetFailure : HasFailure activeForwardOnlyConfiguration.sOne :=
    hdoctrine ▸ sourceFailure
  rcases targetFailure with ⟨source, failure⟩
  exact failure ⟨trivial, trivial, trivial, trivial⟩

/-- The generated pulled square retains the same explicit extraction difference. -/
theorem activeForwardOnly_pulled_extraction_difference :
    (activeForwardOnlyConfiguration.pullbackTargetAt
        activeForwardOnlySource).doctrine.extracts
      (activeForwardOnlyConfiguration.pullbackTargetAt
        activeForwardOnlySource).source
      ((activeForwardOnlyConfiguration.pulledRefinementAt
        activeForwardOnlySource).doctrineHom.atomMap
          FiniteModel.FiniteAtom.componentC) ∧
    ¬ (activeForwardOnlyConfiguration.pullbackSourceAt
        activeForwardOnlySource).doctrine.extracts
      (activeForwardOnlyConfiguration.pullbackSourceAt
        activeForwardOnlySource).source
      FiniteModel.FiniteAtom.componentC := by
  constructor
  · exact ⟨trivial, trivial, trivial, trivial⟩
  · exact FiniteModel.componentC_not_extracted_withoutComponentC

/-- The mixed pulled source and exact pulled target doctrines are unequal. -/
theorem activeForwardOnly_pulled_doctrines_ne :
    (activeForwardOnlyConfiguration.pullbackSourceAt
        activeForwardOnlySource).doctrine ≠
      (activeForwardOnlyConfiguration.pullbackTargetAt
        activeForwardOnlySource).doctrine := by
  intro hdoctrine
  let HasFailure := fun D : ExtractionDoctrine FiniteModel.carrier =>
    ∃ source : D.Source,
      ¬ D.extracts source FiniteModel.FiniteAtom.componentC
  have sourceFailure : HasFailure
      (activeForwardOnlyConfiguration.pullbackSourceAt
        activeForwardOnlySource).doctrine :=
    ⟨(activeForwardOnlyConfiguration.pullbackSourceAt
        activeForwardOnlySource).source,
      activeForwardOnly_pulled_extraction_difference.2⟩
  have targetFailure : HasFailure
      (activeForwardOnlyConfiguration.pullbackTargetAt
        activeForwardOnlySource).doctrine :=
    hdoctrine ▸ sourceFailure
  rcases targetFailure with ⟨source, failure⟩
  exact failure ⟨trivial, trivial, trivial, trivial⟩

/-- Card-fixed typed nontriviality packet for the active forward-only example. -/
theorem activeForwardOnly_nontriviality :
    activeForwardOnlyConfiguration.sOnePrime ≠
        activeForwardOnlyConfiguration.sOne ∧
      (activeForwardOnlyConfiguration.pullbackSourceAt
          activeForwardOnlySource).doctrine ≠
        (activeForwardOnlyConfiguration.pullbackTargetAt
          activeForwardOnlySource).doctrine ∧
      ∃ atom : FiniteModel.carrier.Atom,
        (activeForwardOnlyConfiguration.targetPointAt
          activeForwardOnlySource).doctrine.extracts
          (activeForwardOnlyConfiguration.targetPointAt
            activeForwardOnlySource).source
          ((activeForwardOnlyConfiguration.baseRefinementAt
            activeForwardOnlySource).doctrineHom.atomMap atom) ∧
        ¬ (activeForwardOnlyConfiguration.sourcePointAt
          activeForwardOnlySource).doctrine.extracts
          (activeForwardOnlyConfiguration.sourcePointAt
            activeForwardOnlySource).source atom := by
  exact ⟨activeForwardOnly_base_doctrines_ne,
    activeForwardOnly_pulled_doctrines_ne,
    FiniteModel.FiniteAtom.componentC,
    activeForwardOnly_extraction_difference⟩

/-! ## Active reverse witness -/

/-- A singleton all-admitting second endpoint, used to select only the `all` source. -/
def activeReverseSecondDoctrine : ExtractionDoctrine FiniteModel.carrier where
  Source := PUnit
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ _ _ => True
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- Exact singleton leg landing at the all-admitting bottom source. -/
def activeReverseSecondLeg :
    ExactDoctrineHom activeReverseSecondDoctrine refinementTargetDoctrine where
  sourceMap := fun _ => FiniteModel.ExtractionSource.all
  atomEquiv := Equiv.refl _
  normalize_eq := by intro source; cases source; rfl
  extraction_iff := by
    intro source atom
    cases source
    change (True ∧ True ∧ True ∧ True) ↔ (True ∧ True ∧ True ∧ True)
    simp

/-- The nonexact refinement with compatibility restricted to its reflecting source. -/
noncomputable def activeReverseConfiguration :
    RefinementBCConfiguration FiniteModel.carrier where
  sOnePrime := FiniteModel.extractionDoctrine
  sOne := refinementTargetDoctrine
  sTwo := activeReverseSecondDoctrine
  bottom := refinementTargetDoctrine
  fst := (𝟙 refinementTargetPoint :
    refinementTargetPoint ⟶ refinementTargetPoint).doctrineHom
  snd := activeReverseSecondLeg
  refinement := finiteExtractionRefinement

/-- The unique compatible source uses the all-extracting finite source. -/
noncomputable def activeReverseSource : activeReverseConfiguration.CompatibleSource where
  sourcePrime := FiniteModel.ExtractionSource.all
  sourceTwo := PUnit.unit
  bottom_eq := rfl

/-- Every compatible source is forced to be the all-extracting source. -/
theorem activeReverseSource_eq_all
    (p : activeReverseConfiguration.CompatibleSource) :
    p.sourcePrime = FiniteModel.ExtractionSource.all := by
  simpa [activeReverseConfiguration, activeReverseSecondLeg,
    finiteExtractionRefinement] using p.bottom_eq

/-- The fixed condition holds at every compatible source of the reverse witness. -/
theorem activeReverse_condition :
    ConfigurationRealizedLocusExtractionReflecting activeReverseConfiguration := by
  intro p _support atom _extracted
  have hp := activeReverseSource_eq_all p
  change FiniteModel.extractionDoctrine.extracts p.sourcePrime atom
  rw [hp]
  exact ⟨trivial, Or.inl rfl, trivial, trivial⟩

/-- The reverse witness has a generated configuration-wide regime. -/
noncomputable def activeReverseRegime :
    RefinementBCRegime activeReverseConfiguration :=
  refinementBCRegimeOfCondition activeReverseConfiguration activeReverse_condition

/-- The generated mixed square has a genuinely nonidentity horizontal edge. -/
theorem activeReverse_pulledRefinement_atom_nonidentity :
    (activeReverseConfiguration.pulledRefinementAt activeReverseSource).doctrineHom.atomMap
        FiniteModel.FiniteAtom.componentA ≠
      FiniteModel.FiniteAtom.componentA := by
  intro heq
  change refinementAtomMap FiniteModel.FiniteAtom.componentA =
    FiniteModel.FiniteAtom.componentA at heq
  rw [refinementAtomMap_componentA] at heq
  exact FiniteModel.FiniteAtom.noConfusion heq

/-- The selected target point at the reverse witness. -/
noncomputable def activeReverseTargetPoint : ExtractionInstance FiniteModel.carrier :=
  activeReverseConfiguration.targetPointAt activeReverseSource

/-- Exact repointing of the existing target package to the selected `all` source. -/
noncomputable def activeReverseTargetRepoint :
    refinementTargetPoint ⟶ activeReverseTargetPoint where
  doctrineHom := {
    sourceMap := fun _ => FiniteModel.ExtractionSource.all
    atomEquiv := Equiv.refl _
    normalize_eq := by intro source; cases source <;> rfl
    extraction_iff := by
      intro source atom
      cases source <;>
        change (True ∧ True ∧ True ∧ True) ↔ (True ∧ True ∧ True ∧ True) <;>
        simp
  }
  source_eq := rfl

/-- An actual package over the selected active reverse target. -/
noncomputable def activeReverseTargetPackage : CoreFiber activeReverseTargetPoint :=
  coreFiberTransportObj activeReverseTargetRepoint
    ⟨refinementTargetPackage, refinementTargetPackage_point⟩

/-- The selected reverse configuration is active. -/
theorem activeReverse_active : Active activeReverseConfiguration := by
  exact ⟨⟨activeReverseSource, activeReverseTargetPackage⟩⟩

/-- The active reverse fixture supplies both support and the generated regime. -/
theorem activeReverse_activeRegimeAvailable :
    ActiveRegimeAvailable activeReverseConfiguration :=
  ⟨activeReverse_active, ⟨activeReverseRegime⟩⟩

/-- The underlying strict refinement remains outside the exact comparison image. -/
theorem activeReverse_outside_exact_image :
    ¬ ∃ exact : ExactDoctrineHom FiniteModel.extractionDoctrine
        refinementTargetDoctrine,
      (doctrineToRefinement FiniteModel.carrier).map exact =
        activeReverseConfiguration.refinement := by
  simpa [activeReverseConfiguration] using
    finiteExtractionRefinement_not_in_comparison_image

/-- Realized-support reflection is strictly broader than the exact comparison image. -/
theorem realizedReflection_strictly_broader_than_exactImage :
    ConfigurationRealizedLocusExtractionReflecting activeReverseConfiguration ∧
      ¬ RefinementExactComparisonImage activeReverseConfiguration := by
  refine ⟨activeReverse_condition, ?_⟩
  simpa [RefinementExactComparisonImage, activeReverseConfiguration,
    doctrineToRefinement] using activeReverse_outside_exact_image

/-- The regime-generated lift at the fixed target package. -/
noncomputable def activeReverseLift :
    RefinementCartesianLift
      (activeReverseConfiguration.baseRefinementAt activeReverseSource)
      activeReverseTargetPackage :=
  (activeReverseRegime activeReverseSource).baseCleavage.lift
    activeReverseTargetPackage

/-- The lift edge visibly moves `componentA` to `componentB`. -/
theorem activeReverseLift_atom_nonidentity :
    activeReverseLift.hom.upper.atomEquiv FiniteModel.FiniteAtom.componentA ≠
      FiniteModel.FiniteAtom.componentA := by
  intro heq
  letI := activeReverseLift.isStronglyCartesian
  have hfac := CategoryTheory.IsHomLift.fac'
    (refinementPackageProjection FiniteModel.carrier)
    (activeReverseConfiguration.baseRefinementAt activeReverseSource)
    activeReverseLift.hom
  have hbaseAtom := congrArg
    (fun base => base.doctrineHom.atomMap FiniteModel.FiniteAtom.componentA) hfac
  have hbaseAtom' :
      activeReverseLift.hom.base.doctrineHom.atomMap
          FiniteModel.FiniteAtom.componentA =
        finiteExtractionRefinement.atomMap FiniteModel.FiniteAtom.componentA := by
    simpa [refinementPackageProjection, pointedRefinementCategory,
      PointedRefinementHom.comp, refinementHomComp,
      activeReverseConfiguration, activeReverseSource,
      RefinementBCConfiguration.baseRefinementAt] using hbaseAtom
  have hupperAtom :
      activeReverseLift.hom.upper.atomEquiv FiniteModel.FiniteAtom.componentA =
        finiteExtractionRefinement.atomMap FiniteModel.FiniteAtom.componentA := by
    rw [activeReverseLift.hom.atomEquiv_eq,
      activeReverseLift.hom.base.doctrineHom.atomEquiv_apply]
    exact hbaseAtom'
  rw [hupperAtom] at heq
  change refinementAtomMap FiniteModel.FiniteAtom.componentA =
    FiniteModel.FiniteAtom.componentA at heq
  rw [refinementAtomMap_componentA] at heq
  exact FiniteModel.FiniteAtom.noConfusion heq

/-- Active reverse context generated without supplying a cleavage or mate. -/
noncomputable def activeReverseContext :
    ActiveRefinementBCContext FiniteModel.carrier :=
  activeRefinementBCContextOfCondition activeReverseConfiguration
    activeReverseSource activeReverseTargetPackage
    (activeReverse_condition activeReverseSource)

/-- Evaluation of the base-reverse/exact-pulled route at the actual target package. -/
noncomputable def activeReverseBaseMatePackage :
    CoreFiber (activeReverseConfiguration.pullbackSourceAt activeReverseSource) :=
  activeReverseContext.baseMatePackage

/-- Evaluation of the exact-pullback/pulled-reverse route at the actual target package. -/
noncomputable def activeReversePulledMatePackage :
    CoreFiber (activeReverseConfiguration.pullbackSourceAt activeReverseSource) :=
  activeReverseContext.pulledMatePackage

/-- The canonical mate component between the two evaluated actual packages. -/
noncomputable def activeReverseMateComponent :
    activeReverseBaseMatePackage ⟶ activeReversePulledMatePackage :=
  activeReverseContext.mateAtTarget

/-! ## Inactive infinite regression witness -/

/-- Infinite selected-family identity configuration on the fixed G-112 sum carrier. -/
def inactiveInfiniteConfiguration :
    RefinementBCConfiguration ExactBottomSumCarrier.{u} where
  sOnePrime := exactBottomSummandOneDoctrine.{u}
  sOne := exactBottomSummandOneDoctrine.{u}
  sTwo := exactBottomSummandOneDoctrine.{u}
  bottom := exactBottomSummandOneDoctrine.{u}
  fst := (𝟙 exactBottomSummandOneInstance.{u} :
    exactBottomSummandOneInstance.{u} ⟶
      exactBottomSummandOneInstance.{u}).doctrineHom
  snd := (𝟙 exactBottomSummandOneInstance.{u} :
    exactBottomSummandOneInstance.{u} ⟶
      exactBottomSummandOneInstance.{u}).doctrineHom
  refinement := refinementHomId exactBottomSummandOneDoctrine.{u}

/-- The unique compatible source of the inactive configuration. -/
def inactiveInfiniteSource :
    inactiveInfiniteConfiguration.{u}.CompatibleSource where
  sourcePrime := PUnit.unit
  sourceTwo := PUnit.unit
  bottom_eq := rfl

/-- No core package can realize the fixed non-list-finite first summand. -/
theorem inactiveInfinite_target_empty
    (p : inactiveInfiniteConfiguration.{u}.CompatibleSource) :
    ¬ Nonempty (CoreFiber (inactiveInfiniteConfiguration.{u}.targetPointAt p)) := by
  rintro ⟨⟨Q, hQ⟩⟩
  have hfamily : Q.family =
      (inactiveInfiniteConfiguration.{u}.targetPointAt p).doctrine.atomize
        (inactiveInfiniteConfiguration.{u}.targetPointAt p).source :=
    congrArg (fun X : ExtractionInstance ExactBottomSumCarrier.{u} =>
      X.doctrine.atomize X.source) hQ
  have hfinite :
      ((inactiveInfiniteConfiguration.{u}.targetPointAt p).doctrine.atomize
        (inactiveInfiniteConfiguration.{u}.targetPointAt p).source).ListFinite := by
    rw [← hfamily]
    exact Q.reading.family_listFinite
  rcases hfinite with ⟨atoms, hcover⟩
  apply exactBottomFirstSummand_not_finite
  apply atoms.finite_toSet.subset
  intro atom hatom
  apply hcover atom
  change exactBottomSummandOneDoctrine.{u}.extracts PUnit.unit atom
  exact ⟨trivial, hatom, trivial, trivial⟩

/-- The infinite regression configuration is inactive. -/
theorem inactiveInfinite_not_active :
    ¬ Active inactiveInfiniteConfiguration.{u} := by
  rintro ⟨⟨p, package⟩⟩
  exact inactiveInfinite_target_empty p ⟨package⟩

/-- Inactivity prevents this example from serving as either active witness. -/
theorem inactiveInfinite_not_activeRegimeAvailable :
    ¬ ActiveRegimeAvailable inactiveInfiniteConfiguration.{u} := by
  intro available
  exact inactiveInfinite_not_active available.1

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
