import Formal.AG.Examples.StandardGeometryReferenceModels
import Formal.AG.RepresentationAnalysis.GraphMatrix
import Formal.AG.RepresentationAnalysis.Synthesis
import Formal.AG.RepresentationAnalysis.SignatureCurvature
import Formal.AG.RepresentationAnalysis.RepairMarginDehn
import Formal.AG.Cohomology.GluingMismatch
import Formal.AG.Cohomology.LocalFlatnessGap
import Formal.AG.Measurement.Bootstrap
import Formal.AG.Evolution.Bootstrap
import Formal.AG.SemanticRepair.Bootstrap

noncomputable section

namespace AAT.AG.Examples.LegacyConsolidation
open AAT.AG.RepresentationAnalysis
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry Classical


open Examples

noncomputable def standardPartIPrerequisites : Site.PartIPrerequisites where
  carrier := AAT.AG.FiniteModel.carrier
  core := AAT.AG.FiniteModel.corePackage

noncomputable def standardGeometry : Site.ArchitectureGeometry standardPartIPrerequisites where
  site := StandardGeometryReferenceModels.referenceSite

private noncomputable instance standardGeometry_hasSheafifyInt :
    HasSheafify standardGeometry.site.topology
      (LawAlgebra.AATCommAlgCat Int) :=
  StandardGeometryReferenceModels.referenceSite_hasSheafifyInt

inductive ReferenceObstructionReading where
  | weak
  | strong
deriving DecidableEq

noncomputable def readingParameter :
    AATSchReadingParameter StandardGeometryReferenceModels.referenceRaw where
  AtomLabelReading := PUnit
  LawReading := PUnit
  ObstructionIdealReading := ReferenceObstructionReading
  SignatureReading := PUnit
  InterpretationMapReading := PUnit
  atomLabelsCompatible _ _ _ := True
  lawReadingCompatible _ _ _ := True
  obstructionIdealCompatible _ a b := a = b
  signatureReadingCompatible _ _ _ := True
  interpretationMapCompatible _ _ _ := True
  id_atomLabelsCompatible _ _ := trivial
  id_lawReadingCompatible _ _ := trivial
  id_obstructionIdealCompatible _ _ := rfl
  id_signatureReadingCompatible _ _ := trivial
  id_interpretationMapCompatible _ _ := trivial
  comp_atomLabelsCompatible _ _ := trivial
  comp_lawReadingCompatible _ _ := trivial
  comp_obstructionIdealCompatible hab hbc := hab.trans hbc
  comp_signatureReadingCompatible _ _ := trivial
  comp_interpretationMapCompatible _ _ := trivial

noncomputable def overlapAATSch : AATSch readingParameter where
  scheme := LawAlgebra.StandardArchitectureScheme.singleAffine
    StandardGeometryReferenceModels.referenceRaw
    (StandardGeometryReferenceModels.referenceScheme.atlas.pairContext
      StandardGeometryReferenceModels.referenceRaw
      StandardGeometryReferenceModels.leftIndex
      StandardGeometryReferenceModels.rightIndex)
  atomLabels := PUnit.unit
  lawReading := PUnit.unit
  obstructionIdealReading := .weak
  signatureReading := PUnit.unit
  interpretationMapReading := PUnit.unit

noncomputable def leftAATSch : AATSch readingParameter where
  scheme := LawAlgebra.StandardArchitectureScheme.singleAffine
    StandardGeometryReferenceModels.referenceRaw
    (StandardGeometryReferenceModels.referenceScheme.atlas.chart
      StandardGeometryReferenceModels.leftIndex).context
  atomLabels := PUnit.unit
  lawReading := PUnit.unit
  obstructionIdealReading := .weak
  signatureReading := PUnit.unit
  interpretationMapReading := PUnit.unit

noncomputable def referenceAATSch : AATSch readingParameter where
  scheme := StandardGeometryReferenceModels.referenceScheme
  atomLabels := PUnit.unit
  lawReading := PUnit.unit
  obstructionIdealReading := .weak
  signatureReading := PUnit.unit
  interpretationMapReading := PUnit.unit

noncomputable def strongReferenceAATSch : AATSch readingParameter where
  scheme := StandardGeometryReferenceModels.referenceScheme
  atomLabels := PUnit.unit
  lawReading := PUnit.unit
  obstructionIdealReading := .strong
  signatureReading := PUnit.unit
  interpretationMapReading := PUnit.unit

private noncomputable def overlapSchemeHom : overlapAATSch.scheme ⟶ leftAATSch.scheme where
  base := LawAlgebra.architectureChartRestriction
    StandardGeometryReferenceModels.referenceRaw
    (StandardGeometryReferenceModels.referenceScheme.atlas.pairToLeft
      StandardGeometryReferenceModels.referenceRaw
      StandardGeometryReferenceModels.leftIndex
      StandardGeometryReferenceModels.rightIndex)
  preserves := LawAlgebra.ArchitectureAffineAtlas.overlap_toLeft_preserves
    StandardGeometryReferenceModels.referenceRaw
    StandardGeometryReferenceModels.referenceScheme.atlas
    StandardGeometryReferenceModels.leftIndex
    StandardGeometryReferenceModels.rightIndex

noncomputable def overlapToLeftMorphism : overlapAATSch ⟶ leftAATSch where
  toSchemeHom := overlapSchemeHom
  atomLabelsCompatible := trivial
  lawReadingCompatible := trivial
  obstructionIdealCompatible := rfl
  signatureReadingCompatible := trivial
  interpretationMapCompatible := trivial

private noncomputable def leftChartSchemeHom : leftAATSch.scheme ⟶ referenceAATSch.scheme where
  base := (StandardGeometryReferenceModels.referenceScheme.atlas.chart
    StandardGeometryReferenceModels.leftIndex).map
  preserves := LawAlgebra.ArchitectureAffineChart.localDecoration_preserves
    (StandardGeometryReferenceModels.referenceScheme.atlas.chart
      StandardGeometryReferenceModels.leftIndex)
    (StandardGeometryReferenceModels.referenceScheme.atlasValid.chart_valid
      StandardGeometryReferenceModels.leftIndex)

noncomputable def leftChartMorphism : leftAATSch ⟶ referenceAATSch where
  toSchemeHom := leftChartSchemeHom
  atomLabelsCompatible := trivial
  lawReadingCompatible := trivial
  obstructionIdealCompatible := rfl
  signatureReadingCompatible := trivial
  interpretationMapCompatible := trivial

noncomputable def schemeRepresentation :
    AnalyticRepresentation readingParameter
      (LawAlgebra.StandardArchitectureScheme StandardGeometryReferenceModels.referenceRaw) :=
  AATSch.forget readingParameter

noncomputable def nonPreservingCandidate :
    referenceAATSch.scheme ⟶ strongReferenceAATSch.scheme :=
  𝟙 StandardGeometryReferenceModels.referenceScheme

theorem nonPreservingCandidate_not_compatible :
    ¬ readingParameter.obstructionIdealCompatible nonPreservingCandidate
      referenceAATSch.obstructionIdealReading strongReferenceAATSch.obstructionIdealReading := by
  intro h
  cases h

inductive MigrationVertex | overlap | leftChart | ambient
deriving DecidableEq, Fintype

inductive MigrationEdge | overlapToLeft | leftToAmbient
deriving DecidableEq, Fintype

inductive MigrationLabel | restricts
deriving DecidableEq, Fintype

def migrationGraph : RepresentationAnalysis.FiniteDirectedGraphTarget
    MigrationVertex MigrationEdge MigrationLabel where
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  source | .overlapToLeft => .overlap | .leftToAmbient => .leftChart
  target | .overlapToLeft => .leftChart | .leftToAmbient => .ambient
  relationLabel | .overlapToLeft => .restricts | .leftToAmbient => .restricts

noncomputable def graphRepresentation : AnalyticRepresentation readingParameter
    (RepresentationAnalysis.FiniteDirectedGraphTarget
      MigrationVertex MigrationEdge MigrationLabel) where
  obj _ := migrationGraph
  map _ := 𝟙 migrationGraph
  map_id _ := by simp
  map_comp _ _ := by simp

@[simp] theorem overlapToLeftMorphism_toSchemeMap :
    overlapToLeftMorphism.toSchemeMap =
      LawAlgebra.architectureChartRestriction
        StandardGeometryReferenceModels.referenceRaw
        (StandardGeometryReferenceModels.referenceScheme.atlas.pairToLeft
          StandardGeometryReferenceModels.referenceRaw
          StandardGeometryReferenceModels.leftIndex
          StandardGeometryReferenceModels.rightIndex) := rfl

@[simp] theorem leftChartMorphism_toSchemeMap :
    leftChartMorphism.toSchemeMap =
      (StandardGeometryReferenceModels.referenceScheme.atlas.chart
        StandardGeometryReferenceModels.leftIndex).map := by
  calc
    leftChartMorphism.toSchemeMap =
        StandardGeometryReferenceModels.leftChartDomainIso.hom ≫
          AlgebraicGeometry.Scheme.Spec.map
            (CommRingCat.ofHom
              (algebraMap StandardGeometryReferenceModels.AmbientRing
                (Localization.Away StandardGeometryReferenceModels.leftGenerator))).op := by
      simpa [leftChartMorphism, leftChartSchemeHom, AATSchMorphism.toSchemeMap] using
        StandardGeometryReferenceModels.left_chart_map
    _ = (StandardGeometryReferenceModels.referenceScheme.atlas.chart
          StandardGeometryReferenceModels.leftIndex).map :=
      StandardGeometryReferenceModels.left_chart_map.symm

theorem leftChartMorphism_not_isIso : ¬ IsIso leftChartMorphism.toSchemeMap := by
  simpa [leftChartMorphism_toSchemeMap] using
    StandardGeometryReferenceModels.left_chart_not_isIso

@[simp] theorem schemeRepresentation_map_leftChartMorphism :
    schemeRepresentation.map leftChartMorphism = leftChartMorphism.toSchemeHom := rfl

theorem schemeRepresentation_map_id :
    schemeRepresentation.map (𝟙 referenceAATSch) =
      𝟙 (schemeRepresentation.obj referenceAATSch) := by simp

theorem schemeRepresentation_map_comp :
    schemeRepresentation.map (overlapToLeftMorphism ≫ leftChartMorphism) =
      schemeRepresentation.map overlapToLeftMorphism ≫
        schemeRepresentation.map leftChartMorphism := by
  simpa using schemeRepresentation.map_comp overlapToLeftMorphism leftChartMorphism

@[simp] theorem schemeRepresentation_map_leftChartMorphism_toSchemeMap :
    (schemeRepresentation.map leftChartMorphism).base =
      (StandardGeometryReferenceModels.referenceScheme.atlas.chart
        StandardGeometryReferenceModels.leftIndex).map := rfl

theorem schemeRepresentation_map_leftChartMorphism_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      (schemeRepresentation.map leftChartMorphism).base := by
  simpa using StandardGeometryReferenceModels.left_chart_isOpenImmersion

theorem schemeRepresentation_map_leftChartMorphism_not_isIso :
    ¬ IsIso (schemeRepresentation.map leftChartMorphism).base := by
  simpa using StandardGeometryReferenceModels.left_chart_not_isIso

@[simp] theorem graphRepresentation_obj_reference :
    graphRepresentation.obj referenceAATSch = migrationGraph := rfl

theorem graphRepresentation_map_id :
    graphRepresentation.map (𝟙 referenceAATSch) =
      𝟙 (graphRepresentation.obj referenceAATSch) := by simp

theorem graphRepresentation_map_comp :
    graphRepresentation.map (overlapToLeftMorphism ≫ leftChartMorphism) =
      graphRepresentation.map overlapToLeftMorphism ≫
        graphRepresentation.map leftChartMorphism := by
  exact graphRepresentation.{0}.map_comp
    overlapToLeftMorphism.{0} leftChartMorphism.{0}

private noncomputable def synthesisCover :
    Cohomology.CoverRelativeCechCover StandardGeometryReferenceModels.referenceSite :=
  Cohomology.canonicalCoverRelative StandardGeometryReferenceModels.referenceCover

private def synthesisZeroAddCommGrpPresheaf :
    StandardGeometryReferenceModels.referenceSite.categoryᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (CategoryTheory.Functor.const
    StandardGeometryReferenceModels.referenceSite.categoryᵒᵖ).obj
      (AddCommGrpCat.of PUnit)

private noncomputable def synthesisObstructionSheaf :
    Cohomology.ObstructionSheaf StandardGeometryReferenceModels.referenceSite :=
  Cohomology.ObstructionSheaf.ofAddCommGrpValued
    synthesisZeroAddCommGrpPresheaf (by
      intro _base _cover _hcover family _compatible
      refine ⟨0, ?_, ?_⟩
      · intro _Y f hf
        change family f hf = PUnit.unit
        cases family f hf
        rfl
      · intro y _hy
        change y = PUnit.unit
        cases y
        rfl)

private noncomputable def synthesisCechComplex :
    Cohomology.CoverRelativeCechComplex synthesisCover synthesisObstructionSheaf :=
  Cohomology.canonicalCechComplex
    StandardGeometryReferenceModels.referenceCover synthesisObstructionSheaf

private def synthesisRepairProfile :
    Derived.RepairProfile.RepairComparisonProfile.{0} where
  Section := StandardGeometryReferenceModels.referenceScheme.underlying.IdealSheafData
  Geometry := StandardGeometryReferenceModels.referenceScheme.underlying.IdealSheafData
  sectionComparison := (· ≤ ·)
  geometryComparison := (· ≤ ·)
  sectionImproves := (· < ·)
  geometryImproves := (· < ·)
  section_improves_implies_comparison := fun h => h.le
  geometry_improves_implies_comparison := fun h => h.le

private def synthesisStratumParameter :
    SingularityMonodromyStack.StratumReadingParameter
      StandardGeometryReferenceModels.referenceSite where
  signatureAxes := FiniteModel.concreteNoCycleSignatureAxes
  Coeff := Int
  selectedCoeff := 0

private noncomputable def synthesisArchitectureStratum :
    SingularityMonodromyStack.ArchitectureStratum synthesisStratumParameter Int where
  raw := StandardGeometryReferenceModels.referenceRaw
  sheafify := inferInstance
  geometry := StandardGeometryReferenceModels.referenceScheme
  Point := PUnit
  carrier := Set.univ
  role := .component
  label := "standard-reference-weak-lawful-stratum"
  selectedSubobject := True
  selectedSubobject_cert := trivial
  locallyClosed := True
  locallyClosed_cert := trivial
  decorationCompatible := True
  decorationCompatible_cert := trivial
  readingCompatible := True
  readingCompatible_cert := trivial

private def synthesisOperationCost :
    RepresentationAnalysis.OperationCost standardPartIPrerequisites.architectureObject where
  Operation := PUnit
  cost _ := RepresentationAnalysis.DistanceValue.measured 0
  appliesTo _ _ := True

private def synthesisPathLength :
    RepresentationAnalysis.PathLength synthesisOperationCost where
  Path := PUnit
  startsAt _ := FiniteModel.FiniteAtom.componentA
  endsAt _ := FiniteModel.FiniteAtom.componentA
  length _ := RepresentationAnalysis.DistanceValue.measured 0
  operationsMeasuredSeparately := True
  operationsMeasuredSeparately_holds := trivial

private def synthesisHomotopyFillingCost :
    RepresentationAnalysis.HomotopyFillingCost
      standardPartIPrerequisites.architectureObject where
  HomotopyBoundary := PUnit
  fillingCost _ := RepresentationAnalysis.DistanceValue.measured 0
  finiteWitnessBoundary := True
  finiteWitnessBoundary_holds := trivial

private abbrev synthesisOperationDistance :
    RepresentationAnalysis.OperationDistanceProfile
      standardPartIPrerequisites.architectureObject where
  operationCost := synthesisOperationCost
  pathLength := synthesisPathLength
  homotopyFillingCost := synthesisHomotopyFillingCost
  GeometryState := PUnit
  operationPath _ _ := PUnit
  pathCost _ := RepresentationAnalysis.DistanceValue.measured 0
  pathLengthValue _ := RepresentationAnalysis.DistanceValue.measured 0
  fillingCostValue _ := RepresentationAnalysis.DistanceValue.measured 0
  distance _ _ := RepresentationAnalysis.DistanceValue.measured 0
  distance_reading _ _ := ⟨PUnit.unit, rfl⟩

private abbrev synthesisDistanceToFlatness :
    RepresentationAnalysis.DistanceToFlatnessProfile synthesisOperationDistance where
  Cost := ℕ∞
  costDomain := RepresentationAnalysis.CostInfimumDomain.completeLatticeInfimumDomain
  costToDistanceValue _ := RepresentationAnalysis.DistanceValue.measured 0
  FlatCandidate _ := PUnit
  flatState state _ := state
  factorsThroughFlat _ _ := True
  candidateDistance _ _ := 0
  candidateDistance_reads_d_op _ _ := rfl
  candidateFactorsThroughFlat _ _ := trivial

private def synthesisObstructionMeasure :
    RepresentationAnalysis.SelectedObstructionMeasure
      standardPartIPrerequisites.architectureObject where
  ObstructionSupport := PUnit
  IdealSupport := PUnit
  mu_Ob _ := RepresentationAnalysis.DistanceValue.measured 0
  mu_I _ := RepresentationAnalysis.DistanceValue.measured 0
  selectedObstructionSupport := Set.univ
  selectedIdealSupport := Set.univ
  muObSupported _ _ := trivial
  muISupported _ _ := trivial

private abbrev synthesisObstructionMass :
    RepresentationAnalysis.FiniteSupportObstructionMass
      synthesisObstructionMeasure PUnit where
  finiteSupport _ := [PUnit.unit]
  supportCoversSelected _ obstruction _ := by cases obstruction; simp
  measuredContribution _ _ := 0
  measuredContribution_eq_zero_of_not_mem _ _ _ := rfl
  finiteSum _ _ := 0
  finiteIntegral _ _ := 0
  mass _ := 0
  mass_eq_finiteSum _ := rfl
  finiteIntegral_eq_finiteSum _ := rfl

private abbrev synthesisDistanceMassContext :
    RepresentationAnalysis.DistanceFlatnessMassContext
      standardPartIPrerequisites.architectureObject where
  operationDistance := synthesisOperationDistance
  distanceToFlatness := synthesisDistanceToFlatness
  obstructionMeasure := synthesisObstructionMeasure
  obstructionMass := synthesisObstructionMass

private noncomputable def synthesisRepresentationFamily :
    RepresentationFamily readingParameter where
  Index := PUnit
  Target _ := CategoryTheory.Cat.of
    (RepresentationAnalysis.FiniteDirectedGraphTarget
      MigrationVertex MigrationEdge MigrationLabel)
  representation _ := graphRepresentation

private def synthesisDetectingFamily :
    UDetectingRepresentationFamily synthesisRepresentationFamily where
  ObstructionClass := PUnit
  analyticZeroReading _ _ := True
  WitnessZero_U _ := True
  detects _ _ := trivial
  completenessLevel := .conservative

private noncomputable def synthesisAnalyticReadingContext :
    AnalyticReadingContext
      standardPartIPrerequisites.architectureObject readingParameter where
  AtomVocabulary := FiniteModel.FiniteAtom
  atomVocabularyOf := id
  lawUniverse := FiniteModel.lawUniverse
  CoverageTopology := Site.AATCoverageFamily
    StandardGeometryReferenceModels.referenceSite.requirements
    StandardGeometryReferenceModels.referenceSite.overlap
    StandardGeometryReferenceModels.baseContext
  selectedCoverage := StandardGeometryReferenceModels.referenceCover
  coefficientSheaf := PUnit
  representationFamily := synthesisRepresentationFamily
  distanceMassContext := synthesisDistanceMassContext
  selectedWitnessFamily := PUnit
  selectedWitness := PUnit.unit
  selectedSignatureAxes := FiniteModel.concreteNoCycleSignatureAxes
  signatureProfile := RepresentationAnalysis.SignatureReadingProfile.ofSignatureAxes
    FiniteModel.concreteNoCycleSignatureAxes
  detectingFamily := synthesisDetectingFamily
  coverageAdequacy := True
  witnessExactness := True
  axisExactness := True
  coefficientDiscipline := True
  completenessLevel := .conservative

noncomputable def synthesisPackage :
    AATSynthesisPackage standardPartIPrerequisites Int standardGeometry
      StandardGeometryReferenceModels.referenceRaw where
  architectureScheme := StandardGeometryReferenceModels.referenceScheme
  lawReading := StandardGeometryReferenceModels.weakReading
  lawReadingValid := StandardGeometryReferenceModels.weakReading_valid
  requiredClosed := StandardGeometryReferenceModels.weakReading_requiredClosed
  requiredLawIdealExact := StandardGeometryReferenceModels.weakReading_requiredLawIdealExact
  cover := synthesisCover
  obstructionSheaf := synthesisObstructionSheaf
  obstructionCohomology := synthesisCechComplex
  derivedLawGeometry := synthesisRepairProfile
  stratumParameter := synthesisStratumParameter
  singularityMonodromyStack := synthesisArchitectureStratum
  readingParameter := readingParameter
  representationPeriodMetricAnalysis := synthesisAnalyticReadingContext

theorem synthesisPackage_fires :
    synthesisPackage.site = StandardGeometryReferenceModels.referenceSite ∧
    synthesisPackage.ringedAATSite =
      StandardGeometryReferenceModels.referenceRaw.toRingedSite ∧
    synthesisPackage.architectureScheme =
      StandardGeometryReferenceModels.referenceScheme ∧
    synthesisPackage.lawReading = StandardGeometryReferenceModels.weakReading ∧
    synthesisPackage.readingParameter = readingParameter ∧
    synthesisPackage.obstructionIdealSheaf =
      LawAlgebra.lawGeneratedIdealSheaf
        StandardGeometryReferenceModels.referenceRaw
        StandardGeometryReferenceModels.referenceScheme
        StandardGeometryReferenceModels.weakReading
        StandardGeometryReferenceModels.weakReading_valid
        StandardGeometryReferenceModels.weakReading_requiredClosed ∧
    synthesisPackage.lawfulClosedSubscheme =
      LawAlgebra.lawfulClosedSubscheme
        StandardGeometryReferenceModels.referenceRaw
        StandardGeometryReferenceModels.referenceScheme
        StandardGeometryReferenceModels.weakReading
        StandardGeometryReferenceModels.weakReading_valid
        StandardGeometryReferenceModels.weakReading_requiredClosed ∧
    Nonempty (LawAlgebra.FactorsThroughLawfulClosedSubscheme
      StandardGeometryReferenceModels.referenceRaw
      StandardGeometryReferenceModels.referenceScheme
      StandardGeometryReferenceModels.weakReading
      StandardGeometryReferenceModels.weakReading_valid
      StandardGeometryReferenceModels.weakReading_requiredClosed
      StandardGeometryReferenceModels.zeroPoint) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact StandardGeometryReferenceModels.zeroPoint_fires.2.2.2.1

end AAT.AG.Examples.LegacyConsolidation
