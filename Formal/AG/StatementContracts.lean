import Formal.AG.Site.Geometry
import Formal.AG.Site.MinimalContextProfile
import Formal.AG.Derived.WellFoundedRepair
import Formal.AG.RepresentationAnalysis.GraphMatrix
import Formal.AG.RepresentationAnalysis.Synthesis
import Formal.AG.Examples.RepresentationAnalysisPart7
import Formal.AG.StatementContractsAATCoreObstructionSplit

noncomputable section

/-!
Statement contracts for fixed Lean statements.

Files under `Formal/AG/StatementContracts*.lean` contain only elaboration
contracts of the form

```lean
example : <fixed signature> := <implemented theorem>
```

They are imported by `Formal/AG.lean`, so `lake build` checks that the fixed
signature and the implemented theorem still match definitionally.
-/

namespace AAT.AG

universe u v w x y z

open CategoryTheory
open CategoryTheory.Limits

/--
Sample contract for the §5.2 placement convention: the existing site topology
theorem still has exactly the fixed statement below.
-/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) :
    S.topology = Site.AATGrothendieckTopology S.requirements S.overlap :=
  Site.AATSite.topology_eq S

/-- Fixed readable-equivalence statement for Part II proposition 4.2. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile A Axis Observable) :
    (W ≤ V ∧ V ≤ W) ↔ W = V :=
  Site.MinimalContextProfile.readableEquivalence_iff_eq W V

/-- Fixed presentation-level meet statement before readable quotienting. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile.RawMinimalContextProfile A Axis Observable) :
    Site.MinimalContextProfile.RawMinimalContextProfile.normalize
        (Site.MinimalContextProfile.RawMinimalContextProfile.inf W V) =
      Site.MinimalContextProfile.RawMinimalContextProfile.normalize W ⊓
        Site.MinimalContextProfile.RawMinimalContextProfile.normalize V :=
  Site.MinimalContextProfile.RawMinimalContextProfile.normalize_inf W V

/-- Fixed raw-readable-equivalence statement before quotienting. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile.RawMinimalContextProfile A Axis Observable) :
    Site.MinimalContextProfile.RawMinimalContextProfile.readableSetoid W V ↔
      Site.MinimalContextProfile.RawMinimalContextProfile.normalize W =
        Site.MinimalContextProfile.RawMinimalContextProfile.normalize V :=
  Site.MinimalContextProfile.RawMinimalContextProfile.readableEquivalent_iff_normalize_eq W V

/-- Fixed binary-product statement in the raw preorder category. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile.RawMinimalContextProfile A Axis Observable) :
    IsLimit (Site.MinimalContextProfile.RawMinimalContextProfile.infBinaryFan W V) :=
  Site.MinimalContextProfile.RawMinimalContextProfile.infBinaryFanIsLimit W V

/-- Fixed finite-limit statement before readable quotienting. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u} :
    HasFiniteLimits
      (Site.MinimalContextProfile.RawMinimalContextProfile A Axis Observable) :=
  Site.MinimalContextProfile.RawMinimalContextProfile.hasFiniteLimits

/-- Fixed quotient-to-normal-form order equivalence statement. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u} :
    Site.MinimalContextProfile.RawMinimalContextProfile.QuotientProfile
        (A := A) (Axis := Axis) (Observable := Observable) ≃o
      Site.MinimalContextProfile A Axis Observable :=
  Site.MinimalContextProfile.RawMinimalContextProfile.quotientOrderIso

/-- Fixed meet-descent statement on the readable quotient. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile.RawMinimalContextProfile.QuotientProfile
      (A := A) (Axis := Axis) (Observable := Observable)) :
    Site.MinimalContextProfile.RawMinimalContextProfile.quotientNormalize
        (Site.MinimalContextProfile.RawMinimalContextProfile.quotientInf W V) =
      Site.MinimalContextProfile.RawMinimalContextProfile.quotientNormalize W ⊓
        Site.MinimalContextProfile.RawMinimalContextProfile.quotientNormalize V :=
  Site.MinimalContextProfile.RawMinimalContextProfile.quotientNormalize_inf W V

/-- Fixed finite-limit statement on the readable quotient. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u} :
    HasFiniteLimits
      (Site.MinimalContextProfile.RawMinimalContextProfile.QuotientProfile
        (A := A) (Axis := Axis) (Observable := Observable)) :=
  Site.MinimalContextProfile.RawMinimalContextProfile.quotient_hasFiniteLimits

/-- Fixed actual-hom thinness statement for Part II proposition 4.2. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile A Axis Observable) :
    Subsingleton (W ⟶ V) :=
  Site.MinimalContextProfile.hom_subsingleton W V

/-- Fixed function-valued selected-hom thinness statement for Part II proposition 4.2. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile A Axis Observable) :
    Subsingleton (Site.MinimalContextProfile.ReadableContextHom W V) :=
  Site.MinimalContextProfile.readableContextHom_subsingleton W V

/-- Fixed equivalence between Mathlib homs and function-valued selected homs. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u}
    (W V : Site.MinimalContextProfile A Axis Observable) :
    (W ⟶ V) ≃ Site.MinimalContextProfile.ReadableContextHom W V :=
  Site.MinimalContextProfile.homEquivReadableContextHom W V

/-- Fixed finite-limit statement for Part II proposition 4.2. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u} :
    HasFiniteLimits (Site.MinimalContextProfile A Axis Observable) :=
  Site.MinimalContextProfile.hasFiniteLimits

/-- Fixed categorical pullback statement for Part II proposition 4.2. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u}
    {base left right : Site.MinimalContextProfile A Axis Observable}
    (hl : left ⟶ base) (hr : right ⟶ base) :
    pullback hl hr = left ⊓ right :=
  Site.MinimalContextProfile.pullback_eq_inf hl hr

/-- Fixed legacy restriction comparison for Part II proposition 4.2. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u}
    {W V : Site.MinimalContextProfile A Axis Observable} (f : W ⟶ V) :
    (Site.MinimalContextProfile.homToContextMorphism f).IsRestriction :=
  Site.MinimalContextProfile.homToContextMorphism_isRestriction f

/-- Fixed representative-independence statement for Part II proposition 4.2. -/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {Axis Observable : Type u}
    {W W' V V' : Site.MinimalContextProfile A Axis Observable}
    (hW : W ≤ W' ∧ W' ≤ W) (hV : V ≤ V' ∧ V' ≤ V) :
    W ⊓ V = W' ⊓ V' :=
  Site.MinimalContextProfile.inf_eq_inf_of_mutual_readability hW hV

/-- Fixed constructor equation for Part V theorem 13.4 synthesis. -/
example (P : Derived.WellFoundedRepair.RepairComparisonProfile.{u})
    (rule : (state : P.State) ->
      Derived.WellFoundedRepair.SynthesisDecision P state)
    (start : P.State) :
    Derived.WellFoundedRepair.synthesize P rule start =
      match rule start with
      | .step next hstep =>
          .step hstep (Derived.WellFoundedRepair.synthesize P rule next)
      | .cleared hcleared => .cleared hcleared
      | .noSolution hcertificate => .noSolution hcertificate :=
  Derived.WellFoundedRepair.synthesize_eq P rule start

/-- Fixed sound finite synthesis statement for Part V theorem 13.4. -/
example (P : Derived.WellFoundedRepair.RepairComparisonProfile.{u})
    (rule : (state : P.State) ->
      Derived.WellFoundedRepair.SynthesisDecision P state)
    (start : P.State) :
    let run := Derived.WellFoundedRepair.synthesize P rule start
    Derived.WellFoundedRepair.SynthesisRun.TraceEmitsOnlySoundSteps P run.trace ∧
      run.trace.length = run.depth + 1 ∧
        (P.targetCleared run.outputState ∨
          P.noSolutionCertificate run.outputState) :=
  Derived.WellFoundedRepair.soundRepairSynthesis P rule start

/-- Fixed walk-decomposition cardinality statement for Part VII proposition 3.6. -/
example {Vertex Edge RelationLabel : Type u}
    (G : RepresentationAnalysis.FiniteDirectedGraphTarget
      Vertex Edge RelationLabel)
    [Fintype Vertex]
    (n : Nat) (start finish : Vertex) :
    Fintype.card
        (RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk
          G start finish (n + 1)) =
      ∑ middle : Vertex,
        RepresentationAnalysis.edgeFiberCard G start middle *
          Fintype.card
            (RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk
              G middle finish n) :=
  RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk.card_succ
    G n start finish

/-- Fixed all-length matrix-walk cardinality statement for Part VII proposition 3.6. -/
example {Vertex Edge RelationLabel : Type u}
    (G : RepresentationAnalysis.FiniteDirectedGraphTarget
      Vertex Edge RelationLabel)
    (n : Nat) (start finish : Vertex) :
    (RepresentationAnalysis.adjacencyMatrixPower G n) start finish =
      Fintype.card
        (RepresentationAnalysis.FiniteDirectedGraphTarget.CountedDirectedWalk
          G start finish n) :=
  RepresentationAnalysis.adjacencyMatrixPower_apply_eq_countedDirectedWalk_card
    G n start finish

/-- Fixed constructed-package statement for Part VII theorem 16.1 synthesis. -/
example {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    (I : RepresentationAnalysis.AATSynthesisConstructionInput.{u, v, w, x, y, z} P k) :
    ∃ S : RepresentationAnalysis.AATSynthesisPackage.{u, v, w, x, y, z} P k,
      S = I.toPackage ∧
        S.aatSite = S.architectureGeometry.site ∧
        S.ringedAATTopos = S.architectureScheme.ringedTopos ∧
        S.affineAATCharts = S.architectureScheme.chart ∧
        S.lawfulLocus =
          LawAlgebra.LawfulLocus.lawfulLocus
            S.LawCoordinateAlgebra S.obstructionIdeal ∧
        HEq S.obstructionCohomology I.obstructionCohomology ∧
        S.derivedLawGeometry = I.derivedLawGeometry ∧
        HEq S.singularityMonodromyStack I.singularityMonodromyStack ∧
        HEq S.representationPeriodMetricAnalysis
          I.representationPeriodMetricAnalysis :=
  RepresentationAnalysis.algebraicGeometricAATSynthesis_constructedPackage I

namespace FiniteModel.RepresentationAnalysisPart7

/-- Fixed concrete construction-input type for Issue #3197. -/
example : RepresentationAnalysis.AATSynthesisConstructionInput.{0, 0, 0, 0, 0, 0}
    finiteSynthesisPartI PUnit :=
  nondegenerateSynthesisInput

/-- Fixed concrete package type for Issue #3197. -/
example : RepresentationAnalysis.AATSynthesisPackage.{0, 0, 0, 0, 0, 0}
    finiteSynthesisPartI PUnit :=
  nondegenerateSynthesisPackage

/-- Fixed actual distance-one firing for the safe state. -/
example :
    nondegenerateDistanceToFlatness.dist_flat_value MarginState.safe =
      RepresentationAnalysis.DistanceValue.measured 1 :=
  nondegenerateDistance_safe_eq_one

/-- Fixed actual distance-zero firing for the selected flat state. -/
example :
    nondegenerateDistanceToFlatness.dist_flat_value MarginState.boundary =
      RepresentationAnalysis.DistanceValue.measured 0 :=
  nondegenerateDistance_boundary_eq_zero

/-- Fixed nonconstant-distance statement. -/
example :
    nondegenerateDistanceToFlatness.dist_flat_value MarginState.safe ≠
      RepresentationAnalysis.DistanceValue.measured 0 :=
  nondegenerateDistance_safe_ne_zero

/-- Fixed ideal-to-selected-obstruction identity statement. -/
example :
    nondegenerateSynthesisPackage.representationPeriodMetricAnalysis.selectedWitness =
      nondegenerateSynthesisPackage.obstructionIdeal :=
  nondegenerateSelectedObstruction_eq_ideal

/-- Fixed representation-output provenance statement. -/
example :
    ((nondegenerateSynthesisPackage.representationPeriodMetricAnalysis.representationFamily).representation
        ToyRepIndex.graph).obj
        (nondegenerateDecoratedScheme nondegenerateSynthesisPackage.obstructionIdeal) =
      nondegenerateSynthesisPackage.representationPeriodMetricAnalysis.selectedWitness :=
  nondegenerateRepresentation_reads_selectedIdeal

/-- Fixed concrete Part I--VII package-chain statement. -/
example :
    nondegenerateSynthesisPackage.aatSite =
        nondegenerateSynthesisPackage.architectureGeometry.site ∧
      nondegenerateSynthesisPackage.ringedAATTopos =
        nondegenerateSynthesisPackage.architectureScheme.ringedTopos ∧
      nondegenerateSynthesisPackage.affineAATCharts =
        nondegenerateSynthesisPackage.architectureScheme.chart ∧
      nondegenerateSynthesisPackage.lawfulLocus =
        LawAlgebra.LawfulLocus.lawfulLocus
          nondegenerateSynthesisPackage.LawCoordinateAlgebra
          nondegenerateSynthesisPackage.obstructionIdeal ∧
      nondegenerateSynthesisPackage.obstructionCohomology =
        nondegenerateSynthesisInput.obstructionCohomology ∧
      nondegenerateSynthesisPackage.derivedLawGeometry =
        nondegenerateSynthesisInput.derivedLawGeometry ∧
      nondegenerateSynthesisPackage.singularityMonodromyStack =
        nondegenerateSynthesisInput.singularityMonodromyStack ∧
      @Eq.{2} (RepresentationAnalysis.AnalyticReadingContext.{0, 0, 0, 0, 0, 0}
          object nondegenerateSynthesisReadingParameter)
        nondegenerateSynthesisPackage.representationPeriodMetricAnalysis
        (nondegenerateSynthesisAnalyticReadingContext
          (Ideal.span ({(2 : Int)} : Set Int))) :=
  nondegenerateSynthesis_package_chain.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}

/-- Fixed connected nondegenerate evidence statement. -/
example :
    finiteSynthesisPartI.architectureObject = object ∧
      nondegenerateSynthesisPackage.obstructionIdeal ≠ (⊥ : Ideal Int) ∧
      nondegenerateSynthesisPackage.representationPeriodMetricAnalysis.selectedWitness =
        nondegenerateSynthesisPackage.obstructionIdeal ∧
      ((nondegenerateSynthesisPackage.representationPeriodMetricAnalysis.representationFamily).representation
          ToyRepIndex.graph).obj
          (nondegenerateDecoratedScheme nondegenerateSynthesisPackage.obstructionIdeal) =
        nondegenerateSynthesisPackage.representationPeriodMetricAnalysis.selectedWitness ∧
      (¬ (nondegenerateSynthesisPackage.representationPeriodMetricAnalysis.detectingFamily).analyticZeroReading
        ToyRepIndex.graph
          nondegenerateSynthesisPackage.representationPeriodMetricAnalysis.selectedWitness) ∧
      (nondegenerateSynthesisPackage.representationPeriodMetricAnalysis.distanceMassContext).distanceToFlatness.dist_flat_value
          MarginState.safe =
        RepresentationAnalysis.DistanceValue.measured 1 ∧
      (nondegenerateSynthesisPackage.representationPeriodMetricAnalysis.distanceMassContext).distanceToFlatness.dist_flat_value
          MarginState.boundary =
        RepresentationAnalysis.DistanceValue.measured 0 ∧
      (nondegenerateSynthesisPackage.representationPeriodMetricAnalysis.distanceMassContext).distanceToFlatness.dist_flat_value
          MarginState.safe ≠
        RepresentationAnalysis.DistanceValue.measured 0 :=
  nondegenerateSynthesis_evidence.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}

end FiniteModel.RepresentationAnalysisPart7

end AAT.AG
