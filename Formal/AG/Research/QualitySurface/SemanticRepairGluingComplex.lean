import Formal.AG.Research.QualitySurface.SemanticResidualObstructionClass
import Formal.AG.Research.QualitySurface.SemanticResidualComponentFaithfulness
import Formal.AG.Research.QualitySurface.SemanticResidualTransportNaturality

/-!
Cycle 1 evidence for `G-aat-quality-surface-02`.

This file introduces a finite Cech-style semantic repair-gluing complex.  The
degree-zero data are local repair primitives, the degree-one data are residual
repair-gluing cochains, and `B1` is the image of `delta0`.  Vanishing of the
finite obstruction class means that the selected residual lies in `B1`.

The sufficiency direction is deliberately not a bare algebraic statement.  A
boundary primitive must also satisfy semantic faithfulness: it must cover the
residual components and be faithful back to the actual residual atoms.  Existing
Cycle 83/85 bridge theorems justify that this is the semantic content required
to turn a formal primitive into a real semantic repair certificate.

The result is finite and hypothesis-relative.  It does not assert arbitrary
site/sheaf cohomology, source extraction completeness, ArchMap correctness,
runtime repair synthesis, global minimality, or whole-codebase quality.
-/

universe u v w x y

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairGluingComplex

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffCechExactness
open HandoffCechOverlapBasis
open SemanticSupportProjectionKernel
open SemanticResidualComponentFaithfulness
open SemanticResidualTransportNaturality
open VisibleLocalSemanticGluingObstruction

/-! ## Finite semantic repair-gluing complexes -/

/--
A finite semantic repair-gluing complex.

`C0` contains local repair primitive families, `C1` contains residual
repair-gluing cochains, and `delta0` is the finite restriction-difference map.
The chart / overlap lists and `delta0_exact` field record the finite Cech-style
atlas boundary without claiming an arbitrary site or true sheaf-cohomology
construction.
-/
structure FiniteSemanticRepairGluingComplex
    (Atom : Type u) where
  Chart : Type v
  Overlap : Chart -> Chart -> Type w
  chartOrder : List Chart
  chart_complete : forall chart, chart ∈ chartOrder
  C0 : Type x
  C1 : Type y
  c0Order : List C0
  c0_complete : forall primitive, primitive ∈ c0Order
  c1Order : List C1
  c1_complete : forall cochain, cochain ∈ c1Order
  projection : Atom -> BridgeComponent
  cover : HandoffCechCover
  supportOf : C0 -> Atom -> Prop
  leftRestriction :
    C0 -> forall {source target}, Overlap source target -> Atom -> Prop
  rightRestriction :
    C0 -> forall {source target}, Overlap source target -> Atom -> Prop
  cochainAt :
    C1 -> forall {source target}, Overlap source target -> Atom -> Prop
  delta0 : C0 -> C1
  delta0_exact :
    forall primitive source target (overlap : Overlap source target) atom,
      cochainAt (delta0 primitive) overlap atom <->
        (leftRestriction primitive overlap atom /\
          Not (rightRestriction primitive overlap atom)) \/
        (rightRestriction primitive overlap atom /\
          Not (leftRestriction primitive overlap atom))
  residual : C1

/-- The finite restriction-difference law defining `delta0` on every overlap. -/
theorem delta0_support_exact
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (primitive : K.C0)
    {source target : K.Chart}
    (overlap : K.Overlap source target)
    (atom : Atom) :
    K.cochainAt (K.delta0 primitive) overlap atom <->
      (K.leftRestriction primitive overlap atom /\
        Not (K.rightRestriction primitive overlap atom)) \/
      (K.rightRestriction primitive overlap atom /\
        Not (K.leftRestriction primitive overlap atom)) :=
  K.delta0_exact primitive source target overlap atom

/-- The finite `B1` subgroup/predicate: cochains that are `delta0` boundaries. -/
def B1
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (cochain : K.C1) : Prop :=
  exists primitive, K.delta0 primitive = cochain

/-- The finite obstruction class vanishes when the residual cochain is a boundary. -/
def ObstructionClassVanishes
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom) : Prop :=
  B1 K K.residual

/-- Nonzero obstruction is the failure of finite boundary vanishing. -/
def ObstructionClassNonzero
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom) : Prop :=
  Not (ObstructionClassVanishes K)

/--
A primitive is semantically closed when its semantic support closes every
residual atom of the supplied cover.  This reuses the existing semantic support
closure predicate rather than defining global coherence as a bare proposition.
-/
def PrimitiveSemanticallyClosed
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (primitive : K.C0) : Prop :=
  SemanticRepairClosed K.projection K.cover (K.supportOf primitive)

/--
Global semantic repair coherence: a boundary primitive exists and is a real
semantic repair certificate.
-/
def GlobalSemanticRepairCoherent
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom) : Prop :=
  exists primitive,
    K.delta0 primitive = K.residual /\
      PrimitiveSemanticallyClosed K primitive

/--
Semantic faithfulness hypotheses for the sufficiency direction.

The hypotheses do not return a global certificate directly.  They say that any
primitive whose `delta0` is the selected residual has residual component
coverage and residual-component faithfulness.  The existing Cycle 83 theorem
then converts these two semantic facts into `SemanticRepairClosed`.
-/
structure SemanticFaithfulnessHypotheses
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom) where
  component_covered_of_boundary :
    forall primitive,
      K.delta0 primitive = K.residual ->
        ResidualComponentCoveredSupport
          K.projection K.cover (K.supportOf primitive)
  component_faithful_of_boundary :
    forall primitive,
      K.delta0 primitive = K.residual ->
        ResidualComponentFaithfulSupport
          K.projection K.cover (K.supportOf primitive)

/-! ## Semantic faithfulness bridge -/

/--
Residual component coverage plus residual-component faithfulness is exactly the
semantic content needed for a primitive to be a real repair certificate.
-/
theorem primitive_semanticRepairClosed_of_faithful_delta0
    {Atom : Type u}
    {K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom}
    (hfaithful : SemanticFaithfulnessHypotheses K)
    {primitive : K.C0}
    (hboundary : K.delta0 primitive = K.residual) :
    PrimitiveSemanticallyClosed K primitive := by
  exact
    (semanticRepairClosed_iff_residualComponentCovered_and_faithful).mpr
      ⟨hfaithful.component_covered_of_boundary primitive hboundary,
        hfaithful.component_faithful_of_boundary primitive hboundary⟩

/-- Existing component-faithfulness bridge, exposed for the descent package. -/
theorem residualComponentFaithfulness_bridge_for_descent
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {support : Atom -> Prop} :
    SemanticRepairClosed projection cover support <->
      ResidualComponentCoveredSupport projection cover support /\
        ResidualComponentFaithfulSupport projection cover support := by
  exact semanticRepairClosed_iff_residualComponentCovered_and_faithful

/-- Existing residual-support transport bridge, exposed for the descent package. -/
theorem residualSupportTransport_bridge_for_descent
    {Source : Type u}
    {Target : Type v}
    {sourceProjection : Source -> BridgeComponent}
    {sourceCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {targetSupport : Target -> Prop}
    (transport :
      ResidualSupportTransport
        sourceProjection sourceCover sourceSupport
        targetProjection targetCover targetSupport) :
    SemanticRepairClosed sourceProjection sourceCover sourceSupport <->
      SemanticRepairClosed targetProjection targetCover targetSupport := by
  exact residualSupportTransport_semanticRepairClosed_iff transport

/-! ## Necessity, contrapositive, and sufficiency -/

/-- A coherent global semantic repair primitive forces the obstruction class to vanish. -/
theorem globalRepairCoherent_forces_obstructionVanishes
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom) :
    GlobalSemanticRepairCoherent K -> ObstructionClassVanishes K := by
  intro hglobal
  rcases hglobal with ⟨primitive, hboundary, _hclosed⟩
  exact ⟨primitive, hboundary⟩

/-- Nonzero obstruction rules out global semantic repair coherence. -/
theorem no_globalRepairCoherent_of_nonzero_obstruction
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom) :
    ObstructionClassNonzero K -> Not (GlobalSemanticRepairCoherent K) := by
  intro hnonzero hglobal
  exact hnonzero (globalRepairCoherent_forces_obstructionVanishes K hglobal)

/--
Under explicit semantic faithfulness hypotheses, obstruction vanishing builds a
global semantic repair certificate.
-/
theorem globalRepairCoherent_of_obstructionVanishes
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (hfaithful : SemanticFaithfulnessHypotheses K) :
    ObstructionClassVanishes K -> GlobalSemanticRepairCoherent K := by
  intro hvanishes
  rcases hvanishes with ⟨primitive, hboundary⟩
  exact
    ⟨primitive, hboundary,
      primitive_semanticRepairClosed_of_faithful_delta0
        hfaithful hboundary⟩

/-- Finite semantic repair-gluing descent equivalence under faithfulness. -/
theorem finiteSemanticRepairGluingDescent_iff
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (hfaithful : SemanticFaithfulnessHypotheses K) :
    GlobalSemanticRepairCoherent K <-> ObstructionClassVanishes K := by
  constructor
  · exact globalRepairCoherent_forces_obstructionVanishes K
  · exact globalRepairCoherent_of_obstructionVanishes K hfaithful

/-! ## Visible/local witness validation -/

/--
The selected visible/local witness remains a nontrivial validation boundary:
component-level declared clearance and visible/local repair transport do not
reflect semantic repair-gluing exactness.
-/
theorem visibleLocalSemanticGluing_witness_validation :
    VisibleLocalDeclaredClearanceSemanticObstruction
        RepairTransportCechCommutatorCurvature.selectedRepairTransportCechCommutatorCell
        ComponentClearanceSemanticObstruction.traceRepairFrontierDeclaredPlan /\
      Not
        (forall cell : RepairTransportCechCommutatorCurvature.RepairTransportCechCommutatorCell,
          forall plan : HandoffRepairTransversalTheorem.HandoffRepairPlan,
            VisibleLocalDeclaredClearanceProfile cell plan ->
              SemanticRepairCocycleWitness.SemanticRepairGluingExact cell.flatPath ->
                SemanticRepairCocycleWitness.SemanticRepairGluingExact cell.curvedPath) /\
      Not
        (ResidualComponentFaithfulSupport
          SemanticSupportProjectionKernel.refinedSemanticComponent
          HandoffCechOverlapBasis.repairFrontierOverlapBasisCover
          SemanticSupportProjectionKernel.surfaceRepairSupport) /\
      Not
        (SemanticRepairClosed
          SemanticSupportProjectionKernel.refinedSemanticComponent
          HandoffCechOverlapBasis.repairFrontierOverlapBasisCover
          SemanticSupportProjectionKernel.surfaceRepairSupport) := by
  exact
    ⟨selected_visibleLocalDeclaredClearance_semanticObstruction,
      visibleLocalDeclaredClearance_not_reflect_semanticGluingExact,
      Formal.AG.Research.QualitySurface.SemanticResidualComponentFaithfulness.surfaceRepairSupport_componentCovered_not_faithful.2,
      SemanticSupportProjectionKernel.surfaceRepairSupport_not_semanticRepairClosed⟩

/--
A concrete finite complex attached to the selected visible/local witness.

Its single visible primitive has the surface support, while the selected
residual is not a `delta0` boundary.  This is a calibration instance: the
finite `B1` quotient is not allowed to erase the Cycle 80 semantic residual by
visible/component clearance alone.
-/
def selectedVisibleLocalWitnessComplex :
    FiniteSemanticRepairGluingComplex RefinedSemanticRepairAtom where
  Chart := Unit
  Overlap := fun _ _ => Unit
  chartOrder := [()]
  chart_complete := by
    intro chart
    cases chart
    simp
  C0 := Unit
  C1 := Bool
  c0Order := [()]
  c0_complete := by
    intro primitive
    cases primitive
    simp
  c1Order := [false, true]
  c1_complete := by
    intro cochain
    cases cochain <;> simp
  projection := refinedSemanticComponent
  cover := repairFrontierOverlapBasisCover
  supportOf := fun _ => surfaceRepairSupport
  leftRestriction := fun _ {_source} {_target} _overlap _atom => False
  rightRestriction := fun _ {_source} {_target} _overlap _atom => False
  cochainAt := fun cochain {_source} {_target} _overlap atom =>
    cochain = true /\ atom = RefinedSemanticRepairAtom.repairFrontierObligation
  delta0 := fun _ => false
  delta0_exact := by
    intro primitive source target overlap atom
    cases primitive
    cases source
    cases target
    cases overlap
    cases atom <;> simp
  residual := true

/-- The selected calibration complex has no primitive whose boundary is residual. -/
theorem selectedVisibleLocalWitness_boundary_not_residual
    (primitive : selectedVisibleLocalWitnessComplex.C0) :
    Not
      (selectedVisibleLocalWitnessComplex.delta0 primitive =
        selectedVisibleLocalWitnessComplex.residual) := by
  cases primitive
  intro hboundary
  cases hboundary

/--
The selected visible/local calibration complex has nonzero finite obstruction:
its residual is not in `B1`.
-/
theorem selectedVisibleLocalWitness_obstructionNonzero :
    ObstructionClassNonzero selectedVisibleLocalWitnessComplex := by
  intro hvanishes
  rcases hvanishes with ⟨primitive, hboundary⟩
  exact selectedVisibleLocalWitness_boundary_not_residual primitive hboundary

/-- The selected nonzero finite obstruction rules out global semantic repair coherence. -/
theorem selectedVisibleLocalWitness_noGlobalRepairCoherent :
    Not (GlobalSemanticRepairCoherent selectedVisibleLocalWitnessComplex) := by
  intro hglobal
  rcases hglobal with ⟨primitive, hboundary, _hclosed⟩
  exact selectedVisibleLocalWitness_boundary_not_residual primitive hboundary

/-! ## Faithfulness discharge certificate -/

/--
An explicit finite atlas class whose boundary primitives use the complete
refined semantic repair support on the selected repair-frontier cover.

This class is the Stage 2.5b discharge boundary for the target theorem: within
this finite class, semantic faithfulness is not an undischarged premise because
it follows from the already proved complete-support component coverage and
residual-component faithfulness theorems.
-/
structure CompleteRepairSupportBoundaryComplex where
  K : FiniteSemanticRepairGluingComplex RefinedSemanticRepairAtom
  projection_eq : K.projection = refinedSemanticComponent
  cover_eq : K.cover = repairFrontierOverlapBasisCover
  support_eq : forall primitive, K.supportOf primitive = completeRepairSupport

/--
The complete-support finite atlas class discharges `SemanticFaithfulnessHypotheses`.
-/
theorem completeRepairSupportBoundary_semanticFaithfulnessHypotheses
    (L : CompleteRepairSupportBoundaryComplex) :
    SemanticFaithfulnessHypotheses L.K := by
  constructor
  · intro primitive _hboundary
    simpa [L.projection_eq, L.cover_eq, L.support_eq primitive] using
      completeRepairSupport_closed_decomposes_as_componentCoverage_and_faithfulness.1
  · intro primitive _hboundary
    simpa [L.projection_eq, L.cover_eq, L.support_eq primitive] using
      completeRepairSupport_closed_decomposes_as_componentCoverage_and_faithfulness.2

/--
Finite semantic repair-gluing descent for the complete-support finite atlas
class, with the faithfulness premise discharged by the class certificate.
-/
theorem finiteSemanticRepairGluingDescent_iff_of_completeRepairSupportBoundary
    (L : CompleteRepairSupportBoundaryComplex) :
    GlobalSemanticRepairCoherent L.K <-> ObstructionClassVanishes L.K := by
  exact
    finiteSemanticRepairGluingDescent_iff L.K
      (completeRepairSupportBoundary_semanticFaithfulnessHypotheses L)

/--
Concrete faithful calibration complex: its single boundary primitive has the
complete refined semantic repair support and its selected residual is a
`delta0` boundary.
-/
def selectedFaithfulBoundaryComplex :
    FiniteSemanticRepairGluingComplex RefinedSemanticRepairAtom where
  Chart := Unit
  Overlap := fun _ _ => Unit
  chartOrder := [()]
  chart_complete := by
    intro chart
    cases chart
    simp
  C0 := Unit
  C1 := Bool
  c0Order := [()]
  c0_complete := by
    intro primitive
    cases primitive
    simp
  c1Order := [false, true]
  c1_complete := by
    intro cochain
    cases cochain <;> simp
  projection := refinedSemanticComponent
  cover := repairFrontierOverlapBasisCover
  supportOf := fun _ => completeRepairSupport
  leftRestriction := fun _ {_source} {_target} _overlap _atom => True
  rightRestriction := fun _ {_source} {_target} _overlap _atom => False
  cochainAt := fun cochain {_source} {_target} _overlap _atom => cochain = true
  delta0 := fun _ => true
  delta0_exact := by
    intro primitive source target overlap atom
    cases primitive
    cases source
    cases target
    cases overlap
    simp
  residual := true

/-- The selected faithful complex belongs to the complete-support boundary class. -/
def selectedFaithfulBoundaryClass :
    CompleteRepairSupportBoundaryComplex where
  K := selectedFaithfulBoundaryComplex
  projection_eq := rfl
  cover_eq := rfl
  support_eq := by
    intro primitive
    cases primitive
    rfl

/--
Concrete discharge of `SemanticFaithfulnessHypotheses` for the selected
faithful boundary complex.
-/
theorem selectedFaithfulBoundary_semanticFaithfulnessHypotheses :
    SemanticFaithfulnessHypotheses selectedFaithfulBoundaryComplex := by
  exact
    completeRepairSupportBoundary_semanticFaithfulnessHypotheses
      selectedFaithfulBoundaryClass

/-- The selected faithful boundary complex has vanishing finite obstruction. -/
theorem selectedFaithfulBoundary_obstructionVanishes :
    ObstructionClassVanishes selectedFaithfulBoundaryComplex := by
  exact ⟨(), rfl⟩

/--
The selected faithful boundary complex has a global semantic repair coherent
certificate without leaving `SemanticFaithfulnessHypotheses` undischarged.
-/
theorem selectedFaithfulBoundary_globalRepairCoherent :
    GlobalSemanticRepairCoherent selectedFaithfulBoundaryComplex := by
  exact
    globalRepairCoherent_of_obstructionVanishes
      selectedFaithfulBoundaryComplex
      selectedFaithfulBoundary_semanticFaithfulnessHypotheses
      selectedFaithfulBoundary_obstructionVanishes

/--
Concrete finite descent equivalence for the selected faithful boundary complex,
with all semantic faithfulness evidence discharged.
-/
theorem selectedFaithfulBoundary_descent_iff :
    GlobalSemanticRepairCoherent selectedFaithfulBoundaryComplex <->
      ObstructionClassVanishes selectedFaithfulBoundaryComplex := by
  exact
    finiteSemanticRepairGluingDescent_iff_of_completeRepairSupportBoundary
      selectedFaithfulBoundaryClass

/-! ## Theorem package -/

/--
Finite Semantic Repair-Gluing Descent theorem package.

The package keeps the three target directions separate:
necessity, the nonzero-obstruction contrapositive, and sufficiency under
explicit semantic faithfulness hypotheses.
-/
theorem finiteSemanticRepairGluingDescent_package
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (hfaithful : SemanticFaithfulnessHypotheses K) :
    (GlobalSemanticRepairCoherent K -> ObstructionClassVanishes K) /\
      (ObstructionClassNonzero K -> Not (GlobalSemanticRepairCoherent K)) /\
      (ObstructionClassVanishes K -> GlobalSemanticRepairCoherent K) /\
      (GlobalSemanticRepairCoherent K <-> ObstructionClassVanishes K) /\
      (forall {Atom' : Type u}
        {projection : Atom' -> BridgeComponent}
        {cover : HandoffCechCover}
        {support : Atom' -> Prop},
        SemanticRepairClosed projection cover support <->
          ResidualComponentCoveredSupport projection cover support /\
            ResidualComponentFaithfulSupport projection cover support) /\
      (forall {Source : Type u}
        {Target : Type v}
        {sourceProjection : Source -> BridgeComponent}
        {sourceCover : HandoffCechCover}
        {sourceSupport : Source -> Prop}
        {targetProjection : Target -> BridgeComponent}
        {targetCover : HandoffCechCover}
        {targetSupport : Target -> Prop},
        ResidualSupportTransport
            sourceProjection sourceCover sourceSupport
            targetProjection targetCover targetSupport ->
          (SemanticRepairClosed sourceProjection sourceCover sourceSupport <->
            SemanticRepairClosed targetProjection targetCover targetSupport)) /\
      VisibleLocalDeclaredClearanceSemanticObstruction
        RepairTransportCechCommutatorCurvature.selectedRepairTransportCechCommutatorCell
        ComponentClearanceSemanticObstruction.traceRepairFrontierDeclaredPlan /\
      ObstructionClassNonzero selectedVisibleLocalWitnessComplex /\
      Not (GlobalSemanticRepairCoherent selectedVisibleLocalWitnessComplex) /\
      SemanticFaithfulnessHypotheses selectedFaithfulBoundaryComplex /\
      ObstructionClassVanishes selectedFaithfulBoundaryComplex /\
      GlobalSemanticRepairCoherent selectedFaithfulBoundaryComplex /\
      (GlobalSemanticRepairCoherent selectedFaithfulBoundaryComplex <->
        ObstructionClassVanishes selectedFaithfulBoundaryComplex) /\
      Not
        (forall cell : RepairTransportCechCommutatorCurvature.RepairTransportCechCommutatorCell,
          forall plan : HandoffRepairTransversalTheorem.HandoffRepairPlan,
            VisibleLocalDeclaredClearanceProfile cell plan ->
              SemanticRepairCocycleWitness.SemanticRepairGluingExact cell.flatPath ->
                SemanticRepairCocycleWitness.SemanticRepairGluingExact cell.curvedPath) := by
  exact
    ⟨globalRepairCoherent_forces_obstructionVanishes K,
      no_globalRepairCoherent_of_nonzero_obstruction K,
      globalRepairCoherent_of_obstructionVanishes K hfaithful,
      finiteSemanticRepairGluingDescent_iff K hfaithful,
      fun {_Atom'} {_projection} {_cover} {_support} =>
        residualComponentFaithfulness_bridge_for_descent,
      fun {_Source} {_Target} {_sourceProjection} {_sourceCover} {_sourceSupport}
          {_targetProjection} {_targetCover} {_targetSupport} transport =>
      residualSupportTransport_bridge_for_descent transport,
      visibleLocalSemanticGluing_witness_validation.1,
      selectedVisibleLocalWitness_obstructionNonzero,
      selectedVisibleLocalWitness_noGlobalRepairCoherent,
      selectedFaithfulBoundary_semanticFaithfulnessHypotheses,
      selectedFaithfulBoundary_obstructionVanishes,
      selectedFaithfulBoundary_globalRepairCoherent,
      selectedFaithfulBoundary_descent_iff,
      visibleLocalSemanticGluing_witness_validation.2.1⟩

/--
Finite Semantic Repair-Gluing Descent theorem package for the complete-support
finite atlas class, with `SemanticFaithfulnessHypotheses` discharged by the
class certificate rather than left as a theorem argument.
-/
theorem finiteSemanticRepairGluingDescent_package_of_completeRepairSupportBoundary
    (L : CompleteRepairSupportBoundaryComplex) :
    (GlobalSemanticRepairCoherent L.K -> ObstructionClassVanishes L.K) /\
      (ObstructionClassNonzero L.K -> Not (GlobalSemanticRepairCoherent L.K)) /\
      (ObstructionClassVanishes L.K -> GlobalSemanticRepairCoherent L.K) /\
      (GlobalSemanticRepairCoherent L.K <-> ObstructionClassVanishes L.K) /\
      SemanticFaithfulnessHypotheses L.K /\
      (forall {Atom' : Type u}
        {projection : Atom' -> BridgeComponent}
        {cover : HandoffCechCover}
        {support : Atom' -> Prop},
        SemanticRepairClosed projection cover support <->
          ResidualComponentCoveredSupport projection cover support /\
            ResidualComponentFaithfulSupport projection cover support) /\
      (forall {Source : Type u}
        {Target : Type v}
        {sourceProjection : Source -> BridgeComponent}
        {sourceCover : HandoffCechCover}
        {sourceSupport : Source -> Prop}
        {targetProjection : Target -> BridgeComponent}
        {targetCover : HandoffCechCover}
        {targetSupport : Target -> Prop},
        ResidualSupportTransport
            sourceProjection sourceCover sourceSupport
            targetProjection targetCover targetSupport ->
          (SemanticRepairClosed sourceProjection sourceCover sourceSupport <->
            SemanticRepairClosed targetProjection targetCover targetSupport)) /\
      VisibleLocalDeclaredClearanceSemanticObstruction
        RepairTransportCechCommutatorCurvature.selectedRepairTransportCechCommutatorCell
        ComponentClearanceSemanticObstruction.traceRepairFrontierDeclaredPlan /\
      ObstructionClassNonzero selectedVisibleLocalWitnessComplex /\
      Not (GlobalSemanticRepairCoherent selectedVisibleLocalWitnessComplex) /\
      SemanticFaithfulnessHypotheses selectedFaithfulBoundaryComplex /\
      ObstructionClassVanishes selectedFaithfulBoundaryComplex /\
      GlobalSemanticRepairCoherent selectedFaithfulBoundaryComplex /\
      (GlobalSemanticRepairCoherent selectedFaithfulBoundaryComplex <->
        ObstructionClassVanishes selectedFaithfulBoundaryComplex) /\
      Not
        (forall cell : RepairTransportCechCommutatorCurvature.RepairTransportCechCommutatorCell,
          forall plan : HandoffRepairTransversalTheorem.HandoffRepairPlan,
            VisibleLocalDeclaredClearanceProfile cell plan ->
              SemanticRepairCocycleWitness.SemanticRepairGluingExact cell.flatPath ->
                SemanticRepairCocycleWitness.SemanticRepairGluingExact cell.curvedPath) := by
  have hfaithful :
      SemanticFaithfulnessHypotheses L.K :=
    completeRepairSupportBoundary_semanticFaithfulnessHypotheses L
  exact
    ⟨globalRepairCoherent_forces_obstructionVanishes L.K,
      no_globalRepairCoherent_of_nonzero_obstruction L.K,
      globalRepairCoherent_of_obstructionVanishes L.K hfaithful,
      finiteSemanticRepairGluingDescent_iff L.K hfaithful,
      hfaithful,
      fun {_Atom'} {_projection} {_cover} {_support} =>
        residualComponentFaithfulness_bridge_for_descent,
      fun {_Source} {_Target} {_sourceProjection} {_sourceCover} {_sourceSupport}
          {_targetProjection} {_targetCover} {_targetSupport} transport =>
        residualSupportTransport_bridge_for_descent transport,
      visibleLocalSemanticGluing_witness_validation.1,
      selectedVisibleLocalWitness_obstructionNonzero,
      selectedVisibleLocalWitness_noGlobalRepairCoherent,
      selectedFaithfulBoundary_semanticFaithfulnessHypotheses,
      selectedFaithfulBoundary_obstructionVanishes,
      selectedFaithfulBoundary_globalRepairCoherent,
      selectedFaithfulBoundary_descent_iff,
      visibleLocalSemanticGluing_witness_validation.2.1⟩

end SemanticRepairGluingComplex
end QualitySurface
end Formal.AG.Research
