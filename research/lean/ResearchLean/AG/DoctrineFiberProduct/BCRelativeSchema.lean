import ResearchLean.AG.DoctrineFiberProduct.BCPastingSchema
import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Authored-support signatures for relative Beck--Chevalley coherence

This module fixes the G-110 F0b2b type boundary.  Authored occurrences are
indexed by the finite G-106 2-cell type and form a discrete category.  The
choice is uniform in the input geometry and independent of comparator values;
it records exactly the authored support on which a pointwise table can form a
natural transformation, without asserting an extension to the whole fiber.

The module also separates the comparator-free support context from the raw
authored table.  It fixes the dependent function types that the later K2
direct-route, via-base-route, authored-comparison, and canonical-mate producers
must inhabit.  It deliberately does not supply those producers or define the
public `MateCoherentRel`: K2 must construct named values from the cartesian
regime and universal properties, then close the final relation over those
names.  No comparison, naturality certificate, canonical mate, or expected
equality is an input field here.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v₁ v₂ u₁ u₂

open CategoryTheory
open AtomFoundation
open TransportCoherence
open CrossStageCoherence

/-! ## Comparator-free authored support -/

/--
The semantic incidence needed to place every authored endpoint package in the
southwest core fiber of one realizable BC square.  The selected G-106 lift is
input geometry; `endpoint_eq` only identifies its authored endpoint with the
already selected square vertex.  Neither field contains a comparison, mate,
or coherence conclusion.
-/
structure AuthoredSupportContext (U : AtomCarrier.{u}) [DecidableEq U.Atom] where
  /-- The finite-code BC square whose relative comparison will be studied. -/
  square : RealizableSquare U
  /-- G-106 package and strongly cocartesian edge-lift data on its diagnostic. -/
  lift : AdmissibleLiftData square.semantic.diagnostic U
  /-- Every authored 2-cell endpoint package lies over the southwest vertex. -/
  endpoint_eq : ∀ cell : square.semantic.diagnostic.TwoCell,
    (packageProjection U).obj
        (lift.package (square.semantic.diagnostic.twoTarget cell)) =
      square.semantic.square.southwest

namespace AuthoredSupportContext

/-- The endpoint package supporting one authored 2-cell occurrence. -/
def supportPackage {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (cell : context.square.semantic.diagnostic.TwoCell) : AATCorePackage U :=
  context.lift.package (context.square.semantic.diagnostic.twoTarget cell)

/-- One tagged authored occurrence as an object of the southwest core fiber. -/
def supportObject {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (cell : context.square.semantic.diagnostic.TwoCell) :
    CoreFiber context.square.semantic.square.southwest :=
  ⟨context.supportPackage cell, context.endpoint_eq cell⟩

/--
The fixed authored-support domain.  Tags are retained even when two authored
2-cells have the same endpoint package.
-/
abbrev Category {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :=
  Discrete context.square.semantic.diagnostic.TwoCell

/-- Realize every tagged authored occurrence in the southwest core fiber. -/
def supportFunctor {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :
    context.Category ⥤ CoreFiber context.square.semantic.square.southwest :=
  Discrete.functor context.supportObject

end AuthoredSupportContext

/-! ## Authored datum on the same domain -/

/--
One realizable square with G-106 base data and the one-field authored
comparator table.  The support context is comparator-free, so a future
canonical mate can depend on `context` without seeing the authored values.
-/
structure AuthoredBCDatumSquare (U : AtomCarrier.{u}) [DecidableEq U.Atom] where
  /-- Comparator-free square, endpoint packages, and edge lifts. -/
  context : AuthoredSupportContext U
  /-- Declared parallel diagnostic paths have equal exact base morphisms. -/
  twoCellBase : ∀ cell : context.square.semantic.diagnostic.TwoCell,
    (context.lift.pathLift
        (context.square.semantic.diagnostic.twoLeft cell)).base =
      (context.lift.pathLift
        (context.square.semantic.diagnostic.twoRight cell)).base
  /-- The sole authored field: one endpoint-fiber automorphism per 2-cell. -/
  authored : AuthoredBC2CellPresentation context.supportPackage

namespace AuthoredBCDatumSquare

/-- Reassemble the reviewed G-106 semantic datum from the separated fields. -/
def toTransportData {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    AdmissibleTransportData input.context.square.semantic.diagnostic U where
  lift := input.context.lift
  twoCellBase := input.twoCellBase
  comparator := input.authored.comparator

/-- The same datum as the existing dependent diagnostic interpretation. -/
def toDiagnosticInterpretation {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    BCDiagnosticInterpretation U input.context.square.semantic where
  data := input.toTransportData

/--
Package an existing G-106 interpretation once its endpoint incidence with the
southwest square vertex has been proved.  No comparison output is supplied.
-/
def ofInterpretation {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (square : RealizableSquare U)
    (interpretation : BCDiagnosticInterpretation U square.semantic)
    (endpoint_eq : ∀ cell : square.semantic.diagnostic.TwoCell,
      (packageProjection U).obj
          (interpretation.data.lift.package
            (square.semantic.diagnostic.twoTarget cell)) =
        square.semantic.square.southwest) :
    AuthoredBCDatumSquare U where
  context :=
    { square := square
      lift := interpretation.data.lift
      endpoint_eq := endpoint_eq }
  twoCellBase := interpretation.data.twoCellBase
  authored := AuthoredBC2CellPresentation.ofTransportData interpretation.data

@[simp]
theorem toTransportData_lift {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    input.toTransportData.lift = input.context.lift := rfl

@[simp]
theorem toTransportData_comparator {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.toTransportData.comparator cell = input.authored.comparator cell := rfl

@[simp]
theorem ofInterpretation_comparator {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (square : RealizableSquare U)
    (interpretation : BCDiagnosticInterpretation U square.semantic)
    (endpoint_eq : ∀ cell : square.semantic.diagnostic.TwoCell,
      (packageProjection U).obj
          (interpretation.data.lift.package
            (square.semantic.diagnostic.twoTarget cell)) =
        square.semantic.square.southwest)
    (cell : square.semantic.diagnostic.TwoCell) :
    (ofInterpretation square interpretation endpoint_eq).authored.comparator cell =
      interpretation.data.comparator cell := rfl

/-! ## The raw table as a natural family on tagged support -/

/-- The total-category morphism underlying one authored comparator value. -/
def endpointComponentTotal {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportPackage cell ⟶ input.context.supportPackage cell :=
  PackageFiberAut.hom (input.authored.comparator cell)

/-- The authored endpoint component lies over the southwest identity. -/
theorem endpointComponentTotal_isHomLift
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    (packageProjection U).IsHomLift
      (𝟙 input.context.square.semantic.square.southwest)
      (input.endpointComponentTotal cell) := by
  apply CategoryTheory.IsHomLift.of_commsq
    (packageProjection U)
    (𝟙 input.context.square.semantic.square.southwest)
    (input.endpointComponentTotal cell)
    (input.context.endpoint_eq cell)
    (input.context.endpoint_eq cell)
  rw [packageProjection_map, endpointComponentTotal,
    PackageFiberAut.hom_base_eq]
  rw [Category.comp_id]
  exact Category.id_comp _

/-- One authored comparator as a morphism in the southwest core fiber. -/
def endpointComponent {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportObject cell ⟶ input.context.supportObject cell :=
  ⟨input.endpointComponentTotal cell,
    input.endpointComponentTotal_isHomLift cell⟩

/--
The complete authored table as a natural endotransformation of the discrete
support realization.  This is the raw endpoint family, not the later K2
Beck--Chevalley comparison.
-/
def endpointAutomorphism {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    input.context.supportFunctor ⟶ input.context.supportFunctor :=
  Discrete.natTrans (fun cell => input.endpointComponent cell.as)

@[simp]
theorem endpointAutomorphism_app {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.endpointAutomorphism.app (Discrete.mk cell) =
      input.endpointComponent cell := rfl

theorem endpointAutomorphism_app_val {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    (input.endpointAutomorphism.app (Discrete.mk cell)).1 =
      PackageFiberAut.hom (input.authored.comparator cell) := rfl

end AuthoredBCDatumSquare

/-! ## Exact K2 producer and relative-predicate signatures -/

/-- A route from tagged authored southwest support to the northeast core fiber. -/
abbrev AuthoredSupportRoute {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :=
  context.Category ⥤ CoreFiber context.square.semantic.square.northeast

/-- The dependent type of a named K2 route producer for every support context. -/
abbrev AuthoredSupportRouteFamily (U : AtomCarrier.{u}) [DecidableEq U.Atom] :=
  (context : AuthoredSupportContext U) → AuthoredSupportRoute context

/-- Pointwise components between two routes on the fixed discrete support. -/
abbrev AuthoredComparisonComponents {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] {context : AuthoredSupportContext U}
    (direct viaBase : AuthoredSupportRoute context) :=
  (cell : context.Category) → direct.obj cell ⟶ viaBase.obj cell

/-- Component quantification generates the required support naturality. -/
def authoredComparisonOfComponents {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] {context : AuthoredSupportContext U}
    {direct viaBase : AuthoredSupportRoute context}
    (components : AuthoredComparisonComponents direct viaBase) :
    direct ⟶ viaBase :=
  Discrete.natTrans components

@[simp]
theorem authoredComparisonOfComponents_app {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] {context : AuthoredSupportContext U}
    {direct viaBase : AuthoredSupportRoute context}
    (components : AuthoredComparisonComponents direct viaBase)
    (cell : context.Category) :
    (authoredComparisonOfComponents components).app cell = components cell := rfl

/--
Exact type of the K2 producer generated from an authored datum.  The later
implementation must be a named definition of this type and must prove direct
use of `input.authored`; accepting an arbitrary value of this type as a theorem
argument does not discharge K2.
-/
abbrev AuthoredComparisonProducerSignature
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (direct viaBase : AuthoredSupportRouteFamily U) :=
  (input : AuthoredBCDatumSquare U) →
    direct input.context ⟶ viaBase input.context

/--
Exact type of the canonical mate restricted to authored support.  Its input is
the comparator-free context, so the canonical side cannot inspect raw authored
values.  K2 must generate the value from adjunction units and counits.
-/
abbrev CanonicalMateRestrictionSignature
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (direct viaBase : AuthoredSupportRouteFamily U) :=
  (context : AuthoredSupportContext U) → direct context ⟶ viaBase context

namespace AuthoredSupportComparison

/-- Equality shape used by the final authored-relative coherence predicate. -/
def Agrees {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {direct viaBase : C ⥤ D}
    (authored canonical : direct ⟶ viaBase) : Prop :=
  authored = canonical

theorem agrees_self {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {direct viaBase : C ⥤ D}
    (comparison : direct ⟶ viaBase) : Agrees comparison comparison := rfl

theorem not_agrees_of_app_ne {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {direct viaBase : C ⥤ D}
    {authored canonical : direct ⟶ viaBase}
    (cell : C)
    (hne : authored.app cell ≠ canonical.app cell) :
    ¬ Agrees authored canonical := by
  intro hagrees
  exact hne (congrArg (fun comparison => comparison.app cell) hagrees)

end AuthoredSupportComparison

/--
The public K2 relation must have exactly this authored-datum-square domain.
K2 will define `MateCoherentRel input` by applying
`AuthoredSupportComparison.Agrees` to its two named producers; it may not expose
those producer values as extra relation arguments or input fields.
-/
abbrev MateCoherentRelSignature (U : AtomCarrier.{u}) [DecidableEq U.Atom] :=
  AuthoredBCDatumSquare U → Prop

/--
Type-check the final equation against the two K2 producer signatures.  This is
generic F0 schema scaffolding, not the public relation: K2 must specialize it
to its named generated comparison and named canonical mate, exposing only the
resulting `MateCoherentRelSignature` value.
-/
def mateCoherentRelEquation
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {direct viaBase : AuthoredSupportRouteFamily U}
    (authored : AuthoredComparisonProducerSignature direct viaBase)
    (canonical : CanonicalMateRestrictionSignature direct viaBase) :
    MateCoherentRelSignature U :=
  fun input => AuthoredSupportComparison.Agrees
    (authored input) (canonical input.context)

@[simp]
theorem mateCoherentRelEquation_apply
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {direct viaBase : AuthoredSupportRouteFamily U}
    (authored : AuthoredComparisonProducerSignature direct viaBase)
    (canonical : CanonicalMateRestrictionSignature direct viaBase)
    (input : AuthoredBCDatumSquare U) :
    mateCoherentRelEquation authored canonical input =
      AuthoredSupportComparison.Agrees
        (authored input) (canonical input.context) := rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
