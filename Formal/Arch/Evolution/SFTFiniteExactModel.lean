import Formal.Arch.Evolution.SFTEnvelope
import Formal.Arch.Evolution.SFTFiniteCover

/-!
Finite exact SFT model package.

This module packages the selected finite proof universe used by the SFT
Fundamental Modularity assumption-discharge roadmap.  It is a boundary-carrying
entrypoint over the existing `UniformFiniteFieldCover` and `FiniteSFTModel`
surface; it does not assert ambient source-observation coverage, empirical correctness, or
that every finite cover satisfies descent.
-/

namespace Formal.Arch

universe u v w x y z

/--
Selected finite proof universe for exact SFT theorem packages.

The list fields are the concrete selected carriers.  The proposition fields
record the boundaries under which those carriers, the exact cover, operation
support, observation boundary, and governance basis are being used.
-/
structure FiniteExactSFTModel
    (Global : Type u) (Index : Type v) (Local : Type w)
    (OperationG : Type x) (OperationL : Type y)
    (Governance : Type z) where
  selectedGlobalCarrier : List Global
  selectedIndexCarrier : List Index
  selectedLocalCarrier : List Local
  selectedOperationCarrier : List OperationG
  governanceBasisCarrier : List Governance
  cover : UniformFiniteFieldCover Global Index Local
  cover_indices_eq_selected : cover.indices = selectedIndexCarrier
  finiteModel : FiniteSFTModel cover OperationG OperationL
  observationBoundary : ObservationBoundary Global
  exactCoverBoundary : Prop
  selectedUniverseBoundary : Prop
  operationSupportBoundary : Prop
  operationRelationBoundary : Prop
  observationBoundaryExplicit : Prop
  governanceBasisBoundary : Prop
  finiteModelBoundary : Prop
  extractorBoundary : Prop
  empiricalBoundary : Prop
  nonConclusions : Prop

namespace FiniteExactSFTModel

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {OperationG : Type x} {OperationL : Type y}
variable {Governance : Type z}

/-- Public entrypoint to the selected exact finite cover. -/
def exactCover
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    UniformFiniteFieldCover Global Index Local :=
  model.cover

/-- Public entrypoint to the theorem-bearing finite SFT model. -/
def descentModel
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    FiniteSFTModel model.cover OperationG OperationL :=
  model.finiteModel

/-- Public entrypoint to the selected global finite carrier. -/
def selectedGlobals
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    List Global :=
  model.selectedGlobalCarrier

/-- Public entrypoint to the selected finite index carrier. -/
def selectedIndices
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    List Index :=
  model.selectedIndexCarrier

/-- Public entrypoint to the selected local finite carrier. -/
def selectedLocals
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    List Local :=
  model.selectedLocalCarrier

/-- Public entrypoint to the selected operation carrier. -/
def selectedOperations
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    List OperationG :=
  model.selectedOperationCarrier

/-- Public entrypoint to the selected governance basis carrier. -/
def governanceBasis
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    List Governance :=
  model.governanceBasisCarrier

/-- The exact cover uses the selected finite index carrier. -/
theorem exactCover_indices_eq_selected
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    model.exactCover.indices = model.selectedIndexCarrier :=
  model.cover_indices_eq_selected

/-- The package records its selected finite universe boundary. -/
def RecordsSelectedUniverseBoundary
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    Prop :=
  model.selectedUniverseBoundary

/-- The package records exact-cover assumptions as boundary data. -/
def RecordsExactCoverBoundary
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    Prop :=
  model.exactCoverBoundary ∧
    model.cover.RecordsCoverage ∧ model.cover.RecordsFiniteBoundary

/-- The package records operation-support and step-relation boundaries. -/
def RecordsOperationBoundary
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    Prop :=
  model.operationSupportBoundary ∧ model.operationRelationBoundary ∧
    model.finiteModel.supportBoundary ∧ model.finiteModel.stepBoundary

/-- The package records the finite-model boundary itself. -/
def RecordsFiniteModelBoundary
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    Prop :=
  model.finiteModelBoundary

/-- The package records the selected observation boundary. -/
def RecordsObservationBoundary
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    Prop :=
  model.observationBoundaryExplicit ∧
    model.observationBoundary.RecordsTheoremBoundary ∧
    model.observationBoundary.RecordsNonConclusions

/-- The package records the selected governance-basis boundary. -/
def RecordsGovernanceBasisBoundary
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    Prop :=
  model.governanceBasisBoundary

/--
The package keeps extractor and empirical boundaries explicit.

This accessor is intentionally negative: the package records these boundaries
without turning them into completeness or correctness theorems.
-/
def RecordsExtractorEmpiricalBoundary
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    Prop :=
  model.extractorBoundary ∧ model.empiricalBoundary

/--
Finite-exact non-conclusions remain explicit across the cover, finite model,
observation boundary, extractor boundary, and empirical boundary.
-/
def RecordsNonConclusions
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    Prop :=
  model.nonConclusions ∧
    model.cover.RecordsNonConclusions ∧
    model.finiteModel.nonConclusions ∧
    model.RecordsFiniteModelBoundary ∧
    model.observationBoundary.RecordsNonConclusions ∧
    model.RecordsExtractorEmpiricalBoundary

/-- The selected finite index carrier is available through the exact cover. -/
theorem selectedIndexCarrier_eq_cover_indices
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    model.selectedIndexCarrier = model.exactCover.indices :=
  model.cover_indices_eq_selected.symm

/-- The package exposes the finite descent model without adding descent laws. -/
theorem descentModel_eq_finiteModel
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance) :
    model.descentModel = model.finiteModel :=
  rfl

end FiniteExactSFTModel

/--
Explicit assumptions under which a finite exact SFT model has selected finite
ForecastCone descent.

The gluing data and projection/gluing laws remain caller-supplied theorem
premises.  This package therefore discharges the final-assembly assumption only
for the selected finite exact model and does not claim descent for every finite
cover.
-/
structure FiniteExactDescentAssumptions
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    (model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance)
    where
  glueData : FiniteClockedGluingData model.descentModel
  laws : FiniteProjectionGluingLaws glueData
  recordsExactCoverBoundary : model.RecordsExactCoverBoundary
  recordsOperationBoundary : model.RecordsOperationBoundary
  recordsObservationBoundary : model.RecordsObservationBoundary
  recordsGovernanceBoundary : model.RecordsGovernanceBasisBoundary
  recordsFiniteModelBoundary : model.RecordsFiniteModelBoundary
  selectedCompatibilityBoundary : Prop
  exactDescentBoundary : Prop
  nonConclusions : Prop

namespace FiniteExactDescentAssumptions

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {OperationG : Type x} {OperationL : Type y}
variable {Governance : Type z}
variable {model :
  FiniteExactSFTModel Global Index Local OperationG OperationL Governance}

/-- The assumptions expose the finite selected descent package. -/
def descentPackage
    (assumptions : FiniteExactDescentAssumptions model)
    {source : Global} {horizon : Nat} :
    FiniteSelectedForecastConeDescentPackage
      model.descentModel source horizon :=
  FiniteSelectedForecastConeDescentPackage.ofLaws
    assumptions.glueData assumptions.laws

/-- Exact-cover boundary assumptions remain explicit. -/
theorem records_exactCoverBoundary
    (assumptions : FiniteExactDescentAssumptions model) :
    model.RecordsExactCoverBoundary :=
  assumptions.recordsExactCoverBoundary

/-- Operation support / relation boundary assumptions remain explicit. -/
theorem records_operationBoundary
    (assumptions : FiniteExactDescentAssumptions model) :
    model.RecordsOperationBoundary :=
  assumptions.recordsOperationBoundary

/-- Observation-boundary assumptions remain explicit. -/
theorem records_observationBoundary
    (assumptions : FiniteExactDescentAssumptions model) :
    model.RecordsObservationBoundary :=
  assumptions.recordsObservationBoundary

/-- Governance-basis assumptions remain explicit. -/
theorem records_governanceBoundary
    (assumptions : FiniteExactDescentAssumptions model) :
    model.RecordsGovernanceBasisBoundary :=
  assumptions.recordsGovernanceBoundary

/-- The assumption package records the non-conclusion boundary. -/
def RecordsNonConclusions
    (assumptions : FiniteExactDescentAssumptions model) : Prop :=
  assumptions.nonConclusions ∧ model.RecordsNonConclusions ∧
    assumptions.glueData.nonConclusions ∧ assumptions.laws.nonConclusions

/--
The descent package boundary is the explicit finite gluing and compatibility
boundary supplied by the assumptions.
-/
def DescentPackageBoundary
    (assumptions : FiniteExactDescentAssumptions model)
    (source : Global) (horizon : Nat) : Prop :=
  (assumptions.descentPackage
    (source := source) (horizon := horizon)).packageBoundary

/-- The selected finite descent package keeps an explicit non-conclusion boundary. -/
def DescentPackageNonConclusions
    (assumptions : FiniteExactDescentAssumptions model)
    (source : Global) (horizon : Nat) : Prop :=
  (assumptions.descentPackage
    (source := source) (horizon := horizon)).nonConclusions

end FiniteExactDescentAssumptions

/--
Finite exact cover assumptions imply the selected finite ForecastCone descent
package for each selected source/horizon slice.

The conclusion is intentionally a selected package under explicit assumptions,
not full Cech cohomology and not descent for all finite covers.
-/
theorem finiteExactForecastConeDescentPackage_of_assumptions
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    {model :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
    (assumptions : FiniteExactDescentAssumptions model)
    {source : Global} {horizon : Nat} :
    Nonempty
      (FiniteSelectedForecastConeDescentPackage
        model.descentModel source horizon) :=
  ⟨assumptions.descentPackage⟩

end Formal.Arch
