import Formal.Arch.OperationInvariant
import Formal.Arch.OperationLaws

namespace Formal.Arch

universe u v w q r

/--
State universe for the runtime protection layer.

The component universe and region are explicit fields because runtime
protection claims are bounded by measured components and a selected region.
-/
structure RuntimeProtectionState (C : Type u) (A : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q) (SemanticObs : Type r) where
  X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs
  U : ComponentUniverse X.static
  region : C -> Prop

/--
A proof-carrying runtime protection operation.

The operation family has two representatives: `isolate`, backed by the
selected runtime-localization law, and `protect`, backed by the policy-aware
runtime-protection law.  Both are bounded theorem packages, not global runtime
claims.
-/
inductive RuntimeProtectionOperation
    (C : Type u) (A : Type v) (StaticObs : Type w)
    (SemanticExpr : Type q) (SemanticObs : Type r) where
  | isolate
      (source target :
        RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs)
      (assumptions :
        (ArchitectureCalculusLaw.isolateRuntimeLocalizationLaw
          target.X target.U target.region).AssumptionsHold)
  | protect
      (source target :
        RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs)
      (assumptions :
        (ArchitectureCalculusLaw.protectRuntimeProtectionLaw
          target.X target.U target.region).AssumptionsHold)

/-- Source map for runtime protection operations. -/
def runtimeProtectionOperationSource
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    (op : RuntimeProtectionOperation C A StaticObs SemanticExpr SemanticObs) :
    RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs :=
  match op with
  | RuntimeProtectionOperation.isolate source _target _assumptions => source
  | RuntimeProtectionOperation.protect source _target _assumptions => source

/-- Target map for runtime protection operations. -/
def runtimeProtectionOperationTarget
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    (op : RuntimeProtectionOperation C A StaticObs SemanticExpr SemanticObs) :
    RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs :=
  match op with
  | RuntimeProtectionOperation.isolate _source target _assumptions => target
  | RuntimeProtectionOperation.protect _source target _assumptions => target

/--
Selected invariant axes for the runtime protection layer.

These are only the bounded runtime properties exposed by the existing
`isolate` / `protect` law packages.
-/
inductive RuntimeProtectionInvariant where
  | pathLocalized
  | interactionProtected
  | runtimeFlat

/-- Interpretation of runtime-protection invariants on a selected state. -/
def runtimeProtectionInvariantHolds
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r} :
    RuntimeProtectionInvariant ->
      RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs -> Prop
  | RuntimeProtectionInvariant.pathLocalized, state =>
      ArchitectureCalculusLaw.RuntimePathLocalizedWithin
        state.X state.U state.region
  | RuntimeProtectionInvariant.interactionProtected, state =>
      RuntimeInteractionProtected state.X state.U
  | RuntimeProtectionInvariant.runtimeFlat, state =>
      RuntimeFlatWithin state.X state.U

/-- The representative runtime protection invariant family used by the schema. -/
def runtimeProtectionInvariantFamily (_ : RuntimeProtectionInvariant) : Prop :=
  True

/-- The representative operation family: proof-carrying isolate / protect operations. -/
def runtimeProtectionOperationFamily
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    (_op : RuntimeProtectionOperation C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  True

/-- The isolate runtime law provides selected path localization at the target. -/
theorem runtimeProtectionOperation_isolate_preserves_pathLocalized
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    (_source target :
      RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs)
    (assumptions :
      (ArchitectureCalculusLaw.isolateRuntimeLocalizationLaw
        target.X target.U target.region).AssumptionsHold) :
    ArchitectureCalculusLaw.RuntimePathLocalizedWithin
      target.X target.U target.region :=
  (ArchitectureCalculusLaw.isolateRuntimeLocalizationLaw_conclusion
    target.X target.U target.region assumptions).1

/-- The isolate runtime law carries selected runtime interaction protection as an assumption. -/
theorem runtimeProtectionOperation_isolate_preserves_interactionProtected
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    (_source target :
      RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs)
    (assumptions :
      (ArchitectureCalculusLaw.isolateRuntimeLocalizationLaw
        target.X target.U target.region).AssumptionsHold) :
    RuntimeInteractionProtected target.X target.U :=
  assumptions.2.2.2.1

/-- The isolate runtime law provides bounded runtime flatness at the target. -/
theorem runtimeProtectionOperation_isolate_preserves_runtimeFlat
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    (_source target :
      RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs)
    (assumptions :
      (ArchitectureCalculusLaw.isolateRuntimeLocalizationLaw
        target.X target.U target.region).AssumptionsHold) :
    RuntimeFlatWithin target.X target.U :=
  (ArchitectureCalculusLaw.isolateRuntimeLocalizationLaw_conclusion
    target.X target.U target.region assumptions).2

/-- The protect runtime law provides selected path localization at the target. -/
theorem runtimeProtectionOperation_protect_preserves_pathLocalized
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    (_source target :
      RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs)
    (assumptions :
      (ArchitectureCalculusLaw.protectRuntimeProtectionLaw
        target.X target.U target.region).AssumptionsHold) :
    ArchitectureCalculusLaw.RuntimePathLocalizedWithin
      target.X target.U target.region :=
  (ArchitectureCalculusLaw.protectRuntimeProtectionLaw_conclusion
    target.X target.U target.region assumptions).1

/-- The protect runtime law provides selected runtime interaction protection at the target. -/
theorem runtimeProtectionOperation_protect_preserves_interactionProtected
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    (_source target :
      RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs)
    (assumptions :
      (ArchitectureCalculusLaw.protectRuntimeProtectionLaw
        target.X target.U target.region).AssumptionsHold) :
    RuntimeInteractionProtected target.X target.U :=
  (ArchitectureCalculusLaw.protectRuntimeProtectionLaw_conclusion
    target.X target.U target.region assumptions).2.1

/-- The protect runtime law provides bounded runtime flatness at the target. -/
theorem runtimeProtectionOperation_protect_preserves_runtimeFlat
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    (_source target :
      RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs)
    (assumptions :
      (ArchitectureCalculusLaw.protectRuntimeProtectionLaw
        target.X target.U target.region).AssumptionsHold) :
    RuntimeFlatWithin target.X target.U :=
  (ArchitectureCalculusLaw.protectRuntimeProtectionLaw_conclusion
    target.X target.U target.region assumptions).2.2

/--
The proof-carrying runtime protection operation preserves every invariant in
the selected runtime protection invariant family.
-/
theorem runtimeProtectionOperation_preserves_runtimeProtectionInvariant
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    (op : RuntimeProtectionOperation C A StaticObs SemanticExpr SemanticObs) :
    Ops runtimeProtectionOperationSource runtimeProtectionOperationTarget
      runtimeProtectionInvariantHolds runtimeProtectionInvariantFamily op := by
  intro invariant _hInvariant _hSource
  cases op with
  | isolate source target assumptions =>
      cases invariant
      · exact runtimeProtectionOperation_isolate_preserves_pathLocalized
          source target assumptions
      · exact runtimeProtectionOperation_isolate_preserves_interactionProtected
          source target assumptions
      · exact runtimeProtectionOperation_isolate_preserves_runtimeFlat
          source target assumptions
  | protect source target assumptions =>
      cases invariant
      · exact runtimeProtectionOperation_protect_preserves_pathLocalized
          source target assumptions
      · exact runtimeProtectionOperation_protect_preserves_interactionProtected
          source target assumptions
      · exact runtimeProtectionOperation_protect_preserves_runtimeFlat
          source target assumptions

/-- The runtime protection operation family is contained in `Ops(S)`. -/
theorem runtimeProtectionOperationFamily_subset_ops
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r} :
    PredicateSubset
      (runtimeProtectionOperationFamily :
        RuntimeProtectionOperation C A StaticObs SemanticExpr SemanticObs -> Prop)
      (Ops runtimeProtectionOperationSource runtimeProtectionOperationTarget
        runtimeProtectionInvariantHolds runtimeProtectionInvariantFamily) := by
  intro op _hOp
  exact runtimeProtectionOperation_preserves_runtimeProtectionInvariant op

/-- The selected runtime protection invariants are preserved by the operation family. -/
theorem runtimeProtectionInvariantFamily_subset_inv
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r} :
    PredicateSubset runtimeProtectionInvariantFamily
      (Inv
        (runtimeProtectionOperationSource :
          RuntimeProtectionOperation C A StaticObs SemanticExpr SemanticObs ->
            RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs)
        runtimeProtectionOperationTarget runtimeProtectionInvariantHolds
        runtimeProtectionOperationFamily) := by
  intro invariant _hInvariant op _hOp
  exact runtimeProtectionOperation_preserves_runtimeProtectionInvariant op invariant trivial

/--
Non-conclusion clauses recorded by the runtime protection schema.

These clauses mark empirical or coverage-completeness claims intentionally left
outside the bounded Lean theorem package.
-/
inductive RuntimeProtectionNonConclusionClause where
  | incidentReduction
  | repairCostReduction
  | runtimeTelemetryCompleteness
  | policyAwareCoverageCompleteness

/-- The runtime-protection schema records all explicit non-conclusion clauses. -/
def RuntimeProtectionNonConclusion : Prop :=
  ∀ _clause : RuntimeProtectionNonConclusionClause, True

/-- The runtime-protection non-conclusion clauses are recorded. -/
theorem runtimeProtection_nonConclusion :
    RuntimeProtectionNonConclusion := by
  intro clause
  cases clause <;> trivial

/--
Representative `DesignPattern` schema for protect / isolate runtime protection.

The closure laws are bounded preservation of selected path localization,
selected runtime interaction protection, and bounded runtime flatness.  Incident
reduction, repair cost reduction, telemetry completeness, and policy-aware
coverage completeness remain outside this theorem package.
-/
def runtimeProtectionDesignPattern
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r} :
    DesignPattern
      (runtimeProtectionOperationSource :
        RuntimeProtectionOperation C A StaticObs SemanticExpr SemanticObs ->
          RuntimeProtectionState C A StaticObs SemanticExpr SemanticObs)
      runtimeProtectionOperationTarget runtimeProtectionInvariantHolds where
  operationFamily := runtimeProtectionOperationFamily
  invariantFamily := runtimeProtectionInvariantFamily
  operationsPreserveInvariants := runtimeProtectionOperationFamily_subset_ops
  invariantsPreservedByOperations := runtimeProtectionInvariantFamily_subset_inv
  nonConclusion := RuntimeProtectionNonConclusion

/-- The runtime protection design pattern exposes the expected two closure laws. -/
theorem runtimeProtectionDesignPattern_closure_law
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r} :
    PredicateSubset
        (runtimeProtectionDesignPattern
          (C := C) (A := A) (StaticObs := StaticObs)
          (SemanticExpr := SemanticExpr) (SemanticObs := SemanticObs)).operationFamily
        (Ops runtimeProtectionOperationSource runtimeProtectionOperationTarget
          runtimeProtectionInvariantHolds
          (runtimeProtectionDesignPattern
            (C := C) (A := A) (StaticObs := StaticObs)
            (SemanticExpr := SemanticExpr) (SemanticObs := SemanticObs)).invariantFamily) ∧
      PredicateSubset
        (runtimeProtectionDesignPattern
          (C := C) (A := A) (StaticObs := StaticObs)
          (SemanticExpr := SemanticExpr) (SemanticObs := SemanticObs)).invariantFamily
        (Inv runtimeProtectionOperationSource runtimeProtectionOperationTarget
          runtimeProtectionInvariantHolds
          (runtimeProtectionDesignPattern
            (C := C) (A := A) (StaticObs := StaticObs)
            (SemanticExpr := SemanticExpr) (SemanticObs := SemanticObs)).operationFamily) := by
  constructor
  · exact runtimeProtectionOperationFamily_subset_ops
  · exact runtimeProtectionInvariantFamily_subset_inv

/-- The schema records the runtime-protection non-conclusion clauses. -/
theorem runtimeProtectionDesignPattern_records_nonConclusion
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r} :
    (runtimeProtectionDesignPattern
      (C := C) (A := A) (StaticObs := StaticObs)
      (SemanticExpr := SemanticExpr) (SemanticObs := SemanticObs)).RecordsNonConclusions :=
  runtimeProtection_nonConclusion

end Formal.Arch
