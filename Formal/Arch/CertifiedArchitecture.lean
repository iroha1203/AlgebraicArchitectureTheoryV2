import Formal.Arch.Flatness
import Formal.Arch.Operation

namespace Formal.Arch

universe u v w q r s t

/--
Runtime dependency role used by `ArchitectureCore`.

The role is metadata for a selected runtime edge universe. It does not assert
that runtime telemetry is complete or that forbidden edges have been globally
excluded.
-/
inductive RuntimeDependencyRole where
  | rawDependency
  | protectedDependency
  | forbiddenDependency
  | unprotectedDependency
  deriving DecidableEq, Repr

/--
The minimal proof-carrying architecture object used by the AAT type-system
roadmap.

`flatness` reuses the existing static / runtime / semantic model. The supplied
`staticUniverse` is the proof-carrying finite measurement universe for static
components. Decidability fields record the bounded computation assumptions
needed by downstream theorem packages; they are intentionally explicit fields
instead of global extractor-completeness claims.
-/
structure ArchitectureCore (C : Type u) (A : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q)
    (SemanticObs : Type r) where
  flatness : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs
  staticUniverse : ComponentUniverse flatness.static
  componentDecidableEq : DecidableEq C
  staticEdgeDecidable : DecidableRel flatness.static.edge
  runtimeEdgeDecidable : DecidableRel flatness.runtime.edge
  boundaryPolicyDecidable : DecidableRel flatness.boundaryAllowed
  abstractionPolicyDecidable : DecidableRel flatness.abstractionAllowed
  runtimeRole : C -> C -> RuntimeDependencyRole
  semanticRequiredDecidable :
    ∀ d : RequiredDiagram SemanticExpr, Decidable (flatness.requiredSemantic d)

namespace ArchitectureCore

variable {C : Type u} {A : Type v} {StaticObs : Type w}
  {SemanticExpr : Type q} {SemanticObs : Type r}

/-- Forget the proof-carrying wrapper and recover the flatness model. -/
def toFlatnessModel
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs :=
  X.flatness

/-- The static law model selected by the core's finite component universe. -/
def staticLawModel
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    ArchitectureSignature.ArchitectureLawModel C A StaticObs :=
  ArchitectureFlatnessModel.staticLawModel X.flatness X.staticUniverse

/-- The core's measured semantic diagram universe. -/
def measuredSemanticUniverse
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    List (RequiredDiagram SemanticExpr) :=
  X.flatness.measuredSemantic

/-- The runtime dependency role selected for a component pair. -/
def runtimeDependencyRole
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) (c d : C) :
    RuntimeDependencyRole :=
  X.runtimeRole c d

/-- Every component is covered by the proof-carrying static universe. -/
theorem component_mem_staticUniverse
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) (c : C) :
    c ∈ X.staticUniverse.components :=
  X.staticUniverse.covers c

/-- Static dependency evidence is covered by the core's `ComponentUniverse`. -/
theorem staticCoverageComplete
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    StaticCoverageComplete X.flatness X.staticUniverse :=
  staticCoverageComplete_of_componentUniverse X.flatness X.staticUniverse

end ArchitectureCore

/-- Law role tags for certified architecture law universes. -/
inductive ArchitectureLawRole where
  | required
  | optional
  | derived
  deriving DecidableEq, Repr

/-- A finite law universe with required / optional / derived role metadata. -/
structure ArchitectureLawUniverse (Law : Type s) where
  laws : List Law
  role : Law -> ArchitectureLawRole

namespace ArchitectureLawUniverse

variable {Law : Type s}

/-- Laws selected as required in this bounded law universe. -/
def Required (U : ArchitectureLawUniverse Law) (law : Law) : Prop :=
  law ∈ U.laws ∧ U.role law = ArchitectureLawRole.required

/-- Laws selected as optional in this bounded law universe. -/
def Optional (U : ArchitectureLawUniverse Law) (law : Law) : Prop :=
  law ∈ U.laws ∧ U.role law = ArchitectureLawRole.optional

/-- Laws selected as derived in this bounded law universe. -/
def Derived (U : ArchitectureLawUniverse Law) (law : Law) : Prop :=
  law ∈ U.laws ∧ U.role law = ArchitectureLawRole.derived

end ArchitectureLawUniverse

/--
Finite obstruction-witness universe.

This is a bounded theorem-package input, not a claim that every possible
architecture obstruction has been enumerated.
-/
structure ObstructionWitnessUniverse (Witness : Type t) where
  witnesses : List Witness

/--
Named theorem package with an explicit proof obligation.

The package must also record its non-conclusions, preserving the project rule
that theorem packages expose what they do not prove.
-/
structure ArchitectureTheoremPackage (State : Type s) (Witness : Type t) where
  name : String
  obligation : ProofObligation State Witness
  recordsNonConclusions : obligation.RecordsNonConclusions

/--
Certified architecture object carrying law, invariant, witness, theorem-package,
and proof-obligation discharge data for one `ArchitectureCore`.

The proof field is bounded to the listed theorem packages. It does not assert
global completeness of the measured component universe, runtime telemetry, or
semantic diagram universe.
-/
structure CertifiedArchitecture (C : Type u) (A : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q) (SemanticObs : Type r)
    (Law : Type s) (Witness : Type t) where
  core : ArchitectureCore C A StaticObs SemanticExpr SemanticObs
  laws : ArchitectureLawUniverse Law
  invariants : List (ArchitectureCore C A StaticObs SemanticExpr SemanticObs -> Prop)
  witnessUniverse : ObstructionWitnessUniverse Witness
  theoremPackages :
    List (ArchitectureTheoremPackage
      (ArchitectureCore C A StaticObs SemanticExpr SemanticObs) Witness)
  proofs :
    ∀ {package}, package ∈ theoremPackages ->
      package.obligation.Discharged

namespace CertifiedArchitecture

variable {C : Type u} {A : Type v} {StaticObs : Type w}
  {SemanticExpr : Type q} {SemanticObs : Type r}
  {Law : Type s} {Witness : Type t}

/-- The proof-obligation list induced by the certified theorem packages. -/
def theoremPackageObligations
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness) :
    List (ProofObligation
      (ArchitectureCore C A StaticObs SemanticExpr SemanticObs) Witness) :=
  X.theoremPackages.map (fun package => package.obligation)

/-- All listed theorem packages have discharged proof obligations. -/
def ProofObligationDischargeSet
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness) :
    Prop :=
  ∀ {package}, package ∈ X.theoremPackages ->
    package.obligation.Discharged

/-- Accessor for the discharge proof carried by a certified architecture. -/
theorem theoremPackage_discharged
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness)
    {package :
      ArchitectureTheoremPackage
        (ArchitectureCore C A StaticObs SemanticExpr SemanticObs) Witness}
    (hMem : package ∈ X.theoremPackages) :
    package.obligation.Discharged :=
  X.proofs hMem

/-- The carried theorem packages form a proof-obligation discharge set. -/
theorem proofObligationDischargeSet
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness) :
    X.ProofObligationDischargeSet := by
  intro package hMem
  exact X.theoremPackage_discharged hMem

/-- Accessor for the non-conclusion clause recorded by a theorem package. -/
theorem theoremPackage_recordsNonConclusions
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness)
    {package :
      ArchitectureTheoremPackage
        (ArchitectureCore C A StaticObs SemanticExpr SemanticObs) Witness}
    (_hMem : package ∈ X.theoremPackages) :
    package.obligation.RecordsNonConclusions :=
  package.recordsNonConclusions

/-- A listed theorem package contributes its obligation to the obligation list. -/
theorem theoremPackage_obligation_mem
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness)
    {package :
      ArchitectureTheoremPackage
        (ArchitectureCore C A StaticObs SemanticExpr SemanticObs) Witness}
    (hMem : package ∈ X.theoremPackages) :
    package.obligation ∈ X.theoremPackageObligations :=
  List.mem_map.mpr ⟨package, hMem, rfl⟩

end CertifiedArchitecture

end Formal.Arch
