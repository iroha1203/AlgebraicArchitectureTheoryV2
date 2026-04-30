import Formal.Arch.OperationKernel
import Formal.Arch.Repair
import Formal.Arch.RepairSynthesis

namespace Formal.Arch

universe u v r c

/--
Bounded Architecture Calculus law tags.

These are law-package names, not unconditional algebraic laws over every
operation in every universe.
-/
inductive ArchitectureCalculusLawKind where
  | identity
  | associativity
  | edgeUnion
  | refinementAbstraction
  | edgeEquivalence
  | protectionIdempotence
  | reverseInvolution
  | witnessMappingFunctoriality
  | synthesisSoundness
  | noSolutionSoundness
  deriving DecidableEq, Repr

namespace ArchitectureCalculusLawKind

/-- Human-readable law tag used by documentation-facing theorem packages. -/
def label : ArchitectureCalculusLawKind -> String
  | identity => "identity"
  | associativity => "associativity"
  | edgeUnion => "edgeUnion"
  | refinementAbstraction => "refinementAbstraction"
  | edgeEquivalence => "edgeEquivalence"
  | protectionIdempotence => "protectionIdempotence"
  | reverseInvolution => "reverseInvolution"
  | witnessMappingFunctoriality => "witnessMappingFunctoriality"
  | synthesisSoundness => "synthesisSoundness"
  | noSolutionSoundness => "noSolutionSoundness"

end ArchitectureCalculusLawKind

/--
Minimal bounded theorem package for an Architecture Calculus law.

The package keeps compatibility, coverage, exactness, and observation
equivalence visible.  The conclusion is available only from those selected
assumptions, so this does not state global associativity, global flatness
preservation, or idempotence for every operation.
-/
structure ArchitectureCalculusLaw (State : Type u) (Witness : Type v) where
  law : ArchitectureCalculusLawKind
  operationKind : ArchitectureOperationKind
  boundedUniverse : Prop
  compatibilityAssumptions : Prop
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  observationEquivalence : Prop
  conclusion : Prop
  sound :
    boundedUniverse ->
    compatibilityAssumptions ->
    coverageAssumptions ->
    exactnessAssumptions ->
    observationEquivalence ->
    conclusion
  nonConclusions : Prop

namespace ArchitectureCalculusLaw

variable {State : Type u} {Witness : Type v}

/-- Visible assumptions required before the law conclusion can be used. -/
def AssumptionsHold (L : ArchitectureCalculusLaw State Witness) : Prop :=
  L.boundedUniverse ∧
  L.compatibilityAssumptions ∧
  L.coverageAssumptions ∧
  L.exactnessAssumptions ∧
  L.observationEquivalence

/-- The theorem package explicitly records non-conclusions. -/
def RecordsNonConclusions (L : ArchitectureCalculusLaw State Witness) : Prop :=
  L.nonConclusions

/-- A bounded Architecture Calculus law yields its conclusion from its assumptions. -/
theorem conclusion_of_assumptions
    (L : ArchitectureCalculusLaw State Witness)
    (h : L.AssumptionsHold) :
    L.conclusion := by
  exact L.sound h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- Constructor for a bounded identity law package for a selected operation kind. -/
def identityLaw
    (operationKind : ArchitectureOperationKind)
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.identity
  operationKind := operationKind
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded `compose` associativity law package. -/
def composeAssociativity
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.associativity
  operationKind := ArchitectureOperationKind.compose
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded concrete `compose` edge-union law package. -/
def composeEdgeUnion
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.edgeUnion
  operationKind := ArchitectureOperationKind.compose
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded `replace` refinement/abstraction law package. -/
def replaceRefinementAbstraction
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.refinementAbstraction
  operationKind := ArchitectureOperationKind.replace
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded concrete `replace` edge-equivalence law package. -/
def replaceEdgeEquivalence
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.edgeEquivalence
  operationKind := ArchitectureOperationKind.replace
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded `protect` idempotence law package. -/
def protectIdempotence
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.protectionIdempotence
  operationKind := ArchitectureOperationKind.protect
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for a bounded reverse-involution law package. -/
def reverseInvolution
    (operationKind : ArchitectureOperationKind)
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.reverseInvolution
  operationKind := operationKind
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded `repair` monotonicity law package. -/
def repairMonotonicity
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.witnessMappingFunctoriality
  operationKind := ArchitectureOperationKind.repair
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

theorem identityLaw_kind
    (operationKind : ArchitectureOperationKind)
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (identityLaw (State := State) (Witness := Witness)
      operationKind boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).law =
        ArchitectureCalculusLawKind.identity :=
  rfl

theorem composeAssociativity_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (composeAssociativity (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.compose :=
  rfl

theorem composeEdgeUnion_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (composeEdgeUnion (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.compose :=
  rfl

theorem replaceRefinementAbstraction_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (replaceRefinementAbstraction (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.replace :=
  rfl

theorem replaceEdgeEquivalence_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (replaceEdgeEquivalence (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.replace :=
  rfl

theorem protectIdempotence_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (protectIdempotence (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.protect :=
  rfl

theorem reverseInvolution_kind
    (operationKind : ArchitectureOperationKind)
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (reverseInvolution (State := State) (Witness := Witness)
      operationKind boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).law =
        ArchitectureCalculusLawKind.reverseInvolution :=
  rfl

theorem repairMonotonicity_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (repairMonotonicity (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.repair :=
  rfl

section ConcreteGraphEntrypoints

variable {C : Type u}

/--
Bounded law package connecting concrete finite `compose` to edge union.

This records only the selected graph-kernel statement; it is not an
unconditional associativity or flatness-preservation theorem.
-/
def finiteComposeEdgeUnionLaw
    (FG FH : FiniteArchGraph C) :
    ArchitectureCalculusLaw (FiniteArchGraph C) PUnit :=
  composeEdgeUnion
    True True True True True
    (∀ c d : C,
      (FG.compose FH).graph.edge c d ↔
        FG.graph.edge c d ∨ FH.graph.edge c d)
    True
    (by
      intro _ _ _ _ _
      intro c d
      exact FiniteArchGraph.compose_edge_iff FG FH)

/-- The finite compose edge-union entrypoint keeps the `compose` operation tag. -/
theorem finiteComposeEdgeUnionLaw_operationKind
    (FG FH : FiniteArchGraph C) :
    (finiteComposeEdgeUnionLaw FG FH).operationKind =
      ArchitectureOperationKind.compose :=
  rfl

/-- The finite compose edge-union entrypoint yields the concrete edge-union theorem. -/
theorem finiteComposeEdgeUnionLaw_conclusion
    (FG FH : FiniteArchGraph C)
    (h : (finiteComposeEdgeUnionLaw FG FH).AssumptionsHold) :
    ∀ c d : C,
      (FG.compose FH).graph.edge c d ↔
        FG.graph.edge c d ∨ FH.graph.edge c d :=
  conclusion_of_assumptions (finiteComposeEdgeUnionLaw FG FH) h

/--
Bounded law package connecting edge-equivalent finite `replace` to preservation
of the source edge relation.
-/
def finiteReplaceEdgeEquivalenceLaw
    (FG FH : FiniteArchGraph C) :
    ArchitectureCalculusLaw (FiniteArchGraph C) PUnit :=
  replaceEdgeEquivalence
    True (EdgeEquivalent FG.graph FH.graph) True True True
    (∀ c d : C, (FG.replace FH).graph.edge c d ↔ FG.graph.edge c d)
    True
    (by
      intro _ hEquiv _ _ _
      intro c d
      exact FiniteArchGraph.replace_preserves_edges_of_edgeEquivalent
        FG FH hEquiv)

/-- The finite replace edge-equivalence entrypoint keeps the `replace` operation tag. -/
theorem finiteReplaceEdgeEquivalenceLaw_operationKind
    (FG FH : FiniteArchGraph C) :
    (finiteReplaceEdgeEquivalenceLaw FG FH).operationKind =
      ArchitectureOperationKind.replace :=
  rfl

/--
The finite replace edge-equivalence entrypoint yields source-edge preservation
from its bounded assumptions.
-/
theorem finiteReplaceEdgeEquivalenceLaw_conclusion
    (FG FH : FiniteArchGraph C)
    (h : (finiteReplaceEdgeEquivalenceLaw FG FH).AssumptionsHold) :
    ∀ c d : C, (FG.replace FH).graph.edge c d ↔ FG.graph.edge c d :=
  conclusion_of_assumptions (finiteReplaceEdgeEquivalenceLaw FG FH) h

/--
Bounded law package connecting graph-level `protect` identity to idempotence on
the selected finite graph kernel.
-/
def finiteProtectIdempotenceLaw
    (FG : FiniteArchGraph C) :
    ArchitectureCalculusLaw (FiniteArchGraph C) PUnit :=
  protectIdempotence
    True True True True True
    (∀ c d : C, FG.protect.protect.graph.edge c d ↔ FG.protect.graph.edge c d)
    True
    (by
      intro _ _ _ _ _
      intro c d
      exact FiniteArchGraph.protect_edge_iff FG.protect)

/-- The finite protect idempotence entrypoint keeps the `protect` operation tag. -/
theorem finiteProtectIdempotenceLaw_operationKind
    (FG : FiniteArchGraph C) :
    (finiteProtectIdempotenceLaw FG).operationKind =
      ArchitectureOperationKind.protect :=
  rfl

/-- The finite protect idempotence entrypoint yields concrete protect idempotence. -/
theorem finiteProtectIdempotenceLaw_conclusion
    (FG : FiniteArchGraph C)
    (h : (finiteProtectIdempotenceLaw FG).AssumptionsHold) :
    ∀ c d : C, FG.protect.protect.graph.edge c d ↔ FG.protect.graph.edge c d :=
  conclusion_of_assumptions (finiteProtectIdempotenceLaw FG) h

/--
Bounded law package connecting concrete finite reverse to reverse involution.
-/
def finiteReverseInvolutionLaw
    (FG : FiniteArchGraph C) :
    ArchitectureCalculusLaw (FiniteArchGraph C) PUnit :=
  reverseInvolution ArchitectureOperationKind.reverse
    True True True True True
    (∀ c d : C, FG.reverse.reverse.graph.edge c d ↔ FG.graph.edge c d)
    True
    (by
      intro _ _ _ _ _
      intro c d
      exact FiniteArchGraph.reverse_reverse_edge_iff FG)

/-- The finite reverse involution entrypoint keeps the `reverse` operation tag. -/
theorem finiteReverseInvolutionLaw_operationKind
    (FG : FiniteArchGraph C) :
    (finiteReverseInvolutionLaw FG).operationKind =
      ArchitectureOperationKind.reverse :=
  rfl

/-- The finite reverse involution entrypoint yields concrete double-reverse restoration. -/
theorem finiteReverseInvolutionLaw_conclusion
    (FG : FiniteArchGraph C)
    (h : (finiteReverseInvolutionLaw FG).AssumptionsHold) :
    ∀ c d : C, FG.reverse.reverse.graph.edge c d ↔ FG.graph.edge c d :=
  conclusion_of_assumptions (finiteReverseInvolutionLaw FG) h

end ConcreteGraphEntrypoints

section RepairEntrypoints

variable {Rule : Type r}

/--
Bounded law package connecting repair monotonicity to a selected obstruction
universe and an admissible repair rule.

The conclusion is only the selected-measure decrease for the chosen witness,
rule, and step; it is not termination, all-obstruction clearing, or global
flatness preservation.
-/
def repairStepDecreasesLaw
    (U : SelectedObstructionUniverse State Witness)
    (source target : State) (rule : Rule) (w : Witness) :
    ArchitectureCalculusLaw State Witness :=
  repairMonotonicity
    (U.selected w)
    (NonSplitExtensionWitness U source w)
    True
    (Nonempty (AdmissibleRepairRule U rule w))
    (Nonempty (RepairStep State Rule source rule target))
    (RepairStepDecreases U source target)
    True
    (by
      intro _ hWitness _ hRule hStep
      rcases hRule with ⟨hRule⟩
      rcases hStep with ⟨hStep⟩
      exact repairStepDecreases_of_admissible hWitness hRule hStep)

/-- The repair monotonicity entrypoint keeps the `repair` operation tag. -/
theorem repairStepDecreasesLaw_operationKind
    (U : SelectedObstructionUniverse State Witness)
    (source target : State) (rule : Rule) (w : Witness) :
    (repairStepDecreasesLaw U source target rule w).operationKind =
      ArchitectureOperationKind.repair :=
  rfl

/--
The repair monotonicity entrypoint yields selected-measure decrease from its
bounded assumptions.
-/
theorem repairStepDecreasesLaw_conclusion
    (U : SelectedObstructionUniverse State Witness)
    (source target : State) (rule : Rule) (w : Witness)
    (h : (repairStepDecreasesLaw U source target rule w).AssumptionsHold) :
    RepairStepDecreases U source target :=
  conclusion_of_assumptions (repairStepDecreasesLaw U source target rule w) h

end RepairEntrypoints

section SynthesisEntrypoints

variable {Constraint : Type c}
variable {Certificate : Type r}

/--
Bounded law package exposing soundness of a produced synthesis candidate.

This reads back an already sound candidate package; it does not state solver
completeness or that failure to produce a candidate means no solution exists.
-/
def synthesisCandidateSoundnessLaw
    (C : SynthesisConstraintSystem State Constraint)
    (pkg : SynthesisSoundnessPackage C) :
    ArchitectureCalculusLaw State Constraint where
  law := ArchitectureCalculusLawKind.synthesisSoundness
  operationKind := ArchitectureOperationKind.synthesize
  boundedUniverse := True
  compatibilityAssumptions := True
  coverageAssumptions := pkg.coverageAssumptions
  exactnessAssumptions := pkg.exactnessAssumptions
  observationEquivalence := True
  conclusion := ArchitectureSatisfies C pkg.candidate
  sound := by
    intro _ _ _ _ _
    exact SynthesisSoundnessPackage.candidate_satisfies pkg
  nonConclusions := pkg.nonConclusions

/-- The synthesis candidate soundness entrypoint keeps the `synthesize` operation tag. -/
theorem synthesisCandidateSoundnessLaw_operationKind
    (C : SynthesisConstraintSystem State Constraint)
    (pkg : SynthesisSoundnessPackage C) :
    (synthesisCandidateSoundnessLaw C pkg).operationKind =
      ArchitectureOperationKind.synthesize :=
  rfl

/--
The synthesis candidate soundness entrypoint yields candidate satisfaction from
its bounded assumptions.
-/
theorem synthesisCandidateSoundnessLaw_conclusion
    (C : SynthesisConstraintSystem State Constraint)
    (pkg : SynthesisSoundnessPackage C)
    (h : (synthesisCandidateSoundnessLaw C pkg).AssumptionsHold) :
    ArchitectureSatisfies C pkg.candidate :=
  conclusion_of_assumptions (synthesisCandidateSoundnessLaw C pkg) h

/--
Bounded law package exposing soundness of a valid no-solution certificate.

The certificate validity premise is explicit; solver failure alone is not
treated as evidence of non-existence.
-/
def noSolutionCertificateSoundnessLaw
    (C : SynthesisConstraintSystem State Constraint)
    (cert : Certificate)
    (pkg : NoSolutionCertificate Certificate C cert) :
    ArchitectureCalculusLaw State Certificate where
  law := ArchitectureCalculusLawKind.noSolutionSoundness
  operationKind := ArchitectureOperationKind.synthesize
  boundedUniverse := ValidNoSolutionCertificate pkg
  compatibilityAssumptions := True
  coverageAssumptions := pkg.coverageAssumptions
  exactnessAssumptions := pkg.exactnessAssumptions
  observationEquivalence := True
  conclusion := NoArchitectureSatisfies C
  sound := by
    intro hValid _ _ _ _
    exact NoSolutionCertificate.sound_of_valid pkg hValid
  nonConclusions := pkg.nonConclusions

/-- The no-solution certificate soundness entrypoint keeps the `synthesize` tag. -/
theorem noSolutionCertificateSoundnessLaw_operationKind
    (C : SynthesisConstraintSystem State Constraint)
    (cert : Certificate)
    (pkg : NoSolutionCertificate Certificate C cert) :
    (noSolutionCertificateSoundnessLaw C cert pkg).operationKind =
      ArchitectureOperationKind.synthesize :=
  rfl

/--
The no-solution certificate soundness entrypoint yields non-existence from a
valid certificate and its bounded assumptions.
-/
theorem noSolutionCertificateSoundnessLaw_conclusion
    (C : SynthesisConstraintSystem State Constraint)
    (cert : Certificate)
    (pkg : NoSolutionCertificate Certificate C cert)
    (h : (noSolutionCertificateSoundnessLaw C cert pkg).AssumptionsHold) :
    NoArchitectureSatisfies C :=
  conclusion_of_assumptions (noSolutionCertificateSoundnessLaw C cert pkg) h

end SynthesisEntrypoints

end ArchitectureCalculusLaw

end Formal.Arch
