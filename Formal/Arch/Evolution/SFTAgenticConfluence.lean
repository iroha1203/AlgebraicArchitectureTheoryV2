import Formal.Arch.Evolution.SFTTheoremRoadmap

/-!
Selected Newman-style proof kernel for SFT agentic confluence.

The kernel is deliberately finite and package-relative.  It records a selected
reduction relation on accepted interleavings, an explicit normal-form witness,
and a pairwise joinability consequence supplied under termination and local
confluence assumptions.  It does not assert global AI safety or confluence for
unbounded agent teams.
-/

namespace Formal.Arch
namespace SFTAgenticConfluence

universe u v

/-- Reflexive-transitive closure of a selected interleaving reduction. -/
inductive ReductionReaches
    {Interleaving : Type u}
    (step : Interleaving -> Interleaving -> Prop) :
    Interleaving -> Interleaving -> Prop where
  | refl (state : Interleaving) :
      ReductionReaches step state state
  | trans {left middle right : Interleaving} :
      step left middle ->
        ReductionReaches step middle right ->
          ReductionReaches step left right

/-- A selected state is normal when it admits no outgoing reduction step. -/
def IsNormal
    {Interleaving : Type u}
    (step : Interleaving -> Interleaving -> Prop)
    (state : Interleaving) : Prop :=
  ∀ next, ¬ step state next

/-- Two selected interleavings join at a common reduct with the same landing. -/
def PairwiseJoinableLanding
    {Interleaving : Type u} {ConeQuotient : Type v}
    (step : Interleaving -> Interleaving -> Prop)
    (landing : Interleaving -> ConeQuotient) : Prop :=
  ∀ left right,
    ∃ joined,
      ReductionReaches step left joined ∧
        ReductionReaches step right joined ∧
          landing left = landing joined ∧
            landing right = landing joined

/--
Newman-style selected confluence kernel.

`pairwiseJoinable_of_local` is the explicit Newman-style bridge: selected
termination plus selected local confluence yield a common reduct preserving the
selected cone quotient landing.  The structure keeps interface, policy, and
descent boundaries separate from the proof kernel.
-/
structure NewmanStyleConfluenceKernel
    (Interleaving : Type u) (ConeQuotient : Type v) where
  step : Interleaving -> Interleaving -> Prop
  landing : Interleaving -> ConeQuotient
  normalForm : Interleaving -> Interleaving
  localTermination : Prop
  localConfluence : Prop
  forecastConeDescent : Prop
  interfaceConstraintsPreserved : Prop
  policiesCommutationInvariant : Prop
  reachesNormalForm :
    localTermination ->
      ∀ state, ReductionReaches step state (normalForm state)
  normalForm_isNormal :
    localTermination ->
      ∀ state, IsNormal step (normalForm state)
  pairwiseJoinable_of_local :
    localTermination ->
      localConfluence ->
        PairwiseJoinableLanding step landing
  agentBoundary : Prop
  nonConclusions : Prop

namespace NewmanStyleConfluenceKernel

/-- Pairwise joinability of selected interleavings gives fair landing convergence. -/
theorem fairInterleavingsConverge_of_pairwiseJoinable
    {Interleaving : Type u} {ConeQuotient : Type v}
    {step : Interleaving -> Interleaving -> Prop}
    {landing : Interleaving -> ConeQuotient}
    (hJoin : PairwiseJoinableLanding step landing) :
    SFTTheoremRoadmap.FairInterleavingsConverge landing := by
  intro left right
  rcases hJoin left right with
    ⟨joined, _hLeft, _hRight, hLeftLanding, hRightLanding⟩
  exact hLeftLanding.trans hRightLanding.symm

/-- Selected termination and local confluence imply fair interleaving convergence. -/
theorem newmanStyle_fairInterleavingsConverge
    {Interleaving : Type u} {ConeQuotient : Type v}
    (kernel : NewmanStyleConfluenceKernel Interleaving ConeQuotient)
    (hTermination : kernel.localTermination)
    (hConfluence : kernel.localConfluence) :
    SFTTheoremRoadmap.FairInterleavingsConverge kernel.landing :=
  fairInterleavingsConverge_of_pairwiseJoinable
    (kernel.pairwiseJoinable_of_local hTermination hConfluence)

/-- Read a Newman-style kernel as the existing agentic confluence package. -/
def agenticPackage
    {Interleaving : Type u} {ConeQuotient : Type v}
    (kernel : NewmanStyleConfluenceKernel Interleaving ConeQuotient) :
    SFTTheoremRoadmap.AgenticConfluencePackage Interleaving ConeQuotient where
  landing := kernel.landing
  localTermination := kernel.localTermination
  localConfluence := kernel.localConfluence
  forecastConeDescent := kernel.forecastConeDescent
  interfaceConstraintsPreserved := kernel.interfaceConstraintsPreserved
  policiesCommutationInvariant := kernel.policiesCommutationInvariant
  fairInterleavingsConverge := by
    intro hTermination hConfluence _hDescent _hInterface _hPolicy
    exact kernel.newmanStyle_fairInterleavingsConverge
      hTermination hConfluence
  agentBoundary := kernel.agentBoundary
  nonConclusions := kernel.nonConclusions

/-- The package read from the kernel records the Newman-style convergence theorem. -/
theorem agenticPackage_records_newmanStyle_confluence
    {Interleaving : Type u} {ConeQuotient : Type v}
    (kernel : NewmanStyleConfluenceKernel Interleaving ConeQuotient)
    (hTermination : kernel.localTermination)
    (hConfluence : kernel.localConfluence)
    (hDescent : kernel.forecastConeDescent)
    (hInterface : kernel.interfaceConstraintsPreserved)
    (hPolicy : kernel.policiesCommutationInvariant) :
    SFTTheoremRoadmap.FairInterleavingsConverge
      kernel.agenticPackage.landing :=
  SFTTheoremRoadmap.AgenticConfluencePackage.agentic_confluence
    kernel.agenticPackage hTermination hConfluence hDescent hInterface hPolicy

/-- The kernel keeps agentic proof boundaries explicit. -/
def RecordsAgentBoundary
    {Interleaving : Type u} {ConeQuotient : Type v}
    (kernel : NewmanStyleConfluenceKernel Interleaving ConeQuotient) :
    Prop :=
  kernel.agentBoundary

/-- The kernel records non-conclusions for selected agentic confluence. -/
def RecordsNonConclusions
    {Interleaving : Type u} {ConeQuotient : Type v}
    (kernel : NewmanStyleConfluenceKernel Interleaving ConeQuotient) :
    Prop :=
  kernel.nonConclusions

end NewmanStyleConfluenceKernel

end SFTAgenticConfluence
end Formal.Arch
