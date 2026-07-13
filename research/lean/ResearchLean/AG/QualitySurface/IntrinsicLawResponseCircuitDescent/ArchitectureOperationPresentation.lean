import Formal.Arch.Operation.Operation
import Formal.Util.AssertStandardAxioms
import Mathlib.RingTheory.Derivation.Basic

/-!
# Typed ambient presentation for primitive architecture operations

This file pairs each finite primitive operation label with a selected
`ArchitectureOperation` schema and a derivation of the ambient algebra before
law quotients are formed.  `RealizesFirstOrder` is the graph relation fixing the
schema and derivation selected by the same label.
-/

namespace ResearchLean.AG.QualitySurface
namespace IntrinsicLawResponseCircuitDescent

universe uₖ uA uOp uState uBefore uAfter

/--
The typed ambient presentation shared by the later localization and quotient
constructions.
-/
structure ArchitectureOperationPresentation
    (k : Type uₖ) (A₀ : Type uA) (Op : Type uOp)
    (State : Type uState) (BeforeWitness : Type uBefore)
    (AfterWitness : Type uAfter)
    [Field k] [CommRing A₀] [Algebra k A₀] [Fintype Op] where
  /-- The selected architecture-operation schema at a primitive label. -/
  operation :
    Op → Formal.Arch.ArchitectureOperation State BeforeWitness AfterWitness
  /-- The ambient derivation selected at the same primitive label. -/
  ambientDerivation : Op → Derivation k A₀ A₀

namespace ArchitectureOperationPresentation

variable {k : Type uₖ} {A₀ : Type uA} {Op : Type uOp}
variable {State : Type uState} {BeforeWitness : Type uBefore}
variable {AfterWitness : Type uAfter}
variable [Field k] [CommRing A₀] [Algebra k A₀] [Fintype Op]

/--
The label-indexed graph of the selected architecture-operation schema and its
ambient first-order derivation.
-/
def RealizesFirstOrder
    (P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness)
    (i : Op)
    (op : Formal.Arch.ArchitectureOperation State BeforeWitness AfterWitness)
    (ρ : Derivation k A₀ A₀) : Prop :=
  P.operation i = op ∧ P.ambientDerivation i = ρ

/-- Each label realizes exactly the schema and ambient derivation stored at it. -/
theorem realizesFirstOrder
    (P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness)
    (i : Op) :
    P.RealizesFirstOrder i (P.operation i) (P.ambientDerivation i) :=
  ⟨rfl, rfl⟩

/-- A first-order realization identifies its selected operation schema. -/
theorem RealizesFirstOrder.operation_eq
    {P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness}
    {i : Op}
    {op : Formal.Arch.ArchitectureOperation State BeforeWitness AfterWitness}
    {ρ : Derivation k A₀ A₀}
    (h : P.RealizesFirstOrder i op ρ) :
    P.operation i = op :=
  h.1

/-- A first-order realization identifies its selected ambient derivation. -/
theorem RealizesFirstOrder.ambientDerivation_eq
    {P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness}
    {i : Op}
    {op : Formal.Arch.ArchitectureOperation State BeforeWitness AfterWitness}
    {ρ : Derivation k A₀ A₀}
    (h : P.RealizesFirstOrder i op ρ) :
    P.ambientDerivation i = ρ :=
  h.2

/-- Replacing the selected operation schema breaks the graph relation. -/
theorem not_realizesFirstOrder_of_operation_ne
    (P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness)
    (i : Op)
    (op : Formal.Arch.ArchitectureOperation State BeforeWitness AfterWitness)
    (hop : op ≠ P.operation i) :
    ¬ P.RealizesFirstOrder i op (P.ambientDerivation i) := by
  intro h
  exact hop h.operation_eq.symm

/-- Replacing the selected ambient derivation breaks the graph relation. -/
theorem not_realizesFirstOrder_of_ambientDerivation_ne
    (P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness)
    (i : Op)
    (ρ : Derivation k A₀ A₀)
    (hρ : ρ ≠ P.ambientDerivation i) :
    ¬ P.RealizesFirstOrder i (P.operation i) ρ := by
  intro h
  exact hρ h.ambientDerivation_eq.symm

/-- The realized operation retains the generated-obligation kind of the core schema. -/
theorem RealizesFirstOrder.generatedObligation_kind
    {P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness}
    {i : Op}
    {op : Formal.Arch.ArchitectureOperation State BeforeWitness AfterWitness}
    {ρ : Derivation k A₀ A₀}
    (h : P.RealizesFirstOrder i op ρ) :
    op.generatedProofObligation.kind = op.kind := by
  rw [← h.operation_eq]
  exact (P.operation i).generatedObligation_kind

end ArchitectureOperationPresentation
end IntrinsicLawResponseCircuitDescent
end ResearchLean.AG.QualitySurface

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ArchitectureOperationPresentation
