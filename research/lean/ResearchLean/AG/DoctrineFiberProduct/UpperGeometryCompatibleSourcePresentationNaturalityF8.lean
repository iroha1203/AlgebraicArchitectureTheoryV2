import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF7

/-!
# Whole-input and finite-chain source-presentation coherence

This module closes the record-level part of G-118 C1s.  Identity and typed
composition reconstruct their terminal inputs definitionally.  Inversion also
restores the original input propositionally: its source diagram is a double
conjugation, while its authored comparator is conjugated by mutually inverse
complete-geometry isomorphisms.

The final section packages genuinely dependent finite chains.  Every next
change is indexed by the reconstructed input of the preceding change; hence no
untyped list or hidden cast is used to compose presentation replacements.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleSourcePresentationChange

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- Proof terms inhabiting possibly different propositions are heterogeneously
equal.  This local helper is used only after the corresponding data fields have
been identified by structure congruence. -/
private theorem proof_heq {p q : Prop} (hp : p) (hq : q) : HEq hp hq := by
  have hpq : p = q := propext ⟨fun _ => hq, fun _ => hp⟩
  cases hpq
  exact heq_of_eq (Subsingleton.elim _ _)

/-- The identity change reconstructs the whole original compatible input. -/
@[simp] theorem identity_changedInput
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    (identity input).changedInput = input := by
  rfl

/-- Inverting a source-presentation change reconstructs the whole original
input.  The non-definitional content is cancellation of the double conjugation
on the source diagram and authored comparator. -/
theorem inverse_changedInput
    (change : UpperGeometryCompatibleSourcePresentationChange input) :
    change.inverse.changedInput = input := by
  cases input with
  | mk root rootPath diagram geometry transport =>
      cases transport with
      | mk edgeLift edge_base edgeGeometryStrong edgeCoreStrong twoCellBase
          comparator edgeCoefficient comparatorCoefficient =>
        simp [inverse, changedInput, changedSourceTransport, changedEdgeLift,
          changedComparator]
        constructor
        · apply CategoryTheory.Functor.ext
          · intro source target path
            simp [changedSourceFiberDiagram, Category.assoc]
          · intro object
            rfl
        · congr 1
          · apply CategoryTheory.Functor.ext
            · intro source target path
              simp [changedSourceFiberDiagram, Category.assoc]
            · intro object
              rfl
          · apply proof_heq
          · funext cell
            change CompositeFiberAut.conjugationEquiv
                (change.geometryIso (P.twoTarget cell))
                ((CompositeFiberAut.conjugationEquiv
                  (change.geometryIso (P.twoTarget cell))).symm
                  (comparator cell)) = comparator cell
            exact (CompositeFiberAut.conjugationEquiv
              (change.geometryIso (P.twoTarget cell))).apply_symm_apply
                (comparator cell)
          · apply proof_heq

/-- Typed composition reconstructs exactly the terminal input selected by the
second change. -/
@[simp] theorem comp_changedInput
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput) :
    (first.comp second).changedInput = second.changedInput := by
  rfl

/-! ## Dependent finite chains -/

/-- A finite sequence of source-presentation changes whose next link is indexed
by the reconstructed input of the preceding link. -/
inductive Chain :
    UpperGeometryCompatibleProblemInputData ctx P k → Type (max (u + 1) v)
  | nil (input : UpperGeometryCompatibleProblemInputData ctx P k) : Chain input
  | cons {input : UpperGeometryCompatibleProblemInputData ctx P k}
      (head : UpperGeometryCompatibleSourcePresentationChange input)
      (tail : Chain head.changedInput) : Chain input

namespace Chain

/-- The input reached after all links of a dependent source-change chain. -/
noncomputable def terminalInput
    {input : UpperGeometryCompatibleProblemInputData ctx P k} :
    Chain input → UpperGeometryCompatibleProblemInputData ctx P k
  | .nil initial => initial
  | .cons _ tail => tail.terminalInput

/-- Number of source-presentation replacements in a dependent chain. -/
noncomputable def length
    {input : UpperGeometryCompatibleProblemInputData ctx P k} :
    Chain input → Nat
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

/-- Compose every link of a dependent source-change chain into one change
oriented from its terminal presentation back to its initial presentation. -/
noncomputable def composite
    {input : UpperGeometryCompatibleProblemInputData ctx P k} :
    (chain : Chain input) → UpperGeometryCompatibleSourcePresentationChange input
  | .nil initial => identity initial
  | .cons head tail => head.comp tail.composite

/-- The composite of a dependent finite chain reconstructs precisely the
chain's terminal input. -/
theorem composite_changedInput_eq_terminalInput
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (chain : Chain input) :
    chain.composite.changedInput = chain.terminalInput := by
  induction chain with
  | nil initial =>
      simp [composite, terminalInput]
  | cons head tail inductionHypothesis =>
      simpa [composite, terminalInput] using inductionHypothesis

end Chain

end UpperGeometryCompatibleSourcePresentationChange
end AAT.AG.DoctrineFiberProduct
