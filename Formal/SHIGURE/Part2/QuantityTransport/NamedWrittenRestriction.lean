import Formal.SHIGURE.Part2.QuantityTransport.CoefficientSyntax
import Formal.SHIGURE.Part2.QuantityTransport.WrittenRestriction

/-! # Coefficient equations with names in a primitive presentation

A primitive presentation can register coefficient equations at its Law
names. The comparison uses the registered expressions and the actual
antecedent of each retained Law.

## Implementation notes

The registration stores the literal expressions with their typed
primitive applications. A local occurrence index may simplify evaluation
but must rename back to the registered pair. Ambient and retained
coefficient equations are compiled from this same pair. The support proof
concerns only the applications used by the two expressions, and retention
follows from the dependency closure of Chapter 3.
-/

namespace SHIGURE.Quantities

open DeclarationContext

noncomputable section

universe u

/-- Written scalar equations using the actual quantity and Law declarations. -/
structure NamedWrittenLaws (k : Type u) (P : PrimitivePresentation.{u}) where
  /-- The named quantities that supply scalar coordinates. -/
  quantities : Set (QuantityDeclaration P.signature)
  /-- The required Law names that have scalar equations. -/
  laws : Set P.theory.LawName
  /-- Named applications used for each scalar equation. -/
  Occurrence : laws → Type u
  /-- Each application supplies argument terms typed at that original Law's input. -/
  application (l : laws) : Occurrence l →
    Σ j : quantities, Substitution P.signature j.val.operation.arity.inputs (P.theory.law l.val).context
  /-- The original left coefficient expression. -/
  left (l : laws) : Expression k (Occurrence l)
  /-- The original right coefficient expression. -/
  right (l : laws) : Expression k (Occurrence l)
  /-- Both sides name exactly the original registered applications and literals. -/
  registered (l : laws) : P.coefficientEquation k l.val.val = some
    ((left l).rename (fun a => ⟨(application l a).1.val, (application l a).2⟩),
     (right l).rename (fun a => ⟨(application l a).1.val, (application l a).2⟩))
  /-- Each application in the two written sides belongs to the original Law's declaration support. -/
  supports (l : laws) (a : Occurrence l) (used : a ∈ (left l).occurrences ∪ (right l).occurrences) :
    Declaration.ofOperation (application l a).1.val.operation ∈ Declaration.lawBody (P.theory.law l.val) ∧
      ∀ {s} (i : Var (application l a).1.val.operation.arity.inputs s),
        Declaration.formulaSupport ((application l a).2 i).graph ⊆ Declaration.lawBody (P.theory.law l.val)

namespace NamedWrittenLaws

variable {k : Type u} {P : PrimitivePresentation.{u}} (L : NamedWrittenLaws k P)
variable {U V : DeclarationContext P}

/-- The coefficient equations on the original named quantities, with the original Law arities. -/
def written : WrittenLaws k P.signature where
  Quantity := L.quantities
  domainContext j := j.val.operation.arity.inputs
  Law := L.laws
  inputContext l := (P.theory.law l.val).context
  Occurrence := L.Occurrence
  application := L.application
  left := L.left
  right := L.right

/-- Actual declaration closure supplies the supported inputs and occurrences of every retained equation. -/
def selection (U : DeclarationContext P) : L.written.DeclarationSelection where
  context := U
  quantities := {j | Declaration.ofOperation j.val.operation ∈ U.declarations}
  laws := {l | Declaration.law l.val.val ∈ U.declarations}
  domainSorts {j} keep := operationInputs j.val.operation keep
  inputSorts {l} keep :=
    (Declaration.sorts_subset_lawBody (P.theory.law l.val)).trans (Declaration.lawBody_subset_of_mem keep)
  applicationKept {l} keep a := (Declaration.lawBody_subset_of_mem keep) (L.supports l a.val a.property).1
  termKept {l} keep a := by
    intro s i
    exact (Declaration.termContext_le_iff _).2
      ((L.supports l a.val a.property).2 i |>.trans (Declaration.lawBody_subset_of_mem keep))

/-- An actual inclusion of primitive contexts retains the same named coefficient expressions. -/
def inclusion (inside : V ≤ U) : (L.selection V).Inclusion (L.selection U) where
  context := inside
  quantities := fun _ keep => inside keep
  laws := fun _ keep => inside keep

/-- A coefficient equation keeps the exact antecedent of its named Law. -/
def nativeInput (A : ContextStructure U) (l : (L.selection U).laws) :
    Set (Assignment A.carrier (L.written.inputContext l.val)) :=
  {e | A.evaluation.holds (P.theory.law l.val.val).input
    (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e}

/-- The actual antecedent is preserved and reflected on retained state assignments. -/
theorem nativeInput_restrict_iff (A : ContextStructure U) (inside : V ≤ U)
    (l : (L.selection V).laws) (e : Assignment (A.restrict inside).carrier (L.written.inputContext l.val)) :
    e ∈ L.nativeInput (A.restrict inside) l ↔
      A.restrictAssignmentEquiv inside ((L.selection V).inputSorts l.property) e ∈
        L.nativeInput A (Set.inclusion (L.inclusion inside).laws l) :=
  A.restrict_holds_iff inside _ _ e

/-- The interpretation of a registered Law uses exactly the inputs of its original guard. -/
abbrev GuardedInterpretation (A : ContextStructure U) :=
  {I : (L.selection U).Interpretation A // ∀ l, I.input l = L.nativeInput A l}

/-- The reduct of a guarded interpretation evaluates the original antecedents in the reduced state. -/
theorem restrict_input_eq_native {A : ContextStructure U} (I : L.GuardedInterpretation A) (inside : V ≤ U)
    (l : (L.selection V).laws) :
    (I.val.restrict (L.inclusion inside)).input l = L.nativeInput (A.restrict inside) l := by
  rw [I.val.restrict_input, I.property]
  exact Set.ext fun e => (L.nativeInput_restrict_iff A inside l e).symm

/-- The actual primitive restriction of registered scalar equations commutes with changing coefficients. -/
theorem lawMap_baseChange [CommRing k] {A : ContextStructure U} (I : L.GuardedInterpretation A)
    (inside : V ≤ U) (R : Type u) [CommRing R] [Algebra k R] :
    let F := (I.val.restrict (L.inclusion inside)).presentation
    let ι := I.val.lawMap (L.inclusion inside)
    (baseChangeQuotient (R := k) R I.val.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  I.val.lawMap_baseChange (L.inclusion inside) R

/-- The same registered equation and guard give the comparison on a principal open. -/
theorem lawMap_localization [CommRing k] {A : ContextStructure U} (I : L.GuardedInterpretation A)
    (inside : V ≤ U) (r : k) :
    let R := Localization.Away r
    let F := (I.val.restrict (L.inclusion inside)).presentation
    let ι := I.val.lawMap (L.inclusion inside)
    (baseChangeQuotient (R := k) R I.val.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  L.lawMap_baseChange I inside (Localization.Away r)

end NamedWrittenLaws

end

end SHIGURE.Quantities
