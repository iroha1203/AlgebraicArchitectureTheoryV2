import Formal.SHIGURE.Part1.ContextSelectedSyntax
import Formal.SHIGURE.Part1.ContextStructures

/-! # Rules and proofs over selected names

The required Law declarations and structural rules both use the actual
selected signature. Selecting a proof keeps its inference rule, its
position maps, and the order of its premises at every node.
-/

universe u

namespace SHIGURE
namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- Select all retained named Laws and preserve their declaration roles. -/
def laws (U : DeclarationContext P) : LawDeclarations (signature U) where
  LawName := U.RetainedLaw
  statement name := selectLaw (P.laws.statement name.val) (Declaration.lawBody_subset_of_mem name.property)
  role name := P.laws.role name.val

/-- The ordinary theory of the restriction is defined over the genuinely selected signature. -/
def theory (U : DeclarationContext P) : Theory.{u} := (laws U).toTheory

/-- The selected structural rule retains its original rule and primitive name. -/
def selectRule : (rule : GraphAxiom P.signature) → Declaration.graphRuleName rule ∈ U.declarations →
    GraphAxiom (signature U)
  | .functional op, keep => .functional (operation op keep)
  | .totality f, keep => .totality ⟨f, keep⟩
  | .quantityTotality q, keep => .quantityTotality ⟨q, keep⟩
  | .graphImpliesDomain p, keep => .graphImpliesDomain ⟨p, keep⟩
  | .domainImpliesGraph p, keep => .domainImpliesGraph ⟨p, keep⟩

/-- The selected variable map of an identity is an identity. -/
theorem selectRenaming_id {Γ : List P.signature.SortType} (kept : Declaration.sorts Γ ⊆ U.declarations) :
    (selectRenaming kept kept (fun i => i) : Renaming _ _) = (fun {_} i => i) := by
  funext _ i
  exact selectVar_ambientVar kept i

/-- A selected variable map shifted by two head variables is the same double shift. -/
theorem selectRenaming_there_there {Γ : List P.signature.SortType} {s t : P.signature.SortType}
    (keepS : Declaration.sort s ∈ U.declarations) (keepT : Declaration.sort t ∈ U.declarations)
    (kept : Declaration.sorts Γ ⊆ U.declarations) :
    (selectRenaming kept (Declaration.sorts_cons_subset keepT (Declaration.sorts_cons_subset keepS kept))
      (fun i => .there (.there i)) : Renaming _ _) =
      (fun {_} i => Var.there (t := (⟨t, keepT⟩ : SortName U)) (Var.there (t := (⟨s, keepS⟩ : SortName U)) i)) := by
  funext _ i
  change Var.there (Var.there (selectVar kept (ambientVar kept i))) = _
  rw [selectVar_ambientVar]

/-- A graph axiom remains the same structural axiom of the selected signature. -/
theorem selectRule_toLaw (rule : GraphAxiom P.signature)
    (kept : Declaration.graphRuleName rule ∈ U.declarations) :
    selectLaw rule.toLaw (graphRuleSupport rule kept) = (selectRule rule kept).toLaw := by
  cases rule with
  | functional op =>
    cases op <;>
      simp only [GraphAxiom.toLaw_functional, selectLaw, selectFormula, selectAtomic, selectGraph,
        selectRule, operation, signature, arity, context, selectVar] <;>
      congr 6 <;> exact selectRenaming_there_there _ _ _
  | totality f =>
    simp only [GraphAxiom.toLaw_totality, GraphAxiom.hasOutput_eq_ex_graph, selectLaw, selectFormula, selectAtomic,
      selectGraph, selectRule, operation, signature, arity, context, selectVar]
    congr 6
    exact selectRenaming_there _ _
  | quantityTotality q =>
    simp only [GraphAxiom.toLaw_quantityTotality, GraphAxiom.hasOutput_eq_ex_graph, selectLaw, selectFormula,
      selectAtomic, selectGraph, selectRule, operation, signature, arity, context, selectVar]
    congr 6
    exact selectRenaming_there _ _
  | graphImpliesDomain p =>
    simp only [GraphAxiom.toLaw_graphImpliesDomain, selectLaw, selectFormula, selectAtomic, selectGraph,
      selectRule, operation, signature, arity, context, selectVar]
    congr 6 <;> exact selectRenaming_there _ _
  | domainImpliesGraph p =>
    simp only [GraphAxiom.toLaw_domainImpliesGraph, GraphAxiom.hasOutput_eq_ex_graph, selectLaw, selectFormula,
      selectAtomic, selectGraph, selectRule, operation, signature, arity, context, selectVar]
    congr 6 <;> first | exact selectRenaming_id _ | exact selectRenaming_there _ _

/-- The root sequent is included among the references of any original derivation. -/
theorem derivation_root {Γ : List P.theory.signature.SortType} {p q : Formula P.theory.signature Γ}
    (d : Derivation P.theory p q) : Declaration.lawBody (P := P) ⟨Γ, p, q⟩ ⊆ Declaration.derivation d := by
  cases d <;> exact fun _ h => Or.inl h

/-- A supported proof has a supported antecedent at its root. -/
theorem derivation_input {Γ : List P.theory.signature.SortType} {p q : Formula P.theory.signature Γ}
    (d : Derivation P.theory p q) (keep : Declaration.derivation d ⊆ U.declarations) :
    Declaration.formulaSupport p ⊆ U.declarations :=
  lawInputSupport (law := ⟨Γ, p, q⟩) ((derivation_root d).trans keep)

/-- A supported proof has a supported conclusion at its root. -/
theorem derivation_result {Γ : List P.theory.signature.SortType} {p q : Formula P.theory.signature Γ}
    (d : Derivation P.theory p q) (keep : Declaration.derivation d ⊆ U.declarations) :
    Declaration.formulaSupport q ⊆ U.declarations :=
  lawConclusionSupport (law := ⟨Γ, p, q⟩) ((derivation_root d).trans keep)

/-- Select the complete proof tree as an ordinary derivation of the smaller theory. -/
noncomputable def selectDerivation {Γ : List P.theory.signature.SortType} {p q : Formula P.theory.signature Γ}
    (d : Derivation P.theory p q) (keep : Declaration.derivation d ⊆ U.declarations) :
    Derivation (theory U) (selectFormula p (derivation_input d keep))
      (selectFormula q (derivation_result d keep)) := by
  induction d with
  | refl p => exact Derivation.refl (T := theory U) _
  | cut l r lh rh =>
    exact Derivation.cut (T := theory U) (lh (fun _ h => keep (Or.inr (Or.inl h))))
      (rh (fun _ h => keep (Or.inr (Or.inr h))))
  | required name =>
    have named : Declaration.law name.val ∈ U.declarations := keep (Declaration.required_mem_derivation name)
    exact Derivation.required (T := theory U) ⟨⟨name.val, named⟩, name.property⟩
  | graph rule =>
    let present : Declaration.graphRuleName rule ∈ U.declarations := keep (Declaration.graphRuleName_mem_derivation rule)
    have h : Derivation (theory U) (selectLaw rule.toLaw (graphRuleSupport rule present)).input
        (selectLaw rule.toLaw (graphRuleSupport rule present)).conclusion := by
      rw [selectRule_toLaw rule present]
      exact Derivation.graph (T := theory U) (selectRule rule present)
    exact h
  | @rename Γ Δ p q ρ prior ih =>
    let sub : Declaration.derivation prior ⊆ U.declarations := fun _ h => keep (Or.inr h)
    let node := Derivation.rename (T := P.theory) ρ prior
    have lhs := selectFormula_rename p ρ (derivation_input prior sub) (derivation_input node keep)
    have rhs := selectFormula_rename q ρ (derivation_result prior sub) (derivation_result node keep)
    erw [lhs, rhs]
    exact Derivation.rename (T := theory U) _ (ih sub)
  | truth p => exact Derivation.truth (T := theory U) _
  | falsehood q => exact Derivation.falsehood (T := theory U) _
  | andLeft p q => exact Derivation.andLeft (T := theory U) _ _
  | andRight p q => exact Derivation.andRight (T := theory U) _ _
  | andIntro l r lh rh =>
    exact Derivation.andIntro (T := theory U) (lh (fun _ h => keep (Or.inr (Or.inl h))))
      (rh (fun _ h => keep (Or.inr (Or.inr h))))
  | orLeft p q => exact Derivation.orLeft (T := theory U) _ _
  | orRight p q => exact Derivation.orRight (T := theory U) _ _
  | orElim l r lh rh =>
    exact Derivation.orElim (T := theory U) (lh (fun _ h => keep (Or.inr (Or.inl h))))
      (rh (fun _ h => keep (Or.inr (Or.inr h))))
  | existsIntro p x =>
    let node := Derivation.existsIntro (T := P.theory) p x
    let body := existsSupport (derivation_result node keep)
    have lhs := selectFormula_openHead p x body (derivation_input node keep)
    erw [lhs]
    exact Derivation.existsIntro (T := theory U) (selectFormula p body) _
  | @existsElim Γ s p c q child ih =>
    let node := Derivation.existsElim (T := P.theory) child
    let input := derivation_input node keep
    let output := derivation_result node keep
    let sub : Declaration.derivation child ⊆ U.declarations := fun _ h => keep (Or.inr h)
    have inner := ih sub
    simp only [selectFormula] at inner
    have lhs := selectFormula_there c (leftSupport input) (leftSupport (derivation_input child sub))
    have rhs := selectFormula_there q output (derivation_result child sub)
    erw [lhs, rhs] at inner
    exact Derivation.existsElim (T := theory U) (p := selectFormula p (existsSupport (rightSupport input))) inner
  | eqRefl x => exact Derivation.eqRefl (T := theory U) _
  | eqSubst p x y =>
    let node := Derivation.eqSubst (T := P.theory) p x y
    let out := derivation_result node keep
    have body : Declaration.formulaSupport p ⊆ U.declarations := by
      intro a used
      rcases used with sorts | ref
      · refine Declaration.sorts_cons_subset (varKept (U := U) (fun _ h => out (Or.inl h)) y)
          (fun _ h => out (Or.inl h)) sorts
      · apply out (Or.inr ?_)
        erw [Declaration.formula_rename (P := P) p (Renaming.openHead y)]
        exact ref
    simp only [selectFormula, selectAtomic]
    have lhs := selectFormula_openHead p x body (rightSupport (derivation_input node keep))
    have rhs := selectFormula_openHead p y body out
    erw [lhs, rhs]
    exact Derivation.eqSubst (T := theory U) (selectFormula p body) _ _

end DeclarationContext.Selected
end SHIGURE
