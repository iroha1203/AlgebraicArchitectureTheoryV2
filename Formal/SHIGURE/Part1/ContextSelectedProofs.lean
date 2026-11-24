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
  | .functional op, keep => .functional (operation op (by simpa only [Declaration.graphRuleName_functional] using keep))
  | .totality f, keep => .totality ⟨f, by simpa only [Declaration.graphRuleName_totality] using keep⟩
  | .quantityTotality q, keep => .quantityTotality ⟨q, by simpa only [Declaration.graphRuleName_quantityTotality] using keep⟩
  | .graphImpliesDomain p, keep => .graphImpliesDomain ⟨p, by simpa only [Declaration.graphRuleName_graphImpliesDomain] using keep⟩
  | .domainImpliesGraph p, keep => .domainImpliesGraph ⟨p, by simpa only [Declaration.graphRuleName_domainImpliesGraph] using keep⟩

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
  simp only [selectRenaming_apply, selectVar_there, selectVar_ambientVar]

/-- A graph axiom remains the same structural axiom of the selected signature. -/
theorem selectRule_toLaw (rule : GraphAxiom P.signature)
    (kept : Declaration.graphRuleName rule ∈ U.declarations) :
    selectLaw rule.toLaw (graphRuleSupport rule kept) = (selectRule rule kept).toLaw := by
  cases rule with
  | functional op =>
    cases op <;>
      simp only [GraphAxiom.toLaw_functional, selectLaw_eq, selectFormula_conj, selectFormula_atom,
        selectAtomic_graph, selectAtomic_eq, selectGraph_total, selectGraph_partialOp, selectGraph_quantity,
        selectRule, selectVar_here, selectVar_there] <;>
      congr 6 <;> exact selectRenaming_there_there _ _ _
  | totality f =>
    simp only [GraphAxiom.toLaw_totality, GraphAxiom.hasOutput_eq_ex_graph, selectLaw_eq, selectFormula_truth,
      selectFormula_ex, selectFormula_atom, selectAtomic_graph, selectGraph_total, selectRule, selectVar_here]
    congr 6
    exact selectRenaming_there _ _
  | quantityTotality q =>
    simp only [GraphAxiom.toLaw_quantityTotality, GraphAxiom.hasOutput_eq_ex_graph, selectLaw_eq,
      selectFormula_truth, selectFormula_ex, selectFormula_atom, selectAtomic_graph, selectGraph_quantity, selectRule, selectVar_here]
    congr 6
    exact selectRenaming_there _ _
  | graphImpliesDomain p =>
    simp only [GraphAxiom.toLaw_graphImpliesDomain, selectLaw_eq, selectFormula_atom, selectAtomic_graph,
      selectAtomic_domain, selectGraph_partialOp, selectRule, selectVar_here]
    congr 6 <;> exact selectRenaming_there _ _
  | domainImpliesGraph p =>
    simp only [GraphAxiom.toLaw_domainImpliesGraph, GraphAxiom.hasOutput_eq_ex_graph, selectLaw_eq,
      selectFormula_atom, selectFormula_ex, selectAtomic_domain, selectAtomic_graph, selectGraph_partialOp, selectRule, selectVar_here]
    congr 6 <;> first | exact selectRenaming_id _ | exact selectRenaming_there _ _

/-- The root sequent is included among the references of any original derivation. -/
theorem derivation_root {Γ : List P.theory.signature.SortType} {p q : Formula P.theory.signature Γ}
    (d : Derivation P.theory p q) : Declaration.lawBody (P := P) ⟨Γ, p, q⟩ ⊆ Declaration.derivation d :=
  Declaration.lawBody_subset_derivationOf Subtype.val d

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

/-- Read a theory by referencing original Law names through the supplied name map. -/
private abbrev namedTheory {sig : Signature.{u}} (declarations : LawDeclarations sig)
    {I : Type u} (name : I → declarations.LawName) : Theory.{u} :=
  ⟨sig, I, declarations.statement ∘ name⟩

/-- The support of the whole proof contains its outer sequent support. -/
private theorem derivationOf_root {I : Type u} (source : I → P.laws.LawName)
    {Γ : List (namedTheory P.laws source).signature.SortType}
    {p q : Formula (namedTheory P.laws source).signature Γ}
    (d : Derivation (namedTheory P.laws source) p q) :
    Declaration.lawBody (P := P) ⟨Γ, p, q⟩ ⊆ Declaration.derivationOf rfl source d :=
  Declaration.lawBody_subset_derivationOf source d

/-- A retained proof tree retains the syntax of its input formula. -/
private theorem derivationOf_input {I : Type u} (source : I → P.laws.LawName)
    {Γ : List (namedTheory P.laws source).signature.SortType}
    {p q : Formula (namedTheory P.laws source).signature Γ}
    (d : Derivation (namedTheory P.laws source) p q)
    (keep : Declaration.derivationOf rfl source d ⊆ U.declarations) :
    Declaration.formulaSupport p ⊆ U.declarations :=
  lawInputSupport (law := ⟨Γ, p, q⟩) ((derivationOf_root source d).trans keep)

/-- A retained proof tree retains the syntax of its conclusion. -/
private theorem derivationOf_result {I : Type u} (source : I → P.laws.LawName)
    {Γ : List (namedTheory P.laws source).signature.SortType}
    {p q : Formula (namedTheory P.laws source).signature Γ}
    (d : Derivation (namedTheory P.laws source) p q)
    (keep : Declaration.derivationOf rfl source d ⊆ U.declarations) :
    Declaration.formulaSupport q ⊆ U.declarations :=
  lawConclusionSupport (law := ⟨Γ, p, q⟩) ((derivationOf_root source d).trans keep)

/-- Replay each rule with selected formulas and the supplied required-Law names. -/
private noncomputable def selectDerivationUsing {I J : Type u}
    (source : I → P.laws.LawName) (target : J → U.RetainedLaw)
    (choose : (i : I) → Declaration.law (source i) ∈ U.declarations → J)
    (chosen : ∀ i keep, target (choose i keep) = ⟨source i, keep⟩)
    {Γ : List (namedTheory P.laws source).signature.SortType}
    {p q : Formula (namedTheory P.laws source).signature Γ}
    (d : Derivation (namedTheory P.laws source) p q)
    (keep : Declaration.derivationOf rfl source d ⊆ U.declarations) :
    Derivation (namedTheory (laws U) target)
      (selectFormula p (derivationOf_input source d keep))
      (selectFormula q (derivationOf_result source d keep)) := by
  induction d with
  | refl p => exact Derivation.refl (T := namedTheory (laws U) target) _
  | cut l r lh rh =>
    exact Derivation.cut (T := namedTheory (laws U) target)
      (lh ((Declaration.derivationOf_cut_left rfl source l r).trans keep))
      (rh ((Declaration.derivationOf_cut_right rfl source l r).trans keep))
  | required name =>
    have named : Declaration.law (source name) ∈ U.declarations :=
      keep (Declaration.law_mem_derivationOf_required rfl source name)
    have chosenLaw : (namedTheory (laws U) target).law (choose name named) =
        selectLaw (P.laws.statement (source name)) (Declaration.lawBody_subset_of_mem named) :=
      congrArg (laws U).statement (chosen name named)
    have proof := Derivation.required (T := namedTheory (laws U) target) (choose name named)
    rw [chosenLaw, selectLaw_eq] at proof
    exact proof
  | graph rule =>
    let present : Declaration.graphRuleName rule ∈ U.declarations := keep (derivationOf_root source (Derivation.graph (T := namedTheory P.laws source) rule)
      (Declaration.graphRuleName_mem_lawBody rule))
    have h : Derivation (namedTheory (laws U) target) (selectLaw rule.toLaw (graphRuleSupport rule present)).input
        (selectLaw rule.toLaw (graphRuleSupport rule present)).conclusion := by
      rw [selectRule_toLaw rule present]
      exact Derivation.graph (T := namedTheory (laws U) target) (selectRule rule present)
    simpa only [selectLaw_eq] using h
  | @rename Γ Δ p q ρ prior ih =>
    let sub := (Declaration.derivationOf_rename rfl source ρ prior).trans keep
    let node := Derivation.rename (T := namedTheory P.laws source) ρ prior
    have lhs := selectFormula_rename p ρ (derivationOf_input source prior sub) (derivationOf_input source node keep)
    have rhs := selectFormula_rename q ρ (derivationOf_result source prior sub) (derivationOf_result source node keep)
    erw [lhs, rhs]
    exact Derivation.rename (T := namedTheory (laws U) target) _ (ih sub)
  | truth p =>
    rw [selectFormula_truth]
    exact Derivation.truth (T := namedTheory (laws U) target) _
  | falsehood q =>
    rw [selectFormula_falsehood]
    exact Derivation.falsehood (T := namedTheory (laws U) target) _
  | andLeft p q =>
    rw [selectFormula_conj]
    exact Derivation.andLeft (T := namedTheory (laws U) target) _ _
  | andRight p q =>
    rw [selectFormula_conj]
    exact Derivation.andRight (T := namedTheory (laws U) target) _ _
  | andIntro l r lh rh =>
    rw [selectFormula_conj]
    exact Derivation.andIntro (T := namedTheory (laws U) target)
      (lh ((Declaration.derivationOf_andIntro_left rfl source l r).trans keep))
      (rh ((Declaration.derivationOf_andIntro_right rfl source l r).trans keep))
  | orLeft p q =>
    rw [selectFormula_disj]
    exact Derivation.orLeft (T := namedTheory (laws U) target) _ _
  | orRight p q =>
    rw [selectFormula_disj]
    exact Derivation.orRight (T := namedTheory (laws U) target) _ _
  | orElim l r lh rh =>
    rw [selectFormula_conj, selectFormula_disj]
    have left := lh ((Declaration.derivationOf_orElim_left rfl source l r).trans keep)
    have right := rh ((Declaration.derivationOf_orElim_right rfl source l r).trans keep)
    rw [selectFormula_conj] at left right
    exact Derivation.orElim (T := namedTheory (laws U) target) left right
  | existsIntro p x =>
    let node := Derivation.existsIntro (T := namedTheory P.laws source) p x
    let body := existsSupport (derivationOf_result source node keep)
    have lhs := selectFormula_openHead p x body (derivationOf_input source node keep)
    erw [lhs, selectFormula_ex]
    exact Derivation.existsIntro (T := namedTheory (laws U) target) (selectFormula p body) _
  | @existsElim Γ s p c q child ih =>
    let node := Derivation.existsElim (T := namedTheory P.laws source) child
    let input := derivationOf_input source node keep
    let output := derivationOf_result source node keep
    let sub := (Declaration.derivationOf_existsElim rfl source child).trans keep
    have inner := ih sub
    simp only [selectFormula_conj] at inner
    let keepLeft := (Declaration.binarySupport_left (Declaration.formula_conj c p.ex)).trans input
    let keepInner := (Declaration.binarySupport_left
      (Declaration.formula_conj (c.rename (fun i => Var.there i)) p)).trans (derivationOf_input source child sub)
    have lhs := selectFormula_there c keepLeft keepInner
    have rhs := selectFormula_there q output (derivationOf_result source child sub)
    erw [lhs, rhs] at inner
    rw [selectFormula_conj, selectFormula_ex]
    let keepRight := (Declaration.binarySupport_right (Declaration.formula_conj c p.ex)).trans input
    exact Derivation.existsElim (T := namedTheory (laws U) target)
      (p := selectFormula p (existsSupport keepRight)) inner
  | eqRefl x =>
    rw [selectFormula_truth, selectFormula_atom, selectAtomic_eq]
    exact Derivation.eqRefl (T := namedTheory (laws U) target) _
  | eqSubst p x y =>
    let node := Derivation.eqSubst (T := namedTheory P.laws source) p x y
    let out := derivationOf_result source node keep
    have body : Declaration.formulaSupport p ⊆ U.declarations := by
      let free := (Declaration.sorts_subset_formulaSupport (p.rename (Renaming.openHead y))).trans out
      rw [Declaration.formulaSupport_eq]
      refine Set.union_subset (Declaration.sorts_cons_subset (varKept free y) free) ?_
      have written : Declaration.formula p ⊆ Declaration.formulaSupport (p.rename (Renaming.openHead y)) := by
        rw [Declaration.formulaSupport_eq, Declaration.formula_rename]
        exact Set.subset_union_right
      exact written.trans out
    simp only [selectFormula_conj, selectFormula_atom, selectAtomic_eq]
    let left := Formula.atom (Atomic.eq x y)
    let keepInput := (Declaration.binarySupport_right (Declaration.formula_conj left
      (p.rename (Renaming.openHead x)))).trans (derivationOf_input source node keep)
    have lhs := selectFormula_openHead p x body keepInput
    have rhs := selectFormula_openHead p y body out
    erw [lhs, rhs]
    exact Derivation.eqSubst (T := namedTheory (laws U) target) (selectFormula p body) _ _

/-- Select the original inference tree as an ordinary derivation from the retained required Laws. -/
noncomputable def selectDerivation {Γ : List P.theory.signature.SortType} {p q : Formula P.theory.signature Γ}
    (d : Derivation P.theory p q) (keep : Declaration.derivation d ⊆ U.declarations) :
    Derivation (theory U) (selectFormula p (derivation_input d keep))
      (selectFormula q (derivation_result d keep)) :=
  selectDerivationUsing (I := P.theory.LawName) (J := (theory U).LawName) Subtype.val Subtype.val
    (fun n kept => ⟨⟨n.val, kept⟩, n.property⟩) (fun _ _ => rfl) d keep

/-- Select a proof from named Laws independently of the roles of those declarations. -/
noncomputable def selectNamedDerivation (axioms : Set P.laws.LawName)
    {Γ : List P.signature.SortType} {p q : Formula P.signature Γ}
    (d : Derivation (P.laws.select axioms) p q)
    (keep : Declaration.derivationOf rfl Subtype.val d ⊆ U.declarations) :
    Derivation ((laws U).select (Subtype.val ⁻¹' axioms))
      (selectFormula p (derivationOf_input Subtype.val d keep))
      (selectFormula q (derivationOf_result Subtype.val d keep)) :=
  selectDerivationUsing (I := (P.laws.select axioms).LawName)
    (J := ((laws U).select (Subtype.val ⁻¹' axioms)).LawName) Subtype.val Subtype.val
    (fun n kept => ⟨⟨n.val, kept⟩, n.property⟩) (fun _ _ => rfl) d keep

/-- The conclusion Law of a named proof uses only references already found in its proof tree. -/
theorem namedDerivation_lawBody (axioms : Set P.laws.LawName) (statement : Law P.signature)
    (d : Derivation (P.laws.select axioms) statement.input statement.conclusion) :
    Declaration.lawBody statement ⊆ Declaration.derivationOf rfl Subtype.val d := by
  cases statement
  exact derivationOf_root Subtype.val d

end DeclarationContext.Selected
end SHIGURE
