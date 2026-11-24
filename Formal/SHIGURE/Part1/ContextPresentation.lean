import Formal.SHIGURE.Part1.ContextSupports

/-! # Restriction of a primitive presentation

Names in a restricted presentation are precisely the retained names. Typed
expressions use their original ambient indices and carry the evidence that
all their dependencies are available. The restricted derivation system uses
only retained required Laws. Its additional syntactic check restricts every
sequent and primitive graph rule, while retaining the original inference
rule and variable positions at each node.

## Implementation notes

The support-indexed view keeps the original indices to share comparisons
with the reading APIs. The ordinary restricted presentation in
ContextSelectedPresentation selects the sort and symbol indices themselves;
its actual proof trees use that signature.
-/

universe u

namespace SHIGURE
namespace Declaration

variable {P : PrimitivePresentation.{u}}

/-- The primitive declaration used by a graph rule's sequent. -/
def graphRuleName : GraphAxiom P.signature → Declaration P
  | .functional op => ofOperation op
  | .totality f => .total f
  | .quantityTotality q => .quantity q
  | .graphImpliesDomain p | .domainImpliesGraph p => .partialOp p

/-- The functional rule uses the tagged operation. -/
theorem graphRuleName_functional (op : Operation P.signature) :
    graphRuleName (P := P) (.functional op) = ofOperation op :=
  rfl

/-- The totality rule uses the total operation. -/
theorem graphRuleName_totality (f : P.signature.Total) :
    graphRuleName (P := P) (.totality f) = .total f :=
  rfl

/-- The quantityTotality rule uses the quantity. -/
theorem graphRuleName_quantityTotality (q : P.signature.Quantity) :
    graphRuleName (P := P) (.quantityTotality q) = .quantity q :=
  rfl

/-- The graphImpliesDomain rule uses the partial operation. -/
theorem graphRuleName_graphImpliesDomain (p : P.signature.Partial) :
    graphRuleName (P := P) (.graphImpliesDomain p) = .partialOp p :=
  rfl

/-- The domainImpliesGraph rule uses the partial operation. -/
theorem graphRuleName_domainImpliesGraph (p : P.signature.Partial) :
    graphRuleName (P := P) (.domainImpliesGraph p) = .partialOp p :=
  rfl

/-- Every structural graph rule refers to its primitive in its written sequent. -/
theorem graphRuleName_mem_lawBody (rule : GraphAxiom P.signature) :
    graphRuleName (P := P) rule ∈ lawBody rule.toLaw := by
  cases rule <;> simp [graphRuleName, lawBody_eq, GraphAxiom.toLaw_functional, GraphAxiom.toLaw_totality,
    GraphAxiom.toLaw_quantityTotality, GraphAxiom.toLaw_graphImpliesDomain, GraphAxiom.toLaw_domainImpliesGraph,
    GraphAxiom.hasOutput_eq_ex_graph, formula_atom, formula_truth, formula_conj, formula_ex,
    atomic_eq, atomic_domain, atomic_graph, ofOperation_total, ofOperation_partialOp, ofOperation_quantity]

/-- The proof of a graph rule uses the primitive in that structural rule. -/
theorem graphRuleName_mem_derivation (rule : GraphAxiom P.signature) :
    graphRuleName (P := P) rule ∈ derivation (Derivation.graph (T := P.theory) rule) :=
  lawBody_subset_derivationOf Subtype.val (Derivation.graph (T := P.theory) rule)
    (graphRuleName_mem_lawBody rule)

/-- Cutting two proofs retains every declaration from the first proof. -/
theorem derivation_cut_left {Γ : List P.signature.SortType} {p q r : Formula P.signature Γ}
    (left : Derivation P.theory p q) (right : Derivation P.theory q r) :
    derivation left ⊆ derivation (.cut left right) :=
  derivationOf_cut_left rfl Subtype.val left right

/-- Conjunction introduction retains every declaration from its second proof. -/
theorem derivation_andIntro_right {Γ : List P.signature.SortType} {p q r : Formula P.signature Γ}
    (left : Derivation P.theory p q) (right : Derivation P.theory p r) :
    derivation right ⊆ derivation (.andIntro left right) :=
  derivationOf_andIntro_right rfl Subtype.val left right

end Declaration

namespace DeclarationContext

variable {P : PrimitivePresentation.{u}} (U : DeclarationContext P)

/-- The names of the restricted presentation, with no extra declaration data. -/
abbrev Retained := {d : Declaration P // d ∈ U.declarations}

/-- The retained Law declarations, including the additional and the derived Laws. -/
abbrev RetainedLaw := {name : P.laws.LawName // Declaration.law name ∈ U.declarations}

/-- A positive formula written in the restricted language, indexed by its original variable context. -/
abbrev FormulaIn (Γ : List P.signature.SortType) :=
  {p : Formula P.signature Γ // Declaration.formulaContext p ≤ U}

/-- A term of the restricted language, with its original variable and result sorts. -/
abbrev TermIn (Γ : List P.signature.SortType) (s : P.signature.SortType) :=
  {t : Term P.signature Γ s // Declaration.termContext t ≤ U}

/-- A written Law in the restricted language. -/
abbrev LawIn := {law : Law P.signature // Declaration.lawContext law ≤ U}

/-- Read the original Law in the restricted language with its support retained. -/
def writtenLaw (name : U.RetainedLaw) : U.LawIn :=
  ⟨P.laws.statement name.val, (Declaration.lawContext_le_iff _).2
    (Declaration.lawBody_subset_of_mem name.property)⟩

/-- The selected Law retains its written antecedent, conclusion and input sorts. -/
theorem writtenLaw_val (name : U.RetainedLaw) : (U.writtenLaw name).val = P.laws.statement name.val :=
  rfl

/-- The ambient-index presentation of the retained required rules, used for support checks. -/
def scopedTheory : Theory.{u} where
  signature := P.signature
  LawName := {name : P.theory.LawName // Declaration.law name.val ∈ U.declarations}
  law name := P.theory.law name.val

/-- The required rule retains the original type and formula of each surviving Law. -/
theorem scopedTheory_law (name : U.scopedTheory.LawName) :
    U.scopedTheory.law name = P.theory.law name.val :=
  rfl

/-- The derivations of the restricted presentation check every node's support.
The underlying proof is an ordinary positive derivation from the selected required Laws. -/
abbrev DerivationIn {Γ : List P.signature.SortType} (p q : Formula P.signature Γ) :=
  {d : Derivation U.scopedTheory p q //
    Declaration.derivationOf (T := U.scopedTheory) rfl (fun name => name.val.val) d ⊆ U.declarations}

/-- Retain a proof's rule tree and refine its required-law names to selected names.
All references, including each intermediate sequent, remain supported in the result. -/
noncomputable def restrictDerivation {Γ : List P.theory.signature.SortType} {p q : Formula P.theory.signature Γ}
    (d : Derivation P.theory p q) (used : Declaration.derivation d ⊆ U.declarations) :
    U.DerivationIn p q := by
  induction d with
  | refl p => exact ⟨Derivation.refl (T := U.scopedTheory) p, by simpa only [Declaration.derivationOf_support_eq] using used⟩
  | cut l r left right =>
    let l' := left ((Declaration.derivationOf_cut_left rfl Subtype.val l r).trans used)
    let r' := right ((Declaration.derivationOf_cut_right rfl Subtype.val l r).trans used)
    refine ⟨Derivation.cut (T := U.scopedTheory) l'.val r'.val, ?_⟩
    rw [Declaration.derivationOf_support_eq]
    exact Set.union_subset
      ((Declaration.lawBody_subset_derivationOf Subtype.val (Derivation.cut l r)).trans used)
      (Set.union_subset l'.property r'.property)
  | required name =>
    have kept : Declaration.law name.val ∈ U.declarations :=
      used (Declaration.required_mem_derivation name)
    exact ⟨Derivation.required (T := U.scopedTheory) ⟨name, kept⟩, by simpa only [Declaration.derivationOf_support_eq] using used⟩
  | graph rule => exact ⟨Derivation.graph (T := U.scopedTheory) rule, by simpa only [Declaration.derivationOf_support_eq] using used⟩
  | rename positions child restricted =>
    let child' := restricted ((Declaration.derivationOf_rename rfl Subtype.val positions child).trans used)
    refine ⟨Derivation.rename (T := U.scopedTheory) positions child'.val, ?_⟩
    rw [Declaration.derivationOf_support_eq]
    exact Set.union_subset
      ((Declaration.lawBody_subset_derivationOf Subtype.val (Derivation.rename positions child)).trans used)
      child'.property
  | truth p => exact ⟨Derivation.truth (T := U.scopedTheory) p, by simpa only [Declaration.derivationOf_support_eq] using used⟩
  | falsehood p => exact ⟨Derivation.falsehood (T := U.scopedTheory) _, by simpa only [Declaration.derivationOf_support_eq] using used⟩
  | andLeft p q => exact ⟨Derivation.andLeft (T := U.scopedTheory) _ _, by simpa only [Declaration.derivationOf_support_eq] using used⟩
  | andRight p q => exact ⟨Derivation.andRight (T := U.scopedTheory) p q, by simpa only [Declaration.derivationOf_support_eq] using used⟩
  | andIntro l r left right =>
    let l' := left ((Declaration.derivationOf_andIntro_left rfl Subtype.val l r).trans used)
    let r' := right ((Declaration.derivationOf_andIntro_right rfl Subtype.val l r).trans used)
    refine ⟨Derivation.andIntro (T := U.scopedTheory) l'.val r'.val, ?_⟩
    rw [Declaration.derivationOf_support_eq]
    exact Set.union_subset
      ((Declaration.lawBody_subset_derivationOf Subtype.val (Derivation.andIntro l r)).trans used)
      (Set.union_subset l'.property r'.property)
  | orLeft p q => exact ⟨Derivation.orLeft (T := U.scopedTheory) p q, by simpa only [Declaration.derivationOf_support_eq] using used⟩
  | orRight p q => exact ⟨Derivation.orRight (T := U.scopedTheory) _ _, by simpa only [Declaration.derivationOf_support_eq] using used⟩
  | orElim l r left right =>
    let l' := left ((Declaration.derivationOf_orElim_left rfl Subtype.val l r).trans used)
    let r' := right ((Declaration.derivationOf_orElim_right rfl Subtype.val l r).trans used)
    refine ⟨Derivation.orElim (T := U.scopedTheory) l'.val r'.val, ?_⟩
    rw [Declaration.derivationOf_support_eq]
    exact Set.union_subset
      ((Declaration.lawBody_subset_derivationOf Subtype.val (Derivation.orElim l r)).trans used)
      (Set.union_subset l'.property r'.property)
  | existsIntro body x => exact ⟨Derivation.existsIntro (T := U.scopedTheory) body x, by simpa only [Declaration.derivationOf_support_eq] using used⟩
  | existsElim child restricted =>
    let child' := restricted ((Declaration.derivationOf_existsElim rfl Subtype.val child).trans used)
    refine ⟨Derivation.existsElim (T := U.scopedTheory) child'.val, ?_⟩
    rw [Declaration.derivationOf_support_eq]
    exact Set.union_subset
      ((Declaration.lawBody_subset_derivationOf Subtype.val (Derivation.existsElim child)).trans used)
      child'.property
  | eqRefl x => exact ⟨Derivation.eqRefl (T := U.scopedTheory) x, by simpa only [Declaration.derivationOf_support_eq] using used⟩
  | eqSubst body x y => exact ⟨Derivation.eqSubst (T := U.scopedTheory) body x y, by simpa only [Declaration.derivationOf_support_eq] using used⟩

/-- A retained derived Law's original derivation is valid in the restricted language. -/
noncomputable def derived (name : U.RetainedLaw) (role : P.laws.role name.val = .derived) :
    U.DerivationIn (P.laws.statement name.val).input (P.laws.statement name.val).conclusion :=
  U.restrictDerivation (P.derived name.val role)
    ((Declaration.derivation_subset_dependsOn name.val role).trans (U.closed name.property))

end DeclarationContext
end SHIGURE
