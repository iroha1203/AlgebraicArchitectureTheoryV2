import Formal.SHIGURE.Part1.ContextSupports

/-! # Restriction of a primitive presentation

Names in a restricted presentation are precisely the retained names. Typed
expressions use their original ambient indices and carry the evidence that
all their dependencies are available. The restricted derivation system uses
only retained required Laws. Its additional syntactic check restricts every
sequent and primitive graph rule, while retaining the original inference
rule and variable positions at each node.
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

/-- Every structural graph rule refers to its primitive in its written sequent. -/
theorem graphRuleName_mem_lawBody (rule : GraphAxiom P.signature) :
    graphRuleName (P := P) rule ∈ lawBody rule.toLaw := by
  cases rule <;> simp [graphRuleName, lawBody, GraphAxiom.toLaw, GraphAxiom.hasOutput,
    formula, atomic, ofOperation]

/-- The proof of a graph rule uses the primitive in that structural rule. -/
theorem graphRuleName_mem_derivation (rule : GraphAxiom P.signature) :
    graphRuleName (P := P) rule ∈ derivation (Derivation.graph (T := P.theory) rule) :=
  Or.inl (graphRuleName_mem_lawBody rule)

/-- Cutting two proofs retains every declaration from the first proof. -/
theorem derivation_cut_left {Γ : List P.signature.SortType} {p q r : Formula P.signature Γ}
    (left : Derivation P.theory p q) (right : Derivation P.theory q r) :
    derivation left ⊆ derivation (.cut left right) :=
  fun _ kept => Or.inr (Or.inl kept)

/-- Conjunction introduction retains every declaration from its second proof. -/
theorem derivation_andIntro_right {Γ : List P.signature.SortType} {p q r : Formula P.signature Γ}
    (left : Derivation P.theory p q) (right : Derivation P.theory p r) :
    derivation right ⊆ derivation (.andIntro left right) :=
  fun _ kept => Or.inr (Or.inr kept)

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

/-- The required Laws of the restriction are precisely the retained required names. -/
def requiredTheory : Theory.{u} where
  signature := P.signature
  LawName := {name : P.theory.LawName // Declaration.law name.val ∈ U.declarations}
  law name := P.theory.law name.val

/-- The required rule retains the original type and formula of each surviving Law. -/
theorem requiredTheory_law (name : U.requiredTheory.LawName) :
    U.requiredTheory.law name = P.theory.law name.val :=
  rfl

/-- The derivations of the restricted presentation check every node's support.
The underlying proof is an ordinary positive derivation from the selected required Laws. -/
abbrev DerivationIn {Γ : List P.signature.SortType} (p q : Formula P.signature Γ) :=
  {d : Derivation U.requiredTheory p q //
    Declaration.derivationOf (T := U.requiredTheory) rfl (fun name => name.val.val) d ⊆ U.declarations}

/-- Retain a proof's rule tree and refine its required-law names to selected names.
All references, including each intermediate sequent, remain supported in the result. -/
noncomputable def restrictDerivation {Γ : List P.theory.signature.SortType} {p q : Formula P.theory.signature Γ}
    (d : Derivation P.theory p q) (used : Declaration.derivation d ⊆ U.declarations) :
    U.DerivationIn p q := by
  induction d with
  | refl p => exact ⟨Derivation.refl (T := U.requiredTheory) p, used⟩
  | cut l r left right =>
    let l' := left (fun _ a => used (Or.inr (Or.inl a)))
    let r' := right (fun _ a => used (Or.inr (Or.inr a)))
    exact ⟨Derivation.cut (T := U.requiredTheory) l'.val r'.val, fun _ a => a.elim (fun h => used (Or.inl h))
      (fun h => h.elim (fun kept => l'.property kept) (fun kept => r'.property kept))⟩
  | required name =>
    have kept : Declaration.law name.val ∈ U.declarations :=
      used (Declaration.required_mem_derivation name)
    exact ⟨Derivation.required (T := U.requiredTheory) ⟨name, kept⟩, used⟩
  | graph rule => exact ⟨Derivation.graph (T := U.requiredTheory) rule, used⟩
  | rename positions child restricted =>
    let child' := restricted (fun _ a => used (Or.inr a))
    exact ⟨Derivation.rename (T := U.requiredTheory) positions child'.val, fun _ a => a.elim (fun h => used (Or.inl h)) (fun kept => child'.property kept)⟩
  | truth p => exact ⟨Derivation.truth (T := U.requiredTheory) p, used⟩
  | falsehood p => exact ⟨Derivation.falsehood (T := U.requiredTheory) _, used⟩
  | andLeft p q => exact ⟨Derivation.andLeft (T := U.requiredTheory) _ _, used⟩
  | andRight p q => exact ⟨Derivation.andRight (T := U.requiredTheory) p q, used⟩
  | andIntro l r left right =>
    let l' := left (fun _ a => used (Or.inr (Or.inl a)))
    let r' := right (fun _ a => used (Or.inr (Or.inr a)))
    exact ⟨Derivation.andIntro (T := U.requiredTheory) l'.val r'.val, fun _ a => a.elim (fun h => used (Or.inl h))
      (fun h => h.elim (fun kept => l'.property kept) (fun kept => r'.property kept))⟩
  | orLeft p q => exact ⟨Derivation.orLeft (T := U.requiredTheory) p q, used⟩
  | orRight p q => exact ⟨Derivation.orRight (T := U.requiredTheory) _ _, used⟩
  | orElim l r left right =>
    let l' := left (fun _ a => used (Or.inr (Or.inl a)))
    let r' := right (fun _ a => used (Or.inr (Or.inr a)))
    exact ⟨Derivation.orElim (T := U.requiredTheory) l'.val r'.val, fun _ a => a.elim (fun h => used (Or.inl h))
      (fun h => h.elim (fun kept => l'.property kept) (fun kept => r'.property kept))⟩
  | existsIntro body x => exact ⟨Derivation.existsIntro (T := U.requiredTheory) body x, used⟩
  | existsElim child restricted =>
    let child' := restricted (fun _ a => used (Or.inr a))
    exact ⟨Derivation.existsElim (T := U.requiredTheory) child'.val, fun _ a => a.elim (fun h => used (Or.inl h)) (fun kept => child'.property kept)⟩
  | eqRefl x => exact ⟨Derivation.eqRefl (T := U.requiredTheory) x, used⟩
  | eqSubst body x y => exact ⟨Derivation.eqSubst (T := U.requiredTheory) body x y, used⟩

/-- A retained derived Law's original derivation is valid in the restricted language. -/
noncomputable def derived (name : U.RetainedLaw) (role : P.laws.role name.val = .derived) :
    U.DerivationIn (P.laws.statement name.val).input (P.laws.statement name.val).conclusion :=
  U.restrictDerivation (P.derived name.val role) (by
    intro a used
    apply U.closed name.property
    rw [Declaration.dependsOn]
    refine Or.inr (Or.inr ?_)
    split
    · exact used
    · rename_i otherRole
      cases role.symm.trans otherRole
    · rename_i otherRole
      cases role.symm.trans otherRole)

end DeclarationContext
end SHIGURE
