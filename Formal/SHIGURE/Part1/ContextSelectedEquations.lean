import Formal.SHIGURE.Part1.ContextSelectedSubstitution
import Formal.SHIGURE.Part1.ContextSelectedProofs

/-! # Ordered equality Laws in selected presentations

The terms and the literal expansion history are selected together.
A substitution guard accounts for all positions of its source, so the
selection needs only the dependencies of the written Law.
-/

universe u

namespace SHIGURE
namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- Expose the Law whose conclusion is one chosen writing of the ordered equality. -/
private abbrev writtenLaw (eqn : OrderedEquation P.signature) (p : Formula P.signature eqn.context) :
    Law P.signature :=
  ⟨eqn.context, eqn.input, p⟩

/-- The supported input of a substituted writing is its full guarded input. -/
private theorem guardedInput_kept {eqn : OrderedEquation P.signature} {p : Formula P.signature eqn.context}
    {Γ : List P.signature.SortType} (θ : Substitution P.signature eqn.context Γ)
    (h : Declaration.lawBody (writtenLaw (eqn.substitute θ) (p.substitute θ)) ⊆ U.declarations) :
    Declaration.formulaSupport (θ.defined.conj (eqn.input.substitute θ)) ⊆ U.declarations := by
  simpa only [OrderedEquation.substitute_eq] using lawInputSupport h

/-- The antecedent of the written substitution includes its strict definedness guard. -/
private theorem guard_kept {eqn : OrderedEquation P.signature} {p : Formula P.signature eqn.context}
    {Γ : List P.signature.SortType} (θ : Substitution P.signature eqn.context Γ)
    (h : Declaration.lawBody (writtenLaw (eqn.substitute θ) (p.substitute θ)) ⊆ U.declarations) :
    Declaration.formulaSupport θ.defined ⊆ U.declarations :=
  (Declaration.binarySupport_left (Declaration.formula_conj θ.defined (eqn.input.substitute θ))).trans
    (guardedInput_kept (eqn := eqn) (p := p) θ h)

/-- The guarded antecedent still retains the substituted original formula. -/
private theorem substitutedInput_kept {eqn : OrderedEquation P.signature} {p : Formula P.signature eqn.context}
    {Γ : List P.signature.SortType} (θ : Substitution P.signature eqn.context Γ)
    (h : Declaration.lawBody (writtenLaw (eqn.substitute θ) (p.substitute θ)) ⊆ U.declarations) :
    Declaration.formulaSupport (eqn.input.substitute θ) ⊆ U.declarations :=
  (Declaration.binarySupport_right (Declaration.formula_conj θ.defined (eqn.input.substitute θ))).trans
    (guardedInput_kept (eqn := eqn) (p := p) θ h)

/-- Recover the support of the prior writing from a retained guarded substitution. -/
private theorem priorLaw_kept {eqn : OrderedEquation P.signature} {p : Formula P.signature eqn.context}
    {Γ : List P.signature.SortType} (θ : Substitution P.signature eqn.context Γ)
    (h : Declaration.lawBody (writtenLaw (eqn.substitute θ) (p.substitute θ)) ⊆ U.declarations) :
    Declaration.lawBody (writtenLaw eqn p) ⊆ U.declarations := by
  have hGuard := guard_kept (eqn := eqn) (p := p) θ h
  have hPriorInput := substitutedInput_kept (eqn := eqn) (p := p) θ h
  have hFinalConclusion := lawConclusionSupport h
  rw [Declaration.lawBody_eq]
  simp only [Declaration.formulaSupport_eq] at hPriorInput hFinalConclusion
  exact Set.union_subset
    (Set.union_subset (substitution_source_kept θ hGuard)
      ((formulaReferences_subset_substitute eqn.input θ).trans (Set.subset_union_right.trans hPriorInput)))
    ((formulaReferences_subset_substitute p θ).trans (Set.subset_union_right.trans hFinalConclusion))

/-- Follow the writing history to obtain support for both ordered terms and their value sort. -/
private theorem expansion_terms_kept {eqn : OrderedEquation P.signature} {p : Formula P.signature eqn.context}
    (data : OrderedEquation.Expansion eqn p) :
    (Declaration.lawBody (writtenLaw eqn p) ⊆ U.declarations) →
    Declaration.sort eqn.result ∈ U.declarations ∧
      termReferences eqn.left ⊆ U.declarations ∧ termReferences eqn.right ⊆ U.declarations := by
  induction data with
  | original eqn =>
    intro h
    exact termEq_support eqn.left eqn.right (lawConclusionSupport h)
  | @variablePair eqn x y left right =>
    intro h
    refine ⟨varKept (lawSortSupport h) x, ?_, ?_⟩
    · rw [left, termReferences_var]
      exact Set.empty_subset _
    · rw [right, termReferences_var]
      exact Set.empty_subset _
  | @substitute eqn p prior Γ θ ih =>
    intro h
    obtain ⟨hs, left, right⟩ := ih (priorLaw_kept θ h)
    have terms := fun {s} (i : Var eqn.context s) =>
      (substitution_term_kept θ (guard_kept (eqn := eqn) (p := p) θ h) i).2
    simp only [OrderedEquation.substitute_eq]
    exact ⟨hs, substitute_term_kept eqn.left θ left terms, substitute_term_kept eqn.right θ right terms⟩

/-- Retype both terms and the input formula in the selected signature. -/
private def selectEquation {eqn : OrderedEquation P.signature} {p : Formula P.signature eqn.context}
    (data : OrderedEquation.Expansion eqn p)
    (h : Declaration.lawBody (writtenLaw eqn p) ⊆ U.declarations) : OrderedEquation (signature U) where
  context := context eqn.context (lawSortSupport h)
  result := ⟨eqn.result, (expansion_terms_kept data h).1⟩
  input := selectFormula eqn.input (lawInputSupport h)
  left := selectTerm eqn.left (lawSortSupport h) (expansion_terms_kept data h).1 (expansion_terms_kept data h).2.1
  right := selectTerm eqn.right (lawSortSupport h) (expansion_terms_kept data h).1 (expansion_terms_kept data h).2.2

/-- Selecting a written substitution commutes with substitution by the retyped arguments. -/
private theorem selectEquation_substitute {eqn : OrderedEquation P.signature} {p : Formula P.signature eqn.context}
    (prior : OrderedEquation.Expansion eqn p) {Γ : List P.signature.SortType}
    (θ : Substitution P.signature eqn.context Γ)
    (h : Declaration.lawBody (writtenLaw (eqn.substitute θ) (p.substitute θ)) ⊆ U.declarations) :
    let prev := priorLaw_kept θ h
    let θ' := selectSubstitution θ (lawSortSupport prev) (lawSortSupport h)
      (fun i => (substitution_term_kept θ (guard_kept (eqn := eqn) (p := p) θ h) i).2)
    selectEquation (prior.substitute θ) h = (selectEquation prior prev).substitute θ' := by
  let prev := priorLaw_kept θ h
  let hΓ := lawSortSupport h
  let hOld := lawSortSupport prev
  let hTerms := fun {s} (i : Var eqn.context s) => (substitution_term_kept θ (guard_kept (eqn := eqn) (p := p) θ h) i).2
  let θ' := selectSubstitution θ hOld hΓ hTerms
  let hs := (expansion_terms_kept prior prev).1
  have inputSame := congrArg₂ (Formula.conj (sig := signature U))
    (selectSubstitution_defined θ hOld hΓ hTerms (guard_kept (eqn := eqn) (p := p) θ h))
    (selectFormula_substitute eqn.input θ hOld hΓ hTerms (lawInputSupport prev) (substitutedInput_kept (eqn := eqn) (p := p) θ h))
  have inputClause := selectFormula_conj θ.defined (eqn.input.substitute θ)
    (guardedInput_kept (eqn := eqn) (p := p) θ h)
  have leftKept : termReferences (eqn.left.substitute θ) ⊆ U.declarations := by
    simpa only [OrderedEquation.substitute_eq] using (expansion_terms_kept (prior.substitute θ) h).2.1
  have rightKept : termReferences (eqn.right.substitute θ) ⊆ U.declarations := by
    simpa only [OrderedEquation.substitute_eq] using (expansion_terms_kept (prior.substitute θ) h).2.2
  have leftSame := selectTerm_substitute eqn.left θ hOld hΓ hs (expansion_terms_kept prior prev).2.1 hTerms
    leftKept
  have rightSame := selectTerm_substitute eqn.right θ hOld hΓ hs (expansion_terms_kept prior prev).2.2 hTerms
    rightKept
  let make := OrderedEquation.mk (sig := signature U) (context Γ hΓ) ⟨eqn.result, hs⟩
  change selectEquation (prior.substitute θ) h = (selectEquation prior prev).substitute θ'
  rw [OrderedEquation.substitute_eq (selectEquation prior prev) θ']
  exact (congrArg (fun input => make input _ _) (inputClause.trans inputSame)).trans
    (congrArg₂ (make _) leftSame rightSame)

/-- Transport the type of a writing certificate when its equation and conclusion agree. -/
private theorem expansion_congr {sig : Signature.{u}} {e f : OrderedEquation sig}
    (same : e = f) {p : Formula sig e.context} {q : Formula sig f.context}
    (written : p ≍ q) : OrderedEquation.Expansion e p = OrderedEquation.Expansion f q := by
  cases same
  exact congrArg (OrderedEquation.Expansion _) (eq_of_heq written)

/-- A term identified as a variable retains the corresponding selected variable position. -/
private theorem selectTerm_of_var {Γ : List P.signature.SortType} {s : P.signature.SortType}
    {t : Term P.signature Γ s} (x : Var Γ s) (same : t = .var x)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hs : Declaration.sort s ∈ U.declarations)
    (ht : termReferences t ⊆ U.declarations) :
    selectTerm t hΓ hs ht = .var (selectVar hΓ x) := by
  subst t
  exact selectTerm_var x hΓ hs ht

/-- Replay the entire writing certificate over the genuinely selected signature. -/
private noncomputable def selectExpansion {eqn : OrderedEquation P.signature} {p : Formula P.signature eqn.context}
    (data : OrderedEquation.Expansion eqn p)
    (h : Declaration.lawBody (writtenLaw eqn p) ⊆ U.declarations) :
    OrderedEquation.Expansion (selectEquation data h) (selectFormula p (lawConclusionSupport h)) := by
  induction data with
  | original eqn =>
    have supports := expansion_terms_kept (OrderedEquation.Expansion.original eqn) h
    have selected := selectFormula_termEq eqn.left eqn.right (lawSortSupport h) supports.1 supports.2.1 supports.2.2
      (lawConclusionSupport h)
    exact selected.symm ▸ .original (selectEquation (.original eqn) h)
  | @variablePair eqn x y left right =>
    let hΓ := lawSortSupport h
    let data : OrderedEquation.Expansion eqn (.atom (.eq x y)) := .variablePair x y left right
    simpa only [selectFormula_atom, selectAtomic_eq] using
      (OrderedEquation.Expansion.variablePair (eqn := selectEquation data h)
        (selectVar hΓ x) (selectVar hΓ y)
        (selectTerm_of_var x left hΓ _ _) (selectTerm_of_var y right hΓ _ _))
  | @substitute eqn p prior Γ θ ih =>
    let prev := priorLaw_kept θ h
    let hTerms := fun {s} (i : Var eqn.context s) =>
      (substitution_term_kept θ (guard_kept (eqn := eqn) (p := p) θ h) i).2
    let θ' := selectSubstitution θ (lawSortSupport prev) (lawSortSupport h) hTerms
    have eqnSame := selectEquation_substitute prior θ h
    have conclusionSame := selectFormula_substitute p θ (lawSortSupport prev) (lawSortSupport h) hTerms
      (lawConclusionSupport prev) (lawConclusionSupport h)
    exact cast (expansion_congr eqnSame.symm (heq_of_eq conclusionSame.symm)) ((ih prev).substitute θ')

/-- Retype both members of a supported equation and keep its complete literal expansion. -/
noncomputable def selectWritten (w : OrderedEquation.Written P.signature)
    (h : Declaration.lawBody w.toLaw ⊆ U.declarations) : OrderedEquation.Written (signature U) := by
  have kept : Declaration.lawBody (writtenLaw w.equation w.conclusion) ⊆ U.declarations := by
    simpa only [OrderedEquation.Written.toLaw_eq] using h
  exact ⟨selectEquation w.expansion kept, selectFormula w.conclusion (lawConclusionSupport kept),
    selectExpansion w.expansion kept⟩

/-- The selected left member is obtained by reindexing its own term and context. -/
theorem selectWritten_left (w : OrderedEquation.Written P.signature)
    (h : Declaration.lawBody w.toLaw ⊆ U.declarations)
    (hs : Declaration.sort w.equation.result ∈ U.declarations)
    (hl : termReferences w.equation.left ⊆ U.declarations) :
    (selectWritten w h).equation.left ≍ selectTerm w.equation.left (lawSortSupport h) hs hl :=
  HEq.rfl

/-- The selected right member is obtained by reindexing its own term and context. -/
theorem selectWritten_right (w : OrderedEquation.Written P.signature)
    (h : Declaration.lawBody w.toLaw ⊆ U.declarations)
    (hs : Declaration.sort w.equation.result ∈ U.declarations)
    (hr : termReferences w.equation.right ⊆ U.declarations) :
    (selectWritten w h).equation.right ≍ selectTerm w.equation.right (lawSortSupport h) hs hr :=
  HEq.rfl

/-- The selected ordered text is attached to the selected literal Law. -/
theorem selectWritten_toLaw (w : OrderedEquation.Written P.signature)
    (h : Declaration.lawBody w.toLaw ⊆ U.declarations) :
    (selectWritten w h).toLaw = selectLaw w.toLaw h := by
  simp only [OrderedEquation.Written.toLaw_eq, selectLaw_eq]
  rfl

/-- A selected ordered equality is registered under the original retained Law's name. -/
noncomputable def selectNamedEquation (name : U.RetainedLaw) (w : NamedOrderedEquation P.laws name.val) :
    NamedOrderedEquation (laws U) name := by
  have h := Declaration.lawBody_subset_of_mem name.property
  have hw : Declaration.lawBody w.written.toLaw ⊆ U.declarations := w.statement_eq.symm ▸ h
  exact ⟨selectWritten w.written hw, (selectWritten_toLaw w.written hw).trans
    (selectLaw_congr w.statement_eq hw h)⟩

/-- Selection keeps an ordered equation's result sort under the retained-name subtype. -/
theorem selectNamedEquation_result (name : U.RetainedLaw) (w : NamedOrderedEquation P.laws name.val) :
    (selectNamedEquation name w).written.equation.result.val = w.written.equation.result :=
  rfl

end DeclarationContext.Selected
end SHIGURE
