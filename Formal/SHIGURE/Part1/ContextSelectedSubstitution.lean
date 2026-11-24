import Formal.SHIGURE.Part1.ContextSelectedTerms

/-! # Literal substitution after declaration restriction

Every substitution contributes its full definedness guard to the Law.
The guard supplies the original variable context and the references of
every substituted term, so the history can be retyped on selected names.
-/

universe u

namespace SHIGURE
namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- Each primitive reference of an atom is still needed in its strict substituted formula. -/
private theorem atomicReferences_subset_substitute {Γ Δ : List P.signature.SortType}
    (a : Atomic P.signature Γ) (θ : Substitution P.signature Γ Δ) :
    Declaration.atomic a ⊆ Declaration.formula (a.substitute θ) := by
  cases a with
  | eq x y => rw [Declaration.atomic_eq]; exact Set.empty_subset _
  | rel r ρ =>
    rw [Atomic.substitute_rel, Formula.termRel_eq_bindArguments, Declaration.atomic_rel]
    simpa only [Declaration.formula_atom, Declaration.atomic_rel] using
      (formula_subset_bindArguments _ (fun i => θ (ρ i)) (.atom (.rel r (Var.inLeft Δ))))
  | domain p ρ =>
    rw [Atomic.substitute_domain, Formula.termDomain_eq_bindArguments, Declaration.atomic_domain]
    simpa only [Declaration.formula_atom, Declaration.atomic_domain] using
      (formula_subset_bindArguments _ (fun i => θ (ρ i)) (.atom (.domain p (Var.inLeft Δ))))
  | graph op ρ y =>
    rw [Atomic.substitute_graph, Formula.termGraph_eq_bindArguments, Declaration.atomic_graph]
    simpa only [Declaration.formula_atom, Declaration.atomic_graph] using
      (formula_subset_bindArguments _ (Term.argsCons (θ y) (fun i => θ (ρ i)))
        (.atom (.graph op (fun i => (Var.there i).inLeft Δ) (Var.here.inLeft Δ))))

/-- Literal substitution preserves all original primitive symbols and bound sorts of a formula. -/
theorem formulaReferences_subset_substitute {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    ∀ {Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ),
      Declaration.formula p ⊆ Declaration.formula (p.substitute θ) := by
  induction p with
  | atom a =>
    intro Δ θ
    rw [Formula.substitute_atom, Declaration.formula_atom]
    exact atomicReferences_subset_substitute a θ
  | truth => intro Δ θ; rw [Declaration.formula_truth]; exact Set.empty_subset _
  | falsehood => intro Δ θ; rw [Declaration.formula_falsehood]; exact Set.empty_subset _
  | conj p q hp hq =>
    intro Δ θ
    simp only [Formula.substitute_conj, Declaration.formula_conj]
    intro d hd
    exact hd.elim (fun h => Or.inl (hp θ h)) (fun h => Or.inr (hq θ h))
  | disj p q hp hq =>
    intro Δ θ
    simp only [Formula.substitute_disj, Declaration.formula_disj]
    intro d hd
    exact hd.elim (fun h => Or.inl (hp θ h)) (fun h => Or.inr (hq θ h))
  | ex p hp =>
    intro Δ θ
    simp only [Formula.substitute_ex, Declaration.formula_ex]
    intro d hd
    exact hd.elim Or.inl (fun h => Or.inr (hp θ.lift h))

/-- A substituted term uses only references from the original term and the substitution. -/
theorem substitute_term_kept {Γ : List P.signature.SortType} {s : P.signature.SortType} (t : Term P.signature Γ s) :
    ∀ {Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ),
      (termReferences t ⊆ U.declarations) →
      (∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations) →
      termReferences (t.substitute θ) ⊆ U.declarations := by
  induction t with
  | var i =>
    intro Δ θ _ hθ
    rw [Term.substitute_var]
    exact hθ i
  | app op ts ih =>
    intro Δ θ ht hθ d hd
    rw [Term.substitute_app, termReferences_app] at hd
    rw [termReferences_app] at ht
    rcases hd with hd | ⟨s, i, hd⟩
    · exact ht (Or.inl hd)
    · exact ih i θ (fun _ h => ht (Or.inr ⟨_, i, h⟩)) hθ hd
  | letBind init body hi hb =>
    intro Δ θ ht hθ d hd
    rw [Term.substitute_letBind, termReferences_letBind] at hd
    rw [termReferences_letBind] at ht
    rcases hd with hd | hd | hd
    · exact ht (Or.inl hd)
    · exact hi θ (fun _ h => ht (Or.inr (Or.inl h))) hθ hd
    · exact hb θ.lift (fun _ h => ht (Or.inr (Or.inr h))) (liftTermReferences θ hθ) hd

/-- Retyping the strict witnesses in an atomic substitution agrees with substituting selected terms. -/
private theorem selectFormula_substitute_atom {Γ Δ : List P.signature.SortType} (a : Atomic P.signature Γ)
    (θ : Substitution P.signature Γ Δ) (hΓ : Declaration.sorts Γ ⊆ U.declarations)
    (hΔ : Declaration.sorts Δ ⊆ U.declarations)
    (hθ : ∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations)
    (ha : Declaration.atomicSupport a ⊆ U.declarations)
    (h : Declaration.formulaSupport (a.substitute θ) ⊆ U.declarations) :
    selectFormula (a.substitute θ) h = (selectAtomic a ha).substitute (selectSubstitution θ hΓ hΔ hθ) := by
  let θ' := selectSubstitution θ hΓ hΔ hθ
  cases a with
  | @eq s x y =>
    simp only [Atomic.substitute_eq] at h ⊢
    simp only [selectAtomic_eq, Atomic.substitute_eq]
    refine (selectFormula_termEq (θ x) (θ y) hΔ (varKept hΓ x) (hθ x) (hθ y) h).trans ?_
    exact congrArg₂ (Formula.termEq (sig := signature U))
      (selectSubstitution_apply θ hΓ hΔ hθ x).symm (selectSubstitution_apply θ hΓ hΔ hθ y).symm
  | rel r ρ =>
    simp only [Atomic.substitute_rel] at h ⊢
    simp only [selectAtomic_rel, Atomic.substitute_rel]
    let kept := ha (Declaration.relation_mem_atomicSupport r ρ)
    let hΛ := relationInputs r kept
    refine (selectFormula_termRel r (fun i => θ (ρ i)) hΔ kept (fun i => hθ (ρ i)) h).trans ?_
    apply congrArg (fun (ts : ∀ {s}, Var (context (P.signature.relInputs r) hΛ) s →
      Term (signature U) (context Δ hΔ) s) => Formula.termRel (sig := signature U) ⟨r, kept⟩ ts)
    funext s i
    simpa only [selectRenaming_apply] using (selectSubstitution_apply θ hΓ hΔ hθ (ρ (ambientVar hΛ i))).symm
  | domain p ρ =>
    simp only [Atomic.substitute_domain] at h ⊢
    simp only [selectAtomic_domain, Atomic.substitute_domain]
    let kept := ha (Declaration.domain_mem_atomicSupport p ρ)
    let hΛ := operationInputs (.partialOp p) kept
    refine (selectFormula_termDomain p (fun i => θ (ρ i)) hΔ kept (fun i => hθ (ρ i)) h).trans ?_
    apply congrArg (fun (ts : ∀ {s}, Var (context (P.signature.partialArity p).inputs hΛ) s →
      Term (signature U) (context Δ hΔ) s) => Formula.termDomain (sig := signature U) ⟨p, kept⟩ ts)
    funext s i
    simpa only [selectRenaming_apply] using (selectSubstitution_apply θ hΓ hΔ hθ (ρ (ambientVar hΛ i))).symm
  | graph op ρ y =>
    simp only [Atomic.substitute_graph] at h ⊢
    rw [selectAtomic_graph]
    let kept := ha (Declaration.graph_mem_atomicSupport op ρ y)
    let hΛ := operationInputs op kept
    have atInputs : (fun {s} (i : Var (context op.arity.inputs hΛ) s) =>
        selectTerm (θ (ρ (ambientVar hΛ i))) hΔ s.property (hθ _)) =
        (fun {s} (i : Var (context op.arity.inputs hΛ) s) => θ' (selectRenaming hΛ hΓ ρ i)) := by
      funext s i
      simpa only [selectRenaming_apply] using (selectSubstitution_apply θ hΓ hΔ hθ (ρ (ambientVar hΛ i))).symm
    have atOutput := (selectSubstitution_apply θ hΓ hΔ hθ y).symm
    refine (selectFormula_termGraph op (fun i => θ (ρ i)) (θ y) hΔ kept (fun i => hθ (ρ i)) (hθ y) h).trans ?_
    cases op <;> simp only [selectGraph_total, selectGraph_partialOp, selectGraph_quantity, Atomic.substitute_graph]
    all_goals exact congrArg₂ (Formula.termGraph (operation _ kept)) atInputs atOutput

/-- Selection preserves literal positive-formula substitution, including binder lifts and expanded atoms. -/
theorem selectFormula_substitute {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    ∀ {Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ)
      (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hΔ : Declaration.sorts Δ ⊆ U.declarations)
      (hθ : ∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations)
      (hp : Declaration.formulaSupport p ⊆ U.declarations)
      (hSub : Declaration.formulaSupport (p.substitute θ) ⊆ U.declarations),
      selectFormula (p.substitute θ) hSub =
        (selectFormula p hp).substitute (selectSubstitution θ hΓ hΔ hθ) := by
  induction p with
  | atom a =>
    intro Δ θ hΓ hΔ hθ hp hSub
    simp only [Formula.substitute_atom, selectFormula_atom] at hSub ⊢
    exact selectFormula_substitute_atom a θ hΓ hΔ hθ ((Declaration.formulaSupport_atom a).ge.trans hp) hSub
  | truth =>
    intro Δ θ hΓ hΔ hθ hp hSub
    simp only [Formula.substitute_truth, selectFormula_truth] at hSub ⊢
  | falsehood =>
    intro Δ θ hΓ hΔ hθ hp hSub
    simp only [Formula.substitute_falsehood, selectFormula_falsehood] at hSub ⊢
  | conj p q ihp ihq =>
    intro Δ θ hΓ hΔ hθ hp hSub
    simp only [Formula.substitute_conj, selectFormula_conj] at hSub ⊢
    have written := Declaration.formula_conj (P := P) p q
    have moved := Declaration.formula_conj (P := P) (p.substitute θ) (q.substitute θ)
    exact congrArg₂ Formula.conj
      (ihp θ hΓ hΔ hθ ((Declaration.binarySupport_left written).trans hp)
        ((Declaration.binarySupport_left moved).trans hSub))
      (ihq θ hΓ hΔ hθ ((Declaration.binarySupport_right written).trans hp)
        ((Declaration.binarySupport_right moved).trans hSub))
  | disj p q ihp ihq =>
    intro Δ θ hΓ hΔ hθ hp hSub
    simp only [Formula.substitute_disj, selectFormula_disj] at hSub ⊢
    have written := Declaration.formula_disj (P := P) p q
    have moved := Declaration.formula_disj (P := P) (p.substitute θ) (q.substitute θ)
    exact congrArg₂ Formula.disj
      (ihp θ hΓ hΔ hθ ((Declaration.binarySupport_left written).trans hp)
        ((Declaration.binarySupport_left moved).trans hSub))
      (ihq θ hΓ hΔ hθ ((Declaration.binarySupport_right written).trans hp)
        ((Declaration.binarySupport_right moved).trans hSub))
  | @ex Γ s p ih =>
    intro Δ θ hΓ hΔ hθ hp hSub
    simp only [Formula.substitute_ex, selectFormula_ex] at hSub ⊢
    let hs := hp (Declaration.boundSort_mem_formulaSupport p)
    let hΓ' := Declaration.sorts_cons_subset hs hΓ
    let hΔ' := Declaration.sorts_cons_subset hs hΔ
    have selected := ih (θ.lift (s := s)) hΓ' hΔ' (liftTermReferences θ hθ)
      (existsSupport hp) (existsSupport hSub)
    exact congrArg (Formula.ex (sig := signature U)) (selected.trans
      (congrArg (fun replacement => Formula.substitute replacement (selectFormula p (existsSupport hp)))
        (selectSubstitution_lift θ hΓ hΔ hθ hs)))

end DeclarationContext.Selected
end SHIGURE
