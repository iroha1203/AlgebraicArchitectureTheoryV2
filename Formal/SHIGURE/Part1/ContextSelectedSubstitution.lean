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

private theorem atomicReferences_subset_substitute {Γ Δ : List P.signature.SortType}
    (a : Atomic P.signature Γ) (θ : Substitution P.signature Γ Δ) :
    Declaration.atomic a ⊆ Declaration.formula (a.substitute θ) := by
  cases a with
  | eq x y => exact Set.empty_subset _
  | rel r ρ => exact formula_subset_bindArguments _ (fun i => θ (ρ i)) (.atom (.rel r (Var.inLeft Δ)))
  | domain p ρ => exact formula_subset_bindArguments _ (fun i => θ (ρ i)) (.atom (.domain p (Var.inLeft Δ)))
  | graph op ρ y =>
    exact formula_subset_bindArguments _ (Term.argsCons (θ y) (fun i => θ (ρ i)))
      (.atom (.graph op (fun i => (Var.there i).inLeft Δ) (Var.here.inLeft Δ)))

/-- Literal substitution preserves all original primitive symbols and bound sorts of a formula. -/
theorem formulaReferences_subset_substitute {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    ∀ {Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ),
      Declaration.formula p ⊆ Declaration.formula (p.substitute θ) := by
  induction p with
  | atom a => exact fun θ => atomicReferences_subset_substitute a θ
  | truth => intro Δ θ; exact Set.empty_subset _
  | falsehood => intro Δ θ; exact Set.empty_subset _
  | conj p q hp hq =>
    intro Δ θ d hd
    exact hd.elim (fun h => Or.inl (hp θ h)) (fun h => Or.inr (hq θ h))
  | disj p q hp hq =>
    intro Δ θ d hd
    exact hd.elim (fun h => Or.inl (hp θ h)) (fun h => Or.inr (hq θ h))
  | ex p hp =>
    intro Δ θ d hd
    exact hd.elim Or.inl (fun h => Or.inr (hp θ.lift h))

/-- A substituted term uses only references from the original term and the substitution. -/
theorem substitute_term_kept {Γ : List P.signature.SortType} {s : P.signature.SortType} (t : Term P.signature Γ s) :
    ∀ {Δ : List P.signature.SortType} (θ : Substitution P.signature Γ Δ),
      (termReferences t ⊆ U.declarations) →
      (∀ {s} (i : Var Γ s), termReferences (θ i) ⊆ U.declarations) →
      termReferences (t.substitute θ) ⊆ U.declarations := by
  induction t with
  | var i => exact fun θ _ hθ => hθ i
  | app op ts ih =>
    intro Δ θ ht hθ d hd
    rcases hd with hd | ⟨s, i, hd⟩
    · exact ht (Or.inl hd)
    · exact ih i θ (fun _ h => ht (Or.inr ⟨_, i, h⟩)) hθ hd
  | letBind init body hi hb =>
    intro Δ θ ht hθ d hd
    rcases hd with hd | hd | hd
    · exact ht (Or.inl hd)
    · exact hi θ (fun _ h => ht (Or.inr (Or.inl h))) hθ hd
    · exact hb θ.lift (fun _ h => ht (Or.inr (Or.inr h))) (liftTermReferences θ hθ) hd

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
    refine (selectFormula_termEq (θ x) (θ y) hΔ (varKept hΓ x) (hθ x) (hθ y) h).trans ?_
    exact congrArg₂ (Formula.termEq (sig := signature U))
      (selectSubstitution_apply θ hΓ hΔ hθ x).symm (selectSubstitution_apply θ hΓ hΔ hθ y).symm
  | rel r ρ =>
    let kept := ha (Or.inr (Set.mem_singleton (Declaration.relation r)))
    let hΛ := relationInputs r kept
    refine (selectFormula_termRel r (fun i => θ (ρ i)) hΔ kept (fun i => hθ (ρ i)) h).trans ?_
    apply congrArg (fun (ts : ∀ {s}, Var (context (P.signature.relInputs r) hΛ) s →
      Term (signature U) (context Δ hΔ) s) => Formula.termRel (sig := signature U) ⟨r, kept⟩ ts)
    funext s i
    exact (selectSubstitution_apply θ hΓ hΔ hθ (ρ (ambientVar hΛ i))).symm
  | domain p ρ =>
    let kept := ha (Or.inr (Set.mem_singleton (Declaration.partialOp p)))
    let hΛ := operationInputs (.partialOp p) kept
    refine (selectFormula_termDomain p (fun i => θ (ρ i)) hΔ kept (fun i => hθ (ρ i)) h).trans ?_
    apply congrArg (fun (ts : ∀ {s}, Var (context (P.signature.partialArity p).inputs hΛ) s →
      Term (signature U) (context Δ hΔ) s) => Formula.termDomain (sig := signature U) ⟨p, kept⟩ ts)
    funext s i
    exact (selectSubstitution_apply θ hΓ hΔ hθ (ρ (ambientVar hΛ i))).symm
  | graph op ρ y =>
    let kept := ha (Or.inr (Set.mem_singleton (Declaration.ofOperation op)))
    let hΛ := operationInputs op kept
    have atInputs : (fun {s} (i : Var (context op.arity.inputs hΛ) s) =>
        selectTerm (θ (ρ (ambientVar hΛ i))) hΔ s.property (hθ _)) =
        (fun {s} (i : Var (context op.arity.inputs hΛ) s) => θ' (selectRenaming hΛ hΓ ρ i)) := by
      funext s i
      exact (selectSubstitution_apply θ hΓ hΔ hθ (ρ (ambientVar hΛ i))).symm
    have atOutput := (selectSubstitution_apply θ hΓ hΔ hθ y).symm
    refine (selectFormula_termGraph op (fun i => θ (ρ i)) (θ y) hΔ kept (fun i => hθ (ρ i)) (hθ y) h).trans ?_
    cases op <;> exact congrArg₂ (Formula.termGraph (operation _ kept)) atInputs atOutput

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
  | atom a => exact fun θ hΓ hΔ hθ hp hSub => selectFormula_substitute_atom a θ hΓ hΔ hθ hp hSub
  | truth => intros; rfl
  | falsehood => intros; rfl
  | conj p q ihp ihq =>
    intro Δ θ hΓ hΔ hθ hp hSub
    exact congrArg₂ (Formula.conj (sig := signature U))
      (ihp θ hΓ hΔ hθ (leftSupport hp) (leftSupport hSub))
      (ihq θ hΓ hΔ hθ (rightSupport hp) (rightSupport hSub))
  | disj p q ihp ihq =>
    intro Δ θ hΓ hΔ hθ hp hSub
    exact congrArg₂ (Formula.disj (sig := signature U))
      (ihp θ hΓ hΔ hθ (leftSupport hp) (leftSupport hSub))
      (ihq θ hΓ hΔ hθ (rightSupport hp) (rightSupport hSub))
  | @ex Γ s p ih =>
    intro Δ θ hΓ hΔ hθ hp hSub
    let hs := hp (Or.inr (Or.inl (Set.mem_singleton (Declaration.sort s))))
    let hΓ' := Declaration.sorts_cons_subset hs hΓ
    let hΔ' := Declaration.sorts_cons_subset hs hΔ
    have selected := ih (θ.lift (s := s)) hΓ' hΔ' (liftTermReferences θ hθ)
      (existsSupport hp) (existsSupport hSub)
    exact congrArg (Formula.ex (sig := signature U)) (selected.trans
      (congrArg (fun replacement => Formula.substitute replacement (selectFormula p (existsSupport hp)))
        (selectSubstitution_lift θ hΓ hΔ hθ hs)))

end DeclarationContext.Selected
end SHIGURE
