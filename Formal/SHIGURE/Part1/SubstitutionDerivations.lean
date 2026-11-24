import Formal.SHIGURE.Part1.BoundArguments

/-! # Partial substitution in positive derivations

Appendix A.1. When a tuple of variables carries the values of all
substituted terms, the expanded formula can be moved in both directions
by positive inference. The value graph premises remain available
through conjunction, disjunction and existential binding.

## Implementation notes

The local comparison keeps all value graphs available when a formula opens a
binder. The outer witness block includes unused positions because their
partial terms also contribute to the definedness guard.
-/

universe u

namespace SHIGURE.Derivation

variable {T : Theory.{u}} {Γ Δ E : List T.signature.SortType}

/-- At witnessed argument values, each substituted atom has both syntactic implications. -/
noncomputable def substituteAtomicAt (a : Atomic T.signature Γ) (θ : Substitution T.signature Γ Δ)
    (ambient : Renaming Δ E) (values : Renaming Γ E) (guards : Formula T.signature E)
    (value : ∀ {s} (i : Var Γ s), Derivation T guards ((θ i).graphAt ambient (values i))) :
    Derivation T (guards.conj ((a.substitute θ).rename ambient)) (.atom (a.rename values)) ×
      Derivation T (guards.conj (.atom (a.rename values))) ((a.substitute θ).rename ambient) := by
  cases a with
  | eq x y =>
    rw [Atomic.substitute_eq]
    exact useTermEquality (θ x) (θ y) ambient (values x) (values y) guards (value x) (value y)
  | rel r inputs =>
    simpa only [Atomic.substitute_rel, Formula.termRel_eq_bindArguments, Formula.rename_atom, Atomic.rename_rel,
      Renaming.append_inLeft, Renaming.comp_apply] using
      (useBoundValuesAlong (fun i => θ (inputs i)) ambient (Renaming.comp values inputs)
        guards (fun i => value (inputs i)) (.atom (.rel r (Var.inLeft Δ))))
  | domain p inputs =>
    simpa only [Atomic.substitute_domain, Formula.termDomain_eq_bindArguments, Formula.rename_atom, Atomic.rename_domain,
      Renaming.append_inLeft, Renaming.comp_apply] using
      (useBoundValuesAlong (fun i => θ (inputs i)) ambient (Renaming.comp values inputs)
        guards (fun i => value (inputs i)) (.atom (.domain p (Var.inLeft Δ))))
  | graph op inputs output =>
    let selected : Renaming (op.arity.output :: op.arity.inputs) E :=
      Renaming.cons (values output) (Renaming.comp values inputs)
    let terms : ∀ {s}, Var (op.arity.output :: op.arity.inputs) s → Term T.signature Δ s
      | _, .here => θ output
      | _, .there i => θ (inputs i)
    have evaluate {t : T.signature.SortType} (i : Var (op.arity.output :: op.arity.inputs) t) :
        Derivation T guards ((terms i).graphAt ambient (selected i)) := by
      cases i with
      | here => exact value output
      | there i => exact value (inputs i)
    simpa only [Atomic.substitute_graph, Formula.termGraph_eq_bindArguments, Formula.rename_atom, Atomic.rename_graph,
      Renaming.append_inLeft, selected, Renaming.cons_here, Renaming.cons_there, Renaming.comp_apply] using
      (useBoundValuesAlong terms ambient selected guards evaluate
        (.atom (.graph op (fun i => (Var.there i).inLeft Δ) (Var.here.inLeft Δ))))

/-- Derive an existential implication while keeping a separate antecedent in the outer context. -/
def existsUnder {s : T.signature.SortType} {guards : Formula T.signature E}
    {p q : Formula T.signature (s :: E)}
    (body : Derivation T ((guards.rename (fun i => .there i)).conj p) q) :
    Derivation T (guards.conj p.ex) q.ex := by
  apply Derivation.existsElim
  refine .cut body ?_
  simpa only [Formula.rename_comp, Renaming.openHead_lift_shift, Formula.rename_id, Formula.rename_ex]
    using (Derivation.existsIntro (T := T)
      (q.rename (Renaming.lift (fun i => Var.there (t := s) i))) Var.here)

/-- Witnesses for the original terms extend under a fresh variable by reflexivity and renaming. -/
def liftSubstitutionValues {s : T.signature.SortType} (θ : Substitution T.signature Γ Δ)
    (ambient : Renaming Δ E) (values : Renaming Γ E) (guards : Formula T.signature E)
    (value : ∀ {t} (i : Var Γ t), Derivation T guards ((θ i).graphAt ambient (values i)))
    {t : T.signature.SortType} (i : Var (s :: Γ) t) :
    Derivation T (guards.rename (fun j => .there j))
      ((θ.lift i).graphAt (Renaming.lift ambient) ((Renaming.lift values) i)) := by
  cases i with
  | here =>
    rw [Substitution.lift_here, Term.graphAt_var]
    exact .cut (.truth _) (.eqRefl .here)
  | there j =>
    rw [Substitution.lift_there, Term.graphAt_renameTerm]
    simpa only [Term.graphAt_rename] using (Derivation.rename (fun i => Var.there (t := s) i) (value j))

/-- Under a complete tuple of value graphs, formulas and their partial substitutions imply each other. -/
noncomputable def substituteFormulaAt (p : Formula T.signature Γ) :
    ∀ {Δ E : List T.signature.SortType} (θ : Substitution T.signature Γ Δ)
      (ambient : Renaming Δ E) (values : Renaming Γ E) (guards : Formula T.signature E)
      (_ : ∀ {s} (i : Var Γ s), Derivation T guards ((θ i).graphAt ambient (values i))),
      Derivation T (guards.conj ((p.substitute θ).rename ambient)) (p.rename values) ×
        Derivation T (guards.conj (p.rename values)) ((p.substitute θ).rename ambient) := by
  induction p with
  | atom a =>
    intro Δ E θ ambient values guards value
    simp only [Formula.substitute_atom, Formula.rename_atom]
    exact substituteAtomicAt a θ ambient values guards value
  | truth =>
    intros
    rw [Formula.substitute_truth]
    exact ⟨.andRight _ _, .andRight _ _⟩
  | falsehood =>
    intros
    rw [Formula.substitute_falsehood]
    exact ⟨.andRight _ _, .andRight _ _⟩
  | conj p q hp hq =>
    intro Δ E θ ambient values guards value
    let pProof := hp θ ambient values guards value
    let qProof := hq θ ambient values guards value
    simp only [Formula.substitute_conj, Formula.rename_conj]
    exact ⟨.andIntro
      (.cut (.andIntro (.andLeft _ _) (.cut (.andRight _ _) (.andLeft _ _))) pProof.1)
      (.cut (.andIntro (.andLeft _ _) (.cut (.andRight _ _) (.andRight _ _))) qProof.1),
      .andIntro
        (.cut (.andIntro (.andLeft _ _) (.cut (.andRight _ _) (.andLeft _ _))) pProof.2)
        (.cut (.andIntro (.andLeft _ _) (.cut (.andRight _ _) (.andRight _ _))) qProof.2)⟩
  | disj p q hp hq =>
    intro Δ E θ ambient values guards value
    let pProof := hp θ ambient values guards value
    let qProof := hq θ ambient values guards value
    simp only [Formula.substitute_disj, Formula.rename_disj]
    exact ⟨.orElim (.cut pProof.1 (.orLeft _ _)) (.cut qProof.1 (.orRight _ _)),
      .orElim (.cut pProof.2 (.orLeft _ _)) (.cut qProof.2 (.orRight _ _))⟩
  | @ex Γ s p ih =>
    intro Δ E θ ambient values guards value
    let body := ih θ.lift (Renaming.lift ambient) (Renaming.lift values)
      (guards.rename (fun i => Var.there (t := s) i)) (liftSubstitutionValues θ ambient values guards value)
    simp only [Formula.substitute_ex, Formula.rename_ex]
    exact ⟨existsUnder body.1, existsUnder body.2⟩

end SHIGURE.Derivation

namespace SHIGURE.Substitution

variable {sig : Signature.{u}} {Γ Δ : List sig.SortType}

/-- The value graphs of all substituted terms on fresh variables. -/
def valueGraphs (θ : Substitution sig Γ Δ) : Formula sig (Γ ++ Δ) :=
  Formula.conjoin Γ (fun i => (θ i).graphAt (Var.shift Γ) (i.inLeft Δ))

/-- Bind all substituted values before using a formula on the original variables. -/
def bindFormula (θ : Substitution sig Γ Δ) (p : Formula sig Γ) : Formula sig Δ :=
  Formula.existsMany Γ (θ.valueGraphs.conj (p.rename (Var.inLeft Δ)))

/-- Binding a substitution introduces a value variable for every position before reading the formula. -/
theorem bindFormula_eq_existsMany (θ : Substitution sig Γ Δ) (p : Formula sig Γ) :
    θ.bindFormula p = Formula.existsMany Γ (θ.valueGraphs.conj (p.rename (Var.inLeft Δ))) := rfl

/-- The block of value graphs uses the term graphs as its individual witness conditions. -/
theorem valueGraphs_eq_witnessConjunction (θ : Substitution sig Γ Δ) :
    θ.valueGraphs = Formula.witnessConjunction Γ (fun i => (θ i).graph) := by
  simp only [valueGraphs, Formula.witnessConjunction_eq_conjoin, Term.graphAt_eq_rename_graph]

end SHIGURE.Substitution

namespace SHIGURE.Derivation

variable {T : Theory.{u}} {Γ Δ : List T.signature.SortType}

/-- The definedness of every substituted term supplies a single complete tuple of witnesses. -/
def substitutionWitnesses (θ : Substitution T.signature Γ Δ) :
    Derivation T θ.defined (Formula.existsMany Γ θ.valueGraphs) := by
  rw [Substitution.defined_eq_conjoin, Substitution.valueGraphs_eq_witnessConjunction]
  exact packExistences (fun i => (θ i).graph)

/-- Appendix A.1: binding the substitution values is mutually derivable with guarded substitution. -/
noncomputable def bindFormulaDerivations (θ : Substitution T.signature Γ Δ) (p : Formula T.signature Γ) :
    Derivation T (θ.bindFormula p) (θ.defined.conj (p.substitute θ)) ×
      Derivation T (θ.defined.conj (p.substitute θ)) (θ.bindFormula p) := by
  let lift : Renaming Δ (Γ ++ Δ) := Var.shift Γ
  let witnesses : Renaming Γ (Γ ++ Δ) := Var.inLeft Δ
  let graphs := θ.valueGraphs
  let pAtValues := p.rename witnesses
  let expanded := p.substitute θ
  let comparison := substituteFormulaAt p θ lift witnesses graphs (fun i => conjoinAt _ i)
  have definedAtValues : Derivation T (graphs.conj pAtValues) (θ.defined.rename lift) := by
    simp only [Substitution.defined_eq_conjoin, Formula.rename_conjoin]
    exact conjoinIntro _ (fun i => .cut (.cut (.andLeft _ _) (conjoinAt _ i))
      (graphAtDefined (θ i) lift (witnesses i)))
  have forward : Derivation T (θ.bindFormula p) (θ.defined.conj expanded) :=
    .andIntro (existsManyElim definedAtValues) (existsManyElim comparison.2)
  have pack : Derivation T (graphs.conj pAtValues) ((θ.bindFormula p).rename lift) := by
    rw [Substitution.bindFormula_eq_existsMany]
    simpa only [witnesses, lift, Renaming.append_blocks, Formula.rename_id] using
      (existsManyIntroAlong (T := T) witnesses lift (graphs.conj pAtValues))
  have withWitnesses : Derivation T ((expanded.rename lift).conj graphs) ((θ.bindFormula p).rename lift) :=
    .cut (.andIntro (.andRight _ _) (.cut (.andIntro (.andRight _ _) (.andLeft _ _)) comparison.1)) pack
  have backward : Derivation T (θ.defined.conj expanded) (θ.bindFormula p) :=
    .cut (.andIntro (.andRight _ _) (.cut (.andLeft _ _) (substitutionWitnesses θ)))
      (existsManyElimWith withWitnesses)
  exact ⟨forward, backward⟩

/-- Appendix A.1: substitution of partial terms transports a derivation under all its definedness guards. -/
noncomputable def substitutePartial (θ : Substitution T.signature Γ Δ) {p q : Formula T.signature Γ}
    (d : Derivation T p q) : Derivation T (θ.defined.conj (p.substitute θ)) (q.substitute θ) :=
  .cut (bindFormulaDerivations θ p).2
    (.cut (existsManyMono (andMono (.refl _) (.rename (Var.inLeft Δ) d)))
      (.cut (bindFormulaDerivations θ q).1 (.andRight _ _)))

/-- Derived totality of every substituted term discharges the partial substitution guard. -/
noncomputable def substituteTotal (θ : Substitution T.signature Γ Δ) {p q : Formula T.signature Γ}
    (d : Derivation T p q) (total : ∀ {s} (i : Var Γ s), Derivation T .truth (θ i).defined) :
    Derivation T (p.substitute θ) (q.substitute θ) :=
  .cut (.andIntro (.cut (.truth _) (conjoinIntro _ total)) (.refl _)) (substitutePartial θ d)

end SHIGURE.Derivation
