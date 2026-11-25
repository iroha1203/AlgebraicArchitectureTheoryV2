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

/-- A retained Law's selected statement comes from its original declaration. -/
theorem laws_statement (name : U.RetainedLaw) :
    (laws U).statement name = selectLaw (P.laws.statement name.val)
      (Declaration.lawBody_subset_of_mem name.property) :=
  rfl

/-- The ordinary theory of the restriction is defined over the genuinely selected signature. -/
def theory (U : DeclarationContext P) : Theory.{u} := (laws U).toTheory

/-- A required Law of the ordinary theory is the selection of the corresponding scoped Law. -/
theorem theory_law (name : (theory U).LawName) :
    (theory U).law name = selectLaw
      (U.scopedTheory.law ⟨⟨name.val.val, name.property⟩, name.val.property⟩)
      (Declaration.lawBody_subset_of_mem name.val.property) := by
  let original : U.scopedTheory.LawName := ⟨⟨name.val.val, name.property⟩, name.val.property⟩
  exact selectLaw_congr (U.scopedTheory_law original).symm
    (Declaration.lawBody_subset_of_mem name.val.property) (Declaration.lawBody_subset_of_mem name.val.property)

/-- The selected structural rule retains its original rule and primitive name. -/
def selectRule : (rule : GraphAxiom P.signature) → Declaration.graphRuleName rule ∈ U.declarations →
    GraphAxiom (signature U)
  | .functional op, keep => .functional (operation op (by simpa only [Declaration.graphRuleName_functional] using keep))
  | .totality f, keep => .totality ⟨f, by simpa only [Declaration.graphRuleName_totality] using keep⟩
  | .quantityTotality q, keep => .quantityTotality ⟨q, by simpa only [Declaration.graphRuleName_quantityTotality] using keep⟩
  | .graphImpliesDomain p, keep => .graphImpliesDomain ⟨p, by simpa only [Declaration.graphRuleName_graphImpliesDomain] using keep⟩
  | .domainImpliesGraph p, keep => .domainImpliesGraph ⟨p, by simpa only [Declaration.graphRuleName_domainImpliesGraph] using keep⟩

section

attribute [local irreducible] context arity

/-- A selected variable map shifted twice agrees after transport across both selected heads. -/
theorem selectRenaming_there_there_cast {Γ : List P.signature.SortType} {s t : P.signature.SortType}
    (keepS : Declaration.sort s ∈ U.declarations) (keepT : Declaration.sort t ∈ U.declarations)
    (keep : Declaration.sorts Γ ⊆ U.declarations) :
    let tail := Declaration.sorts_cons_subset keepS keep
    let whole := Declaration.sorts_cons_subset keepT tail
    @cast _ _ (congrArg (Renaming (context Γ keep)) (context_cons_cons s t Γ whole))
      (selectRenaming keep whole (fun i => .there (.there i))) =
      (fun {a} (i : Var (context Γ keep) a) =>
        Var.there (t := (⟨t, keepT⟩ : SortName U)) (Var.there (t := (⟨s, keepS⟩ : SortName U)) i)) := by
  dsimp only
  funext a i
  let tail := Declaration.sorts_cons_subset keepS keep
  let whole := Declaration.sorts_cons_subset keepT tail
  let first := context_cons t (s :: Γ) whole
  let second := context_cons s Γ tail
  rw [Renaming.cast_target_apply (context_cons_cons s t Γ whole), selectRenaming_apply]
  have compose := cast_cast (congrArg (fun ctx => Var ctx a) first)
    (congrArg (fun ctx => Var ctx a) (congrArg (List.cons (⟨t, keepT⟩ : SortName U)) second))
    (selectVar whole (Var.there (t := t) (Var.there (t := s) (ambientVar keep i))))
  rw [← compose, selectVar_cast_there, Renaming.cast_there_target second,
    selectVar_cast_there, selectVar_ambientVar]

/-- Compare graph atoms across equal operation names and variable contexts. -/
private theorem graph_heq {S : Signature.{u}} {Γ Δ : List S.SortType} {op op' : Operation S}
    (contextEq : Γ = Δ) (operationEq : op = op')
    {ρ : Renaming op.arity.inputs Γ} {τ : Renaming op'.arity.inputs Δ}
    {x : Var Γ op.arity.output} {y : Var Δ op'.arity.output}
    (inputs : HEq (fun {s} => ρ (s := s)) (fun {s} => τ (s := s))) (output : HEq x y) :
    HEq (Atomic.graph op ρ x) (Atomic.graph op' τ y) := by
  cases contextEq
  cases operationEq
  have same : (fun {s} => ρ (s := s)) = (fun {s} => τ (s := s)) := eq_of_heq inputs
  rw [same, eq_of_heq output]

/-- Selection of a single shift reindexes the variable past the retained head. -/
private theorem selectRenaming_there_heq {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (head : Declaration.sort s ∈ U.declarations) (kept : Declaration.sorts Γ ⊆ U.declarations) :
    HEq (fun {t} => selectRenaming kept (Declaration.sorts_cons_subset head kept) (fun i => .there i) (s := t))
      (fun {t} (i : Var (context Γ kept) t) => Var.there (t := (⟨s, head⟩ : SortName U)) i) := by
  have shifted := selectRenaming_there_cast head kept kept (fun i => i)
  simp only [selectRenaming_id] at shifted
  exact (cast_heq _ _).symm.trans (heq_of_eq shifted)

/-- Selection of a double shift reindexes the variable past both retained heads. -/
private theorem selectRenaming_twice_heq {Γ : List P.signature.SortType} {s t : P.signature.SortType}
    (keepS : Declaration.sort s ∈ U.declarations) (keepT : Declaration.sort t ∈ U.declarations)
    (keep : Declaration.sorts Γ ⊆ U.declarations) :
    HEq (fun {a} => selectRenaming keep (Declaration.sorts_cons_subset keepT (Declaration.sorts_cons_subset keepS keep))
      (fun i => .there (.there i)) (s := a))
      (fun {a} (i : Var (context Γ keep) a) =>
        Var.there (t := (⟨t, keepT⟩ : SortName U)) (Var.there (t := (⟨s, keepS⟩ : SortName U)) i)) := by
  exact (cast_heq _ _).symm.trans (heq_of_eq (selectRenaming_there_there_cast keepS keepT keep))

/-- The first retained variable agrees at the selected cons context. -/
private theorem selectVar_here_heq {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (keep : Declaration.sorts (s :: Γ) ⊆ U.declarations) :
    HEq (selectVar keep (Var.here : Var (s :: Γ) s))
      (Var.here : Var (⟨s, keep (Declaration.sort_mem_sorts List.mem_cons_self)⟩ ::
        context Γ ((tailSortsSubset s Γ).trans keep)) _) :=
  (cast_heq _ _).symm.trans (heq_of_eq (selectVar_cast_here keep))

/-- The second variable stays second when both leading sorts are retained. -/
private theorem selectVar_there_here_heq {Γ : List P.signature.SortType} {s t : P.signature.SortType}
    (keep : Declaration.sorts (t :: s :: Γ) ⊆ U.declarations) :
    HEq (selectVar keep (Var.there (t := t) (Var.here : Var (s :: Γ) s)))
      (Var.there Var.here : Var
        (⟨t, keep (Declaration.sort_mem_sorts List.mem_cons_self)⟩ ::
          ⟨s, keep (Declaration.sort_mem_sorts (List.mem_cons_of_mem t List.mem_cons_self))⟩ ::
          context Γ ((tailSortsSubset s Γ).trans ((tailSortsSubset t (s :: Γ)).trans keep))) _) := by
  let tail := (tailSortsSubset t (s :: Γ)).trans keep
  let first := context_cons t (s :: Γ) keep
  let second := context_cons s Γ tail
  let retainedHead : SortName U := ⟨t, keep (Declaration.sort_mem_sorts List.mem_cons_self)⟩
  let retainedNext : SortName U := ⟨s, keep (Declaration.sort_mem_sorts (List.mem_cons_of_mem t List.mem_cons_self))⟩
  let alignment := first.trans (congrArg (List.cons retainedHead) second)
  have computation : cast (congrArg (fun ctx => Var ctx _) alignment)
      (selectVar keep (Var.there (t := t) (Var.here : Var (s :: Γ) s))) = .there .here := by
    let i := selectVar keep (Var.there (t := t) (Var.here : Var (s :: Γ) s))
    let carry := congrArg (Var · retainedNext) (congrArg (List.cons retainedHead) second)
    calc
      _ = cast carry (cast (congrArg (Var · retainedNext) first) i) := (cast_cast _ _ i).symm
      _ = cast carry (.there (selectVar tail (Var.here : Var (s :: Γ) s))) :=
        congrArg (cast carry) (selectVar_cast_there keep Var.here)
      _ = .there .here := (Renaming.cast_there_target second _).trans
        (congrArg Var.there (selectVar_cast_here tail))
  exact (cast_heq _ _).symm.trans (heq_of_eq computation)

/-- The first variable stays first when both leading sorts are retained. -/
private theorem selectVar_head_twice_heq {Γ : List P.signature.SortType} {s t : P.signature.SortType}
    (keep : Declaration.sorts (t :: s :: Γ) ⊆ U.declarations) :
    HEq (selectVar keep (Var.here : Var (t :: s :: Γ) t))
      (Var.here : Var
        (⟨t, keep (Declaration.sort_mem_sorts List.mem_cons_self)⟩ ::
          ⟨s, keep (Declaration.sort_mem_sorts (List.mem_cons_of_mem t List.mem_cons_self))⟩ ::
          context Γ ((tailSortsSubset s Γ).trans ((tailSortsSubset t (s :: Γ)).trans keep))) _) := by
  let tail := (tailSortsSubset t (s :: Γ)).trans keep
  let first := context_cons t (s :: Γ) keep
  let second := context_cons s Γ tail
  let retainedHead : SortName U := ⟨t, keep (Declaration.sort_mem_sorts List.mem_cons_self)⟩
  let alignment := first.trans (congrArg (List.cons retainedHead) second)
  have computation : cast (congrArg (fun ctx => Var ctx _) alignment)
      (selectVar keep (Var.here : Var (t :: s :: Γ) t)) = .here := by
    let i := selectVar keep (Var.here : Var (t :: s :: Γ) t)
    let carry := congrArg (Var · retainedHead) (congrArg (List.cons retainedHead) second)
    calc
      _ = cast carry (cast (congrArg (Var · retainedHead) first) i) := (cast_cast _ _ i).symm
      _ = cast carry .here := congrArg (cast carry) (selectVar_cast_here keep)
      _ = .here := Renaming.cast_here_target second
  exact (cast_heq _ _).symm.trans (heq_of_eq computation)

/-- The structural rule places the retained output before the retained input sorts. -/
private theorem context_one_output (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) (selected : Operation (signature U))
    (arityEq : selected.arity = arity op keep)
    (kept : Declaration.sorts (op.arity.output :: op.arity.inputs) ⊆ U.declarations) :
    context (op.arity.output :: op.arity.inputs) kept = selected.arity.output :: selected.arity.inputs := by
  rw [context_cons, arityEq, arity_output, arity_inputs]

/-- The graph functionality rule places two copies of the retained output before the inputs. -/
private theorem context_two_outputs (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) (selected : Operation (signature U))
    (arityEq : selected.arity = arity op keep)
    (kept : Declaration.sorts (op.arity.output :: op.arity.output :: op.arity.inputs) ⊆ U.declarations) :
    context (op.arity.output :: op.arity.output :: op.arity.inputs) kept =
      selected.arity.output :: selected.arity.output :: selected.arity.inputs := by
  rw [context_cons, context_cons, arityEq, arity_output, arity_inputs]

end

/-- The two shifts also agree at the definitionally identical selected contexts. -/
theorem selectRenaming_there_there {Γ : List P.signature.SortType} {s t : P.signature.SortType}
    (keepS : Declaration.sort s ∈ U.declarations) (keepT : Declaration.sort t ∈ U.declarations)
    (kept : Declaration.sorts Γ ⊆ U.declarations) :
    (selectRenaming kept (Declaration.sorts_cons_subset keepT (Declaration.sorts_cons_subset keepS kept))
      (fun i => .there (.there i)) : Renaming _ _) =
      (fun {_} i => Var.there (t := (⟨t, keepT⟩ : SortName U)) (Var.there (t := (⟨s, keepS⟩ : SortName U)) i)) :=
  selectRenaming_there_there_cast keepS keepT kept

/-- Align graph-atom formulas along the context equality of the structural rule. -/
private theorem cast_atom_of_heq {S : Signature.{u}} {Γ Δ : List S.SortType} (same : Γ = Δ)
    {a : Atomic S Γ} {b : Atomic S Δ} (aligned : HEq a b) :
    cast (congrArg (Formula S) same) (.atom a) = .atom b := by
  cases same
  cases eq_of_heq aligned
  rfl

/-- Precomposing with the transport between equal input lists preserves the typed renaming. -/
private theorem renaming_input_heq {S : Type u} {Γ Δ E : List S} (same : Γ = Δ)
    (rename : Renaming Δ E) :
    HEq (fun {s} (i : Var Γ s) => rename (cast (congrArg (Var · s) same) i))
      (fun {s} => rename (s := s)) := by
  cases same
  rfl

/-- The single shift agrees as the input list and output head are transported. -/
private theorem shift_one_heq {S : Type u} {Γ Δ : List S} {s t : S}
    (inputs : Γ = Δ) (output : s = t) :
    HEq (fun {x} (i : Var Γ x) => Var.there (t := s) i)
      (fun {x} (i : Var Δ x) => Var.there (t := t) i) := by
  cases inputs
  cases output
  rfl

/-- The two shifts retain their ordered positions under an arity transport. -/
private theorem shift_two_heq {S : Type u} {Γ Δ : List S} {s t : S}
    (inputs : Γ = Δ) (output : s = t) :
    HEq (fun {x} (i : Var Γ x) => Var.there (t := s) (Var.there (t := s) i))
      (fun {x} (i : Var Δ x) => Var.there (t := t) (Var.there (t := t) i)) := by
  cases inputs
  cases output
  rfl

/-- The head result occupies the same position under an arity transport. -/
private theorem head_position_heq {S : Type u} {Γ Δ : List S} {s t : S}
    (inputs : Γ = Δ) (output : s = t) :
    HEq (Var.here : Var (s :: Γ) s) (Var.here : Var (t :: Δ) t) := by
  cases inputs
  cases output
  rfl

/-- The second result occupies the same position under an arity transport. -/
private theorem next_position_heq {S : Type u} {Γ Δ : List S} {s t : S}
    (inputs : Γ = Δ) (output : s = t) :
    HEq (Var.there Var.here : Var (s :: s :: Γ) s) (Var.there Var.here : Var (t :: t :: Δ) t) := by
  cases inputs
  cases output
  rfl

section

attribute [local irreducible] context arity operation

/-- The chosen graph under one output binder has its original argument and result positions. -/
private theorem selectGraph_shift_one {op : Operation P.signature}
    (keep : Declaration.ofOperation op ∈ U.declarations)
    {selected : Operation (signature U)} (same : operation op keep = selected)
    (guard : Declaration.sorts (op.arity.output :: op.arity.inputs) ⊆ U.declarations) :
    HEq (selectGraph guard op keep (fun i => .there i) .here)
      (Atomic.graph selected (fun i => .there i) .here) := by
  rw [selectGraph_atOperation guard op keep selected same]
  let inputs := operation_selectedInputs same
  let output := operation_selectedOutput same
  apply graph_heq (context_one_output op keep selected (operation_arity_of_eq same) guard) rfl
  · exact (renaming_input_heq inputs (selectRenaming _ guard (fun i => .there i))).trans
      ((selectRenaming_there_heq (operationOutput op keep) (operationInputs op keep)).trans
        (shift_one_heq inputs output).symm)
  · exact (cast_heq _ _).trans ((selectVar_here_heq guard).trans (head_position_heq inputs output).symm)

/-- The first graph in the functionality sequent retains the leading output position. -/
private theorem selectGraph_shift_two_head {op : Operation P.signature}
    (keep : Declaration.ofOperation op ∈ U.declarations)
    {selected : Operation (signature U)} (same : operation op keep = selected)
    (guard : Declaration.sorts (op.arity.output :: op.arity.output :: op.arity.inputs) ⊆ U.declarations) :
    HEq (selectGraph guard op keep (fun i => Var.there (t := op.arity.output) (Var.there i)) .here)
      (Atomic.graph selected (fun i => Var.there (t := selected.arity.output)
        (Var.there (t := selected.arity.output) i)) .here) := by
  rw [selectGraph_atOperation guard op keep selected same]
  let inputs := operation_selectedInputs same
  let output := operation_selectedOutput same
  apply graph_heq (context_two_outputs op keep selected (operation_arity_of_eq same) guard) rfl
  · exact (renaming_input_heq inputs (selectRenaming _ guard (fun i => .there (.there i)))).trans
      ((selectRenaming_twice_heq (operationOutput op keep) (operationOutput op keep) (operationInputs op keep)).trans
        (shift_two_heq inputs output).symm)
  · exact (cast_heq _ _).trans ((selectVar_head_twice_heq guard).trans
      (head_position_heq (congrArg₂ List.cons output inputs) output).symm)

/-- The second graph in the functionality sequent retains the next output position. -/
private theorem selectGraph_shift_two_next {op : Operation P.signature}
    (keep : Declaration.ofOperation op ∈ U.declarations)
    {selected : Operation (signature U)} (same : operation op keep = selected)
    (guard : Declaration.sorts (op.arity.output :: op.arity.output :: op.arity.inputs) ⊆ U.declarations) :
    HEq (selectGraph guard op keep (fun i => Var.there (t := op.arity.output) (Var.there i)) (.there .here))
      (Atomic.graph selected (fun i => Var.there (t := selected.arity.output) (Var.there i)) (.there .here)) := by
  rw [selectGraph_atOperation guard op keep selected same]
  let inputs := operation_selectedInputs same
  let output := operation_selectedOutput same
  apply graph_heq (context_two_outputs op keep selected (operation_arity_of_eq same) guard) rfl
  · exact (renaming_input_heq inputs (selectRenaming _ guard (fun i => .there (.there i)))).trans
      ((selectRenaming_twice_heq (operationOutput op keep) (operationOutput op keep) (operationInputs op keep)).trans
        (shift_two_heq inputs output).symm)
  · exact (cast_heq _ _).trans ((selectVar_there_here_heq guard).trans (next_position_heq inputs output).symm)

/-- A domain atom agrees when its typed positions agree in equal contexts. -/
private theorem domain_atom_heq {S : Signature.{u}} {Γ Δ : List S.SortType} (same : Γ = Δ)
    (p : S.Partial) {ρ : Renaming (S.partialArity p).inputs Γ} {τ : Renaming (S.partialArity p).inputs Δ}
    (args : HEq (fun {s} => ρ (s := s)) (fun {s} => τ (s := s))) :
    HEq (Atomic.domain p ρ) (Atomic.domain p τ) := by
  cases same
  have equal : (fun {s} => ρ (s := s)) = (fun {s} => τ (s := s)) := eq_of_heq args
  rw [equal]

/-- The identity renaming agrees under an equality of input lists. -/
private theorem renaming_id_heq {S : Type u} {Γ Δ : List S} (same : Γ = Δ) :
    HEq (fun {s} (i : Var Γ s) => i) (fun {s} (i : Var Δ s) => i) := by
  cases same
  rfl

/-- The domain test in the existence axiom reads the original input positions. -/
private theorem selectDomain_id_heq (p : P.signature.Partial) (d : Declaration.partialOp p ∈ U.declarations)
    (keep : Declaration.atomicSupport (.domain p (fun i => i)) ⊆ U.declarations) :
    HEq (selectAtomic (.domain p (fun i => i)) keep) (Atomic.domain (sig := signature U) ⟨p, d⟩ (fun i => i)) := by
  rw [selectAtomic_domain_cast p _ keep d]
  let inputs := signature_partialInputs (U := U) ⟨p, d⟩
  apply domain_atom_heq (S := signature U) inputs.symm ⟨p, d⟩
  apply (renaming_input_heq inputs (selectRenaming _ _ (fun i => i))).trans
  exact (heq_of_eq (selectRenaming_id _)).trans (renaming_id_heq inputs.symm)

/-- The domain test under the output binder reads the original shifted input positions. -/
private theorem selectDomain_shift_heq (p : P.signature.Partial) (d : Declaration.partialOp p ∈ U.declarations)
    (keep : Declaration.atomicSupport (.domain p (fun i => Var.there (t := (P.signature.partialArity p).output) i)) ⊆
      U.declarations) :
    HEq (selectAtomic (.domain p (fun i => .there i)) keep)
      (Atomic.domain (sig := signature U) ⟨p, d⟩ (fun i => Var.there (t := ((signature U).partialArity ⟨p, d⟩).output) i)) := by
  rw [selectAtomic_domain_cast p _ keep d]
  let retained := Declaration.ofOperation_partialOp_mem p d
  let same := operation_partialOp p retained
  let inputs := signature_partialInputs (U := U) ⟨p, d⟩
  let output := operation_selectedOutput same
  apply domain_atom_heq (S := signature U) (context_one_output _ retained _ (operation_arity_of_eq same) _) ⟨p, d⟩
  refine (renaming_input_heq inputs (selectRenaming _ _ (fun i => .there i))).trans ?_
  exact (selectRenaming_there_heq (operationOutput (.partialOp p) retained) (operationInputs (.partialOp p) retained)).trans
    (shift_one_heq inputs output).symm

/-- A context cast on an atomic formula preserves its identified atom. -/
private theorem cast_atom_heq {S : Signature.{u}} {Γ Δ E : List S.SortType} (castTo : Γ = Δ)
    (same : Γ = E) {a : Atomic S Γ} {b : Atomic S E} (atoms : HEq a b) :
    HEq (cast (congrArg (Formula S) castTo) (.atom a)) (Formula.atom b) :=
  (cast_heq _ _).trans ((cast_heq (congrArg (Formula S) same) (Formula.atom a)).symm.trans
    (heq_of_eq (cast_atom_of_heq same atoms)))

/-- Two equality atoms agree when their contexts, sorts, and positions agree. -/
private theorem equality_atom_heq {S : Signature.{u}} {Γ Δ : List S.SortType} {s t : S.SortType}
    (contexts : Γ = Δ) (sorts : s = t) {x y : Var Γ s} {x' y' : Var Δ t}
    (left : HEq x x') (right : HEq y y') :
    HEq (Atomic.eq (sig := S) x y) (Atomic.eq (sig := S) x' y') := by
  cases contexts
  cases sorts
  rw [eq_of_heq left, eq_of_heq right]

/-- The equality of the two outputs in functionality preserves both argument positions. -/
private theorem selected_output_equality {op : Operation P.signature}
    (keep : Declaration.ofOperation op ∈ U.declarations) {retained : Operation (signature U)}
    (same : operation op keep = retained)
    (support : Declaration.atomicSupport (Atomic.eq (sig := P.signature)
      (.here : Var (op.arity.output :: op.arity.output :: op.arity.inputs) op.arity.output)
      (.there .here)) ⊆ U.declarations) :
    HEq (selectAtomic (.eq .here (.there .here)) support)
      (Atomic.eq (sig := signature U)
        (.here : Var (retained.arity.output :: retained.arity.output :: retained.arity.inputs) retained.arity.output)
        (.there .here)) := by
  rw [selectAtomic_eq]
  let inputs := operation_selectedInputs same
  let output := operation_selectedOutput same
  apply equality_atom_heq (context_two_outputs op keep retained (operation_arity_of_eq same) _) output.symm
  · exact (selectVar_head_twice_heq _).trans (head_position_heq (congrArg₂ List.cons output inputs) output).symm
  · exact (selectVar_there_here_heq _).trans (next_position_heq inputs output).symm

end

attribute [local irreducible] context arity operation in
/-- A graph axiom remains the same structural axiom of the selected signature. -/
theorem selectRule_toLaw (rule : GraphAxiom P.signature)
    (kept : Declaration.graphRuleName rule ∈ U.declarations) :
    selectLaw rule.toLaw (graphRuleSupport rule kept) = (selectRule rule kept).toLaw := by
  cases rule
  case' functional op =>
    cases op <;>
      simp only [GraphAxiom.toLaw_functional, selectLaw_eq, selectFormula_conj, selectFormula_atom,
        selectAtomic_graph, selectRule, operation_total, operation_partialOp, operation_quantity]
  case' totality f =>
    have named : Declaration.total f ∈ U.declarations := by
      simpa only [Declaration.graphRuleName_totality] using kept
    have inputShape := (signature_totalInputs (U := U) ⟨f, named⟩).symm
    have outputShape := congrArg Subtype.val (operation_selectedOutput
      (operation_total (U := U) f (Declaration.ofOperation_total_mem f named))).symm
    simp only [GraphAxiom.toLaw_totality, GraphAxiom.hasOutput_eq_ex_graph, selectLaw_eq, selectFormula_truth,
      selectFormula_ex_cast, selectFormula_atom, selectAtomic_graph, selectRule]
  case' quantityTotality q =>
    have named : Declaration.quantity q ∈ U.declarations := by
      simpa only [Declaration.graphRuleName_quantityTotality] using kept
    have inputShape := (signature_quantityInputs (U := U) ⟨q, named⟩).symm
    have outputShape := congrArg Subtype.val (operation_selectedOutput
      (operation_quantity (U := U) q (Declaration.ofOperation_quantity_mem q named))).symm
    simp only [GraphAxiom.toLaw_quantityTotality, GraphAxiom.hasOutput_eq_ex_graph, selectLaw_eq,
      selectFormula_truth, selectFormula_ex_cast, selectFormula_atom, selectAtomic_graph, selectRule]
  case' graphImpliesDomain p =>
    simp only [GraphAxiom.toLaw_graphImpliesDomain, selectLaw_eq, selectFormula_atom, selectAtomic_graph,
      selectRule]
  case' domainImpliesGraph p =>
    have named : Declaration.partialOp p ∈ U.declarations := by
      simpa only [Declaration.graphRuleName_domainImpliesGraph] using kept
    have inputShape := (signature_partialInputs (U := U) ⟨p, named⟩).symm
    have outputShape := congrArg Subtype.val (operation_selectedOutput
      (operation_partialOp (U := U) p (Declaration.ofOperation_partialOp_mem p named))).symm
    simp only [GraphAxiom.toLaw_domainImpliesGraph, GraphAxiom.hasOutput_eq_ex_graph, selectLaw_eq,
      selectFormula_atom, selectFormula_ex_cast, selectAtomic_graph, selectRule]
  all_goals congr 4
  all_goals first
    | rfl
    | assumption
    | exact context_two_outputs _ _ _ (operation_arity_of_eq (operation_total _ _)) _
    | exact context_two_outputs _ _ _ (operation_arity_of_eq (operation_partialOp _ _)) _
    | exact context_two_outputs _ _ _ (operation_arity_of_eq (operation_quantity _ _)) _
    | exact context_one_output _ _ _ (operation_arity_of_eq (operation_partialOp _ _)) _
    | exact selectGraph_shift_two_head _ (operation_total _ _) _
    | exact selectGraph_shift_two_head _ (operation_partialOp _ _) _
    | exact selectGraph_shift_two_head _ (operation_quantity _ _) _
    | exact selectGraph_shift_two_next _ (operation_total _ _) _
    | exact selectGraph_shift_two_next _ (operation_partialOp _ _) _
    | exact selectGraph_shift_two_next _ (operation_quantity _ _) _
    | exact selectGraph_shift_one _ (operation_partialOp _ _) _
    | exact selectDomain_id_heq _ _ _
    | exact selectDomain_shift_heq _ _ _
    | exact selected_output_equality _ (operation_total _ _) _
    | exact selected_output_equality _ (operation_partialOp _ _) _
    | exact selected_output_equality _ (operation_quantity _ _) _
    | skip
  case totality.h.e_4.e_4 =>
    let keep := Declaration.ofOperation_total_mem f named
    let same := operation_total (U := U) f keep
    exact cast_atom_heq (context_cons (U := U) _ _ _)
      (context_one_output (.total f) keep _ (operation_arity_of_eq same) _)
      (selectGraph_shift_one keep same _)
  case quantityTotality.h.e_4.e_4 =>
    let keep := Declaration.ofOperation_quantity_mem q named
    let same := operation_quantity (U := U) q keep
    exact cast_atom_heq (context_cons (U := U) _ _ _)
      (context_one_output (.quantity q) keep _ (operation_arity_of_eq same) _)
      (selectGraph_shift_one keep same _)
  case domainImpliesGraph.h.e_4.e_4 =>
    let keep := Declaration.ofOperation_partialOp_mem p named
    let same := operation_partialOp (U := U) p keep
    exact cast_atom_heq (context_cons (U := U) _ _ _)
      (context_one_output (.partialOp p) keep _ (operation_arity_of_eq same) _)
      (selectGraph_shift_one keep same _)

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
      (congrArg (laws U).statement (chosen name named)).trans (laws_statement ⟨source name, named⟩)
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
    have lhs := selectFormula_openHead_cast p x body (derivationOf_input source node keep)
    erw [lhs, selectFormula_ex_cast]
    exact Derivation.existsIntro (T := namedTheory (laws U) target) _ _
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
    let alignment := context_cons s Γ ((Declaration.sorts_subset_formulaSupport _).trans keepInner)
    have transported := Derivation.cast_context alignment inner
    rw [Formula.cast_conj_context alignment, selectFormula_there_cast c keepLeft keepInner,
      selectFormula_there_cast q output (derivationOf_result source child sub)] at transported
    rw [selectFormula_conj, selectFormula_ex_cast]
    exact Derivation.existsElim (T := namedTheory (laws U) target) transported
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
    have lhs := selectFormula_openHead_cast p x body keepInput
    have rhs := selectFormula_openHead_cast p y body out
    erw [lhs, rhs]
    exact Derivation.eqSubst (T := namedTheory (laws U) target) _ _ _

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
