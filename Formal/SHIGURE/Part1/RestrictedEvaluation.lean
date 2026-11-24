import Formal.SHIGURE.Part1.DeclarationContexts
import Formal.SHIGURE.Part1.StructureMaps

/-! # Evaluation in a retained declaration context

The reading comparison evaluates supported formulas from the relation,
domain, and graph data retained by a closed context.

## Implementation notes

The original sort names are used to index assignments. Existence binds a
retained sort and primitive lookup takes a proof that its declaration is
retained. A restricted evaluator keeps one entry for each retained
primitive. A filter applied after evaluating in a full structure would
still use that full structure for lookups. Here the restricted evaluation
has its own recursion and only reads the retained entries.
-/

universe u

namespace SHIGURE

namespace Declaration

variable {P : PrimitivePresentation.{u}} {Γ Δ : List P.signature.SortType}

/-- Renaming a formula's free positions preserves its referenced declarations. -/
theorem formula_rename (p : Formula P.signature Γ) :
    ∀ {Δ : List P.signature.SortType} (ρ : Renaming Γ Δ),
      formula (P := P) (p.rename ρ) = formula p := by
  induction p with
  | atom a =>
    intro Δ ρ
    rw [Formula.rename_atom, formula_atom, formula_atom]
    cases a <;> simp only [Atomic.rename_eq, Atomic.rename_rel, Atomic.rename_domain, Atomic.rename_graph,
      atomic_eq, atomic_rel, atomic_domain, atomic_graph]
  | truth => intro Δ ρ; simp only [Formula.rename_truth, formula_truth]
  | falsehood => intro Δ ρ; simp only [Formula.rename_falsehood, formula_falsehood]
  | conj p q hp hq => intro Δ ρ; simp only [Formula.rename_conj, formula_conj, hp, hq]
  | disj p q hp hq => intro Δ ρ; simp only [Formula.rename_disj, formula_disj, hp, hq]
  | ex p hp => intro Δ ρ; simp only [Formula.rename_ex, formula_ex, hp]

end Declaration

/-- The primitive evaluation data at the retained declarations of a context. -/
structure RestrictedEvaluation {P : PrimitivePresentation.{u}}
    (U : DeclarationContext P) (X : P.signature.SortType → Type u) where
  /-- Read a retained relation on its input tuple. -/
  relation (r : P.signature.Rel) : Declaration.relation r ∈ U.declarations →
    Assignment X (P.signature.relInputs r) → Prop
  /-- Read the retained domain of a partial operation. -/
  domain (p : P.signature.Partial) : Declaration.partialOp p ∈ U.declarations →
    Assignment X (P.signature.partialArity p).inputs → Prop
  /-- Read the graph of a retained operation. -/
  graph (op : Operation P.signature) : Declaration.ofOperation op ∈ U.declarations →
    Assignment X op.arity.inputs → X op.arity.output → Prop

namespace RestrictedEvaluation

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
  {X : P.signature.SortType → Type u} {Γ : List P.signature.SortType}

/-- Restrict each primitive interpretation by indexing it with its retained declaration. -/
def restrict (U : DeclarationContext P) (A : Structure P.signature) :
    RestrictedEvaluation U A.carrier where
  relation r _ xs := xs ∈ A.relation r
  domain p _ xs := xs ∈ A.partialDomain p
  graph op _ xs y := A.Graph op xs y

/-- An atomic fact reads only its own retained declaration and the supplied values. -/
def atomic (R : RestrictedEvaluation U X) (e : Assignment X Γ) :
    (a : Atomic P.signature Γ) → Declaration.atomicSupport a ⊆ U.declarations → Prop
  | .eq x y, _ => e x = e y
  | .rel r vars, h => R.relation r (h (Declaration.relation_mem_atomicSupport r vars)) (e.pull vars)
  | .domain p vars, h => R.domain p (h (Declaration.domain_mem_atomicSupport p vars)) (e.pull vars)
  | .graph op vars y, h => R.graph op (h (Declaration.graph_mem_atomicSupport op vars y)) (e.pull vars) (e y)

/-- Evaluate equality at the two supported variable positions. -/
theorem atomic_eq_iff (R : RestrictedEvaluation U X) (e : Assignment X Γ)
    {s : P.signature.SortType} (x y : Var Γ s)
    (keep : Declaration.atomicSupport (Atomic.eq (sig := P.signature) x y) ⊆ U.declarations) :
    R.atomic e (.eq x y) keep ↔ e x = e y :=
  Iff.rfl

/-- Evaluate a supported relation at the tuple indexed by its arguments. -/
theorem atomic_rel_iff (R : RestrictedEvaluation U X) (e : Assignment X Γ)
    (r : P.signature.Rel) (vars : Renaming (P.signature.relInputs r) Γ)
    (keep : Declaration.atomicSupport (.rel r vars) ⊆ U.declarations) :
    R.atomic e (.rel r vars) keep ↔ R.relation r (keep (Declaration.relation_mem_atomicSupport r vars)) (e.pull vars) :=
  Iff.rfl

/-- A supported partial-operation domain is read on its argument tuple. -/
theorem atomic_domain_iff (R : RestrictedEvaluation U X) (e : Assignment X Γ)
    (p : P.signature.Partial) (vars : Renaming (P.signature.partialArity p).inputs Γ)
    (keep : Declaration.atomicSupport (.domain p vars) ⊆ U.declarations) :
    R.atomic e (.domain p vars) keep ↔ R.domain p (keep (Declaration.domain_mem_atomicSupport p vars)) (e.pull vars) :=
  Iff.rfl

/-- Evaluate a supported graph at its argument tuple and output position. -/
theorem atomic_graph_iff (R : RestrictedEvaluation U X) (e : Assignment X Γ)
    (op : Operation P.signature) (vars : Renaming op.arity.inputs Γ) (y : Var Γ op.arity.output)
    (keep : Declaration.atomicSupport (.graph op vars y) ⊆ U.declarations) :
    R.atomic e (.graph op vars y) keep ↔
      R.graph op (keep (Declaration.graph_mem_atomicSupport op vars y)) (e.pull vars) (e y) :=
  Iff.rfl

/-- Evaluate a positive formula using only retained primitives and bound sorts. -/
def holds (R : RestrictedEvaluation U X) :
    {Γ : List P.signature.SortType} → (p : Formula P.signature Γ) →
    Declaration.formulaSupport p ⊆ U.declarations → Assignment X Γ → Prop
  | _, .atom a, supported, e => R.atomic e a ((Declaration.formulaSupport_atom a).ge.trans supported)
  | _, .truth, _, _ => True
  | _, .falsehood, _, _ => False
  | _, .conj p q, supported, e =>
    R.holds p ((Declaration.binarySupport_left (Declaration.formula_conj p q)).trans supported) e ∧
    R.holds q ((Declaration.binarySupport_right (Declaration.formula_conj p q)).trans supported) e
  | _, .disj p q, supported, e =>
    R.holds p ((Declaration.binarySupport_left (Declaration.formula_disj p q)).trans supported) e ∨
    R.holds q ((Declaration.binarySupport_right (Declaration.formula_disj p q)).trans supported) e
  | _, @Formula.ex _ _ s p, supported, e =>
    ∃ value : X s, R.holds p ((Declaration.formulaSupport_ex_body p).trans supported)
      (Assignment.cons value e)

/-- A supported atomic formula delegates to the evaluator for its atom. -/
theorem holds_atom_iff (R : RestrictedEvaluation U X) (a : Atomic P.signature Γ)
    (keep : Declaration.formulaSupport (.atom a) ⊆ U.declarations) (e : Assignment X Γ) :
    R.holds (.atom a) keep e ↔ R.atomic e a ((Declaration.formulaSupport_atom a).ge.trans keep) :=
  Iff.rfl

/-- Truth has no primitive evaluation requirements in a restricted context. -/
theorem holds_truth_iff (R : RestrictedEvaluation U X)
    (keep : Declaration.formulaSupport (Formula.truth (sig := P.signature) (Γ := Γ)) ⊆ U.declarations)
    (e : Assignment X Γ) :
    R.holds .truth keep e ↔ True :=
  Iff.rfl

/-- Falsehood cannot be satisfied by a restricted assignment. -/
theorem holds_falsehood_iff (R : RestrictedEvaluation U X)
    (keep : Declaration.formulaSupport (Formula.falsehood (sig := P.signature) (Γ := Γ)) ⊆ U.declarations)
    (e : Assignment X Γ) :
    R.holds .falsehood keep e ↔ False :=
  Iff.rfl

/-- Conjunction in a restricted evaluator tests both supported formulas. -/
theorem holds_conj_iff (R : RestrictedEvaluation U X) (p q : Formula P.signature Γ)
    (keep : Declaration.formulaSupport (p.conj q) ⊆ U.declarations) (e : Assignment X Γ) :
    R.holds (p.conj q) keep e ↔
      R.holds p ((Declaration.binarySupport_left (Declaration.formula_conj p q)).trans keep) e ∧
      R.holds q ((Declaration.binarySupport_right (Declaration.formula_conj p q)).trans keep) e :=
  Iff.rfl

/-- Disjunction in a restricted evaluator tests either supported formula. -/
theorem holds_disj_iff (R : RestrictedEvaluation U X) (p q : Formula P.signature Γ)
    (keep : Declaration.formulaSupport (p.disj q) ⊆ U.declarations) (e : Assignment X Γ) :
    R.holds (p.disj q) keep e ↔
      R.holds p ((Declaration.binarySupport_left (Declaration.formula_disj p q)).trans keep) e ∨
      R.holds q ((Declaration.binarySupport_right (Declaration.formula_disj p q)).trans keep) e :=
  Iff.rfl

/-- An existential in a restricted evaluator ranges over the full carrier of
its retained bound sort, including the case when there are no values. -/
theorem holds_ex_iff (R : RestrictedEvaluation U X) {s : P.signature.SortType}
    (p : Formula P.signature (s :: Γ)) (keep : Declaration.formulaSupport p.ex ⊆ U.declarations)
    (e : Assignment X Γ) :
    R.holds p.ex keep e ↔
      ∃ value : X s, R.holds p
        ((Declaration.formulaSupport_ex_body p).trans keep)
        (Assignment.cons value e) :=
  Iff.rfl

/-- The two evaluations use the same interpreted entry for a retained primitive. -/
theorem restrict_atomic_iff (U : DeclarationContext P) (A : Structure P.signature)
    (a : Atomic P.signature Γ) (supported : Declaration.atomicSupport a ⊆ U.declarations)
    (e : Assignment A.carrier Γ) :
    (restrict U A).atomic e a supported ↔ a.Holds A e := by
  cases a with
  | eq x y => rw [atomic_eq_iff, Atomic.holds_eq]
  | rel r vars => rw [atomic_rel_iff, Atomic.holds_rel]; rfl
  | domain p vars => rw [atomic_domain_iff, Atomic.holds_domain]; rfl
  | graph op vars y => rw [atomic_graph_iff, Atomic.holds_graph]; rfl

/-- Restricting primitive data and then evaluating a supported formula agrees with evaluating it
before restricting. The induction uses the restricted evaluator's own clauses. -/
theorem restrict_holds_iff (U : DeclarationContext P) (A : Structure P.signature)
    (p : Formula P.signature Γ) :
    ∀ (supported : Declaration.formulaSupport p ⊆ U.declarations) (e : Assignment A.carrier Γ),
      (restrict U A).holds p supported e ↔ p.Holds A e := by
  induction p with
  | atom a =>
    intro support e
    rw [holds_atom_iff, Formula.holds_atom]
    exact restrict_atomic_iff U A a ((Declaration.formulaSupport_atom a).ge.trans support) e
  | truth =>
    intro support e
    simp only [holds_truth_iff, Formula.holds_truth_iff]
  | falsehood =>
    intro support e
    simp only [holds_falsehood_iff, Formula.holds_falsehood_iff]
  | conj p q hp hq =>
    intro support e
    rw [holds_conj_iff, Formula.holds_conj, hp, hq]
  | disj p q hp hq =>
    intro support e
    rw [holds_disj_iff, Formula.holds_disj, hp, hq]
  | ex p hp =>
    intro support e
    rw [holds_ex_iff, Formula.holds_ex]
    exact exists_congr fun x => hp _ (Assignment.cons x e)

end RestrictedEvaluation

/-- Structures over selected declarations have operations only at retained names.
The carrier family is indexed by the original sort names so typed expressions can be reused. -/
structure RestrictedStructure {P : PrimitivePresentation.{u}} (U : DeclarationContext P) where
  /-- The carriers read at the retained sort names. -/
  carrier : P.signature.SortType → Type u
  /-- The interpretation of each retained total operation. -/
  total (f : P.signature.Total) : Declaration.total f ∈ U.declarations →
    Assignment carrier (P.signature.totalArity f).inputs → carrier (P.signature.totalArity f).output
  /-- The interpretation of each retained relation. -/
  relation (r : P.signature.Rel) : Declaration.relation r ∈ U.declarations →
    Set (Assignment carrier (P.signature.relInputs r))
  /-- The defined inputs at each retained partial operation. -/
  partialDomain (p : P.signature.Partial) : Declaration.partialOp p ∈ U.declarations →
    Set (Assignment carrier (P.signature.partialArity p).inputs)
  /-- The value of a retained partial operation on a defined input. -/
  partialValue (p : P.signature.Partial) (kept : Declaration.partialOp p ∈ U.declarations) :
    partialDomain p kept → carrier (P.signature.partialArity p).output
  /-- The interpretation of each retained marked operation. -/
  quantity (q : P.signature.Quantity) : Declaration.quantity q ∈ U.declarations →
    Assignment carrier (P.signature.quantityArity q).inputs → carrier (P.signature.quantityArity q).output

namespace RestrictedStructure

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- A schematic structure gives every forgotten name the same inert carrier.
This presentation uses the original sort indices so typed terms remain reusable. -/
def HasOnlyRetainedSorts (A : RestrictedStructure U) : Prop :=
  ∀ s, Declaration.sort s ∉ U.declarations → A.carrier s = PUnit

/-- A context that keeps all sort names has no carriers to erase. -/
theorem hasOnlyRetainedSorts_of_all (A : RestrictedStructure U)
    (kept : ∀ s, Declaration.sort s ∈ U.declarations) : A.HasOnlyRetainedSorts :=
  fun s omitted => (omitted (kept s)).elim

/-- A point map is defined on the retained sort carriers. -/
abbrev PointMap (A B : RestrictedStructure U) :=
  ∀ s, Declaration.sort s ∈ U.declarations → A.carrier s → B.carrier s

/-- Transport a tuple by using the point map at its supported positions. -/
def mapAssignment {A B : RestrictedStructure U} (f : PointMap A B)
    {Γ : List P.signature.SortType} (supported : Declaration.sorts (P := P) Γ ⊆ U.declarations)
    (e : Assignment A.carrier Γ) : Assignment B.carrier Γ :=
  ⟨fun i => f _ (supported ⟨_, i.sort_mem, rfl⟩) (e i)⟩

/-- Forget the operations outside the selected declarations. -/
def restrict (U : DeclarationContext P) (A : Structure P.signature) : RestrictedStructure U where
  carrier := A.carrier
  total f _ := A.total f
  relation r _ := A.relation r
  partialDomain p _ := A.partialDomain p
  partialValue p _ := A.partialValue p
  quantity q _ := A.quantity q

/-- Restrict the primitive interpretations of a realized structure to a smaller context. -/
def restrictWithin {V : DeclarationContext P} (A : RestrictedStructure U)
    (inside : V.declarations ⊆ U.declarations) : RestrictedStructure V where
  carrier := A.carrier
  total f kept := A.total f (inside kept)
  relation r kept := A.relation r (inside kept)
  partialDomain p kept := A.partialDomain p (inside kept)
  partialValue p kept := A.partialValue p (inside kept)
  quantity q kept := A.quantity q (inside kept)

/-- Read the graph of a retained total or partial operation on its inputs. -/
def graph (A : RestrictedStructure U) (op : Operation P.signature)
    (kept : Declaration.ofOperation op ∈ U.declarations) (e : Assignment A.carrier op.arity.inputs)
    (y : A.carrier op.arity.output) : Prop :=
  match op with
  | .total f => A.total f kept e = y
  | .partialOp p => ∃ h : e ∈ A.partialDomain p kept, A.partialValue p kept ⟨e, h⟩ = y
  | .quantity q => A.quantity q kept e = y

/-- The evaluator built from this restricted structure uses its retained operations. -/
def evaluation (A : RestrictedStructure U) : RestrictedEvaluation U A.carrier where
  relation r kept e := e ∈ A.relation r kept
  domain p kept e := e ∈ A.partialDomain p kept
  graph := A.graph

/-- Set-valued satisfaction of a Law whose whole support is retained. -/
def satisfies (A : RestrictedStructure U) (law : Law P.signature)
    (supported : Declaration.lawBody (P := P) law ⊆ U.declarations) : Prop :=
  ∀ e : Assignment A.carrier law.context,
    A.evaluation.holds law.input ((Declaration.formulaSupport_input_subset_lawBody law).trans supported) e →
    A.evaluation.holds law.conclusion ((Declaration.formulaSupport_conclusion_subset_lawBody law).trans supported) e

/-- A point map transports every primitive fact supported on the retained declarations. -/
def Preserves (A B : RestrictedStructure U) (f : PointMap A B) : Prop :=
  ∀ {Γ} (a : Atomic P.signature Γ) (supported : Declaration.atomicSupport a ⊆ U.declarations)
    (e : Assignment A.carrier Γ),
    A.evaluation.atomic e a supported →
      B.evaluation.atomic (mapAssignment f ((Declaration.sorts_subset_atomicSupport a).trans supported) e) a supported

end RestrictedStructure

/-- The retained carriers and the truth of their supported primitive facts agree. -/
structure RestrictedStructure.Agrees {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    (A B : RestrictedStructure U) : Prop where
  /-- Identify the carriers of the retained sorts. -/
  carrier_eq (s : P.signature.SortType) (kept : Declaration.sort s ∈ U.declarations) :
    A.carrier s = B.carrier s
  /-- The carrier identifications preserve the retained facts. -/
  preserves : A.Preserves B (fun s kept x => carrier_eq s kept ▸ x)
  /-- The inverse identifications preserve the retained facts. -/
  reflects : B.Preserves A (fun s kept x => (carrier_eq s kept).symm ▸ x)

/-- A restricted structure agrees with itself. -/
theorem RestrictedStructure.Agrees.refl {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    (A : RestrictedStructure U) : A.Agrees A where
  carrier_eq _ _ := rfl
  preserves := by
    intro Γ atom supported assignment held
    exact held
  reflects := by
    intro Γ atom supported assignment held
    exact held


end SHIGURE
