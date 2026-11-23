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
  | atom a => intro Δ ρ; cases a <;> rfl
  | truth => intros; rfl
  | falsehood => intros; rfl
  | conj p q hp hq => intro Δ ρ; simp only [Formula.rename_conj, formula, hp, hq]
  | disj p q hp hq => intro Δ ρ; simp only [Formula.rename_disj, formula, hp, hq]
  | ex p hp => intro Δ ρ; simp only [Formula.rename_ex, formula, hp]

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
  | .rel r vars, h => R.relation r (h (Or.inr (Set.mem_singleton _))) (e.pull vars)
  | .domain p vars, h => R.domain p (h (Or.inr (Set.mem_singleton _))) (e.pull vars)
  | .graph op vars y, h => R.graph op (h (Or.inr (Set.mem_singleton _))) (e.pull vars) (e y)

/-- Evaluate a positive formula using only retained primitives and bound sorts. -/
def holds (R : RestrictedEvaluation U X) :
    {Γ : List P.signature.SortType} → (p : Formula P.signature Γ) →
    Declaration.formulaSupport p ⊆ U.declarations → Assignment X Γ → Prop
  | _, .atom a, supported, e => R.atomic e a supported
  | _, .truth, _, _ => True
  | _, .falsehood, _, _ => False
  | _, .conj p q, supported, e =>
    R.holds p (fun _ h => h.elim (fun h => supported (Or.inl h))
      (fun h => supported (Or.inr (Or.inl h)))) e ∧
    R.holds q (fun _ h => h.elim (fun h => supported (Or.inl h))
      (fun h => supported (Or.inr (Or.inr h)))) e
  | _, .disj p q, supported, e =>
    R.holds p (fun _ h => h.elim (fun h => supported (Or.inl h))
      (fun h => supported (Or.inr (Or.inl h)))) e ∨
    R.holds q (fun _ h => h.elim (fun h => supported (Or.inl h))
      (fun h => supported (Or.inr (Or.inr h)))) e
  | _, @Formula.ex _ _ s p, supported, e =>
    let sorts := Declaration.sorts_cons_subset (s := s)
      (supported (Or.inr (Or.inl (Set.mem_singleton _)))) (fun _ h => supported (Or.inl h))
    ∃ value : X s, R.holds p
      (fun _ h => h.elim (fun h => sorts h) (fun h => supported (Or.inr (Or.inr h))))
      (Assignment.cons value e)

/-- The two evaluations use the same interpreted entry for a retained primitive. -/
theorem restrict_atomic_iff (U : DeclarationContext P) (A : Structure P.signature)
    (a : Atomic P.signature Γ) (supported : Declaration.atomicSupport a ⊆ U.declarations)
    (e : Assignment A.carrier Γ) :
    (restrict U A).atomic e a supported ↔ a.Holds A e := by
  cases a <;> rfl

/-- Restricting primitive data and then evaluating a supported formula agrees with evaluating it
before restricting. The induction uses the restricted evaluator's own clauses. -/
theorem restrict_holds_iff (U : DeclarationContext P) (A : Structure P.signature)
    (p : Formula P.signature Γ) :
    ∀ (supported : Declaration.formulaSupport p ⊆ U.declarations) (e : Assignment A.carrier Γ),
      (restrict U A).holds p supported e ↔ p.Holds A e := by
  induction p with
  | atom a => exact fun support e => restrict_atomic_iff U A a support e
  | truth => intros; rfl
  | falsehood => intros; rfl
  | conj p q hp hq =>
    intro support e
    rw [holds, Formula.holds_conj, hp, hq]
  | disj p q hp hq =>
    intro support e
    rw [holds, Formula.holds_disj, hp, hq]
  | ex p hp =>
    intro support e
    rw [holds, Formula.holds_ex]
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
    A.evaluation.holds law.input
      (fun _ h => h.elim (fun h => supported (Or.inl (Or.inl h)))
        (fun h => supported (Or.inl (Or.inr h)))) e →
    A.evaluation.holds law.conclusion
      (fun _ h => h.elim (fun h => supported (Or.inl (Or.inl h)))
        (fun h => supported (Or.inr h))) e

/-- A point map transports every primitive fact supported on the retained declarations. -/
def Preserves (A B : RestrictedStructure U) (f : PointMap A B) : Prop :=
  ∀ {Γ} (a : Atomic P.signature Γ) (supported : Declaration.atomicSupport a ⊆ U.declarations)
    (e : Assignment A.carrier Γ),
    A.evaluation.atomic e a supported →
      B.evaluation.atomic (mapAssignment f (fun _ h => supported (Or.inl h)) e) a supported

end RestrictedStructure

end SHIGURE
