import Formal.SHIGURE.Part1.RingEquations
import Mathlib.Algebra.Ring.Hom.Defs

/-! # Structure-preserving families of maps

Theorem 1.8(2) and the transport clause of (3).

## Implementation notes

The data for a map follows (1.9): a map of each carrier, equality at the
total operation and quantity values, and separate preservation of the
partial domains and their values. Giving only preservation of graph atoms
would encode the equivalent graph presentation but would keep the
individual conditions of (1.9) implicit. The theorem `StructureMap.map_graph`
connects the displayed data to that presentation.
-/

universe u v w

namespace SHIGURE

namespace Assignment

variable {S : Type u} {X : S → Type v} {Y : S → Type w} {Γ Δ : List S} {s : S}

/-- Apply a family of maps to each coordinate of an assignment. -/
def map (f : ∀ s, X s → Y s) (e : Assignment X Γ) : Assignment Y Γ :=
  ⟨fun {s} i => f s (e i)⟩

/-- Coordinatewise action reads the corresponding carrier map. -/
@[simp] theorem map_apply (f : ∀ s, X s → Y s) (e : Assignment X Γ) (i : Var Γ s) :
    e.map f i = f s (e i) :=
  rfl

/-- Coordinatewise action preserves context extension. -/
@[simp] theorem map_cons (f : ∀ s, X s → Y s) (x : X s) (e : Assignment X Γ) :
    (cons x e).map f = cons (f s x) (e.map f) := by
  apply ext
  intro t i
  cases i <;> rfl

/-- Coordinatewise action commutes with selecting variables. -/
@[simp] theorem pull_map (f : ∀ s, X s → Y s) (e : Assignment X Δ) (ρ : Renaming Γ Δ) :
    (e.map f).pull ρ = (e.pull ρ).map f :=
  rfl

/-- Coordinatewise action on the empty tuple yields the empty tuple. -/
@[simp] theorem map_empty (f : ∀ s, X s → Y s) :
    (empty (X := X)).map f = empty :=
  eq_empty _

end Assignment

variable {sig : Signature.{u}}

/-- A family satisfying the structural conditions of Theorem 1.8(2). -/
structure StructureMap (A B : Structure sig) where
  /-- One function per sort. -/
  onSort : ∀ s, A.carrier s → B.carrier s
  /-- Ordinary total operation values commute with the carrier maps. -/
  total_comm (f : sig.Total) (xs : Assignment A.carrier (sig.totalArity f).inputs) :
    onSort _ (A.total f xs) = B.total f (xs.map onSort)
  /-- Relation membership is preserved. -/
  relation_mem (r : sig.Rel) (xs : Assignment A.carrier (sig.relInputs r)) :
    xs ∈ A.relation r → xs.map onSort ∈ B.relation r
  /-- (1.9), first line: the source domain maps into the target domain. -/
  partial_mem (p : sig.Partial) (xs : Assignment A.carrier (sig.partialArity p).inputs) :
    xs ∈ A.partialDomain p → xs.map onSort ∈ B.partialDomain p
  /-- (1.9), second line: partial operation values commute on the source domain. -/
  partial_comm (p : sig.Partial) (xs : A.partialDomain p) :
    onSort _ (A.partialValue p xs) =
      B.partialValue p ⟨xs.val.map onSort, partial_mem p xs.val xs.property⟩
  /-- Marked operation values commute with the carrier maps. -/
  quantity_comm (q : sig.Quantity) (xs : Assignment A.carrier (sig.quantityArity q).inputs) :
    onSort _ (A.quantity q xs) = B.quantity q (xs.map onSort)

namespace StructureMap

variable {A B : Structure sig} {Γ : List sig.SortType} {s : sig.SortType}

/-- Every edge of an interpreted operation graph maps to an edge. -/
theorem map_graph (h : StructureMap A B) (op : Operation sig)
    (xs : Assignment A.carrier op.arity.inputs) (y : A.carrier op.arity.output)
    (hy : A.Graph op xs y) : B.Graph op (xs.map h.onSort) (h.onSort _ y) := by
  cases op with
  | total f =>
    rw [A.graph_total_iff] at hy
    exact (B.graph_total_iff _ _ _).2 ((h.total_comm f xs).symm.trans (congrArg (h.onSort _) hy))
  | quantity q =>
    rw [A.graph_quantity_iff] at hy
    exact (B.graph_quantity_iff _ _ _).2 ((h.quantity_comm q xs).symm.trans (congrArg (h.onSort _) hy))
  | partialOp p =>
    obtain ⟨hx, hvalue⟩ := (A.graph_partial_iff p xs y).1 hy
    exact (B.graph_partial_iff _ _ _).2
      ⟨h.partial_mem p xs hx, (h.partial_comm p ⟨xs, hx⟩).symm.trans (congrArg (h.onSort _) hvalue)⟩

/-- Term evaluation is preserved by a structural map, including the value as in (1.10). -/
theorem evaluates_map (h : StructureMap A B) (t : Term sig Γ s) :
    ∀ (e : Assignment A.carrier Γ) (y : A.carrier s), t.Evaluates A e y →
      t.Evaluates B (e.map h.onSort) (h.onSort s y) := by
  induction t with
  | var i =>
    intro e y hy
    simpa only [Term.evaluates_var_iff, Assignment.map_apply] using
      congrArg (h.onSort _) ((Term.evaluates_var_iff i A e y).1 hy)
  | app op args ih =>
    intro e y hy
    obtain ⟨xs, ha, hg⟩ := (Term.evaluates_app_iff op args A e y).1 hy
    exact (Term.evaluates_app_iff op args B _ _).2
      ⟨xs.map h.onSort, fun i => ih i e (xs i) (ha i), h.map_graph op xs y hg⟩
  | letBind init body hi hb =>
    intro e y hy
    obtain ⟨x, hx, hbody⟩ := (Term.evaluates_let_iff init body A e y).1 hy
    exact (Term.evaluates_let_iff init body B _ _).2
      ⟨h.onSort _ x, hi e x hx, by
        simpa only [Assignment.map_cons] using hb (Assignment.cons x e) y hbody⟩

/-- The domain of a term maps into its domain in the target structure. -/
theorem mem_domain_map (h : StructureMap A B) (t : Term sig Γ s)
    (e : Assignment A.carrier Γ) (he : e ∈ t.domain A) : e.map h.onSort ∈ t.domain B := by
  obtain ⟨x, hx⟩ := he
  exact ⟨h.onSort s x, h.evaluates_map t e x hx⟩

/-- The two defined term values commute with the carrier map, as in (1.10). -/
theorem eval_get_map (h : StructureMap A B) (t : Term sig Γ s)
    (e : Assignment A.carrier Γ) (he : e ∈ t.domain A) :
    h.onSort s ((t.eval A e).get ((t.mem_domain_iff A e).1 he)) =
      (t.eval B (e.map h.onSort)).get
        ((t.mem_domain_iff B _).1 (h.mem_domain_map t e he)) := by
  apply Part.mem_unique
  · rw [Term.mem_eval_iff]
    exact h.evaluates_map t e _ ((t.mem_eval_iff A e _).1 ⟨_, rfl⟩)
  · exact ⟨_, rfl⟩

/-- Structural maps preserve all four types of primitive atoms. -/
theorem atomic_holds_map (h : StructureMap A B) (a : Atomic sig Γ)
    (e : Assignment A.carrier Γ) (ha : a.Holds A e) : a.Holds B (e.map h.onSort) := by
  cases a with
  | eq x y =>
    exact congrArg (h.onSort _) ha
  | rel r vars =>
    rw [Atomic.holds_rel, Assignment.pull_map]
    exact h.relation_mem r _ ((Atomic.holds_rel _ _ _ _).1 ha)
  | domain p vars =>
    rw [Atomic.holds_domain, Assignment.pull_map]
    exact h.partial_mem p _ ((Atomic.holds_domain _ _ _ _).1 ha)
  | graph op vars y =>
    rw [Atomic.holds_graph, Assignment.pull_map, Assignment.map_apply]
    exact h.map_graph op _ _ ((Atomic.holds_graph _ _ _ _ _).1 ha)

/-- Positive formula truth is preserved by arbitrary structure-preserving maps. -/
theorem holds_map (h : StructureMap A B) (p : Formula sig Γ) :
    ∀ (e : Assignment A.carrier Γ), p.Holds A e → p.Holds B (e.map h.onSort) := by
  induction p with
  | atom a =>
    exact fun e ha => (Formula.holds_atom _ _ _).2
      (h.atomic_holds_map a e ((Formula.holds_atom _ _ _).1 ha))
  | truth => exact fun _ ht => ht
  | falsehood => exact fun _ hf => hf.elim
  | conj p q hp hq =>
    intro e he
    obtain ⟨hl, hr⟩ := (Formula.holds_conj _ _ _ _).1 he
    exact (Formula.holds_conj _ _ _ _).2 ⟨hp e hl, hq e hr⟩
  | disj p q hp hq =>
    intro e he
    exact (Formula.holds_disj _ _ _ _).2
      (((Formula.holds_disj _ _ _ _).1 he).imp (hp e) (hq e))
  | ex p ih =>
    intro e he
    obtain ⟨x, hx⟩ := (Formula.holds_ex _ _ _).1 he
    exact (Formula.holds_ex _ _ _).2 ⟨h.onSort _ x, by
      simpa only [Assignment.map_cons] using ih (Assignment.cons x e) hx⟩

/-- Theorem 1.8(2): the image of the Law input set is contained in the target input set. -/
theorem inputSet_image_subset (h : StructureMap A B) (law : Law sig) :
    (fun e => e.map h.onSort) '' law.inputSet A ⊆ law.inputSet B := by
  rintro _ ⟨e, he, rfl⟩
  exact (law.mem_inputSet_iff B _).2 (h.holds_map law.input e ((law.mem_inputSet_iff A e).1 he))

/-- Map a tagged evaluation fact while retaining its declared symbol and source positions. -/
def mapAtom (h : StructureMap A B) : EvaluationAtom A → EvaluationAtom B
  | .state s x => .state s (h.onSort s x)
  | .total f e x he =>
    .total f (e.map h.onSort) (h.onSort _ x) ((h.total_comm f e).symm.trans (congrArg _ he))
  | .relation r e he => .relation r (e.map h.onSort) (h.relation_mem r e he)
  | .partialDomain p e he => .partialDomain p (e.map h.onSort) (h.partial_mem p e he)
  | .partialGraph p e x he =>
    .partialGraph p ⟨e.val.map h.onSort, h.partial_mem p e.val e.property⟩
      (h.onSort _ x) ((h.partial_comm p e).symm.trans (congrArg _ he))
  | .quantity q e x he =>
    .quantity q (e.map h.onSort) (h.onSort _ x) ((h.quantity_comm q e).symm.trans (congrArg _ he))

end StructureMap

namespace TypedTotal

variable {A B : Structure sig} {profile : Arity sig.SortType}

/-- A structural map commutes with a selected ordinary or marked total symbol. -/
theorem value_map (op : TypedTotal sig profile) (h : StructureMap A B)
    (e : Assignment A.carrier profile.inputs) :
    h.onSort profile.output (op.value A e) = op.value B (e.map h.onSort) := by
  obtain ⟨symbol, same⟩ := op
  subst profile
  cases symbol with
  | ordinary f => exact h.total_comm f e
  | quantity q => exact h.quantity_comm q e

end TypedTotal

namespace RingVocabulary

variable {A B : Structure sig} {s : sig.SortType}

/-- Structural maps restrict to mathlib ring homomorphisms for the declared value rings. -/
def ringHom (ring : RingVocabulary sig s) (h : StructureMap A B)
    (sourceLaws : ∀ name, (ring.law name).Holds A)
    (targetLaws : ∀ name, (ring.law name).Holds B) :
    letI := ring.commRing A sourceLaws
    letI := ring.commRing B targetLaws
    A.carrier s →+* B.carrier s := by
  letI := ring.commRing A sourceLaws
  letI := ring.commRing B targetLaws
  refine { toFun := h.onSort s, map_zero' := ?zero, map_one' := ?one, map_add' := ?add, map_mul' := ?mul }
  case zero => simpa only [Assignment.map_empty] using ring.zero.value_map h Assignment.empty
  case one => simpa only [Assignment.map_empty] using ring.one.value_map h Assignment.empty
  case add =>
    intro x y
    simpa only [Assignment.map_cons, Assignment.map_empty] using
      ring.add.value_map h (Assignment.cons x (Assignment.cons y Assignment.empty))
  case mul =>
    intro x y
    simpa only [Assignment.map_cons, Assignment.map_empty] using
      ring.mul.value_map h (Assignment.cons x (Assignment.cons y Assignment.empty))

/-- The ring homomorphism acts by the original carrier map. -/
theorem ringHom_apply (ring : RingVocabulary sig s) (h : StructureMap A B)
    (sourceLaws : ∀ name, (ring.law name).Holds A)
    (targetLaws : ∀ name, (ring.law name).Holds B) (x : A.carrier s) :
    letI := ring.commRing A sourceLaws
    letI := ring.commRing B targetLaws
    ring.ringHom h sourceLaws targetLaws x = h.onSort s x :=
  rfl

end RingVocabulary

namespace OrderedEquation

variable {A B : Structure sig}

/-- Joint inputs map to joint inputs because both evaluability and the antecedent are preserved. -/
def mapInput (eqn : OrderedEquation sig) (h : StructureMap A B) (e : eqn.jointInputs A) :
    eqn.jointInputs B :=
  ⟨e.val.map h.onSort, h.inputSet_image_subset eqn.toLaw ⟨e.val, e.property.1, rfl⟩,
    h.mem_domain_map eqn.left e.val e.property.2.1, h.mem_domain_map eqn.right e.val e.property.2.2⟩

/-- Theorem 1.8(3): the image of the joint locus is contained in the target joint locus. -/
theorem jointInputs_image_subset (eqn : OrderedEquation sig) (h : StructureMap A B) :
    (fun e => e.map h.onSort) '' eqn.jointInputs A ⊆ eqn.jointInputs B := by
  rintro _ ⟨e, he, rfl⟩
  exact (eqn.mapInput h ⟨e, he⟩).property

/-- Residual transport (1.11) through the ring homomorphism on the value sort. -/
theorem residual_map (eqn : OrderedEquation sig) (h : StructureMap A B)
    [CommRing (A.carrier eqn.result)] [CommRing (B.carrier eqn.result)]
    (f : A.carrier eqn.result →+* B.carrier eqn.result)
    (onValue : ∀ x, f x = h.onSort eqn.result x) (e : eqn.jointInputs A) :
    h.onSort eqn.result (eqn.residual A e) = eqn.residual B (eqn.mapInput h e) := by
  have hl : f (eqn.leftValue A e) = eqn.leftValue B (eqn.mapInput h e) := by
    apply Part.mem_unique _ (eqn.leftValue_mem B (eqn.mapInput h e))
    apply (Term.mem_eval_iff _ _ _ _).2
    rw [onValue]
    exact h.evaluates_map eqn.left e.val _ ((Term.mem_eval_iff _ _ _ _).1 (eqn.leftValue_mem A e))
  have hr : f (eqn.rightValue A e) = eqn.rightValue B (eqn.mapInput h e) := by
    apply Part.mem_unique _ (eqn.rightValue_mem B (eqn.mapInput h e))
    apply (Term.mem_eval_iff _ _ _ _).2
    rw [onValue]
    exact h.evaluates_map eqn.right e.val _ ((Term.mem_eval_iff _ _ _ _).1 (eqn.rightValue_mem A e))
  rw [← onValue, eqn.residual_eq_sub A, eqn.residual_eq_sub B, map_sub, hl, hr]

end OrderedEquation

namespace RingEquation

variable {sig : Signature.{u}} {A B : Structure sig}

@[inherit_doc OrderedEquation.mapInput]
abbrev mapInput (eqn : RingEquation sig) (h : StructureMap A B) (e : eqn.jointInputs A) :=
  eqn.toOrderedEquation.mapInput h e

@[inherit_doc OrderedEquation.jointInputs_image_subset]
theorem jointInputs_image_subset (eqn : RingEquation sig) (h : StructureMap A B) :
    (fun e => e.map h.onSort) '' eqn.jointInputs A ⊆ eqn.jointInputs B :=
  eqn.toOrderedEquation.jointInputs_image_subset h

/-- Naming and interpreting the ring operations supplies the value-sort homomorphism. -/
theorem residual_map (eqn : RingEquation sig) (h : StructureMap A B)
    (sourceLaws : ∀ name, (eqn.ring.law name).Holds A)
    (targetLaws : ∀ name, (eqn.ring.law name).Holds B) (e : eqn.jointInputs A) :
    h.onSort eqn.result (eqn.residual A sourceLaws e) =
      eqn.residual B targetLaws (eqn.mapInput h e) := by
  letI := eqn.ring.commRing A sourceLaws
  letI := eqn.ring.commRing B targetLaws
  exact eqn.toOrderedEquation.residual_map h (eqn.ring.ringHom h sourceLaws targetLaws) (fun _ => rfl) e

end RingEquation

end SHIGURE
