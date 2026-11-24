import Formal.SHIGURE.Part1.SyntacticComparison
import Mathlib.CategoryTheory.Equivalence

/-! # Natural isomorphisms from syntactic inverse terms

Corollary 2.4a(b) is proved by evaluating the given unary terms in each
model. Soundness supplies totality, inverse component functions, and
preservation and reflection of all primitive facts. Theorem 1.8 makes
these components natural in the model arrows.

## Implementation notes

The inverse structure arrow is built from bijective components and
reflection by the structure-category theorem. The proof that its
components evaluate the supplied beta terms identifies the resulting
inverse without presenting an isomorphism as extra input.
-/

universe u

namespace SHIGURE.Interpretation.SyntacticComparison

open CategoryTheory

variable {H : Theory.{u}} {c : Interpretation H H} (d : SyntacticComparison c)

/-- Evaluate the forward comparison term, using the given totality derivation and model soundness. -/
noncomputable def alphaValue (A : Model H) (s : H.signature.SortType) (x : A.obj.carrier s) :
    A.obj.carrier (c.onSort s) :=
  definedValue A.obj (d.alpha s) (Assignment.cons x Assignment.empty)
    ((d.alpha_total s).sound A.obj A.property _ True.intro)

/-- Evaluate the inverse comparison term at a value of the translated sort. -/
noncomputable def betaValue (A : Model H) (s : H.signature.SortType)
    (y : A.obj.carrier (c.onSort s)) : A.obj.carrier s :=
  definedValue A.obj (d.beta s) (Assignment.cons y Assignment.empty)
    ((d.beta_total s).sound A.obj A.property _ True.intro)

/-- The selected forward value is an evaluation of the given unary term. -/
theorem alpha_evaluates (A : Model H) (s : H.signature.SortType) (x : A.obj.carrier s) :
    (d.alpha s).Evaluates A.obj (Assignment.cons x Assignment.empty) (d.alphaValue A s x) :=
  evaluates_definedValue _ _ _ _

/-- The selected inverse value is an evaluation of the given unary term. -/
theorem beta_evaluates (A : Model H) (s : H.signature.SortType) (y : A.obj.carrier (c.onSort s)) :
    (d.beta s).Evaluates A.obj (Assignment.cons y Assignment.empty) (d.betaValue A s y) :=
  evaluates_definedValue _ _ _ _

/-- Soundness of the first inverse sequent gives a left inverse on each original carrier. -/
theorem beta_alpha_value (A : Model H) (s : H.signature.SortType) (x : A.obj.carrier s) :
    d.betaValue A s (d.alphaValue A s x) = x := by
  let xs : Assignment A.obj.carrier [s] := Assignment.cons x Assignment.empty
  have first := d.alpha_evaluates A s x
  have evaluated := (Term.evaluates_applyUnary_iff (d.beta s) (d.alpha s) A.obj xs _ first _).2
    (d.beta_evaluates A s (d.alphaValue A s x))
  have original := (Term.evaluates_var_iff (sig := H.signature) Var.here A.obj xs x).2 rfl
  exact Formula.values_eq_of_holds_termEq ((d.beta_alpha s).sound A.obj A.property xs True.intro)
    evaluated original

/-- Soundness of the second inverse sequent gives a right inverse on the translated carrier. -/
theorem alpha_beta_value (A : Model H) (s : H.signature.SortType) (y : A.obj.carrier (c.onSort s)) :
    d.alphaValue A s (d.betaValue A s y) = y := by
  let xs : Assignment A.obj.carrier [c.onSort s] := Assignment.cons y Assignment.empty
  have first := d.beta_evaluates A s y
  have evaluated := (Term.evaluates_applyUnary_iff (d.alpha s) (d.beta s) A.obj xs _ first _).2
    (d.alpha_evaluates A s (d.betaValue A s y))
  have original := (Term.evaluates_var_iff (sig := H.signature) Var.here A.obj xs y).2 rfl
  exact Formula.values_eq_of_holds_termEq ((d.alpha_beta s).sound A.obj A.property xs True.intro)
    evaluated original

/-- The interpreted forward comparison term is a bijection, with beta as its inverse. -/
theorem alpha_bijective (A : Model H) (s : H.signature.SortType) :
    Function.Bijective (d.alphaValue A s) :=
  ⟨Function.LeftInverse.injective (d.beta_alpha_value A s),
    Function.RightInverse.surjective (d.alpha_beta_value A s)⟩

/-- The comparison arguments evaluate to the tuple obtained by mapping each original variable. -/
theorem comparisonArguments_evaluatesAt (A : Model H) {Γ : List H.signature.SortType}
    (xs : Assignment A.obj.carrier Γ) :
    (comparisonArguments c.onSort d.alpha Γ).EvaluatesAt A.obj xs
      ((xs.map (d.alphaValue A)).mapSorts c.onSort) := by
  refine @Var.forall_mapSorts H.signature.SortType H.signature.SortType Γ c.onSort (fun {_} i =>
    ((comparisonArguments c.onSort d.alpha Γ) i).Evaluates A.obj xs
      (((xs.map (d.alphaValue A)).mapSorts c.onSort) i)) ?_
  intro s i
  simp only [comparisonArguments_apply, Assignment.mapSorts_apply, Assignment.map_apply]
  have variableValue := (Term.evaluates_var_iff i A.obj xs (xs i)).2 rfl
  exact (Term.evaluates_applyUnary_iff (d.alpha s) (.var i) A.obj xs _ variableValue _).2
    (d.alpha_evaluates A s (xs i))

/-- Apply the relation sequent in both directions to the evaluated forward maps. -/
theorem alpha_relation_iff (A : Model H) (r : H.signature.Rel)
    (xs : Assignment A.obj.carrier (H.signature.relInputs r)) :
    xs ∈ A.obj.relation r ↔ xs.map (d.alphaValue A) ∈ (c.pullbackModel A).obj.relation r := by
  have axioms := (d.relation r).holds_iff A.obj A.property xs
  simp only [Formula.holds_atom, Atomic.holds_rel, Assignment.pull_id] at axioms
  exact axioms.trans
    (((c.translation.relation r).holds_substitute_of_evaluatesAt A.obj _ xs _
      (d.comparisonArguments_evaluatesAt A xs)).trans
      (c.pullback_relation_iff A.obj A.property r _).symm)

/-- Apply the domain sequent in both directions to the evaluated forward maps. -/
theorem alpha_partialDomain_iff (A : Model H) (p : H.signature.Partial)
    (xs : Assignment A.obj.carrier (H.signature.partialArity p).inputs) :
    xs ∈ A.obj.partialDomain p ↔ xs.map (d.alphaValue A) ∈ (c.pullbackModel A).obj.partialDomain p := by
  have axioms := (d.partialDomain p).holds_iff A.obj A.property xs
  simp only [Formula.holds_atom, Atomic.holds_domain, Assignment.pull_id] at axioms
  exact axioms.trans
    (((c.translation.partialDomain p).holds_substitute_of_evaluatesAt A.obj _ xs _
      (d.comparisonArguments_evaluatesAt A xs)).trans
      (c.pullback_partialDomain_iff A.obj A.property p _).symm)

/-- A sound operation equation makes the forward comparison commute with the interpreted value. -/
private theorem alpha_value_commutes (A : Model H) (op : Operation H.signature)
    (xs : Assignment A.obj.carrier op.arity.inputs) {y : A.obj.carrier op.arity.output}
    {z : (c.pullbackModel A).obj.carrier op.arity.output}
    (source : A.obj.Graph op xs y)
    (target : (c.pullbackModel A).obj.Graph op (xs.map (d.alphaValue A)) z)
    (equation : (c.comparisonEquation d.alpha op).Holds A.obj xs) :
    d.alphaValue A op.arity.output y = z := by
  have sourceTerm := (Term.primitive_evaluates_iff A.obj op xs y).2 source
  have left := (Term.evaluates_applyUnary_iff (d.alpha _) (Term.primitive op) A.obj xs y sourceTerm _).2
    (d.alpha_evaluates A _ y)
  have targetTerm := (c.pullback_graph_iff A.obj A.property op _ z).1 target
  have right := (Term.evaluates_applyStrict_of_evaluatesAt (c.translation.operation op) _ A.obj xs _
    (d.comparisonArguments_evaluatesAt A xs) z).2 targetTerm
  rw [c.comparisonEquation_eq_termEq] at equation
  exact Formula.values_eq_of_holds_termEq equation left right

/-- Corollary 2.4a(b): the forward terms define a structure map from each model to its pullback. -/
noncomputable def alphaMap (A : Model H) : StructureMap A.obj (c.pullbackModel A).obj where
  onSort := d.alphaValue A
  total_comm f xs := by
    apply d.alpha_value_commutes A (.total f) xs
    · exact (A.obj.graph_total_iff f xs _).2 rfl
    · exact ((c.pullbackModel A).obj.graph_total_iff f _ _).2 rfl
    · exact (d.total f).sound A.obj A.property xs True.intro
  relation_mem r xs held := (d.alpha_relation_iff A r xs).1 held
  partial_mem p xs held := (d.alpha_partialDomain_iff A p xs).1 held
  partial_comm p xs := by
    apply d.alpha_value_commutes A (.partialOp p) xs.val
    · exact (A.obj.graph_partial_iff p xs.val _).2 ⟨xs.property, rfl⟩
    · exact ((c.pullbackModel A).obj.graph_partial_iff p _ _).2
        ⟨(d.alpha_partialDomain_iff A p xs.val).1 xs.property, rfl⟩
    · apply (d.partialValue p).sound A.obj A.property xs.val
      simpa only [Formula.holds_atom, Atomic.holds_domain, Assignment.pull_id] using xs.property
  quantity_comm q xs := by
    apply d.alpha_value_commutes A (.quantity q) xs
    · exact (A.obj.graph_quantity_iff q xs _).2 rfl
    · exact ((c.pullbackModel A).obj.graph_quantity_iff q _ _).2 rfl
    · exact (d.quantity q).sound A.obj A.property xs True.intro

/-- The structure isomorphism uses the two inverse laws and reflection at each model. -/
noncomputable def structureIso (A : Model H) : A.obj ≅ (c.pullbackModel A).obj :=
  (d.alphaMap A).iso_of_bijective_reflects (d.alpha_bijective A)
    (fun r xs => (d.alpha_relation_iff A r xs).2)
    (fun p xs => (d.alpha_partialDomain_iff A p xs).2)

/-- The forward comparison is an isomorphism of actual models. -/
noncomputable def modelIso (A : Model H) : A ≅ c.pullback.obj A :=
  ObjectProperty.isoMk H.modelProperty (d.structureIso A)

/-- The forward isomorphism acts by the evaluated alpha term. -/
theorem modelIso_hom_apply (A : Model H) (s : H.signature.SortType) (x : A.obj.carrier s) :
    (d.modelIso A).hom.hom.onSort s x = d.alphaValue A s x :=
  rfl

/-- The inverse isomorphism acts by the evaluated beta term. -/
theorem modelIso_inv_apply (A : Model H) (s : H.signature.SortType) (y : A.obj.carrier (c.onSort s)) :
    (d.modelIso A).inv.hom.onSort s y = d.betaValue A s y := by
  apply (d.alpha_bijective A s).injective
  exact ((Structure.isoComponent (d.structureIso A) s).apply_symm_apply y).trans
    (d.alpha_beta_value A s y).symm

/-- Corollary 2.4a(b): the evaluated forward terms give a natural isomorphism. -/
noncomputable def naturalIso : 𝟭 (Model H) ≅ c.pullback :=
  NatIso.ofComponents (d.modelIso) (fun {A B} f => by
    apply Model.hom_ext
    intro s x
    simp only [Functor.id_map, Model.comp_apply, modelIso_hom_apply, pullback_map_apply]
    have forwarded := f.hom.evaluates_map (d.alpha s) _ _ (d.alpha_evaluates A s x)
    rw [Assignment.map_cons, Assignment.map_empty] at forwarded
    exact Term.evaluates_unique B.obj _ _ (d.alpha_evaluates B s (f.hom.onSort s x)) forwarded)

end SHIGURE.Interpretation.SyntacticComparison

namespace SHIGURE.Interpretation

open CategoryTheory

variable {S T : Theory.{u}} (u : Interpretation S T) (v : Interpretation T S)

/-- First natural isomorphism in Corollary 2.4a(b), on the source of the interpretation. -/
noncomputable def sourceRoundTrip (comparison : SyntacticComparison (v.comp u)) :
    𝟭 (Model S) ≅ v.pullback ⋙ u.pullback :=
  comparison.naturalIso ≪≫ eqToIso (pullback_comp v u)

/-- Second natural isomorphism in Corollary 2.4a(b), on the target of the interpretation. -/
noncomputable def targetRoundTrip (comparison : SyntacticComparison (u.comp v)) :
    𝟭 (Model T) ≅ u.pullback ⋙ v.pullback :=
  comparison.naturalIso ≪≫ eqToIso (pullback_comp u v)

/-- Corollary 2.4a(b): the two syntactic comparisons yield a mathlib equivalence of model categories. -/
noncomputable def modelEquivalence (source : SyntacticComparison (v.comp u))
    (target : SyntacticComparison (u.comp v)) : Model S ≌ Model T :=
  CategoryTheory.Equivalence.mk v.pullback u.pullback (sourceRoundTrip u v source) (targetRoundTrip u v target).symm

/-- The forward functor of Corollary 2.4a(b) is pullback along the inverse interpretation. -/
theorem modelEquivalence_functor (source : SyntacticComparison (v.comp u))
    (target : SyntacticComparison (u.comp v)) :
    (modelEquivalence u v source target).functor = v.pullback := rfl

/-- The inverse functor of Corollary 2.4a(b) is pullback along the forward interpretation. -/
theorem modelEquivalence_inverse (source : SyntacticComparison (v.comp u))
    (target : SyntacticComparison (u.comp v)) :
    (modelEquivalence u v source target).inverse = u.pullback := rfl

end SHIGURE.Interpretation
