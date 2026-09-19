import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryPrimitiveDeclaration
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite expressions for overlap point and order conditions

The expression constructors contain only context refinement, derived match
flags, individual primitive context comparisons, and Boolean connectives.
There is no arbitrary predicate or completed context constructor in the
syntax. Every expression has finite primitive query support by induction.
The four native order requirements and each positive/negative matching
instance are expressions in this same syntax.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentOverlapFinite

noncomputable section

universe u v

open Site IndependentGeometryPrimitive

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}

/-- Closed overlap-local expression syntax with native primitive references as its parameters. -/
inductive Expr (A : ArchitectureObject U) where
  /-- One primitive context-order query. -/
  | refinement (W V : ArchCtx A)
  /-- One candidate overlap-result flag. -/
  | matching (base left right result : ArchCtx A)
  /-- Compare one primitive overlap-context point with a candidate reference's native point. -/
  | contextPoint (base left right result : ArchCtx A) (q : IndependentContextObjectPrimitive.Query U)
  /-- One support-family condition at a candidate carrier, guarded by its primitive declaration. -/
  | supportAdmission (base left right : ArchCtx A) (K : Type u) (s : K) (a : U.Atom)
  /-- Conjunction of two finitely supported expressions. -/
  | and (p q : Expr A)
  /-- Implication between two finitely supported expressions. -/
  | implies (p q : Expr A)
  /-- Negation of a finitely supported expression. -/
  | not (p : Expr A)

/-- Evaluate the closed syntax through primitive rows, without assuming their lawfulness. -/
def evaluate (d : DependentTable.{u, v} A) : Expr A → Prop
  | .refinement W V => ((d (.context (.le W V))).down).down
  | .matching base left right result => ((d (.overlap (.matching base left right result))).down).down = true
  | .contextPoint base left right result q =>
      (d (.overlap (.context base left right q))).down = IndependentContextObjectPrimitive.read result q
  | .supportAdmission base left right K s a =>
      K = (d (.overlap (.context base left right (.carrier .support)))).down →
      ((d (.overlap (.context base left right (.support K s a)))).down).down → A.configuration.family.mem a
  | .and p q => evaluate d p ∧ evaluate d q
  | .implies p q => evaluate d p → evaluate d q
  | .not p => ¬ evaluate d p

/-- Finite query support is generated solely by the expression's constructors and subexpressions. -/
def support : Expr A → Finset (DependentQuery.{u, v} A)
  | .refinement W V => {.context (.le W V)}
  | .matching base left right result => {.overlap (.matching base left right result)}
  | .contextPoint base left right _ q => {.overlap (.context base left right q)}
  | .supportAdmission base left right K s a => by
    classical
    exact {.overlap (.context base left right (.carrier .support)),
      .overlap (.context base left right (.support K s a))}
  | .and p q => by
    classical
    exact support p ∪ support q
  | .implies p q => by
    classical
    exact support p ∪ support q
  | .not p => support p

/-- Every expression reads only finitely many primitive addresses, without finite-carrier assumptions. -/
theorem support_finite (e : Expr A) : Finite (support.{u, v} e) := inferInstance

/-- Agreement on a closed expression's support implies equality of its pointwise truth value. -/
theorem evaluate_iff_of_support (d e : DependentTable.{u, v} A) (p : Expr A)
    (h : ∀ q ∈ support p, d q = e q) : evaluate d p ↔ evaluate e p := by
  classical
  induction p with
  | refinement W V =>
      have hh := h (.context (.le W V)) (by simp [support])
      simp only [evaluate, hh]
  | matching base left right result =>
      have hh := h (.overlap (.matching base left right result)) (by simp [support])
      simp only [evaluate, hh]
  | contextPoint base left right result q =>
      have hh := h (.overlap (.context base left right q)) (by simp [support])
      simp only [evaluate, hh]
  | supportAdmission base left right K s a =>
      have h1 := h (.overlap (.context base left right (.carrier .support))) (by simp [support])
      have h2 := h (.overlap (.context base left right (.support K s a))) (by simp [support])
      simp only [evaluate, h1, h2]
  | and p q hp hq =>
      exact and_congr (hp (fun r hr => h r (by simp [support, hr])))
        (hq (fun r hr => h r (by simp [support, hr])))
  | implies p q hp hq =>
      exact imp_congr (hp (fun r hr => h r (by simp [support, hr])))
        (hq (fun r hr => h r (by simp [support, hr])))
  | not p hp => exact not_congr (hp h)

/-- Common premises of the three output-refinement requirements. -/
def orderPremise (base left right result : ArchCtx A) : Expr A :=
  .and (.matching base left right result) (.and (.refinement left base) (.refinement right base))

/-- The left overlap requirement as a closed primitive expression. -/
def leftRule (base left right result : ArchCtx A) : Expr A :=
  .implies (orderPremise base left right result) (.refinement result left)

/-- The right overlap requirement as a closed primitive expression. -/
def rightRule (base left right result : ArchCtx A) : Expr A :=
  .implies (orderPremise base left right result) (.refinement result right)

/-- The base overlap requirement as a closed primitive expression. -/
def baseRule (base left right result : ArchCtx A) : Expr A :=
  .implies (orderPremise base left right result) (.refinement result base)

/-- The common-refinement lifting requirement as a closed primitive expression. -/
def liftRule (base left right result X : ArchCtx A) : Expr A :=
  .implies (.and (orderPremise base left right result)
    (.and (.refinement X left) (.refinement X right))) (.refinement X result)

/-- A positive result match requires agreement at this specific primitive point. -/
def positiveMatchRule (base left right result : ArchCtx A) (q : IndependentContextObjectPrimitive.Query U) :
    Expr A := .implies (.matching base left right result) (.contextPoint base left right result q)

/-- A negative result match can use this primitive point as its finite refutation witness. -/
def negativeMatchWitness (base left right result : ArchCtx A) (q : IndependentContextObjectPrimitive.Query U) :
    Expr A := .not (.contextPoint base left right result q)

/-- The closed left expression has exactly the independent candidate-order meaning. -/
theorem evaluate_leftRule (d : DependentTable.{u, v} A) (base left right result : ArchCtx A) :
    evaluate d (leftRule base left right result) ↔
      (IndependentOverlapCandidate.matching (overlapTable d) base left right result = true →
        IndependentContextPrimitive.le (contextTable d) left base →
        IndependentContextPrimitive.le (contextTable d) right base →
        IndependentContextPrimitive.le (contextTable d) result left) := by
  simp only [evaluate, leftRule, orderPremise, and_imp]
  rfl

/-- The right order requirement is represented by the same closed expression constructors. -/
theorem evaluate_rightRule (d : DependentTable.{u, v} A) (base left right result : ArchCtx A) :
    evaluate d (rightRule base left right result) ↔
      (IndependentOverlapCandidate.matching (overlapTable d) base left right result = true →
        IndependentContextPrimitive.le (contextTable d) left base →
        IndependentContextPrimitive.le (contextTable d) right base →
        IndependentContextPrimitive.le (contextTable d) result right) := by
  simp only [evaluate, rightRule, orderPremise, and_imp]
  rfl

/-- The base order requirement is represented by the same closed expression constructors. -/
theorem evaluate_baseRule (d : DependentTable.{u, v} A) (base left right result : ArchCtx A) :
    evaluate d (baseRule base left right result) ↔
      (IndependentOverlapCandidate.matching (overlapTable d) base left right result = true →
        IndependentContextPrimitive.le (contextTable d) left base →
        IndependentContextPrimitive.le (contextTable d) right base →
        IndependentContextPrimitive.le (contextTable d) result base) := by
  simp only [evaluate, baseRule, orderPremise, and_imp]
  rfl

/-- The lifting order requirement is represented without assembling its result context in the expression. -/
theorem evaluate_liftRule (d : DependentTable.{u, v} A) (base left right result X : ArchCtx A) :
    evaluate d (liftRule base left right result X) ↔
      (IndependentOverlapCandidate.matching (overlapTable d) base left right result = true →
        IndependentContextPrimitive.le (contextTable d) left base →
        IndependentContextPrimitive.le (contextTable d) right base →
        IndependentContextPrimitive.le (contextTable d) X left →
        IndependentContextPrimitive.le (contextTable d) X right →
        IndependentContextPrimitive.le (contextTable d) X result) := by
  simp only [evaluate, liftRule, orderPremise, and_imp]
  rfl

/-- The guarded support expressions recover the native support-family condition exactly. -/
theorem support_rules_iff (d : DependentTable.{u, v} A) (base left right : ArchCtx A) :
    (∀ K (s : K) a, evaluate d (.supportAdmission base left right K s a)) ↔
      IndependentContextObjectPrimitive.IsLawful A
        (IndependentContextObjectPrimitive.Overlap.context
          (IndependentOverlapCandidate.context (overlapTable d)) base left right) := by
  constructor
  · intro h s a hs
    exact h _ s a rfl hs
  · intro h K s a hK hs
    cases hK
    exact h s a hs

/-- Every independent overlap law is precisely a quantified instance of the fixed finite syntax. -/
theorem lawful_iff_expressions (d : DependentTable.{u, v} A)
    (ht : IndependentContextPrimitive.IsTyped (contextTable d))
    (hc : IndependentContextPrimitive.IsLawful (contextTable d) ht) :
    IndependentOverlapCandidate.IsLawful (IndependentContextPrimitive.assemble (contextTable d) ht hc)
      (overlapTable d) ↔
    (∀ b l r K (s : K) a, evaluate d (.supportAdmission b l r K s a)) ∧
    (∀ b l r W q, evaluate d (positiveMatchRule b l r W q)) ∧
    (∀ b l r W, IndependentOverlapCandidate.matching (overlapTable d) b l r W = false →
      ∃ q, evaluate d (negativeMatchWitness b l r W q)) ∧
    (∀ b l r W, evaluate d (leftRule b l r W)) ∧
    (∀ b l r W, evaluate d (rightRule b l r W)) ∧
    (∀ b l r W, evaluate d (baseRule b l r W)) ∧
    (∀ b l r W X, evaluate d (liftRule b l r W X)) := by
  constructor
  · intro h
    refine ⟨fun b l r => (support_rules_iff d b l r).2 (h.support b l r),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b l r W q hm
      exact (h.matching b l r).yes W hm q
    · intro b l r W hm
      exact (h.matching b l r).no W hm
    · intro b l r W
      exact (evaluate_leftRule d b l r W).2 (h.left b l r W)
    · intro b l r W
      exact (evaluate_rightRule d b l r W).2 (h.right b l r W)
    · intro b l r W
      exact (evaluate_baseRule d b l r W).2 (h.base b l r W)
    · intro b l r W X
      exact (evaluate_liftRule d b l r W X).2 (h.lift b l r W X)
  · rintro ⟨hs, hy, hn, hl, hr, hb, hx⟩
    refine ⟨fun b l r => (support_rules_iff d b l r).1 (hs b l r), ?_, ?_, ?_, ?_, ?_⟩
    · intro b l r
      exact ⟨fun W hm q => hy b l r W q hm, hn b l r⟩
    · intro b l r W
      exact (evaluate_leftRule d b l r W).1 (hl b l r W)
    · intro b l r W
      exact (evaluate_rightRule d b l r W).1 (hr b l r W)
    · intro b l r W
      exact (evaluate_baseRule d b l r W).1 (hb b l r W)
    · intro b l r W X
      exact (evaluate_liftRule d b l r W X).1 (hx b l r W X)

/-- Lift a finite expression support to the declaration shared by all complete geometry objects. -/
def commonSupport (p : Expr A) : Finset (Query.{u, v} U) := by
  classical
  exact (support p).image (Query.atObject A)

/-- Equal common primitive cells give equal extracted active cells, regardless of presence-proof choices. -/
theorem dependent_cell_eq (t s : Table.{u, v} U) (ht : IsActiveTyped t) (hs : IsActiveTyped s)
    (ha : matching t (.object A) = true) (hb : matching s (.object A) = true)
    (q : DependentQuery.{u, v} A) (hq : t (.atObject A q) = s (.atObject A q)) :
    dependent t ht A ha q = dependent s hs A hb q := by
  apply Option.some.inj
  rw [some_dependent, some_dependent, hq]

/-- Finite support remains sufficient on the common declaration for arbitrary active comparison tables. -/
theorem evaluate_iff_of_commonSupport (t s : Table.{u, v} U) (ht : IsActiveTyped t) (hs : IsActiveTyped s)
    (ha : matching t (.object A) = true) (hb : matching s (.object A) = true) (p : Expr A)
    (h : ∀ q ∈ commonSupport p, t q = s q) :
    evaluate (dependent t ht A ha) p ↔ evaluate (dependent s hs A hb) p := by
  classical
  apply evaluate_iff_of_support
  intro q hq
  exact dependent_cell_eq t s ht hs ha hb q (h (.atObject A q)
    (Finset.mem_image.mpr ⟨q, hq, rfl⟩))

end

end AAT.AG.LocalSemanticReconstruction.IndependentOverlapFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentOverlapFinite
