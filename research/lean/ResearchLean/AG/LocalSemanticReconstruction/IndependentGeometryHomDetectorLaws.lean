import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomEquationLaws
import Formal.Util.AssertStandardAxioms

/-!
# Detector preservation from finite syntax and primitive Atom points

The matching rules recurse over the original finite query/list/detector syntax.
Their leaves compare Boolean polarities and common Hom Atom points. They do
not store a completed Atom equivalence or detector-family transport. Native
code equality is derived after assembling the Atom and equation-index rows.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Detector

noncomputable section

universe u v

open Site

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- One native circuit query uses at most two primitive Atom-image points. -/
def QueryMatch (h : Table.{u, v} U mode) : CircuitQuery U → CircuitQuery U → Prop
  | .atomPresent a, .atomPresent b => h (.atom .forward a b) = true
  | .relationPresent a b, .relationPresent c d =>
      h (.atom .forward a c) = true ∧ h (.atom .forward b d) = true
  | .identificationPresent a b, .identificationPresent c d =>
      h (.atom .forward a c) = true ∧ h (.atom .forward b d) = true
  | _, _ => False

/-- Signed-query matching retains the exact original Boolean polarity and list order. -/
def ListMatch (h : Table.{u, v} U mode) :
    List (CircuitQuery U × Bool) → List (CircuitQuery U × Bool) → Prop
  | [], [] => True
  | x :: xs, y :: ys => QueryMatch h x.1 y.1 ∧ y.2 = x.2 ∧ ListMatch h xs ys
  | _, _ => False

/-- Finite detector constructors must match exactly, with primitive point matching at their leaves. -/
def CodeMatch (h : Table.{u, v} U mode) : CircuitDetectorCode U → CircuitDetectorCode U → Prop
  | .reject, .reject => True
  | .exact p, .exact q => ListMatch h p.queries q.queries
  | .any p q, .any r s => CodeMatch h p r ∧ CodeMatch h q s
  | _, _ => False

variable (h : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper h))

/-- A true forward Atom point is precisely the assembled image, in target/source order. -/
theorem atom_iff (a b : U.Atom) : h (.atom .forward a b) = true ↔
    b = Atom.assemble (Atom.upper h) ha a :=
  ((Atom.graph (Atom.upper h) ha .forward).edge_eq_true_iff_target_eq a b).trans eq_comm

/-- Matching one finite query is exactly its original native transport equality. -/
theorem queryMatch_iff (p q : CircuitQuery U) : QueryMatch h p q ↔
    q = p.transport (Atom.assemble (Atom.upper h) ha) := by
  cases p <;> cases q <;> simp [QueryMatch, CircuitQuery.transport, atom_iff h ha]

/-- Matching the finite signed list is exactly its native pointwise transport. -/
theorem listMatch_iff (xs ys : List (CircuitQuery U × Bool)) : ListMatch h xs ys ↔
    ys = xs.map (fun x => (x.1.transport (Atom.assemble (Atom.upper h) ha), x.2)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [ListMatch]
  | cons x xs ih =>
    cases ys with
    | nil => simp [ListMatch]
    | cons y ys =>
      rcases x with ⟨x, b⟩
      rcases y with ⟨y, c⟩
      simp [ListMatch, queryMatch_iff h ha, ih, and_assoc]

/-- The complete finite detector syntax is preserved exactly, including all branch and template data. -/
theorem codeMatch_iff (c d : CircuitDetectorCode U) : CodeMatch h c d ↔
    d = c.transport (Atom.assemble (Atom.upper h) ha) := by
  induction c generalizing d with
  | reject => cases d <;> simp [CodeMatch, CircuitDetectorCode.transport]
  | exact p =>
    cases d with
    | reject => simp [CodeMatch, CircuitDetectorCode.transport]
    | any a b => simp [CodeMatch, CircuitDetectorCode.transport]
    | exact q =>
      cases p
      cases q
      simp [CodeMatch, listMatch_iff h ha, CircuitDetectorCode.transport, FiniteCircuitDatum.transport]
  | any a b ihA ihB =>
    cases d <;> simp [CodeMatch, CircuitDetectorCode.transport, ihA, ihB]

variable {A B : ArchitectureObject U}

/-- Every active equation point compares the two finite syntax responses by primitive matching. -/
def PointLaws (s t : IndependentEquationPrimitive.Circuit.Table U)
    (h : Table.{u, v} U mode) (A B : ArchitectureObject U) : Prop :=
  ∀ (I J : Type u) (i : I) (j : J) (c d : CircuitDetectorCode U),
    h (.atObjects A B (.equation .forward (.edge I J i j))) = true →
    s (.code I i) = some c → t (.code J j) = some d → CodeMatch h c d

variable {C : ContextPreorderCategory A} {D : ContextPreorderCategory B}
variable (s : IndependentEquationPrimitive.Table A) (t : IndependentEquationPrimitive.Table B)
variable (cs ct : IndependentEquationPrimitive.Circuit.Table U)
variable (hcs : IndependentEquationPrimitive.Circuit.IsTyped (IndependentEquationPrimitive.index s) cs)
variable (hct : IndependentEquationPrimitive.Circuit.IsTyped (IndependentEquationPrimitive.index t) ct)
variable (he : IndependentInverseGraph.IsLawful (IndependentEquationPrimitive.index s)
  (IndependentEquationPrimitive.index t) (InverseRows.equation h A B))

/-- Native detector equality follows from the two finite code responses and their point matching. -/
theorem native_of_points (hp : PointLaws cs ct h A B) (i : IndependentEquationPrimitive.index s) :
    IndependentEquationPrimitive.Circuit.code ct hct (EquationLaws.equationEquiv s t h he i) =
      (IndependentEquationPrimitive.Circuit.code cs hcs i).transport (Atom.assemble (Atom.upper h) ha) := by
  apply (codeMatch_iff h ha _ _).1
  exact hp _ _ i _ _ _ ((EquationLaws.equation_forward_iff s t h he i _).2 rfl)
    (Option.some_get _).symm (Option.some_get _).symm

/-- Original native detector preservation yields all candidate-index primitive matching rules. -/
theorem points_of_native
    (hp : ∀ i, IndependentEquationPrimitive.Circuit.code ct hct (EquationLaws.equationEquiv s t h he i) =
      (IndependentEquationPrimitive.Circuit.code cs hcs i).transport (Atom.assemble (Atom.upper h) ha)) :
    PointLaws cs ct h A B := by
  intro I J i j c d hij hc hd
  obtain ⟨rfl, rfl⟩ := EquationLaws.equation_carriers s t h he I J i j hij
  have hj := (EquationLaws.equation_forward_iff s t h he i j).1 hij
  have hcode : IndependentEquationPrimitive.Circuit.code cs hcs i = c :=
    Option.some.inj ((Option.some_get _).trans hc)
  have hcode' : IndependentEquationPrimitive.Circuit.code ct hct j = d :=
    Option.some.inj ((Option.some_get _).trans hd)
  apply (codeMatch_iff h ha c d).2
  rw [← hcode, ← hcode', ← hj]
  exact hp i

/-- Primitive detector rules have exactly the original full native detector-family preservation meaning. -/
theorem points_iff_native : PointLaws cs ct h A B ↔
    ∀ i, IndependentEquationPrimitive.Circuit.code ct hct (EquationLaws.equationEquiv s t h he i) =
      (IndependentEquationPrimitive.Circuit.code cs hcs i).transport (Atom.assemble (Atom.upper h) ha) :=
  ⟨native_of_points h ha s t cs ct hcs hct he, points_of_native h ha s t cs ct hcs hct he⟩

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Detector

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Detector
