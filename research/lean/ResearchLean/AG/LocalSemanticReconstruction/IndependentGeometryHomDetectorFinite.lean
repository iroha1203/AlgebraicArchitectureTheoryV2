import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomDetectorLaws
import Formal.Util.AssertStandardAxioms

/-!
# Finite supports for detector transport matching

Support is computed recursively from the original finite detector syntax.
No global Atom map, typedness assumption, or successful native assembly is
needed for the support theorem. A detector-preservation instance additionally
reads its two primitive code responses and one equation-index Hom point.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Detector

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- The Atom points inspected by matching a pair of finite circuit queries. -/
def querySupport : CircuitQuery U → CircuitQuery U → Finset (Query.{u, v} U mode)
  | .atomPresent a, .atomPresent b => {.atom .forward a b}
  | .relationPresent a b, .relationPresent c d => by
      classical
      exact {.atom .forward a c, .atom .forward b d}
  | .identificationPresent a b, .identificationPresent c d => by
      classical
      exact {.atom .forward a c, .atom .forward b d}
  | _, _ => ∅

/-- The finite signed list uses the union of its individual query supports. -/
def listSupport : List (CircuitQuery U × Bool) → List (CircuitQuery U × Bool) → Finset (Query.{u, v} U mode)
  | [], [] => ∅
  | x :: xs, y :: ys => by
      classical
      exact querySupport x.1 y.1 ∪ listSupport xs ys
  | _, _ => ∅

/-- Finite code support follows the original detector constructors. -/
def codeSupport : CircuitDetectorCode U → CircuitDetectorCode U → Finset (Query.{u, v} U mode)
  | .reject, .reject => ∅
  | .exact p, .exact q => listSupport p.queries q.queries
  | .any p q, .any r s => by
      classical
      exact codeSupport p r ∪ codeSupport q s
  | _, _ => ∅

/-- Two arbitrary Hom tables agree on a query-matching instance if its finite support agrees. -/
theorem queryMatch_iff_of_support (h k : Table.{u, v} U mode) (p q : CircuitQuery U)
    (hh : ∀ a ∈ querySupport p q, h a = k a) : QueryMatch h p q ↔ QueryMatch k p q := by
  classical
  cases p <;> cases q <;> simp_all [QueryMatch, querySupport]

/-- Signed-list matching is determined by its finite point support. -/
theorem listMatch_iff_of_support (h k : Table.{u, v} U mode) (xs ys : List (CircuitQuery U × Bool))
    (hh : ∀ a ∈ listSupport xs ys, h a = k a) : ListMatch h xs ys ↔ ListMatch k xs ys := by
  classical
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      exact and_congr
        (queryMatch_iff_of_support h k x.1 y.1 (fun a ha => hh a (Finset.mem_union_left _ ha)))
        (and_congr Iff.rfl (ih ys (fun a ha => hh a (Finset.mem_union_right _ ha))))

/-- Every detector-matching expression has finite support independently of table lawfulness. -/
theorem codeMatch_iff_of_support (h k : Table.{u, v} U mode) (c d : CircuitDetectorCode U)
    (hh : ∀ a ∈ codeSupport c d, h a = k a) : CodeMatch h c d ↔ CodeMatch k c d := by
  classical
  induction c generalizing d with
  | reject => cases d <;> rfl
  | exact p =>
    cases d with
    | reject => rfl
    | any a b => rfl
    | exact q => exact listMatch_iff_of_support h k p.queries q.queries hh
  | any a b ihA ihB =>
    cases d with
    | reject => rfl
    | exact p => rfl
    | any c d =>
      exact and_congr (ihA c (fun x hx => hh x (Finset.mem_union_left _ hx)))
        (ihB d (fun x hx => hh x (Finset.mem_union_right _ hx)))

/-- One detector law instance uses two syntax responses, an index point, and finitely many Atom points. -/
theorem point_instance_iff_of_support (s s' t t' : IndependentEquationPrimitive.Circuit.Table U)
    (h k : Table.{u, v} U mode) (A B : ArchitectureObject U)
    (I J : Type u) (i : I) (j : J) (c d : CircuitDetectorCode U)
    (hs : s (.code I i) = s' (.code I i)) (ht : t (.code J j) = t' (.code J j))
    (hi : h (.atObjects A B (.equation .forward (.edge I J i j))) =
      k (.atObjects A B (.equation .forward (.edge I J i j))))
    (hc : ∀ a ∈ codeSupport c d, h a = k a) :
    (h (.atObjects A B (.equation .forward (.edge I J i j))) = true →
      s (.code I i) = some c → t (.code J j) = some d → CodeMatch h c d) ↔
    (k (.atObjects A B (.equation .forward (.edge I J i j))) = true →
      s' (.code I i) = some c → t' (.code J j) = some d → CodeMatch k c d) := by
  rw [hs, ht, hi, codeMatch_iff_of_support h k c d hc]

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Detector

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Detector
