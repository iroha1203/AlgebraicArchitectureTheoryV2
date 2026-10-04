import ResearchLean.AG.VisibleCycleReflection.GraphChains
import Formal.Util.AssertStandardAxioms

/-!
# Primitive-valued periods on the same oriented graph walks

## Implementation notes

Periods add the actual primitive coefficient along each directed step, reversing
its sign when it opposes the T0 orientation. This construction works in an arbitrary
additive group and hence in the original presentation quotient. A rational pairing
alone would establish only a coordinate observation, so a homomorphism comparison
relates that pairing to these original-valued periods.
-/

noncomputable section
namespace AAT.AG.VisibleCycleReflection.Graph
open Classical
universe u v
variable {V : Type u} [LinearOrder V] (G : SimpleGraph V)
variable {M : Type v} [AddCommGroup M]

/-- Read the original coefficient on a directed step with its orientation sign. -/
def hopValue (z : Edge G → M) {a b : V} (h : G.Adj a b) : M :=
  if hab : a < b then z ⟨(a,b),hab,h⟩
  else -z ⟨(b,a),lt_of_le_of_ne (le_of_not_gt hab) h.ne.symm,h.symm⟩

/-- The original-valued signed sum of a walk's actual edge coefficients. -/
def walkPeriod (z : Edge G → M) {a b : V} : G.Walk a b → M
  | .nil => 0
  | .cons h p => hopValue G z h + walkPeriod z p

/-- Public empty-walk period. -/
@[simp] theorem walkPeriod_nil (z : Edge G → M) (a : V) :
    walkPeriod G z (.nil : G.Walk a a) = 0 := rfl
/-- Public period of a walk beginning with one directed step. -/
@[simp] theorem walkPeriod_cons (z : Edge G → M) {a b c : V}
    (h : G.Adj a b) (p : G.Walk b c) :
    walkPeriod G z (.cons h p) = hopValue G z h + walkPeriod G z p := rfl

/-- Vertex differences telescope on each directed step. -/
theorem hopValue_vertex_difference (b : V → M) {a c : V} (h : G.Adj a c) :
    hopValue G (fun e => b (right G e) - b (left G e)) h = b c - b a := by
  unfold hopValue
  split_ifs
  · rfl
  · change -(b a - b c) = _
    abel

/-- Vertex-difference periods telescope on every full graph walk. -/
theorem walkPeriod_vertex_difference (b : V → M) {a c : V} (p : G.Walk a c) :
    walkPeriod G (fun e => b (right G e) - b (left G e)) p = b c - b a := by
  induction p with
  | nil => simp
  | cons h p ih => rw [walkPeriod_cons,hopValue_vertex_difference,ih]; abel

variable [Fintype V]

/-- Rational observation of a step is its standard signed chain pairing. -/
theorem map_hopValue (f : M →+ ℚ) (z : Edge G → M) {a b : V} (h : G.Adj a b) :
    f (hopValue G z h) = ∑ e, hopChain G h e * f (z e) := by
  unfold hopValue
  split_ifs with hab
  · rw [hopChain_of_lt G h hab]
    simp [edgeUnit_apply]
  · rw [hopChain_of_not_lt G h hab, map_neg]
    simp only [Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
    congr 1
    simp [edgeUnit_apply]

/-- Primitive-valued periods and standard rational cycle pairings are compatible. -/
theorem map_walkPeriod (f : M →+ ℚ) (z : Edge G → M) {a b : V} (p : G.Walk a b) :
    f (walkPeriod G z p) = ∑ e, walkChain G p e * f (z e) := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [walkPeriod_cons,map_add,map_hopValue,ih]
    simp only [walkChain_cons,Pi.add_apply,add_mul,Finset.sum_add_distrib]

end AAT.AG.VisibleCycleReflection.Graph
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
