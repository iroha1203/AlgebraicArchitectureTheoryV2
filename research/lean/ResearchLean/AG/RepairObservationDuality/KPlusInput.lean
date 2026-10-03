import ResearchLean.AG.RelativeRepairComposition.NativeAffineRepairs
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCoefficients
import ResearchLean.AG.RelativeRepairComposition.ClosedCovers
import ResearchLean.AG.RepairObservationDuality.PrimitiveInputQueries
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

/-!
# G-131 E: the original four-edge F2 K+ and its actual primitive inputs

## Implementation notes

The two distinct vertices and four original typed edges retain the loop c at
the target. The second authored word is c after e, rather than W5's e alone.
Inputs are arbitrary operations in the whole native affine projection kernel;
the whole-kernel inverse identifies each with its actual value at zero.
No repair predicate or successful correction is part of the input data.
-/
namespace AAT.AG.RepairObservationDuality.KPlusInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open RelativeRepairComposition NativeAffine
set_option autoImplicit false

/-- F2 is a field by the prescribed prime-two arithmetic fact. -/
instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The original common source of e,a,b. -/
def vertexS : Fin 2 := 0
/-- The original common target and source of the candidate loop c. -/
def vertexT : Fin 2 := 1
/-- The original always-correctable shared edge. -/
def edgeE : Fin 4 := 0
/-- The original first physical input edge. -/
def edgeA : Fin 4 := 1
/-- The original second physical input edge. -/
def edgeB : Fin 4 := 2
/-- The original distinct candidate loop at the target. -/
def edgeC : Fin 4 := 3

/-- The loop c starts at t; all three original parallel edges start at s. -/
def edgeSource (e : Fin 4) : Fin 2 := if e = edgeC then vertexT else vertexS

/-- The same two original faces are e=a and c after e=b. -/
def geometry : FiniteTransportPresentation where
  Vertex := Fin 2
  vertexFintype := inferInstance
  Edge := fun i j => {e : Fin 4 // i = edgeSource e ∧ j = vertexT}
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Bool
  twoCellFintype := inferInstance
  twoSource := fun _ => vertexS
  twoTarget := fun _ => vertexT
  twoLeft := fun f => if f then
    .cons (i := vertexS) (j := vertexT) ⟨edgeE,rfl,rfl⟩
      (.cons (i := vertexT) (j := vertexT) ⟨edgeC,rfl,rfl⟩ (.nil vertexT))
    else .cons (i := vertexS) (j := vertexT) ⟨edgeE,rfl,rfl⟩ (.nil vertexT)
  twoRight := fun f => .cons (i := vertexS) (j := vertexT)
    ⟨if f then edgeB else edgeA,by cases f <;> rfl,rfl⟩ (.nil vertexT)
  ThreeCell := Empty
  threeCellFintype := inferInstance
  threeSource := fun t => nomatch t
  threeTarget := fun t => nomatch t
  threeStart := fun t => nomatch t
  threeFinish := fun t => nomatch t
  threeLeft := fun t => nomatch t
  threeRight := fun t => nomatch t

/-- Every typed edge retains its full original finite name and endpoints. -/
instance edgeDecidableEq (i j : geometry.Vertex) : DecidableEq (geometry.Edge i j) :=
  inferInstanceAs (DecidableEq {e : Fin 4 // i = edgeSource e ∧ j = vertexT})
/-- Both authored faces retain the original Boolean equality. -/
instance faceDecidableEq : DecidableEq geometry.TwoCell := inferInstanceAs (DecidableEq Bool)

/-- Every original name reconstructs its original source and target. -/
def name (e : Fin 4) : EdgeName (K := geometry) := ⟨edgeSource e,vertexT,⟨e,rfl,rfl⟩⟩
/-- Basic API: an original typed name keeps its complete finite edge index. -/
theorem name_value (e : Fin 4) : (name e).2.2.1 = e := rfl

/-- Reconstructing an arbitrary original typed edge returns that same edge. -/
theorem name_edge (e : EdgeName (K := geometry)) : name e.2.2.1 = e := by
  rcases e with ⟨i,j,e,hs,ht⟩
  cases hs
  cases ht
  rfl

/-- The complete original edge-name family has exactly these four names. -/
def edgeNameEquiv : Fin 4 ≃ EdgeName (K := geometry) where
  toFun := name
  invFun := fun e => e.2.2.1
  left_inv _ := rfl
  right_inv := name_edge

/-- The actual operation carrier is the entire native affine group on F2. -/
abbrev Op := Operations (ZMod 2) (ZMod 2)
/-- Arbitrary full-kernel physical input operations a and b. -/
abbrev Inputs := Bool → (projection (k := ZMod 2) (A := ZMod 2)).ker
/-- Both original unknown physical values. -/
abbrev Values := Bool → ZMod 2

/-- The input parameters are actual original operations evaluated at zero. -/
def values (X : Inputs) : Values := fun j => (X j).1 0
/-- Every pair is realized by actual native physical input translations. -/
def realize (v : Values) : Inputs := fun j => translationKernel (Multiplicative.ofAdd (v j))
/-- Every parameter pair is realized without imposing a repair condition. -/
theorem values_realize (v : Values) : values (realize v) = v := by
  funext j
  exact add_zero (v j)
/-- Every whole-kernel physical input is recovered exactly from its actual evaluations. -/
theorem realize_values (X : Inputs) : realize (values X) = X := by
  funext j
  apply Subtype.ext
  exact ((projection_eq_one_iff (X j).1).mp (X j).2).symm

/-- References keep a/b as physical inputs and e/c as their identity baselines. -/
noncomputable def reference (v : Values) :
    ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op :=
  fun e => if e.1 = edgeA then translation (k := ZMod 2) (v false)
    else if e.1 = edgeB then translation (k := ZMod 2) (v true) else 1

/-- Every original reference edge has the same known identity linear part. -/
theorem reference_linear (v : Values) {i j : geometry.Vertex} (e : geometry.Edge i j) :
    (reference v e).linear = (1 : ZMod 2 ≃ₗ[ZMod 2] ZMod 2) := by
  unfold reference
  split_ifs <;> rfl

/-- The original e reference is precisely the identity operation. -/
theorem reference_e (v : Values) : reference v (name edgeE).2.2 = 1 := by
  simp [reference,name,edgeE,edgeA,edgeB]
/-- The original c reference is precisely the identity operation. -/
theorem reference_c (v : Values) : reference v (name edgeC).2.2 = 1 := by
  simp [reference,name,edgeC,edgeA,edgeB]
/-- Basic API: the complete original first input map evaluates by its physical translation. -/
theorem reference_a_apply (v : Values) (x : ZMod 2) :
    reference v (name edgeA).2.2 x = x + v false := by
  simp [reference,name,edgeA,add_comm]
/-- Basic API: the complete original second input map evaluates by its physical translation. -/
theorem reference_b_apply (v : Values) (x : ZMod 2) :
    reference v (name edgeB).2.2 x = x + v true := by
  simp [reference,name,edgeA,edgeB,add_comm]
/-- The original a reference is the same full first physical operation. -/
theorem reference_a (X : Inputs) : reference (values X) (name edgeA).2.2 = (X false).1 := by
  rw [(projection_eq_one_iff (X false).1).mp (X false).2]
  simp [reference,name,values,edgeA]
/-- The original b reference is the same full second physical operation. -/
theorem reference_b (X : Inputs) : reference (values X) (name edgeB).2.2 = (X true).1 := by
  rw [(projection_eq_one_iff (X true).1).mp (X true).2]
  simp [reference,name,values,edgeA,edgeB]

/-- The two comparisons on these original authored faces are identity translations. -/
def comparison : geometry.TwoCell → ZMod 2 := fun _ => 0
/-- Basic API: each prescribed original comparison is zero. -/
theorem comparison_zero (f : geometry.TwoCell) : comparison f = 0 := rfl
/-- Basic API: the first complete original left word is the same shared e operation. -/
theorem left_path_false (R : ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op) :
    GroupExtension.pathValue geometry R (geometry.twoLeft false) = R (name edgeE).2.2 := one_mul _
/-- Basic API: the second complete original left word is c after the same e. -/
theorem left_path_true (R : ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op) :
    GroupExtension.pathValue geometry R (geometry.twoLeft true) =
      R (name edgeC).2.2 * R (name edgeE).2.2 := by
  change (1 * R (name edgeC).2.2) * R (name edgeE).2.2 = _
  rw [one_mul]
/-- Basic API: the full original right word retains its same physical input edge. -/
theorem right_path (R : ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op) (f : Bool) :
    GroupExtension.pathValue geometry R (geometry.twoRight f) =
      R (name (if f then edgeB else edgeA)).2.2 := by
  cases f <;> exact one_mul _
/-- Both complete original reference left words compose to the identity. -/
theorem reference_left_path (v : Values) (f : Bool) :
    GroupExtension.pathValue geometry (reference v) (geometry.twoLeft f) = 1 := by
  cases f <;> simp [geometry,GroupExtension.pathValue,reference,edgeE,edgeC,edgeA,edgeB]
/-- Both original reference right words are the corresponding physical input translation. -/
theorem reference_right_path (v : Values) (f : Bool) :
    GroupExtension.pathValue geometry (reference v) (geometry.twoRight f) =
      translation (k := ZMod 2) (v f) := by
  cases f <;> simp [geometry,GroupExtension.pathValue,reference,edgeA,edgeB]
/-- The same original real words have equal known projected linear parts. -/
theorem linear_faces (v : Values) (f : geometry.TwoCell) :
    (GroupExtension.pathValue geometry (reference v) (geometry.twoLeft f)).linear =
      (GroupExtension.pathValue geometry (reference v) (geometry.twoRight f)).linear := by
  rw [reference_left_path,reference_right_path]
  rfl
/-- G-130 generates the original native tower and whole kernels from these actual operations. -/
noncomputable abbrev originalTower (v : Values) :=
  NativeAffine.tower geometry (reference v) (reference v) comparison (linear_faces v)

/-- The original fixed part contains both vertices and precisely the physical a/b edges. -/
def fixedRegion : ClosedRegion geometry where
  vertices := Set.univ
  edges := {name edgeA,name edgeB}
  faces := ∅
  triples := ∅
  edge_closed := by intro e he; exact ⟨Set.mem_univ _,Set.mem_univ _⟩
  face_closed := by intro f hf; exact hf.elim
  triple_closed := by intro t ht; exact ht.elim
/-- The same distinct original loop c is the sole candidate. -/
def candidates : Set (EdgeName (K := geometry)) := {name edgeC}
/-- Candidate permission keeps c separate from the fixed original inputs. -/
theorem candidate_not_fixed : name edgeC ∉ fixedRegion.edges := by
  rintro (h | h)
  · have hi := congrArg (fun e : EdgeName (K := geometry) => e.2.2.1) h
    exact (by decide : edgeC ≠ edgeA) hi
  · have hi := congrArg (fun e : EdgeName (K := geometry) => e.2.2.1) h
    exact (by decide : edgeC ≠ edgeB) hi
/-- Allowing c leaves exactly the original e as the always-correctable edge. -/
theorem edge_partition : fixedRegion.edges ∪ {name edgeE} ∪ candidates = Set.univ := by
  ext e
  rcases e with ⟨i,j,e,hs,ht⟩
  cases hs
  cases ht
  fin_cases e <;>
    simp [fixedRegion,candidates,name,edgeE,edgeA,edgeB,edgeC,edgeSource,vertexS,vertexT]

/-- Each permitted original primitive is its own coordinate linear form. -/
def primitive (j : Bool) : Values →ₗ[ZMod 2] ZMod 2 := LinearMap.proj j
/-- An exact primitive query evaluates one original full physical operation at zero. -/
def evaluate (X : Inputs) (j : Bool) : ZMod 2 := (X j).1 0
/-- Actual primitive evaluation agrees with its linear form on every original input. -/
theorem evaluate_values (X : Inputs) (j : Bool) : evaluate X j = primitive j (values X) := rfl
/-- Querying the same original fixed a and b returns precisely these primitive values. -/
theorem original_evaluation (X : Inputs) :
    reference (values X) (name edgeA).2.2 0 = evaluate X false ∧
      reference (values X) (name edgeB).2.2 0 = evaluate X true := by
  rw [reference_a,reference_b]
  exact ⟨rfl,rfl⟩

end AAT.AG.RepairObservationDuality.KPlusInput
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.KPlusInput
