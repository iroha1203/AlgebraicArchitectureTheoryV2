import ResearchLean.AG.RelativeRepairComposition.NativeAffineRestriction
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCoefficients
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# W5's three original parallel affine edges and two authored faces

All operations belong to the whole affine group on F2. The original physical
input translations a and b vary over every pair; e has identity reference.
The two faces retain these same typed original edges and identity comparisons.
-/
namespace AAT.AG.RelativeRepairComposition.W5AffineInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine

/-- The specified coefficient field follows from the prime-two arithmetic theorem. -/
instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Original common source of all three parallel operations. -/
def vertexS : Fin 2 := 0
/-- Original common target of all three parallel operations. -/
def vertexT : Fin 2 := 1
/-- Original shared always-correctable edge e. -/
def edgeE : Fin 3 := 0
/-- Original physically fixed input edge a. -/
def edgeA : Fin 3 := 1
/-- Original physically fixed input edge b. -/
def edgeB : Fin 3 := 2

/-- The original presentation keeps all three typed parallel edges and both faces. -/
def geometry : FiniteTransportPresentation where
  Vertex := Fin 2
  vertexFintype := inferInstance
  Edge := fun i j => {_e : Fin 3 // i = vertexS ∧ j = vertexT}
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Bool
  twoCellFintype := inferInstance
  twoSource := fun _ => vertexS
  twoTarget := fun _ => vertexT
  twoLeft := fun _ => .cons (i := vertexS) (j := vertexT) ⟨edgeE, rfl, rfl⟩ (.nil vertexT)
  twoRight := fun f => .cons (i := vertexS) (j := vertexT)
    ⟨if f then edgeB else edgeA, rfl, rfl⟩ (.nil vertexT)
  ThreeCell := Empty
  threeCellFintype := inferInstance
  threeSource := fun t => nomatch t
  threeTarget := fun t => nomatch t
  threeStart := fun t => nomatch t
  threeFinish := fun t => nomatch t
  threeLeft := fun t => nomatch t
  threeRight := fun t => nomatch t

/-- Typed equality preserves each original name and both original endpoints. -/
instance edgeDecidableEq (i j : geometry.Vertex) : DecidableEq (geometry.Edge i j) :=
  inferInstanceAs (DecidableEq {_e : Fin 3 // i = vertexS ∧ j = vertexT})
/-- The original two-face equality is the full Boolean equality. -/
instance faceDecidableEq : DecidableEq geometry.TwoCell := inferInstanceAs (DecidableEq Bool)

/-- Every finite index restores its complete original typed edge name. -/
def name (e : Fin 3) : EdgeName (K := geometry) := ⟨vertexS, vertexT, ⟨e,rfl,rfl⟩⟩
/-- Reconstructing an arbitrary original typed name returns that same name. -/
theorem name_edge (e : EdgeName (K := geometry)) : name e.2.2.1 = e := by
  rcases e with ⟨i,j,e,hs,ht⟩
  cases hs
  cases ht
  rfl
/-- The entire original edge family is exactly the three named parallel operations. -/
def edgeNameEquiv : Fin 3 ≃ EdgeName (K := geometry) where
  toFun := name
  invFun := fun e => e.2.2.1
  left_inv _ := rfl
  right_inv := name_edge

/-- The operation carrier is the whole group of invertible affine maps on F2. -/
abbrev Op := Operations (ZMod 2) (ZMod 2)

/-- Reference operations retain e=identity and both original physical input translations. -/
noncomputable def reference (b₁ b₂ : ZMod 2) :
    ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op :=
  fun e => if e.1 = edgeA then translation (k := ZMod 2) b₁
    else if e.1 = edgeB then translation (k := ZMod 2) b₂ else 1

/-- The shared original reference edge is the identity on every input. -/
theorem reference_e_apply (b₁ b₂ x : ZMod 2) :
    reference b₁ b₂ (name edgeE).2.2 x = x := by
  simp [reference, name, edgeE, edgeA, edgeB]
/-- The physical a reference edge retains the first original input translation. -/
theorem reference_a_apply (b₁ b₂ x : ZMod 2) :
    reference b₁ b₂ (name edgeA).2.2 x = x + b₁ := by
  simp [reference, name, edgeA, add_comm]
/-- The physical b reference edge retains the second original input translation. -/
theorem reference_b_apply (b₁ b₂ x : ZMod 2) :
    reference b₁ b₂ (name edgeB).2.2 x = x + b₂ := by
  simp [reference, name, edgeA, edgeB, add_comm]

/-- Both original face comparisons are identity translations. -/
def comparison : geometry.TwoCell → ZMod 2 := fun _ => 0

/-- The left original reference word is the identity on every input. -/
theorem reference_left_path (b₁ b₂ : ZMod 2) (f : geometry.TwoCell) :
    GroupExtension.pathValue geometry (reference b₁ b₂) (geometry.twoLeft f) = 1 := by
  simp [geometry, GroupExtension.pathValue, reference, edgeE, edgeA, edgeB]
/-- The right original reference word is exactly the relevant physical input translation. -/
theorem reference_right_path (b₁ b₂ : ZMod 2) (f : geometry.TwoCell) :
    GroupExtension.pathValue geometry (reference b₁ b₂) (geometry.twoRight f) =
      translation (k := ZMod 2) (if (f : Bool) = true then b₂ else b₁) := by
  cases f <;> simp [geometry, GroupExtension.pathValue, reference, edgeA, edgeB]
/-- Both reference words have the same actual projected linear part. -/
theorem linear_faces (b₁ b₂ : ZMod 2) (f : geometry.TwoCell) :
    (GroupExtension.pathValue geometry (reference b₁ b₂) (geometry.twoLeft f)).linear =
      (GroupExtension.pathValue geometry (reference b₁ b₂) (geometry.twoRight f)).linear := by
  rw [reference_left_path, reference_right_path]
  rfl

/-- The original full affine projection generates the tower, strongness and complete kernels. -/
noncomputable abbrev originalTower (b₁ b₂ : ZMod 2) :=
  NativeAffine.tower geometry (reference b₁ b₂) (reference b₁ b₂) comparison (linear_faces b₁ b₂)

end AAT.AG.RelativeRepairComposition.W5AffineInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5AffineInput
