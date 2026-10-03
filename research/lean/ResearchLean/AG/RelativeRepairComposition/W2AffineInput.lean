import ResearchLean.AG.RelativeRepairComposition.NativeAffineRestriction
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCoefficients
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# W2's original two-edge full affine path

The original vertices are p,w,q and the two named edges have types p→w and
w→q. There are no authored faces or three-cells. Both references are the
actual identity in the entire affine group on F3. The physical endpoints and
candidate restrictions are imposed separately in W2Regions.
-/
namespace AAT.AG.RelativeRepairComposition.W2AffineInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine

/-- The specified coefficient field uses the prime-three arithmetic theorem. -/
instance primeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The original physical initial endpoint p. -/
def vertexP : Fin 3 := 0
/-- The original internal vertex w. -/
def vertexW : Fin 3 := 1
/-- The original physical final endpoint q. -/
def vertexQ : Fin 3 := 2

/-- Original candidate e1, with type p→w. -/
def edgeOne : Fin 2 := 0
/-- Original candidate e2, with type w→q. -/
def edgeTwo : Fin 2 := 1
/-- Each original named edge starts at its original endpoint. -/
def edgeSource (e : Fin 2) : Fin 3 := e.castSucc
/-- Each original named edge ends at the next original endpoint. -/
def edgeTarget (e : Fin 2) : Fin 3 := e.succ

/-- The specified original path has exactly the two typed edges and no higher cells. -/
def geometry : FiniteTransportPresentation where
  Vertex := Fin 3
  vertexFintype := inferInstance
  Edge := fun i j => {e : Fin 2 // i = edgeSource e ∧ j = edgeTarget e}
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Empty
  twoCellFintype := inferInstance
  twoSource := fun f => nomatch f
  twoTarget := fun f => nomatch f
  twoLeft := fun f => nomatch f
  twoRight := fun f => nomatch f
  ThreeCell := Empty
  threeCellFintype := inferInstance
  threeSource := fun t => nomatch t
  threeTarget := fun t => nomatch t
  threeStart := fun t => nomatch t
  threeFinish := fun t => nomatch t
  threeLeft := fun t => nomatch t
  threeRight := fun t => nomatch t

/-- Equality retains both the original edge name and original typed endpoints. -/
instance edgeDecidableEq (i j : geometry.Vertex) : DecidableEq (geometry.Edge i j) :=
  inferInstanceAs (DecidableEq {e : Fin 2 // i = edgeSource e ∧ j = edgeTarget e})

/-- The complete face type has its original empty equality. -/
instance faceDecidableEq : DecidableEq geometry.TwoCell := inferInstanceAs (DecidableEq Empty)

/-- Each named candidate denotes its complete original typed edge. -/
def name (e : Fin 2) : EdgeName (K := geometry) :=
  ⟨edgeSource e, edgeTarget e, ⟨e, rfl, rfl⟩⟩

/-- Every original typed edge name is restored from its own original finite index. -/
theorem name_edge (e : EdgeName (K := geometry)) : name e.2.2.1 = e := by
  rcases e with ⟨i, j, e, hs, ht⟩
  cases hs
  cases ht
  rfl

/-- The complete original typed edge family is exactly the two named candidates. -/
def edgeNameEquiv : Fin 2 ≃ EdgeName (K := geometry) where
  toFun := name
  invFun := fun e => e.2.2.1
  left_inv := fun _ => rfl
  right_inv := name_edge

/-- Every original operation is taken in the full affine group on F3. -/
abbrev Op := Operations (ZMod 3) (ZMod 3)

/-- Both original reference edges are the actual identity affine operation. -/
def reference : ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op := fun _ => 1

/-- There is no comparison to supply because the original face type is empty. -/
def comparison : geometry.TwoCell → ZMod 3 := fun f => nomatch f

/-- Every original face has matching projected words, on the original empty face type. -/
theorem linear_faces (f : geometry.TwoCell) :
    (GroupExtension.pathValue geometry reference (geometry.twoLeft f)).linear =
      (GroupExtension.pathValue geometry reference (geometry.twoRight f)).linear := by
  exact f.elim

/-- The actual original references generate the full affine tower, core and complete kernels. -/
noncomputable abbrev originalTower :=
  NativeAffine.tower geometry reference reference comparison linear_faces

end AAT.AG.RelativeRepairComposition.W2AffineInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2AffineInput
