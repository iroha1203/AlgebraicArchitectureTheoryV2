import ResearchLean.AG.RelativeRepairComposition.W3LinearAction
import ResearchLean.AG.RelativeRepairComposition.NativeAffineRestriction
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCoefficients

/-!
# W3's original two-vertex full affine loop

The same two typed edges s→t and t→s and the same full affine carrier are
used for both original loop actions. There are no authored higher cells.
-/
namespace AAT.AG.RelativeRepairComposition.W3AffineInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction

/-- Original source vertex s. -/
def vertexS : Fin 2 := 0
/-- Original target vertex t. -/
def vertexT : Fin 2 := 1
/-- Original forward edge e. -/
def edgeE : Fin 2 := 0
/-- Original return edge f. -/
def edgeF : Fin 2 := 1
/-- Each original named edge starts at its own original vertex. -/
def edgeSource (e : Fin 2) : Fin 2 := e
/-- Each original edge ends at the other original vertex. -/
def edgeTarget (e : Fin 2) : Fin 2 := if e = 0 then 1 else 0

/-- The full original typed two-edge loop, without faces or three-cells. -/
def geometry : FiniteTransportPresentation where
  Vertex := Fin 2
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

/-- Typed equality retains the original edge and both endpoints. -/
instance edgeDecidableEq (i j : geometry.Vertex) : DecidableEq (geometry.Edge i j) :=
  inferInstanceAs (DecidableEq {e : Fin 2 // i = edgeSource e ∧ j = edgeTarget e})

/-- Equality on the whole original empty face type. -/
instance faceDecidableEq : DecidableEq geometry.TwoCell := inferInstanceAs (DecidableEq Empty)

/-- Each original edge name denotes the same complete typed edge. -/
def name (e : Fin 2) : EdgeName (K := geometry) :=
  ⟨edgeSource e, edgeTarget e, ⟨e, rfl, rfl⟩⟩

/-- Every typed original edge is restored from its own original name. -/
theorem name_edge (e : EdgeName (K := geometry)) : name e.2.2.1 = e := by
  rcases e with ⟨i,j,e,hs,ht⟩
  cases hs
  cases ht
  rfl

/-- The entire original edge family has exactly the two original names. -/
def edgeNameEquiv : Fin 2 ≃ EdgeName (K := geometry) where
  toFun := name
  invFun := fun e => e.2.2.1
  left_inv _ := rfl
  right_inv := name_edge

/-- Every actual operation is a full invertible affine map on the whole F3². -/
abbrev Op := Operations (ZMod 3) A

/-- The return reference is the specified shear or identity as an actual affine operation. -/
def returnLinear (sheared : Bool) : Op := (linearAction sheared).toAffineEquiv

/-- The original e is identity and the original f has the specified actual linear action. -/
def reference (sheared : Bool) : ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op :=
  fun e => if e.1 = edgeF then returnLinear sheared else 1

/-- Original e evaluates to the actual identity operation. -/
theorem reference_e (sheared : Bool) : reference sheared (name edgeE).2.2 = 1 := by
  simp [reference, name, edgeE, edgeF]

/-- Original f evaluates to the actual selected linear operation. -/
theorem reference_f (sheared : Bool) :
    reference sheared (name edgeF).2.2 = returnLinear sheared := by
  simp [reference, name]

/-- The full return affine operation evaluates the original linear map on every vector. -/
theorem return_apply (sheared : Bool) (x : A) : returnLinear sheared x = linearAction sheared x := rfl

/-- The original presentation has no face comparison to supply. -/
def comparison : geometry.TwoCell → A := fun f => nomatch f

/-- Every original face has matching linear words on the specified empty face type. -/
theorem linear_faces (sheared : Bool) (f : geometry.TwoCell) :
    (GroupExtension.pathValue geometry (reference sheared) (geometry.twoLeft f)).linear =
      (GroupExtension.pathValue geometry (reference sheared) (geometry.twoRight f)).linear := by
  exact f.elim

/-- Actual references generate strongness, full kernels and original transports for both choices. -/
noncomputable abbrev originalTower (sheared : Bool) :=
  NativeAffine.tower geometry (reference sheared) (reference sheared) comparison (linear_faces sheared)

end AAT.AG.RelativeRepairComposition.W3AffineInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3AffineInput
