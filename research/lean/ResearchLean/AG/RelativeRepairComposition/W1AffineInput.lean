import ResearchLean.AG.RelativeRepairComposition.NativeAffineRepairs
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCoefficients
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# W1's original six-edge full affine input

## Implementation notes

The two temporal paths keep the original named operations: b,e and
c,a,b,a,e, respectively. Their right sides are the physically fixed rx,ry.
The entire affine group, rather than its translation subgroup, supplies every
original operation. The identity-linear comparison changes only a's linear
part on this same presentation and keeps both candidate names and permissions.
-/
namespace AAT.AG.RelativeRepairComposition.W1AffineInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine

/-- F3 is the specified coefficient field, from the arithmetic prime-three theorem. -/
instance primeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Original always edge e, retaining its own name in the complete six-loop presentation. -/
def edgeE : Fin 6 := 0
/-- Original always edge a; both authored appearances use this same name. -/
def edgeA : Fin 6 := 1
/-- Original candidate b, whose correction is transported by a between its appearances. -/
def edgeB : Fin 6 := 2
/-- Original candidate c, separate from the always edge e. -/
def edgeC : Fin 6 := 3
/-- The physically fixed original input operation rx. -/
def edgeRx : Fin 6 := 4
/-- The physically fixed original input operation ry. -/
def edgeRy : Fin 6 := 5

/-- The specified W1 geometry has all six original loops, both Laws and no three-cell. -/
def geometry : FiniteTransportPresentation where
  Vertex := Unit
  vertexFintype := inferInstance
  Edge := fun _ _ => Fin 6
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Bool
  twoCellFintype := inferInstance
  twoSource := fun _ => ()
  twoTarget := fun _ => ()
  twoLeft := fun f => if f then
    .cons (i := ()) (j := ()) edgeC
      (.cons (i := ()) (j := ()) edgeA
        (.cons (i := ()) (j := ()) edgeB
          (.cons (i := ()) (j := ()) edgeA
            (.cons (i := ()) (j := ()) edgeE (.nil ())))))
    else .cons (i := ()) (j := ()) edgeB
      (.cons (i := ()) (j := ()) edgeE (.nil ()))
  twoRight := fun f => .cons (i := ()) (j := ()) (if f then edgeRy else edgeRx) (.nil ())
  ThreeCell := Empty
  threeCellFintype := inferInstance
  threeSource := fun t => nomatch t
  threeTarget := fun t => nomatch t
  threeStart := fun t => nomatch t
  threeFinish := fun t => nomatch t
  threeLeft := fun t => nomatch t
  threeRight := fun t => nomatch t

/-- Original named-loop equality is the complete finite-six equality. -/
instance edgeDecidableEq (i j : geometry.Vertex) : DecidableEq (geometry.Edge i j) :=
  inferInstanceAs (DecidableEq (Fin 6))

/-- Authored face equality is the complete two-face equality. -/
instance faceDecidableEq : DecidableEq geometry.TwoCell := inferInstanceAs (DecidableEq Bool)

/-- W1 uses the entire native group of invertible affine operations on F3. -/
abbrev Op := Operations (ZMod 3) (ZMod 3)

/-- The original negative-linear operation is the whole affine negation. -/
noncomputable def flip : Op := (LinearEquiv.neg (ZMod 3) : ZMod 3 ≃ₗ[ZMod 3] ZMod 3).toAffineEquiv

/-- The negative-linear operation evaluates on every original field point. -/
theorem flip_apply (t : ZMod 3) : flip t = -t := rfl

/-- Two visits to the same uncorrected negative-linear operation compose to identity. -/
theorem flip_square : flip * flip = (1 : Op) := by
  ext t
  change -(-t) = t
  exact neg_neg t

/-- The comparison changes only the original a linear part on the same named geometry. -/
noncomputable def linearA (negative : Bool) : Op := if negative then flip else 1

/-- Both prescribed linear choices square to the same identity operation. -/
theorem linearA_square (negative : Bool) : linearA negative * linearA negative = (1 : Op) := by
  cases negative <;> simp [linearA, flip_square]

/-- Original references keep rx and ry as their actual input translations and a as its selected linear operation. -/
noncomputable def reference (negative : Bool) (x y : ZMod 3) :
    ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op :=
  fun e => if (e : Fin 6) = edgeA then linearA negative
    else if (e : Fin 6) = edgeRx then translation (k := ZMod 3) x
    else if (e : Fin 6) = edgeRy then translation (k := ZMod 3) y else 1

/-- Both designated comparisons are identity translations on these same original authored faces. -/
def comparison : geometry.TwoCell → ZMod 3 := fun _ => 0

/-- The uncorrected left reference words compose to identity for every input and either linear choice. -/
theorem reference_left_path (negative : Bool) (x y : ZMod 3) (f : geometry.TwoCell) :
    GroupExtension.pathValue geometry (reference negative x y) (geometry.twoLeft f) = 1 := by
  cases f <;> simp [geometry, GroupExtension.pathValue, reference,
    edgeE, edgeA, edgeB, edgeC, edgeRx, edgeRy, linearA_square]

/-- The uncorrected right words are precisely the physically fixed original input operations. -/
theorem reference_right_path (negative : Bool) (x y : ZMod 3) (f : geometry.TwoCell) :
    GroupExtension.pathValue geometry (reference negative x y) (geometry.twoRight f) =
      translation (k := ZMod 3) (if (f : Bool) = true then y else x) := by
  cases f <;> simp [geometry, GroupExtension.pathValue, reference,
    edgeE, edgeA, edgeB, edgeC, edgeRx, edgeRy]

/-- Every authored face retains equal original linear path components, for all x,y and both a choices. -/
theorem linear_faces (negative : Bool) (x y : ZMod 3) (f : geometry.TwoCell) :
    (GroupExtension.pathValue geometry (reference negative x y) (geometry.twoLeft f)).linear =
      (GroupExtension.pathValue geometry (reference negative x y) (geometry.twoRight f)).linear := by
  rw [reference_left_path, reference_right_path]
  rfl

/-- The same original six-edge operations supply the full native affine tower with generated strongness and full kernels. -/
noncomputable abbrev originalTower (negative : Bool) (x y : ZMod 3) :=
  NativeAffine.tower geometry (reference negative x y) (reference negative x y)
    comparison (linear_faces negative x y)

end AAT.AG.RelativeRepairComposition.W1AffineInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1AffineInput
