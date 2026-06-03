import Formal.Arch.AAT.GeneratedObject

namespace Formal.Arch
namespace AAT

universe u v

/--
AtomShape coordinate used by generated distance calculations.

This is intentionally an intrinsic shape coordinate. Observation metadata such
as source refs, confidence, or extractor boundary is not part of the distance.
-/
structure GeneratedAtomShapeCoordinate where
  family : AtomKind
  axis : Axis
  subjectName : String
  predicate : String
  direction : AtomDirection
  arity : Nat
  deriving DecidableEq, Repr

namespace GeneratedAtomShapeCoordinate

/-- Coordinate projection from an AtomShape. -/
def ofShape (shape : AtomShape) : GeneratedAtomShapeCoordinate where
  family := shape.family
  axis := shape.axis
  subjectName := shape.subject.name
  predicate := shape.predicate
  direction := shape.direction
  arity := shape.arity

/-- One component of a mismatch-count distance. -/
def mismatchBit {α : Type u} [DecidableEq α] (left right : α) : Nat :=
  if left = right then 0 else 1

/--
AtomShape coordinate distance used by generated layout and review surfaces.

This is a bounded mismatch count over intrinsic coordinates. It is not a
semantic equivalence theorem, causal distance, or extractor-completeness claim.
-/
def mismatchCount
    (left right : GeneratedAtomShapeCoordinate) : Nat :=
  mismatchBit left.family right.family +
  mismatchBit left.axis right.axis +
  mismatchBit left.subjectName right.subjectName +
  mismatchBit left.predicate right.predicate +
  mismatchBit left.direction right.direction +
  mismatchBit left.arity right.arity

/-- Stable component labels for the generated coordinate distance. -/
def componentLabels : List String :=
  ["family", "axis", "subject", "predicate", "direction", "arity"]

@[simp] theorem mismatchBit_self
    {α : Type u} [DecidableEq α] (value : α) :
    mismatchBit value value = 0 := by
  simp [mismatchBit]

@[simp] theorem mismatchCount_self
    (coordinate : GeneratedAtomShapeCoordinate) :
    mismatchCount coordinate coordinate = 0 := by
  simp [mismatchCount]

theorem mismatchCount_eq_zero_of_eq
    {left right : GeneratedAtomShapeCoordinate}
    (hEq : left = right) :
    mismatchCount left right = 0 := by
  cases hEq
  simp

end GeneratedAtomShapeCoordinate

namespace GeneratedArchitectureObject

/-- AtomShape coordinate generated for one carrier. -/
def generatedAtomShapeCoordinate
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (carrier : GeneratedCarrier object) :
    GeneratedAtomShapeCoordinate :=
  GeneratedAtomShapeCoordinate.ofShape
    (AtomShapeOf presentation carrier.val)

/-- Distance between two carriers, computed only from their generated AtomShape coordinates. -/
def generatedCarrierShapeDistance
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (left right : GeneratedCarrier object) : Nat :=
  GeneratedAtomShapeCoordinate.mismatchCount
    (object.generatedAtomShapeCoordinate left)
    (object.generatedAtomShapeCoordinate right)

/-- Generated carrier distance is zero on identical carriers. -/
theorem generatedCarrierShapeDistance_self
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (carrier : GeneratedCarrier object) :
    object.generatedCarrierShapeDistance carrier carrier = 0 := by
  simp [generatedCarrierShapeDistance, generatedAtomShapeCoordinate]

/-- Carrier distance unfolds to the AtomShape coordinate mismatch count. -/
theorem generatedCarrierShapeDistance_eq_coordinate_mismatchCount
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (left right : GeneratedCarrier object) :
    object.generatedCarrierShapeDistance left right =
      GeneratedAtomShapeCoordinate.mismatchCount
        (GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation left.val))
        (GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation right.val)) := by
  rfl

end GeneratedArchitectureObject

end AAT
end Formal.Arch
