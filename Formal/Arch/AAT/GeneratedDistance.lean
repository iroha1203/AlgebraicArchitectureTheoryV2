import Formal.Arch.AAT.GeneratedObject

namespace Formal.Arch
namespace AAT

universe u v

/--
AtomShape coordinate used by generated distance calculations.

This is intentionally an intrinsic shape coordinate. Measurement metadata such
as source refs or confidence is not part of the distance.
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
semantic equivalence theorem or causal distance.
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

theorem mismatchBit_eq_zero_iff
    {α : Type u} [DecidableEq α] (left right : α) :
    mismatchBit left right = 0 ↔ left = right := by
  by_cases hEq : left = right
  · simp [mismatchBit, hEq]
  · simp [mismatchBit, hEq]

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

theorem mismatchCount_eq_zero_iff
    {left right : GeneratedAtomShapeCoordinate} :
    mismatchCount left right = 0 ↔ left = right := by
  cases left
  cases right
  simp [mismatchCount, mismatchBit_eq_zero_iff]
  constructor
  · intro h
    rcases h with
      ⟨⟨⟨⟨⟨hFamily, hAxis⟩, hSubject⟩, hPredicate⟩,
        hDirection⟩, hArity⟩
    exact
      ⟨hFamily, hAxis, hSubject, hPredicate, hDirection, hArity⟩
  · intro h
    rcases h with
      ⟨hFamily, hAxis, hSubject, hPredicate, hDirection, hArity⟩
    exact
      ⟨⟨⟨⟨⟨hFamily, hAxis⟩, hSubject⟩, hPredicate⟩,
        hDirection⟩, hArity⟩

end GeneratedAtomShapeCoordinate

/--
Selected full-shape coordinate used by Part IV root-distance geometry.

`AtomShape` carries object slots, payload slots, valence, and semantic anchors
as predicates and structure.  A selected finite coordinate universe supplies
the selected footprints below.  This keeps root distance tied to Atom shape
without pretending that every slot or semantic coordinate has been globally
enumerated.
-/
structure GeneratedAtomFullShapeCoordinate where
  base : GeneratedAtomShapeCoordinate
  objectSlotFootprint : Nat
  payloadSlotFootprint : Nat
  valencePortFootprint : Nat
  requiredPortFootprint : Nat
  semanticAnchorName : String
  deriving DecidableEq, Repr

namespace GeneratedAtomFullShapeCoordinate

/-- Selected full-shape coordinate projection from an AtomShape. -/
def ofShapeWith
    (objectSlotFootprint : AtomShape -> Nat)
    (payloadSlotFootprint : AtomShape -> Nat)
    (valencePortFootprint : AtomShape -> Nat)
    (requiredPortFootprint : AtomShape -> Nat)
    (semanticAnchorName : AtomShape -> String)
    (shape : AtomShape) : GeneratedAtomFullShapeCoordinate where
  base := GeneratedAtomShapeCoordinate.ofShape shape
  objectSlotFootprint := objectSlotFootprint shape
  payloadSlotFootprint := payloadSlotFootprint shape
  valencePortFootprint := valencePortFootprint shape
  requiredPortFootprint := requiredPortFootprint shape
  semanticAnchorName := semanticAnchorName shape

/-- The legacy shape-coordinate component of a full-shape coordinate. -/
def baseMismatchCount
    (left right : GeneratedAtomFullShapeCoordinate) : Nat :=
  GeneratedAtomShapeCoordinate.mismatchCount left.base right.base

/-- Selected object-slot distance component. -/
def objectSlotMismatchCount
    (left right : GeneratedAtomFullShapeCoordinate) : Nat :=
  GeneratedAtomShapeCoordinate.mismatchBit
    left.objectSlotFootprint right.objectSlotFootprint

/-- Selected payload-slot distance component. -/
def payloadSlotMismatchCount
    (left right : GeneratedAtomFullShapeCoordinate) : Nat :=
  GeneratedAtomShapeCoordinate.mismatchBit
    left.payloadSlotFootprint right.payloadSlotFootprint

/-- Selected carrier slot distance component. -/
def carrierSlotMismatchCount
    (left right : GeneratedAtomFullShapeCoordinate) : Nat :=
  objectSlotMismatchCount left right + payloadSlotMismatchCount left right

/-- Selected valence distance component. -/
def valenceMismatchCount
    (left right : GeneratedAtomFullShapeCoordinate) : Nat :=
  GeneratedAtomShapeCoordinate.mismatchBit
    left.valencePortFootprint right.valencePortFootprint +
  GeneratedAtomShapeCoordinate.mismatchBit
    left.requiredPortFootprint right.requiredPortFootprint

/-- Selected semantic-anchor distance component. -/
def semanticAnchorMismatchCount
    (left right : GeneratedAtomFullShapeCoordinate) : Nat :=
  GeneratedAtomShapeCoordinate.mismatchBit
    left.semanticAnchorName right.semanticAnchorName

/--
Selected full-shape distance.

The value is a bounded diagnostic sum over selected AtomShape coordinates.  It
does not calibrate empirical semantic distance and does not generate atoms.
-/
def fullMismatchCount
    (left right : GeneratedAtomFullShapeCoordinate) : Nat :=
  baseMismatchCount left right +
    carrierSlotMismatchCount left right +
    valenceMismatchCount left right +
    semanticAnchorMismatchCount left right

/-- Stable labels for the full-shape distance components. -/
def fullComponentLabels : List String :=
  ["base", "objectSlots", "payloadSlots", "valencePorts",
    "requiredPorts", "semanticAnchor"]

@[simp] theorem objectSlotMismatchCount_self
    (coordinate : GeneratedAtomFullShapeCoordinate) :
    objectSlotMismatchCount coordinate coordinate = 0 := by
  simp [objectSlotMismatchCount, GeneratedAtomShapeCoordinate.mismatchBit]

@[simp] theorem payloadSlotMismatchCount_self
    (coordinate : GeneratedAtomFullShapeCoordinate) :
    payloadSlotMismatchCount coordinate coordinate = 0 := by
  simp [payloadSlotMismatchCount, GeneratedAtomShapeCoordinate.mismatchBit]

@[simp] theorem carrierSlotMismatchCount_self
    (coordinate : GeneratedAtomFullShapeCoordinate) :
    carrierSlotMismatchCount coordinate coordinate = 0 := by
  simp [carrierSlotMismatchCount]

@[simp] theorem valenceMismatchCount_self
    (coordinate : GeneratedAtomFullShapeCoordinate) :
    valenceMismatchCount coordinate coordinate = 0 := by
  simp [valenceMismatchCount, GeneratedAtomShapeCoordinate.mismatchBit]

@[simp] theorem semanticAnchorMismatchCount_self
    (coordinate : GeneratedAtomFullShapeCoordinate) :
    semanticAnchorMismatchCount coordinate coordinate = 0 := by
  simp [semanticAnchorMismatchCount,
    GeneratedAtomShapeCoordinate.mismatchBit]

@[simp] theorem fullMismatchCount_self
    (coordinate : GeneratedAtomFullShapeCoordinate) :
    fullMismatchCount coordinate coordinate = 0 := by
  simp [fullMismatchCount, baseMismatchCount]

theorem fullMismatchCount_eq_components
    (left right : GeneratedAtomFullShapeCoordinate) :
    fullMismatchCount left right =
      baseMismatchCount left right +
        carrierSlotMismatchCount left right +
        valenceMismatchCount left right +
        semanticAnchorMismatchCount left right := by
  rfl

end GeneratedAtomFullShapeCoordinate

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

/-- Selected full AtomShape coordinate generated for one carrier. -/
def generatedAtomFullShapeCoordinate
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (objectSlotFootprint : AtomShape -> Nat)
    (payloadSlotFootprint : AtomShape -> Nat)
    (valencePortFootprint : AtomShape -> Nat)
    (requiredPortFootprint : AtomShape -> Nat)
    (semanticAnchorName : AtomShape -> String)
    (carrier : GeneratedCarrier object) :
    GeneratedAtomFullShapeCoordinate :=
  GeneratedAtomFullShapeCoordinate.ofShapeWith
    objectSlotFootprint payloadSlotFootprint
    valencePortFootprint requiredPortFootprint semanticAnchorName
    (AtomShapeOf presentation carrier.val)

/-- Selected full-shape distance between two generated carriers. -/
def generatedCarrierFullShapeDistance
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (objectSlotFootprint : AtomShape -> Nat)
    (payloadSlotFootprint : AtomShape -> Nat)
    (valencePortFootprint : AtomShape -> Nat)
    (requiredPortFootprint : AtomShape -> Nat)
    (semanticAnchorName : AtomShape -> String)
    (left right : GeneratedCarrier object) : Nat :=
  GeneratedAtomFullShapeCoordinate.fullMismatchCount
    (object.generatedAtomFullShapeCoordinate
      objectSlotFootprint payloadSlotFootprint
      valencePortFootprint requiredPortFootprint semanticAnchorName left)
    (object.generatedAtomFullShapeCoordinate
      objectSlotFootprint payloadSlotFootprint
      valencePortFootprint requiredPortFootprint semanticAnchorName right)

/-- Selected carrier slot distance between two generated carriers. -/
def generatedCarrierSlotDistance
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (objectSlotFootprint : AtomShape -> Nat)
    (payloadSlotFootprint : AtomShape -> Nat)
    (valencePortFootprint : AtomShape -> Nat)
    (requiredPortFootprint : AtomShape -> Nat)
    (semanticAnchorName : AtomShape -> String)
    (left right : GeneratedCarrier object) : Nat :=
  GeneratedAtomFullShapeCoordinate.carrierSlotMismatchCount
    (object.generatedAtomFullShapeCoordinate
      objectSlotFootprint payloadSlotFootprint
      valencePortFootprint requiredPortFootprint semanticAnchorName left)
    (object.generatedAtomFullShapeCoordinate
      objectSlotFootprint payloadSlotFootprint
      valencePortFootprint requiredPortFootprint semanticAnchorName right)

/-- Selected valence distance between two generated carriers. -/
def generatedCarrierValenceDistance
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (objectSlotFootprint : AtomShape -> Nat)
    (payloadSlotFootprint : AtomShape -> Nat)
    (valencePortFootprint : AtomShape -> Nat)
    (requiredPortFootprint : AtomShape -> Nat)
    (semanticAnchorName : AtomShape -> String)
    (left right : GeneratedCarrier object) : Nat :=
  GeneratedAtomFullShapeCoordinate.valenceMismatchCount
    (object.generatedAtomFullShapeCoordinate
      objectSlotFootprint payloadSlotFootprint
      valencePortFootprint requiredPortFootprint semanticAnchorName left)
    (object.generatedAtomFullShapeCoordinate
      objectSlotFootprint payloadSlotFootprint
      valencePortFootprint requiredPortFootprint semanticAnchorName right)

/-- Selected semantic-anchor distance between two generated carriers. -/
def generatedCarrierSemanticAnchorDistance
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (objectSlotFootprint : AtomShape -> Nat)
    (payloadSlotFootprint : AtomShape -> Nat)
    (valencePortFootprint : AtomShape -> Nat)
    (requiredPortFootprint : AtomShape -> Nat)
    (semanticAnchorName : AtomShape -> String)
    (left right : GeneratedCarrier object) : Nat :=
  GeneratedAtomFullShapeCoordinate.semanticAnchorMismatchCount
    (object.generatedAtomFullShapeCoordinate
      objectSlotFootprint payloadSlotFootprint
      valencePortFootprint requiredPortFootprint semanticAnchorName left)
    (object.generatedAtomFullShapeCoordinate
      objectSlotFootprint payloadSlotFootprint
      valencePortFootprint requiredPortFootprint semanticAnchorName right)

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

/-- Full-shape carrier distance unfolds to the selected full coordinate mismatch. -/
theorem generatedCarrierFullShapeDistance_eq_full_mismatchCount
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (objectSlotFootprint : AtomShape -> Nat)
    (payloadSlotFootprint : AtomShape -> Nat)
    (valencePortFootprint : AtomShape -> Nat)
    (requiredPortFootprint : AtomShape -> Nat)
    (semanticAnchorName : AtomShape -> String)
    (left right : GeneratedCarrier object) :
    object.generatedCarrierFullShapeDistance
        objectSlotFootprint payloadSlotFootprint
        valencePortFootprint requiredPortFootprint semanticAnchorName
        left right =
      GeneratedAtomFullShapeCoordinate.fullMismatchCount
        (GeneratedAtomFullShapeCoordinate.ofShapeWith
          objectSlotFootprint payloadSlotFootprint
          valencePortFootprint requiredPortFootprint semanticAnchorName
          (AtomShapeOf presentation left.val))
        (GeneratedAtomFullShapeCoordinate.ofShapeWith
          objectSlotFootprint payloadSlotFootprint
          valencePortFootprint requiredPortFootprint semanticAnchorName
          (AtomShapeOf presentation right.val)) := by
  rfl

theorem generatedCarrierFullShapeDistance_self
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (objectSlotFootprint : AtomShape -> Nat)
    (payloadSlotFootprint : AtomShape -> Nat)
    (valencePortFootprint : AtomShape -> Nat)
    (requiredPortFootprint : AtomShape -> Nat)
    (semanticAnchorName : AtomShape -> String)
    (carrier : GeneratedCarrier object) :
    object.generatedCarrierFullShapeDistance
        objectSlotFootprint payloadSlotFootprint
        valencePortFootprint requiredPortFootprint semanticAnchorName
        carrier carrier = 0 := by
  simp [generatedCarrierFullShapeDistance, generatedAtomFullShapeCoordinate]

end GeneratedArchitectureObject

end AAT
end Formal.Arch
