import Formal.Arch.ArchitecturePath

namespace Formal.Arch

universe u v w

/--
A semantic architecture diagram is a pair of finite architecture paths with the
same endpoints.

The intended examples are operation-order diagrams such as coupon-before-
discount versus discount-before-coupon. The type records only the finite path
skeleton; concrete semantic equality, repair, or obstruction predicates are
supplied by the surrounding theorem package.
-/
structure ArchitectureDiagram {State : Type u}
    (Step : State -> State -> Type v) (X Y : State) : Type (max u v) where
  lhs : ArchitecturePath Step X Y
  rhs : ArchitecturePath Step X Y

/--
A filler for an architecture diagram is a generated homotopy between its two
paths.

The three predicate parameters are the same generators used by
`ArchitecturePath.PathHomotopy`: independent-step swaps, same-contract
replacement, and repair fills. This keeps diagram filling tied to the finite
path calculus without introducing higher-category machinery.
-/
def DiagramFiller {State : Type u} {Step : State -> State -> Type v}
    (IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop)
    (SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop)
    (RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop)
    {X Y : State} (D : ArchitectureDiagram Step X Y) : Prop :=
  ArchitecturePath.PathHomotopy (Step := Step)
    IndependentSquare SameExternalContract RepairFill D.lhs D.rhs

/--
A concrete non-fillability witness for a diagram.

The `witness` field is intentionally domain-specific data supplied by the
caller. The sound part of the witness is the constructive refutation of any
diagram filler. Bounded completeness is stated separately, relative to a finite
witness universe completeness premise, so it is not built into this definition.
-/
structure NonFillabilityWitness {State : Type u}
    {Step : State -> State -> Type v}
    (IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop)
    (SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop)
    (RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop)
    {X Y : State} (D : ArchitectureDiagram Step X Y)
    (Witness : Type w) : Type (max u v w) where
  witness : Witness
  refutesFiller :
    DiagramFiller IndependentSquare SameExternalContract RepairFill D -> False

/-- The witness record above is about the particular witness value `w`. -/
def NonFillabilityWitnessFor {State : Type u}
    {Step : State -> State -> Type v}
    (IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop)
    (SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop)
    (RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop)
    {X Y : State} (D : ArchitectureDiagram Step X Y)
    {Witness : Type w} (w : Witness) : Prop :=
  ∃ h : NonFillabilityWitness
      IndependentSquare SameExternalContract RepairFill D Witness,
    h.witness = w

/--
Soundness of non-fillability witnesses.

This is the safe direction: once a concrete witness refutes every filler, the
diagram is not fillable. The converse requires finite witness coverage and
exactness assumptions, represented by `WitnessUniverseComplete` below.
-/
theorem obstructionAsNonFillability_sound {State : Type u}
    {Step : State -> State -> Type v}
    {IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop}
    {SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop}
    {RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop}
    {X Y : State} {D : ArchitectureDiagram Step X Y}
    {Witness : Type w} {w : Witness}
    (hWitness :
      NonFillabilityWitnessFor
        IndependentSquare SameExternalContract RepairFill D w) :
    ¬ DiagramFiller IndependentSquare SameExternalContract RepairFill D := by
  intro hFiller
  rcases hWitness with ⟨h, _hEq⟩
  exact h.refutesFiller hFiller

/--
Bounded completeness premise for the converse theorem.

This definition is a named assumption, not a theorem: it says a finite witness
universe is complete enough to explain non-fillability of this diagram.
-/
def WitnessUniverseComplete {State : Type u}
    {Step : State -> State -> Type v}
    (IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop)
    (SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop)
    (RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop)
    {X Y : State} (D : ArchitectureDiagram Step X Y)
    {Witness : Type w} (U : List Witness) : Prop :=
  (¬ DiagramFiller IndependentSquare SameExternalContract RepairFill D) ->
    ∃ witness : Witness, witness ∈ U ∧
      NonFillabilityWitnessFor
        IndependentSquare SameExternalContract RepairFill D witness

/--
Bounded completeness of obstruction-as-non-fillability.

Under a finite witness-universe completeness premise, every non-fillable
diagram has a selected non-fillability witness in that universe. This theorem
does not assert global semantic completeness; all coverage is carried by
`WitnessUniverseComplete`.
-/
theorem obstructionAsNonFillability_complete_bounded {State : Type u}
    {Step : State -> State -> Type v}
    {IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop}
    {SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop}
    {RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop}
    {X Y : State} {D : ArchitectureDiagram Step X Y}
    {Witness : Type w} {U : List Witness}
    (hComplete :
      WitnessUniverseComplete
        IndependentSquare SameExternalContract RepairFill D U)
    (hNonfillable :
      ¬ DiagramFiller IndependentSquare SameExternalContract RepairFill D) :
    ∃ witness : Witness, witness ∈ U ∧
      NonFillabilityWitnessFor
        IndependentSquare SameExternalContract RepairFill D witness :=
  hComplete hNonfillable

/-
A small path skeleton for the canonical coupon/discount ordering example from
the design note.

No non-fillability theorem is asserted here. The example only exposes the two
operation orders as a diagram so later semantic contracts can attach a concrete
rounding-order witness.
-/
namespace CouponDiscountExample

inductive CouponState where
  | start
  | couponApplied
  | discountApplied
  | finished

inductive CouponDiscountStep : CouponState -> CouponState -> Type where
  | applyCouponFirst :
      CouponDiscountStep .start .couponApplied
  | applyDiscountAfterCoupon :
      CouponDiscountStep .couponApplied .finished
  | applyDiscountFirst :
      CouponDiscountStep .start .discountApplied
  | applyCouponAfterDiscount :
      CouponDiscountStep .discountApplied .finished

def couponThenDiscount :
    ArchitecturePath CouponDiscountStep .start .finished :=
  ArchitecturePath.cons CouponDiscountStep.applyCouponFirst
    (ArchitecturePath.cons CouponDiscountStep.applyDiscountAfterCoupon
      (ArchitecturePath.nil CouponState.finished))

def discountThenCoupon :
    ArchitecturePath CouponDiscountStep .start .finished :=
  ArchitecturePath.cons CouponDiscountStep.applyDiscountFirst
    (ArchitecturePath.cons CouponDiscountStep.applyCouponAfterDiscount
      (ArchitecturePath.nil CouponState.finished))

def couponDiscountDiagram :
    ArchitectureDiagram CouponDiscountStep .start .finished where
  lhs := couponThenDiscount
  rhs := discountThenCoupon

inductive CouponDiscountWitness where
  | roundingOrder

end CouponDiscountExample

end Formal.Arch
