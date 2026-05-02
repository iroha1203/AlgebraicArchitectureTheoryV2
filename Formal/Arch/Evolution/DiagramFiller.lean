import Formal.Arch.Evolution.ArchitecturePath
import Formal.Arch.AnalyticRepresentation

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

The selected semantic contract below tracks only rounding-order observations.
It is a bounded example: it does not claim global semantic completeness or
extractor completeness outside this selected diagram and witness.
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
  deriving DecidableEq, Repr

namespace CouponDiscountStep

/-- Selected observation code for the coupon/discount ordering example. -/
def roundingCode : {X Y : CouponState} -> CouponDiscountStep X Y -> Nat
  | _, _, applyCouponFirst => 1
  | _, _, applyDiscountAfterCoupon => 2
  | _, _, applyDiscountFirst => 3
  | _, _, applyCouponAfterDiscount => 4

end CouponDiscountStep

/-- Selected semantic observation of an operation path. -/
def roundingTrace :
    {X Y : CouponState} -> ArchitecturePath CouponDiscountStep X Y -> Nat
  | _, _, ArchitecturePath.nil _ => 0
  | _, _, ArchitecturePath.cons step rest =>
      CouponDiscountStep.roundingCode step + 10 * roundingTrace rest

/--
Selected independent-square contract for the coupon example: only swaps that
preserve the rounding observation for every suffix are allowed.
-/
def RoundingIndependentSquare
    (W X Y Z : CouponState)
    (a : CouponDiscountStep W X) (b : CouponDiscountStep X Z)
    (c : CouponDiscountStep W Y) (d : CouponDiscountStep Y Z) : Prop :=
  ∀ {T : CouponState} (rest : ArchitecturePath CouponDiscountStep Z T),
    roundingTrace (ArchitecturePath.cons a (ArchitecturePath.cons b rest)) =
      roundingTrace (ArchitecturePath.cons c (ArchitecturePath.cons d rest))

/-- Selected same-contract replacement: replacement must preserve observation. -/
def RoundingSameExternalContract
    (X Y : CouponState) (s t : CouponDiscountStep X Y) : Prop :=
  ∀ {Z : CouponState} (rest : ArchitecturePath CouponDiscountStep Y Z),
    roundingTrace (ArchitecturePath.cons s rest) =
      roundingTrace (ArchitecturePath.cons t rest)

/-- Selected repair fills are exactly those that preserve rounding observation. -/
def RoundingRepairFill
    (X Y : CouponState)
    (p q : ArchitecturePath CouponDiscountStep X Y) : Prop :=
  roundingTrace p = roundingTrace q

/-- The selected filler generators preserve the rounding observation. -/
theorem pathHomotopy_preserves_roundingTrace
    {X Y : CouponState} {p q : ArchitecturePath CouponDiscountStep X Y}
    (h :
      ArchitecturePath.PathHomotopy
        RoundingIndependentSquare RoundingSameExternalContract
        RoundingRepairFill p q) :
    roundingTrace p = roundingTrace q := by
  induction h with
  | refl p => rfl
  | symm _ ih => exact Eq.symm ih
  | trans _ _ ihLeft ihRight => exact Eq.trans ihLeft ihRight
  | swapIndependent a b c d rest hIndependent =>
      exact hIndependent rest
  | replaceBySameContract s t rest hSame =>
      exact hSame rest
  | repairFill hRepair =>
      exact hRepair

theorem couponThenDiscount_roundingTrace :
    roundingTrace couponThenDiscount = 21 :=
  rfl

theorem discountThenCoupon_roundingTrace :
    roundingTrace discountThenCoupon = 43 :=
  rfl

/--
The rounding-order witness refutes the selected filler: every selected filler
would preserve `roundingTrace`, but the two operation orders have different
selected observations.
-/
theorem roundingOrder_refutes_selectedDiagramFiller :
    ¬ DiagramFiller
      RoundingIndependentSquare RoundingSameExternalContract RoundingRepairFill
      couponDiscountDiagram := by
  intro hFiller
  have hTrace := pathHomotopy_preserves_roundingTrace hFiller
  change roundingTrace couponThenDiscount = roundingTrace discountThenCoupon at hTrace
  rw [couponThenDiscount_roundingTrace, discountThenCoupon_roundingTrace] at hTrace
  exact (by decide : (21 : Nat) ≠ 43) hTrace

/-- Concrete non-fillability witness for the selected coupon/discount diagram. -/
def roundingOrderNonFillabilityWitness :
    NonFillabilityWitness
      RoundingIndependentSquare RoundingSameExternalContract RoundingRepairFill
      couponDiscountDiagram CouponDiscountWitness where
  witness := CouponDiscountWitness.roundingOrder
  refutesFiller := by
    intro hFiller
    exact roundingOrder_refutes_selectedDiagramFiller hFiller

/-- The concrete witness is the selected `roundingOrder` witness. -/
theorem roundingOrder_nonFillabilityWitnessFor :
    NonFillabilityWitnessFor
      RoundingIndependentSquare RoundingSameExternalContract RoundingRepairFill
      couponDiscountDiagram CouponDiscountWitness.roundingOrder := by
  exact ⟨roundingOrderNonFillabilityWitness, rfl⟩

/-- Selected semantic residual for the coupon/discount diagram. -/
def roundingOrderResidual
    (D : ArchitectureDiagram CouponDiscountStep .start .finished) : Nat :=
  if roundingTrace D.lhs = roundingTrace D.rhs then 0 else 1

/-- Selected semantic obstruction tracked by the coupon/discount valuation. -/
def RoundingSemanticObstruction
    (D : ArchitectureDiagram CouponDiscountStep .start .finished)
    (w : CouponDiscountWitness) : Prop :=
  w = CouponDiscountWitness.roundingOrder ∧
    roundingTrace D.lhs ≠ roundingTrace D.rhs

/--
Selected valuation for the canonical coupon/discount example.

This valuation is witness-relative and records only the selected rounding-order
residual. It does not make claims about unmeasured semantic axes.
-/
def roundingOrderValuation :
    ObstructionValuation
      (ArchitectureDiagram CouponDiscountStep .start .finished)
      CouponDiscountWitness where
  obstruction := RoundingSemanticObstruction
  value := fun D _w => roundingOrderResidual D
  zeroReflectsAbsence := by
    intro D w hZero hObs
    rcases hObs with ⟨_hWitness, hNe⟩
    unfold roundingOrderResidual at hZero
    by_cases hEq : roundingTrace D.lhs = roundingTrace D.rhs
    · exact hNe hEq
    · rw [if_neg hEq] at hZero
      exact (by decide : (1 : Nat) ≠ 0) hZero
  obstructionGivesPositive := by
    intro D w hObs
    rcases hObs with ⟨_hWitness, hNe⟩
    unfold roundingOrderResidual
    by_cases hEq : roundingTrace D.lhs = roundingTrace D.rhs
    · exact False.elim (hNe hEq)
    · rw [if_neg hEq]
      decide
  coverageAssumptions := True
  nonConclusions := True

theorem couponDiscount_roundingOrderResidual_positive :
    0 < roundingOrderResidual couponDiscountDiagram := by
  unfold roundingOrderResidual
  change 0 < if roundingTrace couponThenDiscount =
    roundingTrace discountThenCoupon then 0 else 1
  rw [couponThenDiscount_roundingTrace, discountThenCoupon_roundingTrace]
  rw [if_neg (by decide : (21 : Nat) ≠ 43)]
  decide

theorem roundingOrderValuation_obstruction :
    roundingOrderValuation.obstruction
      couponDiscountDiagram CouponDiscountWitness.roundingOrder := by
  constructor
  · rfl
  · change roundingTrace couponThenDiscount ≠ roundingTrace discountThenCoupon
    rw [couponThenDiscount_roundingTrace, discountThenCoupon_roundingTrace]
    decide

theorem roundingOrderValuation_positive :
    0 < roundingOrderValuation.value
      couponDiscountDiagram CouponDiscountWitness.roundingOrder :=
  roundingOrderValuation.obstructionGivesPositive
    couponDiscountDiagram CouponDiscountWitness.roundingOrder
    roundingOrderValuation_obstruction

theorem roundingOrderValuation_recordsNonConclusions :
    ObstructionValuation.RecordsNonConclusions roundingOrderValuation := by
  trivial

end CouponDiscountExample

end Formal.Arch
