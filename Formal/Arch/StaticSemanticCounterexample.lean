import Formal.Arch.FeatureExtensionExamples
import Formal.Arch.DiagramFiller
import Formal.Arch.Flatness

namespace Formal.Arch

/-
Canonical counterexample showing that static flatness does not eliminate a
selected semantic obstruction.

The static side reuses the repaired coupon feature extension: the hidden
dependency has been factored through the declared payment port, so the selected
static split package and a bounded `StaticFlatWithin` statement hold.  The
semantic side separately measures the coupon/discount order diagram, where the
selected rounding trace still differs.
-/
namespace StaticSemanticCounterexample

open CouponStaticDependencyExample

inductive SelectedCouponOrder where
  | couponThenDiscount
  | discountThenCoupon

def selectedCouponOrderPath :
    SelectedCouponOrder ->
      ArchitecturePath CouponDiscountExample.CouponDiscountStep
        CouponDiscountExample.CouponState.start
        CouponDiscountExample.CouponState.finished
  | .couponThenDiscount => CouponDiscountExample.couponThenDiscount
  | .discountThenCoupon => CouponDiscountExample.discountThenCoupon

def selectedCouponOrderSemantics : Semantics SelectedCouponOrder Nat where
  eval := fun order =>
    CouponDiscountExample.roundingTrace (selectedCouponOrderPath order)

def selectedCouponDiscountDiagram : RequiredDiagram SelectedCouponOrder where
  lhs := .couponThenDiscount
  rhs := .discountThenCoupon

def measuredSemanticDiagrams : List (RequiredDiagram SelectedCouponOrder) :=
  [selectedCouponDiscountDiagram]

def selectedCouponDiscountRequired
    (D : RequiredDiagram SelectedCouponOrder) : Prop :=
  D = selectedCouponDiscountDiagram

theorem selectedCouponDiscount_semanticCoverage :
    CoversRequired selectedCouponDiscountRequired measuredSemanticDiagrams := by
  intro D hRequired
  cases hRequired
  simp [measuredSemanticDiagrams]

theorem selectedCouponDiscount_not_commutes :
    ¬ DiagramCommutes selectedCouponOrderSemantics
      selectedCouponDiscountDiagram := by
  intro hCommutes
  have hTrace :
      CouponDiscountExample.roundingTrace
          CouponDiscountExample.couponThenDiscount =
        CouponDiscountExample.roundingTrace
          CouponDiscountExample.discountThenCoupon := by
    simpa [DiagramCommutes, selectedCouponOrderSemantics,
      selectedCouponDiscountDiagram, selectedCouponOrderPath] using hCommutes
  rw [CouponDiscountExample.couponThenDiscount_roundingTrace,
    CouponDiscountExample.discountThenCoupon_roundingTrace] at hTrace
  exact (by decide : (21 : Nat) ≠ 43) hTrace

def allExtendedComponents : List ExtendedComponent :=
  [ .paymentApi
  , .paymentAdapter
  , .internalCache
  , .couponService
  , .declaredPaymentPort
  ]

theorem allExtendedComponents_nodup : allExtendedComponents.Nodup := by
  decide

theorem mem_allExtendedComponents (c : ExtendedComponent) :
    c ∈ allExtendedComponents := by
  cases c <;> simp [allExtendedComponents]

def repairedUniverse : ComponentUniverse repairedGraph :=
  ComponentUniverse.full repairedGraph allExtendedComponents
    allExtendedComponents_nodup mem_allExtendedComponents

def repairedLayer : Layering ExtendedComponent
  | .paymentApi => 0
  | .paymentAdapter => 0
  | .internalCache => 0
  | .declaredPaymentPort => 1
  | .couponService => 2

theorem repaired_strictLayering :
    StrictLayering repairedGraph repairedLayer := by
  intro src dst hEdge
  cases hEdge <;> decide

theorem repaired_walkAcyclic : WalkAcyclic repairedGraph :=
  walkAcyclic_of_acyclic
    (acyclic_of_strictLayering repaired_strictLayering)

def trivialProjection : InterfaceProjection ExtendedComponent Unit where
  expose := fun _ => ()

def trivialAbstractGraph : AbstractGraph Unit where
  edge := fun _ _ => True

def trivialStaticObservation : Observation ExtendedComponent Unit where
  observe := fun _ => ()

def emptyRuntimeGraph : RuntimeDependencyGraph ExtendedComponent where
  edge := fun _ _ => False

def canonicalFlatnessModel :
    ArchitectureFlatnessModel ExtendedComponent Unit Unit
      SelectedCouponOrder Nat where
  static := repairedGraph
  runtime := emptyRuntimeGraph
  projection := trivialProjection
  abstractStatic := trivialAbstractGraph
  staticObservation := trivialStaticObservation
  boundaryAllowed := fun _ _ => True
  abstractionAllowed := fun _ _ => True
  runtimeAllowed := fun _ _ => True
  semantic := selectedCouponOrderSemantics
  requiredSemantic := selectedCouponDiscountRequired
  measuredSemantic := measuredSemanticDiagrams

theorem repaired_staticSplit :
    SelectedStaticSplitExtension repairedExtension declaredInterface
      coreAllowedStaticEdge extendedAllowedStaticEdge :=
  repaired_selectedStaticSplitFeatureExtension

theorem canonical_staticFlatWithin :
    StaticFlatWithin canonicalFlatnessModel repairedUniverse := by
  refine ⟨repaired_walkAcyclic, ?_, ?_, ?_, ?_⟩
  · intro src dst _hEdge
    trivial
  · intro src dst _hSame
    rfl
  · intro src dst _hEdge
    trivial
  · intro src dst _hEdge
    trivial

theorem canonical_not_semanticFlatWithin :
    ¬ SemanticFlatWithin canonicalFlatnessModel := by
  intro hSemanticFlat
  have hCommutes :
      DiagramCommutes selectedCouponOrderSemantics
        selectedCouponDiscountDiagram := by
    exact hSemanticFlat selectedCouponDiscountDiagram
      (by
        simp [canonicalFlatnessModel, measuredSemanticDiagrams,
          RequiredDiagramsByList, RequiredByList])
  exact selectedCouponDiscount_not_commutes hCommutes

theorem canonical_not_architectureFlatWithin :
    ¬ ArchitectureFlatWithin canonicalFlatnessModel repairedUniverse := by
  intro hFlat
  exact canonical_not_semanticFlatWithin
    (semanticFlatWithin_of_architectureFlatWithin hFlat)

theorem canonical_not_architectureFlat :
    ¬ ArchitectureFlat canonicalFlatnessModel := by
  intro hFlat
  rcases hFlat with ⟨certificate⟩
  exact canonical_not_semanticFlatWithin
    (semanticFlatWithin_of_architectureFlatWithin certificate.flatWithin)

theorem staticFlat_with_semanticObstruction :
    StaticFlatWithin canonicalFlatnessModel repairedUniverse ∧
      ¬ SemanticFlatWithin canonicalFlatnessModel :=
  ⟨canonical_staticFlatWithin, canonical_not_semanticFlatWithin⟩

theorem staticFlat_not_architectureFlat :
    StaticFlatWithin canonicalFlatnessModel repairedUniverse ∧
      ¬ ArchitectureFlat canonicalFlatnessModel :=
  ⟨canonical_staticFlatWithin, canonical_not_architectureFlat⟩

end StaticSemanticCounterexample

end Formal.Arch
