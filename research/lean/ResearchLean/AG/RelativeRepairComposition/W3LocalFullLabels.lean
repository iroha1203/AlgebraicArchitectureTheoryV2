import ResearchLean.AG.RelativeRepairComposition.W3LocalOperationCoordinates
import ResearchLean.AG.RelativeRepairComposition.W3GaugeLabels

/-! # All original W3 local labels before taking stabilizers

At unrestricted permission both original patch vertices remain physically
free. Every original pair of whole A vectors is a permitted actual label.
The additive equivalences retain all 81 pairs on each one-edge patch.
-/
namespace AAT.AG.RelativeRepairComposition.W3LocalFullLabels
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs
open W3GaugeLabels W3LocalRepairs W3LocalLabels

/-- Arbitrary whole original source and target vectors restrict to a full actual patch label. -/
noncomputable def freeLabel (sheared : Bool) (U : ClosedRegion geometry) (bs bt : A) :
    LocalLabels sheared U candidates :=
  restrictAffineLabels U (reference sheared) (fixedEdges candidates) fixedRegion.vertices
    (unrestrictedLabel sheared bs bt)

/-- U's free source coordinate is the entire original s vector. -/
theorem left_source (sheared : Bool) (bs bt : A) :
    (freeLabel sheared leftRegion bs bt).1 leftS = bs := rfl
/-- U's free target coordinate is the entire original t vector. -/
theorem left_target (sheared : Bool) (bs bt : A) :
    (freeLabel sheared leftRegion bs bt).1 leftT = bt := rfl
/-- V's original s coordinate is the same whole original vector. -/
theorem right_source (sheared : Bool) (bs bt : A) :
    (freeLabel sheared rightRegion bs bt).1 rightS = bs := rfl
/-- V's original t coordinate is the same whole original vector. -/
theorem right_target (sheared : Bool) (bs bt : A) :
    (freeLabel sheared rightRegion bs bt).1 rightT = bt := rfl

/-- All actual unrestricted U labels and all of A² have both additive inverse coordinates. -/
noncomputable def leftFullLabelEquiv (sheared : Bool) :
    LocalLabels sheared leftRegion candidates ≃+ (A × A) where
  toFun b := (b.1 leftS,b.1 leftT)
  invFun b := freeLabel sheared leftRegion b.1 b.2
  left_inv b := by
    apply Subtype.ext
    funext v
    rcases v with ⟨v,hv⟩
    fin_cases v <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- All actual unrestricted V labels and all of A² have both additive inverse coordinates. -/
noncomputable def rightFullLabelEquiv (sheared : Bool) :
    LocalLabels sheared rightRegion candidates ≃+ (A × A) where
  toFun b := (b.1 rightS,b.1 rightT)
  invFun b := freeLabel sheared rightRegion b.1 b.2
  left_inv b := by
    apply Subtype.ext
    funext v
    rcases v with ⟨v,hv⟩
    fin_cases v <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Each original unrestricted U patch retains all 81 full vertex labels. -/
theorem left_label_card (sheared : Bool) :
    Nat.card (LocalLabels sheared leftRegion candidates) = 81 := by
  rw [Nat.card_congr (leftFullLabelEquiv sheared).toEquiv]
  simp [A, Nat.card_eq_fintype_card]

/-- Each original unrestricted V patch retains all 81 full vertex labels. -/
theorem right_label_card (sheared : Bool) :
    Nat.card (LocalLabels sheared rightRegion candidates) = 81 := by
  rw [Nat.card_congr (rightFullLabelEquiv sheared).toEquiv]
  simp [A, Nat.card_eq_fintype_card]

end AAT.AG.RelativeRepairComposition.W3LocalFullLabels
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3LocalFullLabels
