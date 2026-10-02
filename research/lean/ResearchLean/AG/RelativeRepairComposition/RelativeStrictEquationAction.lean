import ResearchLean.AG.RelativeRepairComposition.RelativeGeneratedStrictCover
import ResearchLean.AG.RelativeRepairComposition.StrictSupportedCover

/-!
# All native strict labels acting on arbitrary full local equations

## Implementation notes

Labels retain all original vertex values and literal shared-vertex agreement.
Their forbidden-edge coboundary condition is imposed independently of the
objects. The actual action is the full native local coboundary action.
-/
namespace AAT.AG.RelativeRepairComposition.RelativeStrictEquationAction
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA uI
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI}
variable (M : LocalCoefficients.{uG,uA} K) (U : I → ClosedRegion K) (P : ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))
local notation "forbidden" => (candidates \ allowed)
local notation "Labels" => StrictSupportedCover.Labels M P U candidates allowed

/-- Every full native strict label acts componentwise on all independent actual equations. -/
noncomputable def gauge (values : ∀ j, RelativeCover.C2 M (U j) P)
    (b : Labels) (h : RelativeGeneratedStrictCover.EquationObjects M U P values forbidden) :
    RelativeGeneratedStrictCover.EquationObjects M U P values forbidden :=
  ⟨fun j => Multiplicative.ofAdd (b.1 j).1 • (h.1 j),by
    constructor
    · intro j e he
      change (h.1 j).1.1 e + (RelativeCover.d0 M (U j) P (b.1 j).1).1 e = 0
      rw [h.2.1 j e he,(b.1 j).2 e he,add_zero]
    · intro j l e hj hl hlj
      have hd := congrArg (RelativeCover.d0 M (ClosedRegion.inter (U j) (U l)) P)
        (StrictSupportedCover.label_overlap M P U candidates allowed b j l)
      rw [← RelativeCover.r_d0,← RelativeCover.r_d0] at hd
      have hv := congrArg (fun c => c.1 ⟨e,⟨hj,hl⟩⟩) hd
      exact congrArg₂ (· + ·) (h.2.2 j l e hj hl hlj) hv⟩

/-- The full zero label fixes every actual local equation. -/
theorem gauge_zero (values : ∀ j, RelativeCover.C2 M (U j) P)
    (h : RelativeGeneratedStrictCover.EquationObjects M U P values forbidden) :
    gauge M U P candidates allowed values 0 h = h := by
  apply Subtype.ext
  funext j
  exact one_smul _ (h.1 j)

/-- Composing full strict labels adds every original label value. -/
theorem gauge_add (values : ∀ j, RelativeCover.C2 M (U j) P) (b c : Labels)
    (h : RelativeGeneratedStrictCover.EquationObjects M U P values forbidden) :
    gauge M U P candidates allowed values (b+c) h =
      gauge M U P candidates allowed values b (gauge M U P candidates allowed values c h) := by
  apply Subtype.ext
  funext j
  exact mul_smul (Multiplicative.ofAdd (b.1 j).1) (Multiplicative.ofAdd (c.1 j).1) (h.1 j)

/-- All independently permitted strict vertex labels remain in the native action. -/
noncomputable instance addAction (values : ∀ j, RelativeCover.C2 M (U j) P) :
    AddAction Labels (RelativeGeneratedStrictCover.EquationObjects M U P values forbidden) where
  vadd := gauge M U P candidates allowed values
  zero_vadd := gauge_zero M U P candidates allowed values
  add_vadd := gauge_add M U P candidates allowed values

/-- The full strict action reads the original local label and actual correction at every region. -/
theorem action_component (values : ∀ j, RelativeCover.C2 M (U j) P)
    (b : Multiplicative Labels) (h : RelativeGeneratedStrictCover.EquationObjects M U P values forbidden) (j : I) :
    (b • h).1 j = Multiplicative.ofAdd (b.toAdd.1 j).1 • (h.1 j) := rfl

end AAT.AG.RelativeRepairComposition.RelativeStrictEquationAction
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.RelativeStrictEquationAction
