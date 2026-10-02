import ResearchLean.AG.RelativeRepairComposition.AffineEquation

/-!
# Full original-label action paired with supplemental translation

## Implementation notes

The original action is retained on its complete object carrier; the second
label translates the whole supplemental group. This native product action
serves the actual subdivision comparison. Taking effect quotients or selecting
zero supplemental representatives would discard original label arrows.
-/
namespace AAT.AG.RelativeRepairComposition.SupplementalAction
universe ug uy ur
variable {G : Type ug} {Y : Type uy} {R : Type ur}
variable [AddCommGroup G] [AddCommGroup R] [AddAction G Y]

/-- Full original labels and all supplemental labels act on their respective complete values. -/
instance productAddAction : AddAction (G × R) (Y × R) where
  vadd b y := (b.1 +ᵥ y.1,y.2 + b.2)
  zero_vadd y := Prod.ext (zero_vadd G y.1) (add_zero y.2)
  add_vadd b c y := by
    apply Prod.ext
    · exact add_vadd b.1 c.1 y.1
    · change y.2 + (b.2 + c.2) = (y.2 + c.2) + b.2
      abel

/-- The product action reads the full original action and the entire additive displacement. -/
theorem product_action_value (b : Multiplicative (G × R)) (y : Y × R) :
    b • y = (Multiplicative.ofAdd b.toAdd.1 • y.1,y.2 + b.toAdd.2) := rfl

end AAT.AG.RelativeRepairComposition.SupplementalAction
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.SupplementalAction
