import ResearchLean.AG.RelativeRepairComposition.W1PrivateMatrixZero
import ResearchLean.AG.RelativeRepairComposition.W1LocalEquationCriteria

/-!
# The independently generated full W1 public relations are the original laws

The original private matrices are zero on their entire spaces. Consequently
the generated cokernel projection preserves the whole local face value. Reading
the original public values therefore yields precisely u+z=x in U and u-z+v=y
in V, with all private kernel values retained by the same generator.
-/
namespace AAT.AG.RelativeRepairComposition.W1GeneratedRelations
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
open W1LocalDifferentials W1LocalEquationCriteria W1PrivateMatrixZero
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (x y : ZMod 3)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))
local notation "priv" j => ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j
local notation "D" j => FiniteNative.D (M) (bases true x y) (regions j) fixedRegion (priv j) (original_linear true x y)
local notation "rhs" j => RelativeCover.r2 (M) fixedRegion (ClosedRegion.to_all (regions j)) (-actualDefect true x y)

/-- Each independently generated private cokernel projection retains every whole original local face vector. -/
theorem projection_identity (j : Bool)
    (r : FiniteNative.Index2 (M) (bases true x y) (regions j) fixedRegion → ZMod 3) :
    LinearInterface.projection (D j) (W1LocalInterfaces.generatedSection x y j) r = r := by
  change r - (D j) (W1LocalInterfaces.generatedSection x y j r) = r
  rw [private_d_zero, LinearMap.zero_apply, sub_zero]

/-- The public original cochain reconstructs every full original public basis value before solving any face. -/
noncomputable def publicCochain (j : Bool)
    (z : FiniteNative.ZIndex (M) (bases true x y) (regions j) fixedRegion (priv j) → ZMod 3) :=
  (FiniteNative.edgeSplit (M) (bases true x y) (regions j) fixedRegion (priv j)).symm (0, z)

/-- The complete independently generated relation holds exactly when the restored original local cochain solves its actual authored face. -/
theorem relation_iff_equation (j : Bool)
    (z : FiniteNative.ZIndex (M) (bases true x y) (regions j) fixedRegion (priv j) → ZMod 3) :
    z ∈ W1LocalInterfaces.relation x y j ↔
      RelativeCover.d1 (M) (regions j) fixedRegion (publicCochain x y j z) = (rhs j) := by
  change LinearInterface.projection (D j) (W1LocalInterfaces.generatedSection x y j)
      (FiniteNative.F (M) (bases true x y) (regions j) fixedRegion (priv j) (original_linear true x y) z) =
    LinearInterface.projection (D j) (W1LocalInterfaces.generatedSection x y j)
      (FiniteNative.coordinate2 (M) (bases true x y) (regions j) fixedRegion (rhs j)) ↔ _
  rw [projection_identity, projection_identity]
  change FiniteNative.coordinate2 (M) (bases true x y) (regions j) fixedRegion
      (FiniteCoefficients.differential1 (M) (original_linear true x y) (regions j) fixedRegion
        (publicCochain x y j z)) =
    FiniteNative.coordinate2 (M) (bases true x y) (regions j) fixedRegion (rhs j) ↔ _
  rw [(FiniteNative.coordinate2 (M) (bases true x y) (regions j) fixedRegion).injective.eq_iff,
    FiniteCoefficients.differential1_eq]

/-- U's independently generated complete relation is the single original u+z=x equation. -/
theorem left_relation (z : FiniteNative.ZIndex (M) (bases true x y) (regions false) fixedRegion (priv false) → ZMod 3) :
    z ∈ W1LocalInterfaces.relation x y false ↔
      value x y leftRegion (publicCochain x y false z) ⟨name edgeE, Or.inl rfl⟩ +
        value x y leftRegion (publicCochain x y false z) ⟨name edgeB, Or.inr (Or.inl rfl)⟩ = x :=
  (relation_iff_equation x y false z).trans (left_equation_iff x y (publicCochain x y false z))

/-- V's independently generated complete relation is the original u-z+v=y equation, with no restriction on private h. -/
theorem right_relation (z : FiniteNative.ZIndex (M) (bases true x y) (regions true) fixedRegion (priv true) → ZMod 3) :
    z ∈ W1LocalInterfaces.relation x y true ↔
      value x y rightRegion (publicCochain x y true z) ⟨name edgeE, Or.inl rfl⟩ -
        value x y rightRegion (publicCochain x y true z) ⟨name edgeB, Or.inr (Or.inr (Or.inl rfl))⟩ +
          value x y rightRegion (publicCochain x y true z) ⟨name edgeC, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩ = y :=
  (relation_iff_equation x y true z).trans (right_equation_iff x y (publicCochain x y true z))

end AAT.AG.RelativeRepairComposition.W1GeneratedRelations
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1GeneratedRelations
