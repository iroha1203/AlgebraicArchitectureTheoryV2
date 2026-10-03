import ResearchLean.AG.RelativeRepairComposition.W1LocalPublicValues

/-!
# Reusing the complete original W1 public generator for all x,y

The actual full original differential is read on every public basis value,
with no rhs or permission argument. Its entire F matrix and projected public
matrix coincide with the single generator at (0,0).
-/
namespace AAT.AG.RelativeRepairComposition.W1SymbolicPublicStructure
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
open W1LocalInterfaces W1LocalDifferentials W1GeneratedRelations W1LocalPublicValues
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (x y : ZMod 3)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))
local notation "priv" j => ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j

/-- The shared original e index is public in each complete original patch. -/
def eIndex (j : Bool) : FiniteNative.ZIndex (M) (bases true x y) (regions j) fixedRegion (priv j) :=
  publicIndex x y j ⟨name edgeE, by cases j <;> exact Or.inl rfl⟩
    (by simp [fixedRegion, geometry, name, edgeE, edgeB, edgeC, edgeRx, edgeRy]) (shared_e_public j)

/-- The original candidate b index is public in each complete original patch. -/
def bIndex (j : Bool) : FiniteNative.ZIndex (M) (bases true x y) (regions j) fixedRegion (priv j) :=
  publicIndex x y j ⟨name edgeB, by cases j; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr (Or.inl rfl))⟩
    (by simp [fixedRegion, geometry, name, edgeE, edgeB, edgeC, edgeRx, edgeRy]) (candidates_public j ⟨name edgeB, Or.inl rfl⟩)

/-- V's complete original c index is retained by the public generator. -/
def cIndex : FiniteNative.ZIndex (M) (bases true x y) (regions true) fixedRegion (priv true) :=
  publicIndex x y true ⟨name edgeC, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    (by simp [fixedRegion, geometry, name, edgeE, edgeB, edgeC, edgeRx, edgeRy]) (candidates_public true ⟨name edgeC, Or.inr rfl⟩)

/-- The entire U public face map evaluates its original e,b coordinates. -/
theorem left_public (z : FiniteNative.ZIndex (M) (bases true x y) (regions false) fixedRegion (priv false) → ZMod 3) :
    FiniteNative.F (M) (bases true x y) (regions false) fixedRegion (priv false) (original_linear true x y) z
      ⟨⟨false, rfl, fun h => h.elim⟩, basisIndex true x y ()⟩ =
      z (eIndex x y false) + z (bIndex x y false) := by
  rw [FiniteNative.F, LinearMap.comp_apply, LinearMap.inr_apply, FiniteNative.faceMap_apply]
  rw [FiniteCoefficients.differential1_eq]
  change kernelCoordinate true x y ()
    ((RelativeCover.d1 (M) leftRegion fixedRegion (publicCochain x y false z)).1 ⟨false,rfl⟩) = _
  rw [left_differential]
  have he := public_value x y false z ⟨name edgeE, Or.inl rfl⟩
    (by simp [fixedRegion, geometry, name, edgeE, edgeRx, edgeRy]) (shared_e_public false)
  have hb := public_value x y false z ⟨name edgeB, Or.inr (Or.inl rfl)⟩
    (by simp [fixedRegion, geometry, name, edgeB, edgeRx, edgeRy])
    (candidates_public false ⟨name edgeB, Or.inl rfl⟩)
  change value x y leftRegion (publicCochain x y false z) ⟨name edgeE, Or.inl rfl⟩ = z (eIndex x y false) at he
  change value x y leftRegion (publicCochain x y false z) ⟨name edgeB, Or.inr (Or.inl rfl)⟩ = z (bIndex x y false) at hb
  rw [he,hb]

/-- The entire V public face map evaluates its original e,b,c coordinates. -/
theorem right_public (z : FiniteNative.ZIndex (M) (bases true x y) (regions true) fixedRegion (priv true) → ZMod 3) :
    FiniteNative.F (M) (bases true x y) (regions true) fixedRegion (priv true) (original_linear true x y) z
      ⟨⟨true, rfl, fun h => h.elim⟩, basisIndex true x y ()⟩ =
      z (eIndex x y true) - z (bIndex x y true) + z (cIndex x y) := by
  rw [FiniteNative.F, LinearMap.comp_apply, LinearMap.inr_apply, FiniteNative.faceMap_apply]
  rw [FiniteCoefficients.differential1_eq]
  change kernelCoordinate true x y ()
    ((RelativeCover.d1 (M) rightRegion fixedRegion (publicCochain x y true z)).1 ⟨true,rfl⟩) = _
  rw [right_differential]
  have he := public_value x y true z ⟨name edgeE, Or.inl rfl⟩
    (by simp [fixedRegion, geometry, name, edgeE, edgeRx, edgeRy]) (shared_e_public true)
  have hb := public_value x y true z ⟨name edgeB, Or.inr (Or.inr (Or.inl rfl))⟩
    (by simp [fixedRegion, geometry, name, edgeB, edgeRx, edgeRy])
    (candidates_public true ⟨name edgeB, Or.inl rfl⟩)
  have hc := public_value x y true z ⟨name edgeC, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    (by simp [fixedRegion, geometry, name, edgeC, edgeRx, edgeRy])
    (candidates_public true ⟨name edgeC, Or.inr rfl⟩)
  change value x y rightRegion (publicCochain x y true z) ⟨name edgeE, Or.inl rfl⟩ = z (eIndex x y true) at he
  change value x y rightRegion (publicCochain x y true z) ⟨name edgeB, Or.inr (Or.inr (Or.inl rfl))⟩ = z (bIndex x y true) at hb
  change value x y rightRegion (publicCochain x y true z) ⟨name edgeC, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩ = z (cIndex x y) at hc
  rw [he,hb,hc]

end AAT.AG.RelativeRepairComposition.W1SymbolicPublicStructure
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SymbolicPublicStructure
