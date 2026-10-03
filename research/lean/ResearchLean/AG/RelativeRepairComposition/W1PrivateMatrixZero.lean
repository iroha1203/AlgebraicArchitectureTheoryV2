import ResearchLean.AG.RelativeRepairComposition.W1LocalDifferentials

/-!
# The complete W1 private matrices vanish on their full original spaces

U has no private edge. In V the full a column is zero because its two original
occurrences cancel. Public values are read independently from the exact original
split cochain. The complete private kernel is therefore retained by generation.
-/
namespace AAT.AG.RelativeRepairComposition.W1PrivateMatrixZero
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
open W1LocalDifferentials
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (x y : ZMod 3)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))
local notation "priv" j => ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j

/-- Every zero-public restored original value is zero at its same full nonprivate nonfixed edge. -/
theorem zero_public_value (j : Bool)
    (a : FiniteNative.XIndex (M) (bases true x y) (regions j) fixedRegion (priv j) → ZMod 3)
    (e : (regions j).edges) (hp : e.1 ∉ fixedRegion.edges) (hi : e.1 ∉ priv j) :
    value x y (regions j)
      ((FiniteNative.edgeSplit (M) (bases true x y) (regions j) fixedRegion (priv j)).symm (a, 0)) e = 0 := by
  rw [value, FiniteNative.public_edge_value (M) (bases true x y) (regions j) fixedRegion (priv j) a 0 e hp hi]
  change kernelCoordinate true x y e.1.2.1
    (((bases true x y).coordinate e.1.2.1).symm (0 : Fin ((bases true x y).dimension e.1.2.1) → ZMod 3)) = 0
  rw [map_zero, map_zero]

/-- The independently computed whole private D vanishes for both original patches and all private coordinate vectors. -/
theorem private_d_zero (j : Bool) :
    FiniteNative.D (M) (bases true x y) (regions j) fixedRegion (priv j) (original_linear true x y) = 0 := by
  apply LinearMap.ext
  intro a
  change FiniteNative.coordinate2 (M) (bases true x y) (regions j) fixedRegion
    (FiniteCoefficients.differential1 (M) (original_linear true x y) (regions j) fixedRegion
      ((FiniteNative.edgeSplit (M) (bases true x y) (regions j) fixedRegion (priv j)).symm (a, 0))) = 0
  rw [← map_zero (FiniteNative.coordinate2 (M) (bases true x y) (regions j) fixedRegion)]
  apply congrArg (FiniteNative.coordinate2 (M) (bases true x y) (regions j) fixedRegion)
  rw [FiniteCoefficients.differential1_eq]
  apply Subtype.ext
  funext f
  apply (kernelCoordinate true x y ()).injective
  cases j
  · rcases f with ⟨f, hf⟩
    have hf' : (f : Bool) = false := hf
    subst f
    let h := (FiniteNative.edgeSplit (M) (bases true x y) (regions false) fixedRegion (priv false)).symm (a, 0)
    have hv := left_differential x y h
    have h0 := zero_public_value x y false a ⟨name edgeE, Or.inl rfl⟩ (by simp [fixedRegion, geometry, name, edgeE, edgeRx, edgeRy]) (by rw [private_left]; simp)
    change value x y leftRegion h ⟨name edgeE, Or.inl rfl⟩ = 0 at h0
    have h1 := zero_public_value x y false a ⟨name edgeB, Or.inr (Or.inl rfl)⟩ (by simp [fixedRegion, geometry, name, edgeB, edgeRx, edgeRy]) (by rw [private_left]; simp)
    change value x y leftRegion h ⟨name edgeB, Or.inr (Or.inl rfl)⟩ = 0 at h1
    rw [h0, h1] at hv
    have hz : kernelCoordinate true x y ()
        ((0 : RelativeCover.C2 (M) (regions false) fixedRegion).1 ⟨false, rfl⟩) = 0 :=
      map_zero (kernelCoordinate true x y ())
    exact hv.trans hz.symm
  · rcases f with ⟨f, hf⟩
    have hf' : (f : Bool) = true := hf
    subst f
    let h := (FiniteNative.edgeSplit (M) (bases true x y) (regions true) fixedRegion (priv true)).symm (a, 0)
    have hv := right_differential x y h
    have h0 := zero_public_value x y true a ⟨name edgeE, Or.inl rfl⟩ (by simp [fixedRegion, geometry, name, edgeE, edgeRx, edgeRy]) (by rw [private_right]; simp [geometry, name, edgeE, edgeA])
    change value x y rightRegion h ⟨name edgeE, Or.inl rfl⟩ = 0 at h0
    have h1 := zero_public_value x y true a ⟨name edgeB, Or.inr (Or.inr (Or.inl rfl))⟩ (by simp [fixedRegion, geometry, name, edgeB, edgeRx, edgeRy]) (by rw [private_right]; simp [geometry, name, edgeB, edgeA])
    change value x y rightRegion h ⟨name edgeB, Or.inr (Or.inr (Or.inl rfl))⟩ = 0 at h1
    have h2 := zero_public_value x y true a ⟨name edgeC, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩ (by simp [fixedRegion, geometry, name, edgeC, edgeRx, edgeRy]) (by rw [private_right]; simp [geometry, name, edgeC, edgeA])
    change value x y rightRegion h ⟨name edgeC, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩ = 0 at h2
    rw [h0, h1, h2] at hv
    have hz : kernelCoordinate true x y ()
        ((0 : RelativeCover.C2 (M) (regions true) fixedRegion).1 ⟨true, rfl⟩) = 0 :=
      map_zero (kernelCoordinate true x y ())
    exact hv.trans hz.symm

/-- The whole actual private kernel equals its entire original coordinate space, without selecting a representative h. -/
theorem private_kernel_top (j : Bool) :
    LinearMap.ker (FiniteNative.D (M) (bases true x y) (regions j) fixedRegion (priv j) (original_linear true x y)) = ⊤ := by
  rw [private_d_zero]
  exact LinearMap.ker_zero

/-- The generated private matrix is exactly zero on every full original column. -/
theorem private_matrix_zero (j : Bool) : W1LocalInterfaces.privateMatrix x y j = 0 := by
  unfold W1LocalInterfaces.privateMatrix FiniteNative.Dmatrix
  rw [private_d_zero]
  exact map_zero LinearMap.toMatrix'

end AAT.AG.RelativeRepairComposition.W1PrivateMatrixZero
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1PrivateMatrixZero
