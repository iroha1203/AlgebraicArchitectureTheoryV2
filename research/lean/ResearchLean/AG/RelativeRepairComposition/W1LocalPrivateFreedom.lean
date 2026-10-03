import ResearchLean.AG.RelativeRepairComposition.W1LocalPublicValues

/-!
# The whole original private h retained by the independent V generator

U has no private coordinate. V has exactly the complete original a basis
coordinate. The whole private kernel is the whole coordinate space, and its
arbitrary scalar value restores the actual full original a kernel correction.
-/
namespace AAT.AG.RelativeRepairComposition.W1LocalPrivateFreedom
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
open W1LocalDifferentials W1PrivateMatrixZero
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
variable (x y : ZMod 3)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))
local notation "priv" j => ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j

/-- The original U generator has no private coordinate to eliminate. -/
theorem left_private_empty (i : FiniteNative.XIndex (M) (bases true x y) (regions false) fixedRegion (priv false)) : False := by
  rcases i with ⟨⟨⟨e,hu,hp⟩,n⟩,hi⟩
  change e ∈ (priv false) at hi
  rw [private_left] at hi
  exact hi

/-- V retains the complete original a basis coordinate as its private index. -/
def aIndex : FiniteNative.XIndex (M) (bases true x y) (regions true) fixedRegion (priv true) :=
  ⟨⟨⟨name edgeA, Or.inr (Or.inl rfl),
    by simp [fixedRegion,geometry,name,edgeA,edgeRx,edgeRy]⟩,basisIndex true x y ()⟩,
    by rw [private_right]; exact rfl⟩

/-- Every private V coordinate is this same complete original a basis component. -/
theorem aIndex_unique (i : FiniteNative.XIndex (M) (bases true x y) (regions true) fixedRegion (priv true)) : i = aIndex x y := by
  rcases i with ⟨⟨⟨e,hu,hp⟩,n⟩,hi⟩
  have he : e = name edgeA := by change e ∈ (priv true) at hi; rw [private_right] at hi; exact hi
  subst e
  change Fin 1 at n
  have hn : n = (0 : Fin 1) := Subsingleton.elim _ _
  subst n
  rfl

/-- The independent private kernel contains every complete original h vector. -/
theorem private_h_mem (h : ZMod 3) :
    (fun _ : FiniteNative.XIndex (M) (bases true x y) (regions true) fixedRegion (priv true) => h) ∈
      LinearMap.ker (FiniteNative.D (M) (bases true x y) (regions true) fixedRegion (priv true) (original_linear true x y)) := by
  rw [private_kernel_top]
  exact Submodule.mem_top

/-- Every whole private-kernel vector is exactly its arbitrary full original a value. -/
theorem private_vector_complete
    (a : FiniteNative.XIndex (M) (bases true x y) (regions true) fixedRegion (priv true) → ZMod 3) :
    a = fun _ => a (aIndex x y) := by
  funext i
  rw [aIndex_unique x y i]

/-- Restoring arbitrary full private and public vectors reads the exact whole original h value at a. -/
theorem restored_a_value
    (a : FiniteNative.XIndex (M) (bases true x y) (regions true) fixedRegion (priv true) → ZMod 3)
    (z : FiniteNative.ZIndex (M) (bases true x y) (regions true) fixedRegion (priv true) → ZMod 3) :
    value x y rightRegion
      ((FiniteNative.edgeSplit (M) (bases true x y) (regions true) fixedRegion (priv true)).symm (a,z))
      ⟨name edgeA,Or.inr (Or.inl rfl)⟩ = a (aIndex x y) := by
  rw [value,FiniteNative.private_edge_value (M) (bases true x y) (regions true) fixedRegion (priv true)
    a z ⟨name edgeA,Or.inr (Or.inl rfl)⟩
    (by simp [fixedRegion,geometry,name,edgeA,edgeRx,edgeRy])
    (by rw [private_right]; exact rfl)]
  let t : Fin ((bases true x y).dimension ()) → ZMod 3 :=
    fun j => a ⟨⟨⟨name edgeA,Or.inr (Or.inl rfl),
      by simp [fixedRegion,geometry,name,edgeA,edgeRx,edgeRy]⟩,j⟩,
      by rw [private_right]; exact rfl⟩
  exact congrFun (((bases true x y).coordinate ()).apply_symm_apply t) (basisIndex true x y ())

end AAT.AG.RelativeRepairComposition.W1LocalPrivateFreedom
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1LocalPrivateFreedom
