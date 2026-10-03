import ResearchLean.AG.RelativeRepairComposition.W1GeneratedRelations

/-!
# Full original W1 public basis values before solving the generated relation

The index keeps the original edge, its physical exclusion, its full sole basis
component and its nonprivate status. No value or permission set is used to build
that index. Restoration reads exactly that original full public scalar value.
-/
namespace AAT.AG.RelativeRepairComposition.W1LocalPublicValues
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
open W1LocalDifferentials W1GeneratedRelations
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (x y : ZMod 3)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))
local notation "priv" j => ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j

/-- A complete original nonfixed public index retains its original name and full coefficient basis. -/
def publicIndex (j : Bool) (e : (regions j).edges) (hp : e.1 ∉ fixedRegion.edges) (hi : e.1 ∉ priv j) :
    FiniteNative.ZIndex (M) (bases true x y) (regions j) fixedRegion (priv j) :=
  ⟨⟨⟨e.1, e.2, hp⟩, basisIndex true x y e.1.2.1⟩, hi⟩

/-- Restoring arbitrary original public coordinates reads precisely their unchanged complete named scalar. -/
theorem public_value (j : Bool)
    (z : FiniteNative.ZIndex (M) (bases true x y) (regions j) fixedRegion (priv j) → ZMod 3)
    (e : (regions j).edges) (hp : e.1 ∉ fixedRegion.edges) (hi : e.1 ∉ priv j) :
    value x y (regions j) (publicCochain x y j z) e = z (publicIndex x y j e hp hi) := by
  rw [value, publicCochain, FiniteNative.public_edge_value (M) (bases true x y)
    (regions j) fixedRegion (priv j) 0 z e hp hi]
  let t : Fin ((bases true x y).dimension e.1.2.1) → ZMod 3 :=
    fun i => z ⟨⟨⟨e.1, e.2, hp⟩, i⟩, hi⟩
  exact congrFun (((bases true x y).coordinate e.1.2.1).apply_symm_apply t)
    (basisIndex true x y e.1.2.1)

/-- Every full local face basis coordinate is the same whole original kernel value at that face. -/
theorem face_coordinate (j : Bool) (a : RelativeCover.C2 (M) (regions j) fixedRegion)
    (f : (regions j).faces) :
    FiniteNative.coordinate2 (M) (bases true x y) (regions j) fixedRegion a
      ⟨⟨f.1, f.2, fun h => h.elim⟩, basisIndex true x y ()⟩ =
      kernelCoordinate true x y () (a.1 f) := rfl

end AAT.AG.RelativeRepairComposition.W1LocalPublicValues
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1LocalPublicValues
