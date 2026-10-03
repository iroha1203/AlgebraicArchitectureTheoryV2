import ResearchLean.AG.RelativeRepairComposition.W3StrictGeneratedCover
import ResearchLean.AG.RelativeRepairComposition.W2StrictInverseChecks

/-! # Literal W3 strict inverse functors on every permission

Each constituent restores the complete original objects and labeled arrows.
The accepted composition laws retain those literal identities for both
original loop transports and every permission S.
-/
namespace AAT.AG.RelativeRepairComposition.W3StrictInverseChecks
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3AffineInput W3Regions W3ActualRepairs W3FiniteCoefficients W3StrictGeneratedCover
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (sheared : Bool) (S : Set (EdgeName (K := geometry)))
local notation "T" => originalTower sheared
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower T)

/-- Every original native object and every whole original label return exactly after generation. -/
theorem native_forward_inverse :
    (nativeEquivalence sheared S).functor ⋙ (nativeEquivalence sheared S).inverse =
      𝟭 (NativeCategory sheared S) :=
  W2StrictInverseChecks.trans_forward_inverse _ _
    (SupportedNativeEquation.functor_inverse T fixedRegion candidates S (fixed_faces sheared))
    (W2StrictInverseChecks.trans_forward_inverse _ _
      (StrictCoverRestoration.functor_inverse M fixedRegion regions candidates S
        (actualDefect sheared) enumRegions indexed_cover)
      (GeneratedCoverAction.functor_inverse M (bases sheared) fixedRegion regions candidates
        (original_linear sheared) (actualDefect sheared) enumK enumEdges enumFaces S))

/-- Every strict generated object and full compatible label return exactly after native restoration. -/
theorem native_inverse_forward :
    (nativeEquivalence sheared S).inverse ⋙ (nativeEquivalence sheared S).functor =
      𝟭 (W3StrictGeneratedCover.Groupoid sheared S) :=
  W2StrictInverseChecks.trans_inverse_forward _ _
    (SupportedNativeEquation.inverse_functor T fixedRegion candidates S (fixed_faces sheared))
    (W2StrictInverseChecks.trans_inverse_forward _ _
      (StrictCoverRestoration.inverse_functor M fixedRegion regions candidates S
        (actualDefect sheared) enumRegions indexed_cover)
      (GeneratedCoverAction.inverse_functor M (bases sheared) fixedRegion regions candidates
        (original_linear sheared) (actualDefect sheared) enumK enumEdges enumFaces S))

/-- All independent actual full affine objects and original full labels return exactly after strict generation. -/
theorem actual_forward_inverse :
    (actualEquivalence sheared S).functor ⋙ (actualEquivalence sheared S).inverse =
      𝟭 (ActualCategory sheared S) :=
  W2StrictInverseChecks.trans_forward_inverse _ _
    (NativeAffine.groupoid_inverse_functor geometry (reference sheared) (reference sheared)
      comparison (linear_faces sheared) fixedRegion.vertices (fixedEdges S))
    (native_forward_inverse sheared S)

/-- All generated strict objects and original full compatible labels return exactly after actual restoration. -/
theorem actual_inverse_forward :
    (actualEquivalence sheared S).inverse ⋙ (actualEquivalence sheared S).functor =
      𝟭 (W3StrictGeneratedCover.Groupoid sheared S) :=
  W2StrictInverseChecks.trans_inverse_forward _ _
    (NativeAffine.groupoid_functor_inverse geometry (reference sheared) (reference sheared)
      comparison (linear_faces sheared) fixedRegion.vertices (fixedEdges S))
    (native_inverse_forward sheared S)

end AAT.AG.RelativeRepairComposition.W3StrictInverseChecks
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3StrictInverseChecks
