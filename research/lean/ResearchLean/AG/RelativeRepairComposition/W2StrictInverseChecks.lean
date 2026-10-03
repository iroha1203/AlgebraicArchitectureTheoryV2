import ResearchLean.AG.RelativeRepairComposition.W2StrictGeneratedCover

/-!
# Exact W2 strict restoration of whole objects and whole labeled arrows

Each constituent restores its complete original object and full label exactly.
Composition preserves these literal inverse functor laws on every permission
set; no arrows are identified by their effects.
-/
namespace AAT.AG.RelativeRepairComposition.W2StrictInverseChecks
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W2AffineInput W2Regions W2ActualRepairs W2FiniteCoefficients W2StrictGeneratedCover
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

/-- Composition retains exact whole forward-inverse functors when both constituents do. -/
theorem trans_forward_inverse {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) (f : D ≌ E)
    (he : e.functor ⋙ e.inverse = 𝟭 C) (hf : f.functor ⋙ f.inverse = 𝟭 D) :
    (e.trans f).functor ⋙ (e.trans f).inverse = 𝟭 C := by
  change (e.functor ⋙ f.functor) ⋙ (f.inverse ⋙ e.inverse) = _
  calc
    _ = e.functor ⋙ ((f.functor ⋙ f.inverse) ⋙ e.inverse) := by simp only [Functor.assoc]
    _ = 𝟭 C := by rw [hf, Functor.id_comp, he]

/-- Composition retains exact whole inverse-forward functors when both constituents do. -/
theorem trans_inverse_forward {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) (f : D ≌ E)
    (he : e.inverse ⋙ e.functor = 𝟭 D) (hf : f.inverse ⋙ f.functor = 𝟭 E) :
    (e.trans f).inverse ⋙ (e.trans f).functor = 𝟭 E := by
  change (f.inverse ⋙ e.inverse) ⋙ (e.functor ⋙ f.functor) = _
  calc
    _ = f.inverse ⋙ ((e.inverse ⋙ e.functor) ⋙ f.functor) := by simp only [Functor.assoc]
    _ = 𝟭 E := by rw [he, Functor.id_comp, hf]

variable (S : Set (EdgeName (K := geometry)))
local notation "T" => originalTower
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower T)

/-- Every original native object and every whole original label return exactly after strict generation. -/
theorem native_forward_inverse :
    (nativeEquivalence S).functor ⋙ (nativeEquivalence S).inverse = 𝟭 (NativeCategory S) :=
  trans_forward_inverse _ _
    (SupportedNativeEquation.functor_inverse T fixedRegion candidates S fixed_faces)
    (trans_forward_inverse _ _
      (StrictCoverRestoration.functor_inverse M fixedRegion regions candidates S actualDefect enumRegions indexed_cover)
      (GeneratedCoverAction.functor_inverse M bases fixedRegion regions candidates original_linear actualDefect enumK enumEdges enumFaces S))

/-- Every strict generated object and every whole compatible original label return exactly after native restoration. -/
theorem native_inverse_forward :
    (nativeEquivalence S).inverse ⋙ (nativeEquivalence S).functor = 𝟭 (W2StrictGeneratedCover.Groupoid S) :=
  trans_inverse_forward _ _
    (SupportedNativeEquation.inverse_functor T fixedRegion candidates S fixed_faces)
    (trans_inverse_forward _ _
      (StrictCoverRestoration.inverse_functor M fixedRegion regions candidates S actualDefect enumRegions indexed_cover)
      (GeneratedCoverAction.inverse_functor M bases fixedRegion regions candidates original_linear actualDefect enumK enumEdges enumFaces S))

/-- All independent actual full affine objects and full label arrows return exactly after strict generation. -/
theorem actual_forward_inverse :
    (actualEquivalence S).functor ⋙ (actualEquivalence S).inverse = 𝟭 (ActualCategory S) :=
  trans_forward_inverse _ _
    (NativeAffine.groupoid_inverse_functor geometry reference reference comparison linear_faces fixedRegion.vertices (fixedEdges S))
    (native_forward_inverse S)

/-- All strictly generated full objects and full label arrows return exactly after actual restoration. -/
theorem actual_inverse_forward :
    (actualEquivalence S).inverse ⋙ (actualEquivalence S).functor = 𝟭 (W2StrictGeneratedCover.Groupoid S) :=
  trans_inverse_forward _ _
    (NativeAffine.groupoid_functor_inverse geometry reference reference comparison linear_faces fixedRegion.vertices (fixedEdges S))
    (native_inverse_forward S)

end AAT.AG.RelativeRepairComposition.W2StrictInverseChecks
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2StrictInverseChecks
