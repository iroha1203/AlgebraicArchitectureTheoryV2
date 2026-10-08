import ResearchLean.AG.AtlasCoefficientFiber.SupportFiberChains

/-!
# G-135 D：同じ垂直閉路商の台包含と原κ

## Implementation notes

原V像を保つことを細chainの微分可換性から示し、同じ閉路包含を実商へ降ろす。
raw κの自然性は原Dyの閉路代表で示す。商間の射を任意に選ぶ案は原V像との接続を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 同じ原垂直面微分Vは元の細微分を介して台包含と可換。 -/
theorem supportVerticalBoundary (x : VerticalFace M A →₀ ℚ) :
    verticalBoundary M B (supportVerticalFaceChainInclude M hab x) =
      supportVerticalEdgeChainInclude M hab (verticalBoundary M A x) := by
  apply verticalEdgeInclusion_injective M B
  calc
    verticalEdgeInclusion M B (verticalBoundary M B (supportVerticalFaceChainInclude M hab x)) =
        chainD2 Nf _ (verticalFaceInclusion M B (supportVerticalFaceChainInclude M hab x)) :=
      LinearMap.congr_fun (verticalBoundary_inclusion M B) _
    _ = chainD2 Nf _ (selectedInclude Nf.faceSupport (fun _ ht => hab ht) (verticalFaceInclusion M A x)) :=
      congrArg (chainD2 Nf _) (supportVerticalFaceChainInclude_inclusion M hab x)
    _ = selectedInclude Nf.edgeSupport (fun _ ht => hab ht) (chainD2 Nf _ (verticalFaceInclusion M A x)) :=
      (LinearMap.congr_fun (supportChainInclude_boundary2 Nf (fun _ ht => hab ht)) _).symm
    _ = selectedInclude Nf.edgeSupport (fun _ ht => hab ht) (verticalEdgeInclusion M A (verticalBoundary M A x)) :=
      congrArg (selectedInclude Nf.edgeSupport (fun _ ht => hab ht))
        (LinearMap.congr_fun (verticalBoundary_inclusion M A) x).symm
    _ = verticalEdgeInclusion M B (supportVerticalEdgeChainInclude M hab (verticalBoundary M A x)) :=
      (supportVerticalEdgeChainInclude_inclusion M hab _).symm

/-- 同じVの閉路への制限も全代表で可換。 -/
theorem supportVerticalBoundaryToCycles (x : VerticalFace M A →₀ ℚ) :
    supportVerticalCyclesInclude M hab (verticalBoundaryToCycles M A x) =
      verticalBoundaryToCycles M B (supportVerticalFaceChainInclude M hab x) := by
  apply Subtype.ext
  rw [supportVerticalCyclesInclude_val, verticalBoundaryToCycles_val,
    verticalBoundaryToCycles_val, supportVerticalBoundary]

/-- 原V像を保つ同じ垂直閉路包含を同じH₁商へ降ろす。 -/
def supportVerticalHomology : VerticalHomology M A →ₗ[ℚ] VerticalHomology M B :=
  Submodule.mapQ _ _ (supportVerticalCyclesInclude M hab) (fun x hx => by
    obtain ⟨t, rfl⟩ := hx
    exact ⟨supportVerticalFaceChainInclude M hab t,
      (supportVerticalBoundaryToCycles M hab t).symm⟩)

/-- 同じ垂直H₁包含の全閉路代表式。 -/
@[simp] theorem supportVerticalHomology_mk (x : verticalCycles M A) :
    supportVerticalHomology M hab (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (supportVerticalCyclesInclude M hab x) :=
  Submodule.mapQ_apply _ _ _ x

/-- 原raw κは同じ混在閉路包含と垂直H₁包含に対して自然。 -/
theorem supportRawKappa (x : mixedCycles M A) :
    supportVerticalHomology M hab (rawKappa M A x) =
      rawKappa M B (supportMixedCyclesInclude M hab x) := by
  rw [rawKappa_apply, supportVerticalHomology_mk, rawKappa_apply, supportMixedCycleToVertical]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalBoundaryToCycles
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalHomology
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalHomology_mk
#print axioms AAT.AG.AtlasCoefficientFiber.supportRawKappa
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
