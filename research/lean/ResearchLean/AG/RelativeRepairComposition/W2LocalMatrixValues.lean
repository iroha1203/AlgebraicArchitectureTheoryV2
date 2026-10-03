import ResearchLean.AG.RelativeRepairComposition.W2LocalInterfaces

/-!
# W2's actual full zero-row matrices and retained candidate coordinates

The empty actual face domain makes both generated matrices zero. No original
private coordinate exists, while every selected original candidate keeps its
complete kernel basis on the public side.
-/
namespace AAT.AG.RelativeRepairComposition.W2LocalMatrixValues
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open W2AffineInput W2Regions W2FiniteCoefficients W2LocalInterfaces
attribute [local instance] Classical.propDecidable
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower originalTower)
local notation "priv" j => ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j

/-- The actual original private coordinate family is empty on both original patches. -/
theorem no_private_coordinate (j : Bool)
    (x : FiniteNative.XIndex M bases (regions j) fixedRegion (priv j)) : False := by
  have h : x.1.1.1 ∈ (∅ : Set (EdgeName (K := geometry))) := by
    simpa only [private_empty] using (show x.1.1.1 ∈ priv j from x.2)
  exact h

/-- Every actual private matrix has its original empty row domain and is exactly zero. -/
theorem private_matrix_zero (j : Bool) : privateMatrix j = 0 := by
  funext row col
  exact row.1.1.elim

/-- Every actual public matrix has its original empty row domain and is exactly zero. -/
theorem public_matrix_zero (j : Bool) : publicMatrix j = 0 := by
  funext row col
  exact row.1.1.elim

/-- The once generated image section retains the entire original empty private coordinate family. -/
theorem generated_section_zero (j : Bool) : generatedSection j = 0 := by
  ext y x
  exact (no_private_coordinate j x).elim

/-- Every selected original candidate edge retains its complete original public kernel coordinate. -/
noncomputable def publicIndex (j : Bool) (e : EdgeName (K := geometry))
    (he : e ∈ (regions j).edges) : FiniteNative.ZIndex M bases (regions j) fixedRegion (priv j) :=
  ⟨⟨⟨e,he,by simp [fixedRegion]⟩,basisIndex e.2.1⟩,by
    change e ∉ priv j
    rw [private_empty]
    simp⟩

/-- The full public coordinate still names the same original selected actual edge. -/
theorem public_original_edge (j : Bool) (e : EdgeName (K := geometry))
    (he : e ∈ (regions j).edges) : (publicIndex j e he).1.1.1 = e := rfl

end AAT.AG.RelativeRepairComposition.W2LocalMatrixValues
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2LocalMatrixValues
