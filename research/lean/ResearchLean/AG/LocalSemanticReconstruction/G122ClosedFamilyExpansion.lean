import ResearchLean.AG.RealizationReconstruction.AATClosedRealizationCategory
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldComparisonIndex
import Formal.Util.AssertStandardAxioms

/-!
# Expansion of the closed G-122 fiber to its generated endpoints

The original-cell fiber of the common family contains every complete geometry
morphism between original G-122 inputs.  The already constructed generated
G-122 category adds the direct and via-base endpoints needed by the fixed
comparison example, while retaining all complete geometry morphisms.

This module includes the original fiber fully faithfully in that expanded
category and names the two fixed endpoints and three required comparison
cases there.  It does not yet replace the final four-branch realization
family or construct the G-122 local-model equivalence.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction

namespace G122ClosedFamilyExpansion

noncomputable section

universe u v

/-- Include every original-cell realization and every admitted Hom in the
display-independent category that also contains the generated endpoints. -/
noncomputable def originalInclusion (input : G122FamilyInput.{u, v}) :
    FamilyRealization.{u, v} (.g122 input) ⥤
      G122GeneratedGeometryObject input where
  obj
    | .g122 object => .original object
  map {X Y} morphism := by
    cases X with
    | g122 source =>
      cases Y with
      | g122 target => exact morphism.down
  map_id X := by
    cases X
    rfl
  map_comp {X Y Z} first second := by
    cases X
    cases Y
    cases Z
    rfl

/-- The inclusion retains the original cell object without changing its
source data. -/
@[simp] theorem originalInclusion_obj (input : G122FamilyInput.{u, v})
    (object : G122CellInput input) :
    (originalInclusion input).obj (.g122 object) = .original object :=
  by rfl

/-- The inclusion removes only the universe lift around an original complete
geometry Hom. -/
@[simp] theorem originalInclusion_map (input : G122FamilyInput.{u, v})
    {source target : G122CellInput input}
    (morphism :
      (FamilyRealization.g122 source : FamilyRealization (.g122 input)) ⟶
        FamilyRealization.g122 target) :
    (originalInclusion input).map morphism = morphism.down :=
  rfl

/-- Every complete geometry Hom between included original objects has a
unique preimage in the closed-family fiber. -/
noncomputable def originalInclusionFullyFaithful
    (input : G122FamilyInput.{u, v}) :
    (originalInclusion input).FullyFaithful where
  preimage {X Y} morphism := by
    cases X
    cases Y
    exact ULift.up morphism
  map_preimage {X Y} morphism := by
    cases X
    cases Y
    rfl
  preimage_map {X Y} morphism := by
    cases X
    cases Y
    rfl

/-- The direct endpoint of the fixed finite-axis-fold comparison in the
expanded G-122 category. -/
abbrev finiteAxisFoldDirectObject :
    G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput :=
  .direct finiteAxisFoldG122CellInput

/-- The via-base endpoint of the fixed finite-axis-fold comparison in the
expanded G-122 category. -/
abbrev finiteAxisFoldViaBaseObject :
    G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput :=
  .viaBase finiteAxisFoldG122CellInput

/-- The actual five-factor comparison between the fixed generated endpoints. -/
noncomputable abbrev finiteAxisFoldBarAlpha :
    finiteAxisFoldDirectObject ⟶ finiteAxisFoldViaBaseObject :=
  FiniteAxisFoldComparisonCode.evaluate .barAlpha

/-- The actual generated-cochain comparison between the same endpoints. -/
noncomputable abbrev finiteAxisFoldGeneratedBarBeta :
    finiteAxisFoldDirectObject ⟶ finiteAxisFoldViaBaseObject :=
  FiniteAxisFoldComparisonCode.evaluate .generatedBarBeta

/-- The actual constant-one comparison between the same endpoints. -/
noncomputable abbrev finiteAxisFoldIdentityBarBeta :
    finiteAxisFoldDirectObject ⟶ finiteAxisFoldViaBaseObject :=
  FiniteAxisFoldComparisonCode.evaluate .identityBarBeta

/-- The generated-cochain comparison remains distinct from the five-factor
comparison after placing both in the expanded G-122 category. -/
theorem finiteAxisFoldGeneratedBarBeta_ne_barAlpha :
    finiteAxisFoldGeneratedBarBeta ≠ finiteAxisFoldBarAlpha :=
  FiniteAxisFoldComparisonCode.generatedBarBeta_ne_barAlpha

/-- The constant-one comparison is the five-factor comparison as an actual
expanded-category Hom. -/
theorem finiteAxisFoldIdentityBarBeta_eq_barAlpha :
    finiteAxisFoldIdentityBarBeta = finiteAxisFoldBarAlpha :=
  FiniteAxisFoldComparisonCode.evaluate_identityBarBeta_eq_barAlpha

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion

end

end G122ClosedFamilyExpansion

end AAT.AG.LocalSemanticReconstruction
