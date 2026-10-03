import ResearchLean.AG.RelativeRepairComposition.W2FiniteCoefficients
import ResearchLean.AG.RelativeRepairComposition.FiniteCoverInterfaces
import ResearchLean.AG.RelativeRepairComposition.FiniteNativeArbitraryEquation

/-!
# Independent full W2 local D/F, generated sections and native interfaces

Each generator is computed directly from its patch of the complete original
affine tower, before any permission set is supplied. Both enumerations and full
kernel bases are retained. The actual reference defect supplies the local rhs;
no relation or section certificate is an input.
-/
namespace AAT.AG.RelativeRepairComposition.W2LocalInterfaces
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W2AffineInput W2Regions W2FiniteCoefficients
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

local notation "T" => originalTower
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower T)
local notation "priv" j => ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j

/-- The full private D matrix is generated from the actual original local d1. -/
noncomputable def privateMatrix (j : Bool) :=
  FiniteNative.Dmatrix (M) (bases) (regions j) fixedRegion (priv j) (original_linear)

/-- The full public F matrix retains every shared always and candidate coordinate. -/
noncomputable def publicMatrix (j : Bool) :=
  FiniteNative.Fmatrix (M) (bases) (regions j) fixedRegion (priv j) (original_linear)

/-- The independent private elimination uses the same D and complete input lists, before choosing rhs or S. -/
noncomputable def elimination (j : Bool) :=
  FiniteNative.generatedElimination (M) (bases) (regions j) fixedRegion (priv j)
    (original_linear) enumK enumEdges enumFaces

/-- The actual matrix generates its full image section once, without a permission argument. -/
noncomputable def generatedSection (j : Bool) :=
  FiniteNative.generatedSection (M) (bases) (regions j) fixedRegion (priv j)
    (original_linear) enumK enumEdges enumFaces

/-- The generated section law is proved on the entire original private coordinate space. -/
theorem section_regular (j : Bool)
    (a : FiniteNative.XIndex (M) (bases) (regions j) fixedRegion (priv j) → ZMod 3) :
    FiniteNative.D (M) (bases) (regions j) fixedRegion (priv j) (original_linear)
      (generatedSection j
        (FiniteNative.D (M) (bases) (regions j) fixedRegion (priv j) (original_linear) a)) =
      FiniteNative.D (M) (bases) (regions j) fixedRegion (priv j) (original_linear) a :=
  FiniteNative.generatedSection_regular (M) (bases) (regions j) fixedRegion (priv j)
    (original_linear) enumK enumEdges enumFaces a

/-- Each local generated public relation uses its own actual original differential and signed original defect. -/
noncomputable def relation (j : Bool) :=
  FiniteNative.generatedRelation (M) (bases) (regions j) fixedRegion (priv j)
    (original_linear)
    (RelativeCover.r2 (M) fixedRegion (ClosedRegion.to_all (regions j)) (-actualDefect))
    enumK enumEdges enumFaces

/-- Both full private kernels and full public relations restore all original local equations in both directions. -/
noncomputable def equationEquiv (j : Bool) :=
  FiniteNative.generatedRelativeEquiv (M) (bases) (regions j) fixedRegion (priv j)
    (original_linear)
    (RelativeCover.r2 (M) fixedRegion (ClosedRegion.to_all (regions j)) (-actualDefect))
    enumK enumEdges enumFaces

/-- The whole native original local repair groupoid has the independently generated interface with all its original arrows. -/
noncomputable def nativeEquivalence (j : Bool) :=
  FiniteCoverInterfaces.localEquivalence (T) (bases) regions fixedRegion candidates
    (original_linear) (fixed_faces) enumK enumEdges enumFaces j

/-- The same full projected public matrix supplies independent generated relations. -/
theorem public_rows_independent (j : Bool) :
    LinearIndependent (ZMod 3)
      (FiniteNative.generatedPublicRows (M) (bases) (regions j) fixedRegion (priv j)
        (original_linear) enumK enumEdges enumFaces) :=
  FiniteNative.generated_public_rows_independent (M) (bases) (regions j) fixedRegion (priv j)
    (original_linear) enumK enumEdges enumFaces

/-- Independent public relation counts are bounded by the complete public dimension of the original patch. -/
theorem public_row_count (j : Bool) :
    Fintype.card (FiniteElimination.RectangularActive
      (FiniteNative.publicMatrix (M) (bases) (regions j) fixedRegion (priv j)
        (original_linear) enumK enumEdges enumFaces) enumK
      (FiniteNative.enum2 (M) (bases) (regions j) fixedRegion enumFaces)
      (FiniteNative.enumZ (M) (bases) (regions j) fixedRegion (priv j) enumEdges)) ≤
      Fintype.card (FiniteNative.ZIndex (M) (bases) (regions j) fixedRegion (priv j)) :=
  FiniteNative.generated_public_row_count (M) (bases) (regions j) fixedRegion (priv j)
    (original_linear) enumK enumEdges enumFaces

end AAT.AG.RelativeRepairComposition.W2LocalInterfaces
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2LocalInterfaces
