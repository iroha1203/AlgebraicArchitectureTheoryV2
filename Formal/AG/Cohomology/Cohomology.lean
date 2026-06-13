import Formal.AG.Cohomology.CechComplex

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

/--
IV.定義4.1 / R3: a Čech-to-sheaf comparison hypothesis.

This is only a hypothesis package for notation.  It does not construct
assumption-free sheaf cohomology.
-/
structure CechToSheafComparisonHypothesis {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob) where
  comparisonName : String
  computesSpaceCohomology : Prop
  proof : computesSpaceCohomology

/--
IV.定義4.1 / R3: a refinement-system hypothesis under which cover-relative
Čech cohomology is used as the selected space-level reading.
-/
structure RefinementSystemHypothesis {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob) where
  refinementSystem : Type u
  computesByRefinement : Prop
  proof : computesByRefinement

/--
IV.定義4.1 / R3: allowed reasons for writing the conditional notation
`H^n(X, Ob_U)`.
-/
inductive SpaceCohomologyNotationJustification {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob) where
  | cechToSheaf : CechToSheafComparisonHypothesis K ->
      SpaceCohomologyNotationJustification K
  | refinementSystem : RefinementSystemHypothesis K ->
      SpaceCohomologyNotationJustification K

/--
IV.定義4.1 / R3: conditional notation package for `H^n(X, Ob_U)`.

The value is definitionally the selected cover-relative `H^n(𝒰, Ob_U)`, and the
package must carry either a Čech-to-sheaf comparison or a refinement-system
hypothesis.  There is no unconditional sheaf-cohomology construction here.
-/
structure ConditionalSpaceCohomology {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) where
  justification : SpaceCohomologyNotationJustification K

namespace ConditionalSpaceCohomology

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S} {K : CoverRelativeCechComplex 𝒰 Ob}

/-- IV.定義4.1 / R3: read the selected cover-relative value. -/
def HnX {n : Nat} (_H : ConditionalSpaceCohomology K n) : Type u :=
  K.CoverRelativeHn n

/-- IV.定義4.1 / R3: the conditional notation is the cover-relative object. -/
theorem HnX_eq_coverRelative {n : Nat} (H : ConditionalSpaceCohomology K n) :
    H.HnX = K.CoverRelativeHn n :=
  rfl

end ConditionalSpaceCohomology

end Cohomology
end AAT.AG
