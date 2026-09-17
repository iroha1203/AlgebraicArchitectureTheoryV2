import ResearchLean.AG.LocalSemanticReconstruction.FinitePermutationExtension
import ResearchLean.AG.RealizationReconstruction.FixedFFiniteExamples
import Formal.Util.AssertStandardAxioms

/-!
# Finite preserving-change output and accepted fiber cardinalities

G-124(D) requires the executable finite-table route to meet the already
accepted finite examples and following-change fiber counts.  The Cycle 14
algorithm returns the actual operation-preserving following-change subtype
over a fixed visible automorphism.  This file identifies that exact subtype
with the existing actual projection fiber and transfers both the general
cardinality and the fixed Bool-lens / two-session protocol counts.

Implementation notes:

* The bridge composes the accepted preserving-change/component-family
  classification with the accepted component-family/projection-fiber
  equivalence.  A new proxy fiber or a cardinality-only coincidence was
  rejected because either would fail to identify the algorithm's output type.
* Concrete counts are transported from the existing finite-example theorems.
  Recomputing parallel counts was rejected because it would not establish the
  required connection to the accepted evidence.
-/

namespace AAT.AG.LocalSemanticReconstruction

open RealizationReconstruction
open RealizationReconstruction.FixedFSplitExactSequenceAndTorsor

namespace FinitePermutationExampleCardinality

universe u v w

/-- The actual preserving-change output type used by the Cycle 14 algorithm
is equivalent to the already accepted actual projection fiber. -/
def preservingChangeEquivProjectionFiber
    {F : FixedFDirectedMultigraph} {K : Type w}
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H) :
    PermutationRestriction.PreservingChange F K automorphism.1 ≃
      ProjectionFiber (K := K) H automorphism :=
  (FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
    (F := F) (K := K) (u := automorphism.1)).trans
      (componentGroupEquivProjectionFiber (K := K) H automorphism)

/-- Therefore the executable algorithm's actual codomain and the accepted
projection fiber have the same finite cardinality. -/
theorem natCard_preservingChange_eq_projectionFiber
    {F : FixedFDirectedMultigraph} {K : Type w}
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H) :
    Nat.card (PermutationRestriction.PreservingChange F K automorphism.1) =
      Nat.card (ProjectionFiber (K := K) H automorphism) :=
  Nat.card_congr (preservingChangeEquivProjectionFiber H automorphism)

/-- The actual preserving-change output type has one `|K|!` choice for every
generated component, matching the accepted following-change fiber formula. -/
theorem natCard_preservingChange
    {F : FixedFDirectedMultigraph} {K : Type w}
    [Finite F.Vertex] [Finite K]
    (automorphism : FixedFGraphAutomorphism F) :
    Nat.card (PermutationRestriction.PreservingChange F K automorphism) =
      Nat.factorial (Nat.card K) ^ Nat.card (FixedFComponent F) := by
  calc
    Nat.card (PermutationRestriction.PreservingChange F K automorphism) =
        Nat.card
          (FixedFRestrictedKernelIdentification.ComponentGroup
            (F := F) (K := K)) :=
      Nat.card_congr
        (FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
          (F := F) (K := K) (u := automorphism))
    _ = Nat.factorial (Nat.card K) ^ Nat.card (FixedFComponent F) :=
      FixedFFiberCardinality.natCard_componentGroup

open RealizationReconstruction.FixedFFiniteExamples

/-- The Cycle 14 output type over the fixed Bool-lens identity has the
accepted two-element preserving-change fiber. -/
theorem boolLens_preservingChange_count_identity :
    Nat.card
        (PermutationRestriction.PreservingChange
          BoolLensGraph Bool boolLensIdentityAutomorphism) = 2 := by
  calc
    Nat.card
        (PermutationRestriction.PreservingChange
          BoolLensGraph Bool boolLensIdentityAutomorphism) =
        Nat.card
          (ProjectionFiber (K := Bool) BoolLensVisibleGroup
            boolLensVisibleIdentity) :=
      natCard_preservingChange_eq_projectionFiber
        BoolLensVisibleGroup boolLensVisibleIdentity
    _ = 2 := boolLens_get_put_count_identity

/-- The Cycle 14 output type over the fixed Bool-lens flip has the accepted
two-element preserving-change fiber. -/
theorem boolLens_preservingChange_count_flip :
    Nat.card
        (PermutationRestriction.PreservingChange
          BoolLensGraph Bool boolLensFlipAutomorphism) = 2 := by
  calc
    Nat.card
        (PermutationRestriction.PreservingChange
          BoolLensGraph Bool boolLensFlipAutomorphism) =
        Nat.card
          (ProjectionFiber (K := Bool) BoolLensVisibleGroup
            boolLensVisibleFlip) :=
      natCard_preservingChange_eq_projectionFiber
        BoolLensVisibleGroup boolLensVisibleFlip
    _ = 2 := boolLens_get_put_count_flip

/-- The Cycle 14 output type over the fixed protocol identity has the
accepted four-element preserving-change fiber. -/
theorem protocol_preservingChange_count_identity :
    Nat.card
        (PermutationRestriction.PreservingChange
          protocolGraph Bool protocolIdentityAutomorphism) = 4 := by
  calc
    Nat.card
        (PermutationRestriction.PreservingChange
          protocolGraph Bool protocolIdentityAutomorphism) =
        Nat.card
          (ProjectionFiber (K := Bool) ProtocolVisibleGroup
            protocolVisibleIdentity) :=
      natCard_preservingChange_eq_projectionFiber
        ProtocolVisibleGroup protocolVisibleIdentity
    _ = 4 := protocol_operation_count_identity

/-- The Cycle 14 output type over the fixed protocol session swap has the
accepted four-element preserving-change fiber. -/
theorem protocol_preservingChange_count_sessionSwap :
    Nat.card
        (PermutationRestriction.PreservingChange
          protocolGraph Bool protocolSessionSwapAutomorphism) = 4 := by
  calc
    Nat.card
        (PermutationRestriction.PreservingChange
          protocolGraph Bool protocolSessionSwapAutomorphism) =
        Nat.card
          (ProjectionFiber (K := Bool) ProtocolVisibleGroup
            protocolVisibleSessionSwap) :=
      natCard_preservingChange_eq_projectionFiber
        ProtocolVisibleGroup protocolVisibleSessionSwap
    _ = 4 := protocol_operation_count_sessionSwap

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FinitePermutationExampleCardinality

end FinitePermutationExampleCardinality

end AAT.AG.LocalSemanticReconstruction
