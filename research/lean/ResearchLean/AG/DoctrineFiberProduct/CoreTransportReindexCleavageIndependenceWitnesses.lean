import ResearchLean.AG.DoctrineFiberProduct.CoreTransportReindexCleavageIndependence
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingCleavageWitnesses

/-!
# Finite witnesses for adjunction cleavage independence

The arbitrary-cleavage adjunction is fired on the literal and twisted identity
cleavages from Cycle 33.  Their canonical comparison visibly swaps the zero and
one axes at the named four-axis target, so the compatibility of hom equivalence,
unit, and counit is not an identity-comparison-only fixture.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

local instance finiteCoreCleavageAdjunctionAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The realized typed identity arrow supporting the two concrete cleavages. -/
def finiteCoreCleavageAdjunctionInput : RealizableHom FiniteModel.carrier :=
  typedRealizableHom (idTypedPresentation finitePortfolioSupportInstance)

/-- Core transport is left adjoint to the literal cleavage reindexing functor. -/
noncomputable def finiteCoreLiteralCleavageAdjunction :
    coreFiberTransportFunctor finiteCoreCleavageAdjunctionInput.semantic.hom ⊣
      finiteCleavageLiteralIdentityChoice.reindexFunctor :=
  coreTransportCleavageAdjunction finiteCoreCleavageAdjunctionInput
    finiteCleavageLiteralIdentityChoice

/-- Core transport is also left adjoint to the visibly twisted cleavage. -/
noncomputable def finiteCoreTwistedCleavageAdjunction :
    coreFiberTransportFunctor finiteCoreCleavageAdjunctionInput.semantic.hom ⊣
      finiteCleavageTwistedIdentityChoice.reindexFunctor :=
  coreTransportCleavageAdjunction finiteCoreCleavageAdjunctionInput
    finiteCleavageTwistedIdentityChoice

/--
The forward hom correspondence commutes with the visible literal-to-twisted
comparison, fired on the literal counit.
-/
theorem finiteCoreCleavageHomEquiv_comparison :
    finiteCoreLiteralCleavageAdjunction.homEquiv
        (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
          finiteCleavageFourAxisTarget)
        finiteCleavageFourAxisTarget
        ((coreTransportCleavageCounit finiteCoreCleavageAdjunctionInput
          finiteCleavageLiteralIdentityChoice).app
            finiteCleavageFourAxisTarget) ≫
      finiteCleavageComparisonApp.hom =
    finiteCoreTwistedCleavageAdjunction.homEquiv
      (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
        finiteCleavageFourAxisTarget)
      finiteCleavageFourAxisTarget
      ((coreTransportCleavageCounit finiteCoreCleavageAdjunctionInput
        finiteCleavageLiteralIdentityChoice).app
          finiteCleavageFourAxisTarget) :=
  coreTransportCleavageHomEquiv_comparison finiteCoreCleavageAdjunctionInput
    finiteCleavageLiteralIdentityChoice finiteCleavageTwistedIdentityChoice
    (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
      finiteCleavageFourAxisTarget)
    finiteCleavageFourAxisTarget
    ((coreTransportCleavageCounit finiteCoreCleavageAdjunctionInput
      finiteCleavageLiteralIdentityChoice).app finiteCleavageFourAxisTarget)

/-- The inverse correspondence commutes with the same nonidentity comparison. -/
theorem finiteCoreCleavageHomEquiv_symm_comparison :
    (finiteCoreTwistedCleavageAdjunction.homEquiv
      (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
        finiteCleavageFourAxisTarget)
      finiteCleavageFourAxisTarget).symm
        ((𝟙 (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
          finiteCleavageFourAxisTarget)) ≫ finiteCleavageComparisonApp.hom) =
    (finiteCoreLiteralCleavageAdjunction.homEquiv
      (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
        finiteCleavageFourAxisTarget)
      finiteCleavageFourAxisTarget).symm
        (𝟙 (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
          finiteCleavageFourAxisTarget)) :=
  coreTransportCleavageHomEquiv_symm_comparison
    finiteCoreCleavageAdjunctionInput finiteCleavageLiteralIdentityChoice
    finiteCleavageTwistedIdentityChoice
    (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
      finiteCleavageFourAxisTarget)
    finiteCleavageFourAxisTarget
    (𝟙 (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
      finiteCleavageFourAxisTarget))

/-- The generated units commute with the visible cleavage comparison. -/
theorem finiteCoreCleavageUnit_comparison :
    (coreTransportCleavageUnit finiteCoreCleavageAdjunctionInput
      finiteCleavageLiteralIdentityChoice).app
        (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
          finiteCleavageFourAxisTarget) ≫
      (CoreFiberCartesianCleavage.comparisonApp
        finiteCleavageLiteralIdentityChoice finiteCleavageTwistedIdentityChoice
        ((coreFiberTransportFunctor
          finiteCoreCleavageAdjunctionInput.semantic.hom).obj
            (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
              finiteCleavageFourAxisTarget))).hom =
    (coreTransportCleavageUnit finiteCoreCleavageAdjunctionInput
      finiteCleavageTwistedIdentityChoice).app
        (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
          finiteCleavageFourAxisTarget) :=
  coreTransportCleavageUnit_comparison finiteCoreCleavageAdjunctionInput
    finiteCleavageLiteralIdentityChoice finiteCleavageTwistedIdentityChoice
    (finiteCleavageLiteralIdentityChoice.reindexFunctor.obj
      finiteCleavageFourAxisTarget)

/-- The generated counits commute with the visible cleavage comparison. -/
theorem finiteCoreCleavageCounit_comparison :
    (coreFiberTransportFunctor
      finiteCoreCleavageAdjunctionInput.semantic.hom).map
        finiteCleavageComparisonApp.hom ≫
      (coreTransportCleavageCounit finiteCoreCleavageAdjunctionInput
        finiteCleavageTwistedIdentityChoice).app
          finiteCleavageFourAxisTarget =
    (coreTransportCleavageCounit finiteCoreCleavageAdjunctionInput
      finiteCleavageLiteralIdentityChoice).app finiteCleavageFourAxisTarget :=
  coreTransportCleavageCounit_comparison finiteCoreCleavageAdjunctionInput
    finiteCleavageLiteralIdentityChoice finiteCleavageTwistedIdentityChoice
    finiteCleavageFourAxisTarget

/-- The literal arbitrary-cleavage adjunction fires its left triangle. -/
theorem finiteCoreLiteralCleavage_left_triangle :
    Functor.whiskerRight
        (coreTransportCleavageUnit finiteCoreCleavageAdjunctionInput
          finiteCleavageLiteralIdentityChoice)
        (coreFiberTransportFunctor
          finiteCoreCleavageAdjunctionInput.semantic.hom) ≫
      (Functor.associator
        (coreFiberTransportFunctor
          finiteCoreCleavageAdjunctionInput.semantic.hom)
        finiteCleavageLiteralIdentityChoice.reindexFunctor
        (coreFiberTransportFunctor
          finiteCoreCleavageAdjunctionInput.semantic.hom)).hom ≫
      Functor.whiskerLeft
        (coreFiberTransportFunctor
          finiteCoreCleavageAdjunctionInput.semantic.hom)
        (coreTransportCleavageCounit finiteCoreCleavageAdjunctionInput
          finiteCleavageLiteralIdentityChoice) =
      NatTrans.id
        (𝟭 (CoreFiber finiteCoreCleavageAdjunctionInput.semantic.source) ⋙
          coreFiberTransportFunctor
            finiteCoreCleavageAdjunctionInput.semantic.hom) :=
  coreTransportCleavage_left_triangle finiteCoreCleavageAdjunctionInput
    finiteCleavageLiteralIdentityChoice

/-- The twisted arbitrary-cleavage adjunction fires its right triangle. -/
theorem finiteCoreTwistedCleavage_right_triangle :
    Functor.whiskerLeft
        finiteCleavageTwistedIdentityChoice.reindexFunctor
        (coreTransportCleavageUnit finiteCoreCleavageAdjunctionInput
          finiteCleavageTwistedIdentityChoice) ≫
      (Functor.associator
        finiteCleavageTwistedIdentityChoice.reindexFunctor
        (coreFiberTransportFunctor
          finiteCoreCleavageAdjunctionInput.semantic.hom)
        finiteCleavageTwistedIdentityChoice.reindexFunctor).inv ≫
      Functor.whiskerRight
        (coreTransportCleavageCounit finiteCoreCleavageAdjunctionInput
          finiteCleavageTwistedIdentityChoice)
        finiteCleavageTwistedIdentityChoice.reindexFunctor =
      NatTrans.id
        (finiteCleavageTwistedIdentityChoice.reindexFunctor ⋙
          𝟭 (CoreFiber finiteCoreCleavageAdjunctionInput.semantic.source)) :=
  coreTransportCleavage_right_triangle finiteCoreCleavageAdjunctionInput
    finiteCleavageTwistedIdentityChoice

/-- The comparison used by every compatibility theorem visibly swaps zero to one. -/
theorem finiteCoreCleavageComparison_axis_zero :
    finiteCleavageTwistedAxisReflect
        (finiteCleavageComparisonApp.hom.1.upper.axisMap
          finiteReindexAxisZero) = finiteReindexAxisOne :=
  finiteCleavageComparisonApp_axis_zero

/-- The target vertical swap retained by the same finite fixture is nonidentity. -/
theorem finiteCoreCleavageAxisSwap_ne_id :
    finiteCleavageAxisSwapHom ≠ 𝟙 finiteCleavageFourAxisTarget :=
  finiteCleavageAxisSwapHom_ne_id

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
