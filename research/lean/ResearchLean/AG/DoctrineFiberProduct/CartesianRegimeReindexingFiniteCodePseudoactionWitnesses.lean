import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingFiniteCodePseudoaction
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingPresentationWitnesses

/-!
# Finite witnesses for the selected finite-code quotient pseudoaction

This module inserts the existing selective chain `3 → 2 → 1 → support`
into `FiniteCodeCartHom`.  The canonical and padded two-to-support
presentations are raw-distinct but decode to the same semantic arrow, so they
become the same quotient morphism.  The padded representative is then compared
with the representative selected by `Quotient.out`; both lift triangles,
naturality, reflexivity, symmetry, and the three-representative cocycle are
fired on the same finite data.

The quotient compositor, unitor, their arbitrary-representative compatibility,
associativity, and both unit laws are fired without supplying a lift,
comparison, natural isomorphism, or coherence certificate.  Nondegeneracy is
recorded independently by a noninvertible quotient leg and the genuine
four-axis swap.  The packaged pseudofunctor's object, morphism, identity, and
composition fields are observed through its public projection API on these
same fixtures.  Raw presentation inequality is not used to assert that an
opaque comparison component is nonidentity.

## Implementation notes

The quotient composite is defined from the two authored quotient legs, rather
than by selecting a direct presentation.  The canonical and padded direct
presentations are separately proved to represent this composite from their
decoder equations.  This keeps `Quotient.out` confined to the generic selected
action and rejects a strict `Quotient.lift` into `Functor` as well as any
caller-supplied cleavage or comparison packet.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-- Executable Atom equality for the concrete quotient-pseudoaction witness. -/
local instance finiteCodePseudoactionWitnessAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## Quotient morphisms and representative membership -/

/-- The quotient morphism represented by the noninvertible three-to-two leg. -/
def finiteCodeSelectiveThreeToTwoHom :
    FiniteCodeCartHom finiteSelectiveThreeInstance
      finiteSelectiveTwoInstance :=
  FiniteCodeCartHom.ofPresentation
    finiteSelectiveThreeToTwoCoherencePresentation

/-- The quotient morphism represented by the noninvertible two-to-one leg. -/
def finiteCodeSelectiveTwoToOneHom :
    FiniteCodeCartHom finiteSelectiveTwoInstance finiteSelectiveOneInstance :=
  FiniteCodeCartHom.ofPresentation finiteSelectiveTwoToOnePresentation

/-- The quotient morphism from the one-cell endpoint to finite support. -/
def finiteCodeSelectiveOneToSupportHom :
    FiniteCodeCartHom finiteSelectiveOneInstance
      finitePortfolioSupportInstance :=
  FiniteCodeCartHom.ofPresentation finiteSelectiveOneToSupportPresentation

/-- The two-to-support quotient morphism, defined as the actual quotient composite. -/
def finiteCodeSelectiveTwoToSupportHom :
    FiniteCodeCartHom finiteSelectiveTwoInstance
      finitePortfolioSupportInstance :=
  FiniteCodeCartHom.comp finiteCodeSelectiveTwoToOneHom
    finiteCodeSelectiveOneToSupportHom

/-- The authored canonical direct presentation represents the quotient composite. -/
theorem finiteCodeSelectiveTwoToSupportPresentation_eq :
    FiniteCodeCartHom.ofPresentation
        finiteSelectiveTwoToSupportPresentation =
      finiteCodeSelectiveTwoToSupportHom := by
  simpa only [finiteSelectiveTwoToSupportPresentation,
    finiteCodeSelectiveTwoToSupportHom,
    finiteCodeSelectiveTwoToOneHom,
    finiteCodeSelectiveOneToSupportHom] using
      FiniteCodeCartHom.ofPresentation_comp
        finiteSelectiveTwoToOnePresentation
        finiteSelectiveOneToSupportPresentation

/-- The raw-distinct padded direct presentation represents the same quotient composite. -/
theorem finiteCodePaddedSelectiveTwoToSupportPresentation_eq :
    FiniteCodeCartHom.ofPresentation
        finitePaddedSelectiveTwoToSupportPresentation =
      finiteCodeSelectiveTwoToSupportHom := by
  calc
    _ = FiniteCodeCartHom.ofPresentation
        finiteSelectiveTwoToSupportPresentation :=
      FiniteCodeCartHom.ofPresentation_eq_of_semantic
        finitePaddedSelectiveTwoToSupportPresentation
        finiteSelectiveTwoToSupportPresentation
        finiteSelectiveTwoToSupportPresentation_semanticHom_eq.symm
    _ = finiteCodeSelectiveTwoToSupportHom :=
      finiteCodeSelectiveTwoToSupportPresentation_eq

/-- The raw-distinct semantic-equal pair inserts as one quotient morphism. -/
theorem finiteCodeRawDistinctSelectivePresentations_eq :
    FiniteCodeCartHom.ofPresentation
        finiteSelectiveTwoToSupportPresentation =
      FiniteCodeCartHom.ofPresentation
        finitePaddedSelectiveTwoToSupportPresentation :=
  FiniteCodeCartHom.ofPresentation_eq_of_semantic
    finiteSelectiveTwoToSupportPresentation
    finitePaddedSelectiveTwoToSupportPresentation
    finiteSelectiveTwoToSupportPresentation_semanticHom_eq

/-- Raw inequality, decoder equality, and quotient equality hold for the same pair. -/
theorem finiteCodeRawDistinctSelectivePresentationPair :
    finiteSelectiveTwoToSupportPresentation ≠
        finitePaddedSelectiveTwoToSupportPresentation ∧
      typedPresentationToSemantic finiteSelectiveTwoToSupportPresentation =
          typedPresentationToSemantic
            finitePaddedSelectiveTwoToSupportPresentation ∧
        FiniteCodeCartHom.ofPresentation
            finiteSelectiveTwoToSupportPresentation =
          FiniteCodeCartHom.ofPresentation
            finitePaddedSelectiveTwoToSupportPresentation :=
  ⟨finiteSelectiveTwoToSupportPresentation_ne_padded,
    finiteSelectiveTwoToSupportPresentation_semanticHom_eq,
    finiteCodeRawDistinctSelectivePresentations_eq⟩

/-- The raw-distinct padded support identity represents the quotient identity. -/
theorem finiteCodePaddedSupportIdentityPresentation_eq :
    FiniteCodeCartHom.ofPresentation finitePaddedSupportIdentityPresentation =
      𝟙 finitePortfolioSupportInstance := by
  calc
    _ = FiniteCodeCartHom.ofPresentation
        (idTypedPresentation finitePortfolioSupportInstance) :=
      FiniteCodeCartHom.ofPresentation_eq_of_semantic
        finitePaddedSupportIdentityPresentation
        (idTypedPresentation finitePortfolioSupportInstance)
        finiteSupportIdentityPresentation_semanticHom_eq.symm
    _ = 𝟙 finitePortfolioSupportInstance :=
      FiniteCodeCartHom.ofPresentation_id finitePortfolioSupportInstance

/-! ## Arbitrary representatives versus the selected canonical action -/

/-- The padded representative compared with the `Quotient.out` representative. -/
noncomputable def finiteCodeSelectivePaddedCanonicalComparisonApp :
    (selectedTypedCoreFiberReindexFunctor
      finitePaddedSelectiveTwoToSupportPresentation).obj
        finiteReindexFourAxisTarget ≅
      (finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveTwoToSupportHom).obj
          finiteReindexFourAxisTarget :=
  finiteCodeSelectedCoreFiberRepresentativeComparisonApp
    finiteCodeSelectiveTwoToSupportHom
    finitePaddedSelectiveTwoToSupportPresentation
    finiteCodeSelectiveTwoToSupportHom.representative
    finiteCodePaddedSelectiveTwoToSupportPresentation_eq
    (FiniteCodeCartHom.ofPresentation_representative
      finiteCodeSelectiveTwoToSupportHom)
    finiteReindexFourAxisTarget

/-- The padded-to-canonical comparison satisfies its forward lift triangle. -/
theorem finiteCodeSelectivePaddedCanonicalComparisonApp_hom_fac :
    finiteCodeSelectivePaddedCanonicalComparisonApp.hom.1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift
          finiteCodeSelectiveTwoToSupportHom
          finiteReindexFourAxisTarget).hom =
      (selectedTypedCoreFiberCartesianLift
        finitePaddedSelectiveTwoToSupportPresentation
        finiteReindexFourAxisTarget).hom :=
  finiteCodeSelectedCoreFiberRepresentativeComparisonApp_hom_fac
    finiteCodeSelectiveTwoToSupportHom
    finitePaddedSelectiveTwoToSupportPresentation
    finiteCodeSelectiveTwoToSupportHom.representative
    finiteCodePaddedSelectiveTwoToSupportPresentation_eq
    (FiniteCodeCartHom.ofPresentation_representative
      finiteCodeSelectiveTwoToSupportHom)
    finiteReindexFourAxisTarget

/-- The inverse padded-to-canonical comparison satisfies the reverse triangle. -/
theorem finiteCodeSelectivePaddedCanonicalComparisonApp_inv_fac :
    finiteCodeSelectivePaddedCanonicalComparisonApp.inv.1 ≫
        (selectedTypedCoreFiberCartesianLift
          finitePaddedSelectiveTwoToSupportPresentation
          finiteReindexFourAxisTarget).hom =
      (finiteCodeSelectedCoreFiberCartesianLift
        finiteCodeSelectiveTwoToSupportHom
        finiteReindexFourAxisTarget).hom :=
  finiteCodeSelectedCoreFiberRepresentativeComparisonApp_inv_fac
    finiteCodeSelectiveTwoToSupportHom
    finitePaddedSelectiveTwoToSupportPresentation
    finiteCodeSelectiveTwoToSupportHom.representative
    finiteCodePaddedSelectiveTwoToSupportPresentation_eq
    (FiniteCodeCartHom.ofPresentation_representative
      finiteCodeSelectiveTwoToSupportHom)
    finiteReindexFourAxisTarget

/-- Representative-comparison naturality fires on the genuine four-axis swap. -/
theorem finiteCodeSelectivePaddedCanonicalComparison_naturality :
    (selectedTypedCoreFiberReindexFunctor
        finitePaddedSelectiveTwoToSupportPresentation).map
          finiteReindexAxisSwapHom ≫
        finiteCodeSelectivePaddedCanonicalComparisonApp.hom =
      finiteCodeSelectivePaddedCanonicalComparisonApp.hom ≫
        (finiteCodeSelectedCoreFiberReindexFunctor
          finiteCodeSelectiveTwoToSupportHom).map
            finiteReindexAxisSwapHom :=
  finiteCodeSelectedCoreFiberRepresentativeComparison_naturality
    finiteCodeSelectiveTwoToSupportHom
    finitePaddedSelectiveTwoToSupportPresentation
    finiteCodeSelectiveTwoToSupportHom.representative
    finiteCodePaddedSelectiveTwoToSupportPresentation_eq
    (FiniteCodeCartHom.ofPresentation_representative
      finiteCodeSelectiveTwoToSupportHom)
    finiteReindexAxisSwapHom

/-- The whole generated comparison from the padded representative to the selected action. -/
noncomputable def finiteCodeSelectivePaddedCanonicalComparison :
    selectedTypedCoreFiberReindexFunctor
        finitePaddedSelectiveTwoToSupportPresentation ≅
      finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveTwoToSupportHom :=
  finiteCodeSelectedCoreFiberCanonicalComparison
    finiteCodeSelectiveTwoToSupportHom
    finitePaddedSelectiveTwoToSupportPresentation
    finiteCodePaddedSelectiveTwoToSupportPresentation_eq

/-- Representative comparison is reflexive at the selected `Quotient.out` representative. -/
theorem finiteCodeSelectiveCanonicalRepresentativeComparison_refl :
    finiteCodeSelectedCoreFiberRepresentativeComparison
        finiteCodeSelectiveTwoToSupportHom
        finiteCodeSelectiveTwoToSupportHom.representative
        finiteCodeSelectiveTwoToSupportHom.representative
        (FiniteCodeCartHom.ofPresentation_representative
          finiteCodeSelectiveTwoToSupportHom)
        (FiniteCodeCartHom.ofPresentation_representative
          finiteCodeSelectiveTwoToSupportHom) =
      Iso.refl (finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveTwoToSupportHom) :=
  finiteCodeSelectedCoreFiberRepresentativeComparison_refl
    finiteCodeSelectiveTwoToSupportHom
    finiteCodeSelectiveTwoToSupportHom.representative
    (FiniteCodeCartHom.ofPresentation_representative
      finiteCodeSelectiveTwoToSupportHom)

/-- Reversing the padded comparison gives the generated canonical-to-padded comparison. -/
theorem finiteCodeSelectivePaddedCanonicalComparison_symm :
    finiteCodeSelectivePaddedCanonicalComparison.symm =
      finiteCodeSelectedCoreFiberRepresentativeComparison
        finiteCodeSelectiveTwoToSupportHom
        finiteCodeSelectiveTwoToSupportHom.representative
        finitePaddedSelectiveTwoToSupportPresentation
        (FiniteCodeCartHom.ofPresentation_representative
          finiteCodeSelectiveTwoToSupportHom)
        finiteCodePaddedSelectiveTwoToSupportPresentation_eq := by
  simpa only [finiteCodeSelectivePaddedCanonicalComparison,
    finiteCodeSelectedCoreFiberCanonicalComparison] using
      finiteCodeSelectedCoreFiberRepresentativeComparison_symm
        finiteCodeSelectiveTwoToSupportHom
        finitePaddedSelectiveTwoToSupportPresentation
        finiteCodeSelectiveTwoToSupportHom.representative
        finiteCodePaddedSelectiveTwoToSupportPresentation_eq
        (FiniteCodeCartHom.ofPresentation_representative
          finiteCodeSelectiveTwoToSupportHom)

/-- Canonical, padded, and `Quotient.out` representatives satisfy the cocycle. -/
theorem finiteCodeSelectiveRepresentativeComparison_cocycle :
    (finiteCodeSelectedCoreFiberRepresentativeComparison
      finiteCodeSelectiveTwoToSupportHom
      finiteSelectiveTwoToSupportPresentation
      finitePaddedSelectiveTwoToSupportPresentation
      finiteCodeSelectiveTwoToSupportPresentation_eq
      finiteCodePaddedSelectiveTwoToSupportPresentation_eq).trans
        finiteCodeSelectivePaddedCanonicalComparison =
      finiteCodeSelectedCoreFiberRepresentativeComparison
        finiteCodeSelectiveTwoToSupportHom
        finiteSelectiveTwoToSupportPresentation
        finiteCodeSelectiveTwoToSupportHom.representative
        finiteCodeSelectiveTwoToSupportPresentation_eq
        (FiniteCodeCartHom.ofPresentation_representative
          finiteCodeSelectiveTwoToSupportHom) := by
  simpa only [finiteCodeSelectivePaddedCanonicalComparison,
    finiteCodeSelectedCoreFiberCanonicalComparison] using
      finiteCodeSelectedCoreFiberRepresentativeComparison_cocycle
        finiteCodeSelectiveTwoToSupportHom
        finiteSelectiveTwoToSupportPresentation
        finitePaddedSelectiveTwoToSupportPresentation
        finiteCodeSelectiveTwoToSupportHom.representative
        finiteCodeSelectiveTwoToSupportPresentation_eq
        finiteCodePaddedSelectiveTwoToSupportPresentation_eq
        (FiniteCodeCartHom.ofPresentation_representative
          finiteCodeSelectiveTwoToSupportHom)

/-! ## Quotient compositor and unitor -/

/-- The quotient compositor on the two-to-one-to-support chain. -/
noncomputable def finiteCodeSelectiveQuotientCompositorApp :
    (finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveOneToSupportHom ⋙
      finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveTwoToOneHom).obj finiteReindexFourAxisTarget ≅
      (finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveTwoToSupportHom).obj
          finiteReindexFourAxisTarget :=
  finiteCodeSelectedCoreFiberCompositorApp
    finiteCodeSelectiveTwoToOneHom finiteCodeSelectiveOneToSupportHom
    finiteReindexFourAxisTarget

/-- The concrete quotient compositor satisfies its forward two-step triangle. -/
theorem finiteCodeSelectiveQuotientCompositorApp_hom_fac :
    finiteCodeSelectiveQuotientCompositorApp.hom.1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift
          finiteCodeSelectiveTwoToSupportHom
          finiteReindexFourAxisTarget).hom =
      (selectedCoreFiberIteratedCartesianLift
        finiteCodeSelectiveTwoToOneHom.representative
        finiteCodeSelectiveOneToSupportHom.representative
        finiteReindexFourAxisTarget).hom :=
  finiteCodeSelectedCoreFiberCompositorApp_hom_fac
    finiteCodeSelectiveTwoToOneHom finiteCodeSelectiveOneToSupportHom
    finiteReindexFourAxisTarget

/-- The inverse concrete quotient compositor satisfies the reverse triangle. -/
theorem finiteCodeSelectiveQuotientCompositorApp_inv_fac :
    finiteCodeSelectiveQuotientCompositorApp.inv.1 ≫
        (selectedCoreFiberIteratedCartesianLift
          finiteCodeSelectiveTwoToOneHom.representative
          finiteCodeSelectiveOneToSupportHom.representative
          finiteReindexFourAxisTarget).hom =
      (finiteCodeSelectedCoreFiberCartesianLift
        finiteCodeSelectiveTwoToSupportHom
        finiteReindexFourAxisTarget).hom :=
  finiteCodeSelectedCoreFiberCompositorApp_inv_fac
    finiteCodeSelectiveTwoToOneHom finiteCodeSelectiveOneToSupportHom
    finiteReindexFourAxisTarget

/-- Quotient-compositor naturality fires on the genuine four-axis swap. -/
theorem finiteCodeSelectiveQuotientCompositor_naturality :
    (finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveOneToSupportHom ⋙
      finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveTwoToOneHom).map finiteReindexAxisSwapHom ≫
        finiteCodeSelectiveQuotientCompositorApp.hom =
      finiteCodeSelectiveQuotientCompositorApp.hom ≫
        (finiteCodeSelectedCoreFiberReindexFunctor
          finiteCodeSelectiveTwoToSupportHom).map
            finiteReindexAxisSwapHom :=
  finiteCodeSelectedCoreFiberCompositor_naturality
    finiteCodeSelectiveTwoToOneHom finiteCodeSelectiveOneToSupportHom
    finiteReindexAxisSwapHom

/-- The whole quotient compositor on the selective two-step chain. -/
noncomputable def finiteCodeSelectiveQuotientCompositor :
    finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveOneToSupportHom ⋙
      finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveTwoToOneHom ≅
      finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveTwoToSupportHom :=
  finiteCodeSelectedCoreFiberCompositor
    finiteCodeSelectiveTwoToOneHom finiteCodeSelectiveOneToSupportHom

/-- The quotient unitor at the finite support endpoint. -/
noncomputable def finiteCodeSupportQuotientUnitorApp :
    finiteReindexFourAxisTarget ≅
      (finiteCodeSelectedCoreFiberReindexFunctor
        (𝟙 finitePortfolioSupportInstance)).obj
          finiteReindexFourAxisTarget :=
  finiteCodeSelectedCoreFiberUnitorApp finitePortfolioSupportInstance
    finiteReindexFourAxisTarget

/-- The concrete quotient unitor satisfies its forward selected-lift triangle. -/
theorem finiteCodeSupportQuotientUnitorApp_hom_fac :
    finiteCodeSupportQuotientUnitorApp.hom.1 ≫
        (finiteCodeSelectedCoreFiberCartesianLift
          (𝟙 finitePortfolioSupportInstance)
          finiteReindexFourAxisTarget).hom =
      𝟙 finiteReindexFourAxisTarget.1 :=
  finiteCodeSelectedCoreFiberUnitorApp_hom_fac
    finitePortfolioSupportInstance finiteReindexFourAxisTarget

/-- The inverse quotient unitor component is the selected quotient identity lift. -/
theorem finiteCodeSupportQuotientUnitorApp_inv :
    finiteCodeSupportQuotientUnitorApp.inv.1 =
      (finiteCodeSelectedCoreFiberCartesianLift
        (𝟙 finitePortfolioSupportInstance)
        finiteReindexFourAxisTarget).hom :=
  finiteCodeSelectedCoreFiberUnitorApp_inv
    finitePortfolioSupportInstance finiteReindexFourAxisTarget

/-- Quotient-unitor naturality fires on the genuine four-axis swap. -/
theorem finiteCodeSupportQuotientUnitor_naturality :
    finiteReindexAxisSwapHom ≫ finiteCodeSupportQuotientUnitorApp.hom =
      finiteCodeSupportQuotientUnitorApp.hom ≫
        (finiteCodeSelectedCoreFiberReindexFunctor
          (𝟙 finitePortfolioSupportInstance)).map
            finiteReindexAxisSwapHom :=
  finiteCodeSelectedCoreFiberUnitor_naturality
    finitePortfolioSupportInstance finiteReindexAxisSwapHom

/-- The whole quotient unitor at the finite support endpoint. -/
noncomputable def finiteCodeSupportQuotientUnitor :
    Functor.id (CoreFiber finitePortfolioSupportInstance.toSemantic) ≅
      finiteCodeSelectedCoreFiberReindexFunctor
        (𝟙 finitePortfolioSupportInstance) :=
  finiteCodeSelectedCoreFiberUnitor finitePortfolioSupportInstance

/-! ## Packaged pseudoaction projections -/

/-- The packaged pseudoaction exposes the finite support core fiber as its object. -/
theorem finiteCodeSupportPseudoaction_obj :
    (finiteCodeSelectedCoreFiberReindexPseudoaction
      (U := FiniteModel.carrier)).obj
        (LocallyDiscrete.mk
          (Opposite.op finitePortfolioSupportInstance)) =
      Cat.of (CoreFiber finitePortfolioSupportInstance.toSemantic) := by
  simpa using
    finiteCodeSelectedCoreFiberReindexPseudoaction_obj
      (U := FiniteModel.carrier)
      (LocallyDiscrete.mk (Opposite.op finitePortfolioSupportInstance))

/-- The packaged morphism action is the selected action of the noninvertible leg. -/
theorem finiteCodeSelectivePseudoaction_map :
    (finiteCodeSelectedCoreFiberReindexPseudoaction
      (U := FiniteModel.carrier)).map
        (Quiver.Hom.op
          (X := (finiteSelectiveTwoInstance :
            FiniteCodeCartCategory FiniteModel.carrier))
          (Y := (finiteSelectiveOneInstance :
            FiniteCodeCartCategory FiniteModel.carrier))
          finiteCodeSelectiveTwoToOneHom).toLoc =
      (finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveTwoToOneHom).toCatHom := by
  simpa using
    finiteCodeSelectedCoreFiberReindexPseudoaction_map
      (U := FiniteModel.carrier)
      (Quiver.Hom.op
        (X := (finiteSelectiveTwoInstance :
          FiniteCodeCartCategory FiniteModel.carrier))
        (Y := (finiteSelectiveOneInstance :
          FiniteCodeCartCategory FiniteModel.carrier))
        finiteCodeSelectiveTwoToOneHom).toLoc

/-- The packaged identity comparison is the inverse concrete quotient unitor. -/
theorem finiteCodeSupportPseudoaction_mapId :
    (finiteCodeSelectedCoreFiberReindexPseudoaction
      (U := FiniteModel.carrier)).mapId
        (LocallyDiscrete.mk
          (Opposite.op finitePortfolioSupportInstance)) =
      Cat.Hom.isoMk finiteCodeSupportQuotientUnitor.symm := by
  simpa only [finiteCodeSupportQuotientUnitor] using
    finiteCodeSelectedCoreFiberReindexPseudoaction_mapId
      (U := FiniteModel.carrier)
      (LocallyDiscrete.mk (Opposite.op finitePortfolioSupportInstance))

/-- The packaged composition comparison is the inverse selective quotient compositor. -/
theorem finiteCodeSelectivePseudoaction_mapComp :
    (finiteCodeSelectedCoreFiberReindexPseudoaction
      (U := FiniteModel.carrier)).mapComp
        (Quiver.Hom.op
          (X := (finiteSelectiveOneInstance :
            FiniteCodeCartCategory FiniteModel.carrier))
          (Y := (finitePortfolioSupportInstance :
            FiniteCodeCartCategory FiniteModel.carrier))
          finiteCodeSelectiveOneToSupportHom).toLoc
        (Quiver.Hom.op
          (X := (finiteSelectiveTwoInstance :
            FiniteCodeCartCategory FiniteModel.carrier))
          (Y := (finiteSelectiveOneInstance :
            FiniteCodeCartCategory FiniteModel.carrier))
          finiteCodeSelectiveTwoToOneHom).toLoc =
      Cat.Hom.isoMk finiteCodeSelectiveQuotientCompositor.symm := by
  simpa only [finiteCodeSelectiveQuotientCompositor] using
    finiteCodeSelectedCoreFiberReindexPseudoaction_mapComp
      (U := FiniteModel.carrier)
      (Quiver.Hom.op
        (X := (finiteSelectiveOneInstance :
          FiniteCodeCartCategory FiniteModel.carrier))
        (Y := (finitePortfolioSupportInstance :
          FiniteCodeCartCategory FiniteModel.carrier))
        finiteCodeSelectiveOneToSupportHom).toLoc
      (Quiver.Hom.op
        (X := (finiteSelectiveTwoInstance :
          FiniteCodeCartCategory FiniteModel.carrier))
        (Y := (finiteSelectiveOneInstance :
          FiniteCodeCartCategory FiniteModel.carrier))
        finiteCodeSelectiveTwoToOneHom).toLoc

/-! ## Representative compatibility and quotient coherence -/

/-- The padded direct representative compositor descends to the quotient compositor. -/
theorem finiteCodePaddedSelectiveRepresentativeCompositor_compatibility :
    (finiteCodeSelectedCoreFiberRepresentativeCompositor
      finiteCodeSelectiveTwoToOneHom finiteCodeSelectiveOneToSupportHom
      finitePaddedSelectiveTwoToSupportPresentation
      finiteSelectiveTwoToOnePresentation
      finiteSelectiveOneToSupportPresentation
      finiteCodePaddedSelectiveTwoToSupportPresentation_eq rfl rfl).trans
        (finiteCodeSelectedCoreFiberCanonicalComparison
          finiteCodeSelectiveTwoToSupportHom
          finitePaddedSelectiveTwoToSupportPresentation
          finiteCodePaddedSelectiveTwoToSupportPresentation_eq) =
      (finiteCodeSelectedCoreFiberRepresentativeHorizontalComparison
        finiteCodeSelectiveTwoToOneHom finiteCodeSelectiveOneToSupportHom
        finiteSelectiveTwoToOnePresentation
        finiteSelectiveOneToSupportPresentation rfl rfl).trans
          (finiteCodeSelectedCoreFiberCompositor
            finiteCodeSelectiveTwoToOneHom
            finiteCodeSelectiveOneToSupportHom) :=
  finiteCodeSelectedCoreFiberRepresentativeCompositor_compatibility
    finiteCodeSelectiveTwoToOneHom finiteCodeSelectiveOneToSupportHom
    finitePaddedSelectiveTwoToSupportPresentation
    finiteSelectiveTwoToOnePresentation
    finiteSelectiveOneToSupportPresentation
    finiteCodePaddedSelectiveTwoToSupportPresentation_eq rfl rfl

/-- The padded identity representative unitor descends to the quotient unitor. -/
theorem finiteCodePaddedSupportRepresentativeUnitor_compatibility :
    (finiteCodeSelectedCoreFiberRepresentativeUnitor
      finitePortfolioSupportInstance finitePaddedSupportIdentityPresentation
      finiteCodePaddedSupportIdentityPresentation_eq).trans
        (finiteCodeSelectedCoreFiberCanonicalComparison
          (𝟙 finitePortfolioSupportInstance)
          finitePaddedSupportIdentityPresentation
          finiteCodePaddedSupportIdentityPresentation_eq) =
      finiteCodeSelectedCoreFiberUnitor finitePortfolioSupportInstance :=
  finiteCodeSelectedCoreFiberRepresentativeUnitor_compatibility
    finitePortfolioSupportInstance finitePaddedSupportIdentityPresentation
    finiteCodePaddedSupportIdentityPresentation_eq

/-- Quotient associativity fires on the nondegenerate three-step selective chain. -/
theorem finiteCodeSelectiveQuotientCompositor_assoc :
    finiteCodeSelectedCoreFiberAssocLeftRoute
        finiteCodeSelectiveThreeToTwoHom
        finiteCodeSelectiveTwoToOneHom
        finiteCodeSelectiveOneToSupportHom
        finiteReindexFourAxisTarget =
      finiteCodeSelectedCoreFiberAssocRightRoute
        finiteCodeSelectiveThreeToTwoHom
        finiteCodeSelectiveTwoToOneHom
        finiteCodeSelectiveOneToSupportHom
        finiteReindexFourAxisTarget :=
  finiteCodeSelectedCoreFiberCompositor_assoc
    finiteCodeSelectiveThreeToTwoHom finiteCodeSelectiveTwoToOneHom
    finiteCodeSelectiveOneToSupportHom finiteReindexFourAxisTarget

/-- Source-unit coherence fires on the noninvertible two-to-support quotient arrow. -/
theorem finiteCodeSelectiveQuotientCompositor_left_unit :
    finiteCodeSelectedCoreFiberLeftUnitRoute
        finiteCodeSelectiveTwoToSupportHom finiteReindexFourAxisTarget =
      𝟙 ((finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveTwoToSupportHom).obj
          finiteReindexFourAxisTarget) :=
  finiteCodeSelectedCoreFiberCompositor_left_unit
    finiteCodeSelectiveTwoToSupportHom finiteReindexFourAxisTarget

/-- Target-unit coherence fires on the same noninvertible quotient arrow. -/
theorem finiteCodeSelectiveQuotientCompositor_right_unit :
    finiteCodeSelectedCoreFiberRightUnitRoute
        finiteCodeSelectiveTwoToSupportHom finiteReindexFourAxisTarget =
      𝟙 ((finiteCodeSelectedCoreFiberReindexFunctor
        finiteCodeSelectiveTwoToSupportHom).obj
          finiteReindexFourAxisTarget) :=
  finiteCodeSelectedCoreFiberCompositor_right_unit
    finiteCodeSelectiveTwoToSupportHom finiteReindexFourAxisTarget

/-! ## Independent nondegeneracy controls -/

/-- The quotient two-to-one leg retains its independently proved noninvertibility. -/
theorem finiteCodeSelectiveTwoToOneHom_not_isIso :
    ¬ IsIso
      (FiniteCodeCartHom.toSemantic finiteCodeSelectiveTwoToOneHom) := by
  simpa only [finiteCodeSelectiveTwoToOneHom,
    FiniteCodeCartHom.toSemantic_ofPresentation,
    typedRealizableHom_hom] using
      finitePresentationDescentCompositorFirstLeg_not_isIso

/-- The direct quotient composite also retains the selective noninvertibility witness. -/
theorem finiteCodeSelectiveTwoToSupportHom_not_isIso :
    ¬ IsIso
      (FiniteCodeCartHom.toSemantic finiteCodeSelectiveTwoToSupportHom) := by
  rw [← finiteCodeSelectiveTwoToSupportPresentation_eq]
  simpa only [FiniteCodeCartHom.toSemantic_ofPresentation,
    typedRealizableHom_hom] using
      finitePresentationDescentSelectiveLeg_not_isIso

/-- The vertical map used by all quotient naturality laws is genuinely nonidentity. -/
theorem finiteCodePseudoactionWitnessAxisSwap_ne_id :
    finiteReindexAxisSwapHom ≠ 𝟙 finiteReindexFourAxisTarget :=
  finitePresentationDescentAxisSwap_ne_id

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
