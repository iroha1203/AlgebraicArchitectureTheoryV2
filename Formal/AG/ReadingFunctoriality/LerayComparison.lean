import Formal.AG.ReadingFunctoriality.Coverage
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Leray comparison foundations

This module owns the injective-resolution computation used by the selected
Čech-to-sheaf-cohomology comparison fixed by Part 4 R5c.
-/

noncomputable section

namespace AAT.AG.Cohomology

universe u

open CategoryTheory

private theorem addCommGrpIsGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} AddCommGrpCat.{u + 1} := by
  exact {
    locallySmall := by infer_instance
    hasFilteredColimitsOfSize := by infer_instance
    ab5OfSize := by infer_instance
    hasSeparator := HasSeparator.of_equivalence
      (forget₂ (ModuleCat.{u + 1} ℤ)
        AddCommGrpCat.{u + 1}).asEquivalence }

/--
Additive sheaves on an AAT site have enough injectives under the Part 4
`HasSheafify` premise.

The proof transfers sheafification to a small equivalent site, applies the
Grothendieck-abelian sheaf theorem, and then obtains enough injectives.  Thus
the injective-resolution premise required below is derived rather than added
to the fixed statement.
-/
theorem standardAddCommGrpSheafEnoughInjectives
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    EnoughInjectives (Sheaf S.topology AddCommGrpCat.{u + 1}) := by
  letI : IsGrothendieckAbelian.{u + 1} AddCommGrpCat.{u + 1} :=
    addCommGrpIsGrothendieckAbelian
  letI : Functor.IsDenseSubsite S.topology
      ((equivSmallModel.{u + 1} S.category).inverse.inducedTopology S.topology)
      (equivSmallModel.{u + 1} S.category).symm.inverse := by
    change Functor.IsDenseSubsite S.topology
      ((equivSmallModel.{u + 1} S.category).inverse.inducedTopology S.topology)
      (equivSmallModel.{u + 1} S.category).functor
    infer_instance
  letI : HasSheafify
      ((equivSmallModel.{u + 1} S.category).inverse.inducedTopology S.topology)
      AddCommGrpCat.{u + 1} :=
    Equivalence.hasSheafify
      ((equivSmallModel.{u + 1} S.category).inverse.inducedTopology S.topology)
      S.topology (equivSmallModel.{u + 1} S.category).symm
      AddCommGrpCat.{u + 1}
  letI : IsGrothendieckAbelian.{u + 1}
      (Sheaf S.topology AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  infer_instance

/--
The chosen injective resolution used to compute obstruction sheaf
cohomology.

Implementation notes: this definition constructs Mathlib's actual
`InjectiveResolution`; it does not store a user-supplied resolution or a
cohomology conclusion in a certificate.
-/
noncomputable def obstructionInjectiveResolution
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    InjectiveResolution Ob.toAddCommGrpSheaf := by
  letI := standardAddCommGrpSheafEnoughInjectives (S := S)
  exact InjectiveResolution.of Ob.toAddCommGrpSheaf

/--
Mathlib's Ext model of `H'` is computed by the chosen injective resolution.

Implementation notes: this is the library equivalence attached to the actual
injective resolution above, rather than an independently supplied comparison
isomorphism.
-/
noncomputable def obstructionHPrimeInjectiveEquiv
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (X : S.category) (n : Nat) :
    (Ob.toAddCommGrpSheaf).H' n X ≃+
      CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor
          (Sheaf S.topology AddCommGrpCat.{u + 1}) 0).obj
            ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
              (yoneda.obj X ⋙ AddCommGrpCat.free)))
        (obstructionInjectiveResolution Ob).cochainComplex n :=
  (obstructionInjectiveResolution Ob).extAddEquivCohomologyClass

end AAT.AG.Cohomology
