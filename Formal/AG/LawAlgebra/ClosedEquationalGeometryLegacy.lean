import Formal.AG.Atom.LawfulnessZeroLegacy
import Formal.AG.Equation.Legacy
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Formal.Util.AssertStandardAxioms

/-!
# Legacy obstruction-valuation comparisons

This compatibility leaf compares equation-generated lawfulness with the older
law-indexed obstruction valuation. The standard closed-equational geometry
module uses `ArchitecturalEquationSystem` directly and does not import the
legacy bridge.
-/

noncomputable section

namespace AAT.AG.LawAlgebra

open CategoryTheory

universe u v

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {E : ArchitecturalEquationSystem S.contextPreorder}
variable (raw : RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (AATCommAlgCat k)]
variable (X : StandardArchitectureScheme raw)

/-- Required equation fulfillment agrees with zero in the legacy aggregate valuation. -/
theorem semanticLawfulAlong_iff_omegaU_zero
    (R : ClosedEquationalLawReading raw X E)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U)
    {Value : Type u}
    (valuation : ObstructionValuation U Value)
    (aggregation : ZeroReflectingAggregation Value valuation.domain
      E.toLegacyLawUniverse.RequiredIndex)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (hsound : ∀ i : E.toLegacyLawUniverse.RequiredIndex,
      ObstructionSound valuation
        (E.toLegacyLawUniverse.law i.1))
    (hcomplete : ∀ i : E.toLegacyLawUniverse.RequiredIndex,
      ObstructionComplete valuation
        (E.toLegacyLawUniverse.law i.1)) :
    SemanticLawfulAlong raw X R s ↔
      omegaU valuation E.toLegacyLawUniverse aggregation Obj =
        valuation.domain.zero :=
  (semanticLawfulAlong_iff_lawfulness raw X R s Obj hpoint).trans
    ((E.equationLawful_iff_legacyLawfulness Obj).trans
      (lawfulness_iff_omegaU_zero valuation
        E.toLegacyLawUniverse aggregation
        hsound hcomplete Obj))

/-- Required closed-subscheme factorization agrees with the legacy aggregate valuation. -/
theorem factorsThroughLawfulClosedSubscheme_iff_omegaU_zero
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (hexact : RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U)
    {Value : Type u}
    (valuation : ObstructionValuation U Value)
    (aggregation : ZeroReflectingAggregation Value valuation.domain
      E.toLegacyLawUniverse.RequiredIndex)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (hsound : ∀ i : E.toLegacyLawUniverse.RequiredIndex,
      ObstructionSound valuation
        (E.toLegacyLawUniverse.law i.1))
    (hcomplete : ∀ i : E.toLegacyLawUniverse.RequiredIndex,
      ObstructionComplete valuation
        (E.toLegacyLawUniverse.law i.1)) :
    Nonempty (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s) ↔
      omegaU valuation E.toLegacyLawUniverse aggregation Obj =
        valuation.domain.zero := by
  have hcorr := lawfulnessIdealFactorizationCorrespondence raw X R hR hclosed hexact s
  exact (hcorr.1.trans (hcorr.2.1.trans hcorr.2.2)).symm.trans
    (semanticLawfulAlong_iff_omegaU_zero raw X R s Obj valuation aggregation
      hpoint hsound hcomplete)

end AAT.AG.LawAlgebra

#assert_standard_axioms_only AAT.AG.LawAlgebra
