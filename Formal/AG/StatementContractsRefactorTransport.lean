import Formal.AG.Measurement.RefactorTransport

noncomputable section

/-!
Fixed statement contracts for Part VIII Definition 7.2 and Theorem 7.3.
-/

namespace AAT.AG
namespace Measurement

universe u v w

variable {M_X M_Y : MeasurementProfile.{u, v}}
variable {ρ : RefactorMorphism M_X M_Y}
variable {P : PullbackObstructionClass.{u, v, w} ρ}

/-- Fixed contract: selected finite sites are compared by an actual equivalence. -/
example (E : RefactorEquivalenceAssumptions ρ P) :
    M_X.SiteObj ≃ M_Y.SiteObj :=
  E.selectedFiniteSiteEquivalence

/-- Fixed contract: the site equivalence realizes the selected refactor map. -/
example (E : RefactorEquivalenceAssumptions ρ P) (x : M_X.SiteObj) :
    E.selectedFiniteSiteEquivalence x = ρ.selectedSiteMap x :=
  E.selectedFiniteSiteEquivalence_apply x

/-- Fixed contract: the ringed ambient isomorphism is the selected pullback. -/
example (E : RefactorEquivalenceAssumptions ρ P)
    (x : M_Y.ObstructionObject) :
    E.ringedAmbientIso x = ρ.selectedRingedAmbientComparison x :=
  E.ringedAmbientIso_apply x

/-- Fixed contract: the coefficient isomorphism is the selected comparison. -/
example (E : RefactorEquivalenceAssumptions ρ P) (x : M_Y.Coeff) :
    E.coefficientIso x = ρ.selectedCoefficientComparison x :=
  E.coefficientIso_apply x

/-- Fixed contract: the law-ideal isomorphism is the selected pullback. -/
example (E : RefactorEquivalenceAssumptions ρ P)
    (x : M_Y.ObstructionIdeal) :
    E.lawIdealPullbackIso x = ρ.selectedLawIdealPullback x :=
  E.lawIdealPullbackIso_apply x

/-- Fixed contract: witness readings realize the selected transformation. -/
example (E : RefactorEquivalenceAssumptions ρ P)
    (x : M_Y.WitnessVariables) :
    E.witnessReadingIso x = ρ.selectedWitnessComparison x :=
  E.witnessReadingIso_apply x

/-- Fixed contract: axis readings realize the selected transformation. -/
example (E : RefactorEquivalenceAssumptions ρ P)
    (x : M_Y.RepresentationFamily) :
    E.axisReadingIso x = ρ.selectedAxisComparison x :=
  E.axisReadingIso_apply x

/-- Fixed contract: the ringed ambient isomorphism is realized in degree zero. -/
example (E : RefactorEquivalenceAssumptions ρ P) (c : P.TargetC0) :
    P.sourceAmbientRealization (E.ambientCochainIso c) =
      E.ringedAmbientIso (P.targetAmbientRealization c) :=
  E.ambientCochainIso_realizes c

/-- Fixed contract: the coefficient isomorphism is realized in degree one. -/
example (E : RefactorEquivalenceAssumptions ρ P) (c : P.TargetC1) :
    P.sourceCoefficientRealization (E.coefficientCochainIso c) =
      E.coefficientIso (P.targetCoefficientRealization c) :=
  E.coefficientCochainIso_realizes c

/-- Fixed contract: the law-ideal isomorphism is realized in degree two. -/
example (E : RefactorEquivalenceAssumptions ρ P) (c : P.TargetC2) :
    P.sourceLawIdealRealization (E.lawIdealCochainIso c) =
      E.lawIdealPullbackIso (P.targetLawIdealRealization c) :=
  E.lawIdealCochainIso_realizes c

/-- Fixed contract: the selected degreewise maps construct a cochain equivalence. -/
example (E : RefactorEquivalenceAssumptions ρ P) :
    Cohomology.AdditiveThreeTermComplex.Equivalence
      P.sourceComplex P.targetComplex :=
  E.cochainEquivalence

/-- Fixed contract: pullback is the quotient map generated from cochains. -/
example (E : RefactorEquivalenceAssumptions ρ P) :
    P.targetComplex.H1 → P.sourceComplex.H1 :=
  P.pullback E

/-- Fixed contract: the generated quotient pullback preserves and reflects zero. -/
example (E : RefactorEquivalenceAssumptions ρ P)
    (targetClass : P.targetComplex.H1) :
    P.sourceComplex.H1IsZero (P.pullback E targetClass) ↔
      P.targetComplex.H1IsZero targetClass :=
  P.pullback_h1Zero_iff E targetClass

/-- Fixed contract: theorem 7.3 derives profile-zero preservation and reflection. -/
example (E : RefactorEquivalenceAssumptions ρ P)
    (targetClass : P.targetComplex.H1) :
    M_Y.Zero (P.targetDomain targetClass) ↔
      M_X.Zero (P.sourceDomain (P.pullback E targetClass)) :=
  refactorZero_iff_pullbackZero E targetClass

end Measurement
end AAT.AG
