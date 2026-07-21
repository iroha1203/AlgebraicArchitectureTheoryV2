import Formal.AG.Cohomology.PeriodStokes
import Formal.AG.Examples.DerivedPart5
import Formal.AG.Measurement.FiniteRegime
import Formal.AG.Measurement.Packet

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII theorem 12.3: finite AAT-GAGA comparison.

The certified comparison is rooted in a generated finite-poset Čech source.
The source fixes the actual site, adequate cover, obstruction sheaf,
coefficient ring, canonical differential, and its nerve presentation before
any Hodge, period, capacity, or derived reading is formed.
-/

/-- VIII.Theorem 12.3: source data for one selected finite Čech comparison. -/
structure AATGAGAFiniteCechSource (M : MeasurementProfile.{u, v})
    [Field M.Coeff] where
  /-- The selected finite-poset site, adequate cover, coefficient sheaf, and
  canonical Čech differential. -/
  geometry : FiniteMeasurementGeometry M
  /-- Context selected from the actual finite-poset site. -/
  selectedContext : geometry.coverGeometry.ContextIndex
  /-- Cover index selected from the actual adequate cover. -/
  selectedCoverIndex : geometry.coverGeometry.cover.Index
  /-- The selected nerve presented by canonical Čech simplices. -/
  nerve : Cohomology.CoverNerve
  /-- The selected nerve cochain complex, over the profile coefficient field. -/
  nerveComplex : Cohomology.FiniteNerveCochainComplex nerve M.Coeff
  /-- The nerve vertices are the actual generated Čech zero-simplices. -/
  chartToCanonical : nerve.Chart ≃
    Site.FinitePosetCechSimplex geometry.coefficientRegime 0
  /-- The nerve edges are the actual generated Čech one-simplices. -/
  edgeToCanonical : nerve.EdgeComponent ≃
    Site.FinitePosetCechSimplex geometry.coefficientRegime 1
  /-- The nerve faces are the actual generated Čech two-simplices. -/
  faceToCanonical : nerve.FaceComponent ≃
    Site.FinitePosetCechSimplex geometry.coefficientRegime 2
  /-- Degree-zero nerve cochains compare with the generated canonical cochains. -/
  zeroToCanonical : nerveComplex.C0 ≃+ geometry.CechCochain 0
  /-- Degree-one nerve cochains compare with the generated canonical cochains. -/
  oneToCanonical : nerveComplex.C1 ≃+ geometry.CechCochain 1
  /-- Degree-two nerve cochains compare with the generated canonical cochains. -/
  twoToCanonical : nerveComplex.C2 ≃+ geometry.CechCochain 2
  /-- The selected degree-zero differential is the canonical Čech differential. -/
  d0_toCanonical : ∀ c : nerveComplex.C0,
    oneToCanonical (nerveComplex.d0 c) =
      geometry.cechComplex.differential 0 (zeroToCanonical c)
  /-- The selected degree-one differential is the canonical Čech differential. -/
  d1_toCanonical : ∀ c : nerveComplex.C1,
    twoToCanonical (nerveComplex.d1 c) =
      geometry.cechComplex.differential 1 (oneToCanonical c)

namespace AATGAGAFiniteCechSource

/-- The profile site selected through the actual finite-poset realization. -/
def selectedSite {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) : M.SiteObj :=
  S.geometry.siteObjEquiv.symm S.selectedContext

/-- The profile cover selected through the actual adequate-cover realization. -/
def selectedCover {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) : M.Cover :=
  S.geometry.coverEquiv.symm S.selectedCoverIndex

/-- Capacity is read from the profile-coefficient nerve complex. -/
def topologicalCapacityStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) : Prop :=
  Module.finrank M.Coeff S.nerveComplex.C1 <=
    Module.finrank M.Coeff S.nerveComplex.H1 +
      Module.finrank M.Coeff S.nerveComplex.C0 +
        Module.finrank M.Coeff S.nerveComplex.C2

/-- Derive capacity from the selected profile-coefficient nerve complex. -/
theorem topologicalCapacityStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) : S.topologicalCapacityStatement :=
  S.nerveComplex.topologicalDebtCapacity_fromComplex

end AATGAGAFiniteCechSource

/-- VIII.Theorem 12.3: real Hodge realization of a selected profile Čech complex. -/
structure AATGAGARealCechHodgeInput {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (S : AATGAGAFiniteCechSource M) where
  /-- Real coordinates for the selected canonical Čech zero-cochains. -/
  RealC0 : Type v
  /-- Real coordinates for the selected canonical Čech one-cochains. -/
  RealC1 : Type v
  /-- Real coordinates for the selected canonical Čech two-cochains. -/
  RealC2 : Type v
  /-- Normed group structure on selected zero-cochain coordinates. -/
  [zeroNormed : NormedAddCommGroup RealC0]
  /-- Inner product on selected zero-cochain coordinates. -/
  [zeroInner : InnerProductSpace ℝ RealC0]
  /-- Finiteness of selected zero-cochain coordinates. -/
  [zeroFinite : @Module.Finite ℝ RealC0 _ _
    ((@InnerProductSpace.toNormedSpace ℝ RealC0 _ _ zeroInner).toModule)]
  /-- Normed group structure on selected one-cochain coordinates. -/
  [oneNormed : NormedAddCommGroup RealC1]
  /-- Inner product on selected one-cochain coordinates. -/
  [oneInner : InnerProductSpace ℝ RealC1]
  /-- Finiteness of selected one-cochain coordinates. -/
  [oneFinite : @Module.Finite ℝ RealC1 _ _
    ((@InnerProductSpace.toNormedSpace ℝ RealC1 _ _ oneInner).toModule)]
  /-- Normed group structure on selected two-cochain coordinates. -/
  [twoNormed : NormedAddCommGroup RealC2]
  /-- Inner product on selected two-cochain coordinates. -/
  [twoInner : InnerProductSpace ℝ RealC2]
  /-- Finiteness of selected two-cochain coordinates. -/
  [twoFinite : @Module.Finite ℝ RealC2 _ _
    ((@InnerProductSpace.toNormedSpace ℝ RealC2 _ _ twoInner).toModule)]
  /-- Additive coordinate identifications for the selected canonical Čech complex. -/
  zeroToReal : S.nerveComplex.C0 ≃+ RealC0
  oneToReal : S.nerveComplex.C1 ≃+ RealC1
  twoToReal : S.nerveComplex.C2 ≃+ RealC2
  /-- The real Hodge complex transported from the selected canonical Čech cochains. -/
  realFiniteComplex : RealFiniteInnerProductComplex RealC0 RealC1 RealC2
  /-- The real degree-zero map is the selected Čech differential in these coordinates. -/
  d0Real_eq_profile : ∀ c,
    realFiniteComplex.dPrev (zeroToReal c) = oneToReal (S.nerveComplex.d0 c)
  /-- The real degree-one map is the selected Čech differential in these coordinates. -/
  d1Real_eq_profile : ∀ c,
    realFiniteComplex.dNext (oneToReal c) = twoToReal (S.nerveComplex.d1 c)

namespace AATGAGARealCechHodgeInput

/-- Hodge and harmonic/cohomology conclusions for the selected Čech model. -/
def hodgeStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) : Prop := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  exact (∀ c, H.realFiniteComplex.exactPart c + H.realFiniteComplex.harmonicPart c +
      H.realFiniteComplex.coexactPart c = c) ∧
    Nonempty (H.realFiniteComplex.laplacian.ker ≃ₗ[ℝ] H.realFiniteComplex.cohomology)

/-- Derive the selected Hodge and harmonic/cohomology statements. -/
theorem hodgeStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) :
    H.hodgeStatement := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  exact ⟨H.realFiniteComplex.hodge_decomposition,
    ⟨H.realFiniteComplex.laplacianKernelEquivCohomology⟩⟩

/-- Period/Stokes on the selected real Čech differential and its adjoint chain map. -/
def periodStokesStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) : Prop := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  exact ∀ (omega : H.RealC0) (gamma : H.RealC1),
    inner ℝ (H.realFiniteComplex.dPrev omega) gamma =
      inner ℝ omega (H.realFiniteComplex.dPrev.adjoint gamma)

/-- Derive Period/Stokes from the adjoint of the selected real Čech map. -/
theorem periodStokesStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {S : AATGAGAFiniteCechSource M} (H : AATGAGARealCechHodgeInput S) :
    H.periodStokesStatement := by
  letI := H.zeroNormed
  letI := H.zeroInner
  letI := H.zeroFinite
  letI := H.oneNormed
  letI := H.oneInner
  letI := H.oneFinite
  letI := H.twoNormed
  letI := H.twoInner
  letI := H.twoFinite
  intro omega gamma
  simpa using (H.realFiniteComplex.dPrev.adjoint_inner_right omega gamma).symm

end AATGAGARealCechHodgeInput

/-- VIII.Theorem 12.3: finite data shared by every certified comparison. -/
structure AATGAGACommonFiniteData (M : MeasurementProfile.{u, v}) [Field M.Coeff] where
  /-- The finite Čech source shared by all certified axes. -/
  finiteCechSource : AATGAGAFiniteCechSource M
  /-- The measurement-domain element selected for the comparison. -/
  selectedMeasurement : M.Domain
  /-- Evidence that the selected measurement belongs to the measured profile. -/
  measuredSelection : M.Measured_M selectedMeasurement
  /-- The common ambient used for the selected law-ideal reading. -/
  commonAmbient : CommonAmbientPair M
  /-- The left ambient domain is the selected measurement-domain element. -/
  ambientLeftDomain_eq : commonAmbient.leftDomain = selectedMeasurement
  /-- The right ambient domain is the selected measurement-domain element. -/
  ambientRightDomain_eq : commonAmbient.rightDomain = selectedMeasurement

namespace AATGAGACommonFiniteData

/-- The site used by all axes is read from the finite Čech source. -/
def selectedSite {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) : M.SiteObj :=
  C.finiteCechSource.selectedSite

/-- The cover used by all axes is read from the finite Čech source. -/
def selectedCover {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) : M.Cover :=
  C.finiteCechSource.selectedCover

/-- Coherence facts tying every selected datum to its source realization. -/
def coherent {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) : Prop :=
  M.InScope C.selectedMeasurement ∧
    C.commonAmbient.leftDomain = C.selectedMeasurement ∧
      C.commonAmbient.rightDomain = C.selectedMeasurement

/-- The selected finite data satisfy their direct realization equalities. -/
theorem coherent_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) : C.coherent :=
  ⟨C.measuredSelection.inScope, C.ambientLeftDomain_eq, C.ambientRightDomain_eq⟩

end AATGAGACommonFiniteData

/-- VIII.Theorem 12.3: common-ambient reading of the selected monomial conflict. -/
structure SelectedDerivedConflictTheoremPackage {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) where
  /-- Reading of common-ambient law ideals as shared-witness monomial ideals. -/
  readLawIdeal : C.commonAmbient.LawIdeal →
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
  /-- The left common-ambient law ideal reads as `idealU`. -/
  leftIdeal_eq : readLawIdeal C.commonAmbient.leftLawIdeal =
    Derived.Counterexample.SharedWitnessCoord.idealU M.Coeff
  /-- The right common-ambient law ideal reads as `idealV`. -/
  rightIdeal_eq : readLawIdeal C.commonAmbient.rightLawIdeal =
    Derived.Counterexample.SharedWitnessCoord.idealV M.Coeff

namespace SelectedDerivedConflictTheoremPackage

/-- The left monomial ideal read from the common ambient. -/
def leftIdeal {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff) :=
  P.readLawIdeal C.commonAmbient.leftLawIdeal

/-- The right monomial ideal read from the common ambient. -/
def rightIdeal {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Ideal (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff) :=
  P.readLawIdeal C.commonAmbient.rightLawIdeal

/-- The degree-one LawConflict object computed by the canonical Tor bridge. -/
abbrev lawConflict {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :=
  (Derived.Intersection.canonicalSelectedTorBridge
    (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
    P.leftIdeal P.rightIdeal).LawConflict 1

/-- The canonical degree-one LawConflict/Mathlib Tor equivalence. -/
noncomputable def lawConflictLinearEquivMathlibTor {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    P.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
      Derived.Intersection.mathlibTor
        (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
        P.leftIdeal P.rightIdeal 1 :=
  (Derived.Intersection.canonicalSelectedTorBridge
    (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
    P.leftIdeal P.rightIdeal).lawConflictLinearEquivMathlibTor 1

/-- The selected LawConflict has the canonical Tor reading. -/
theorem lawConflictTorReading_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    Nonempty
      (P.lawConflict ≃ₗ[Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
        Derived.Intersection.mathlibTor
          (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
          P.leftIdeal P.rightIdeal 1) :=
  ⟨P.lawConflictLinearEquivMathlibTor⟩

/-- Monomial Hilbert-series accounting over the profile coefficient ring. -/
def profileCoefficientHilbertIdentity (M : MeasurementProfile.{u, v}) [Field M.Coeff] : Prop :=
  let G := FiniteModel.DerivedPart5.sharedWitnessG5IdentityPackage M.Coeff
  G.regime.quotientUHilbertSeries * G.regime.quotientVHilbertSeries =
    G.regime.ambientHilbertSeries * G.conflictAlternatingSum

/-- Monomial Hilbert-series accounting over the profile coefficient ring. -/
def hilbertSeriesAccountingStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) : Prop :=
  (P.leftIdeal = Derived.Counterexample.SharedWitnessCoord.idealU M.Coeff) ∧
    (P.rightIdeal = Derived.Counterexample.SharedWitnessCoord.idealV M.Coeff) ∧
      profileCoefficientHilbertIdentity M

/-- Derive selected monomial Hilbert-series accounting. -/
theorem hilbertSeriesAccounting_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (P : SelectedDerivedConflictTheoremPackage C) :
    P.hilbertSeriesAccountingStatement :=
  ⟨P.leftIdeal_eq, P.rightIdeal_eq, by
    simpa [profileCoefficientHilbertIdentity] using
      (FiniteModel.DerivedPart5.sharedWitnessG5IdentityPackage M.Coeff).denominatorClearedIdentity⟩

end SelectedDerivedConflictTheoremPackage

/-- VIII.Theorem 12.3: theorem inputs over one common selected finite datum. -/
structure AATGAGACertifiedFields {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (C : AATGAGACommonFiniteData M) where
  /-- The selected real reading of the source Čech complex. -/
  hodgeInput : AATGAGARealCechHodgeInput C.finiteCechSource
  /-- Input from which LawConflict/Tor and Hilbert readings are derived. -/
  derivedConflictInput : SelectedDerivedConflictTheoremPackage C

/-- VIII.Principle 12.4: candidate interfaces remain separate from certified results. -/
structure AATGAGACandidateInterfaces (M : MeasurementProfile.{u, v}) where
  MonotoneWitnessStabilityInterface : Type v
  FiniteCechStabilityInterface : Type v
  FlatBaseChangeInterface : Type v
  SpectralHotspotInterface : Type v
  TransferLowerBoundInterface : Type v
  monotoneWitnessStability : Option MonotoneWitnessStabilityInterface
  finiteCechStability : Option FiniteCechStabilityInterface
  flatBaseChange : Option FlatBaseChangeInterface
  spectralHotspot : Option SpectralHotspotInterface
  transferLowerBound : Option TransferLowerBoundInterface

/-- VIII.Principle 12.4: non-conclusion data retained outside the theorem statement. -/
structure AATGAGANonConclusionData (M : MeasurementProfile.{u, v}) where
  noExternalDataSourceFidelity : Prop
  noExternalDataSourceFidelity_cert : noExternalDataSourceFidelity
  noExternalProcedureCorrectness : Prop
  noExternalProcedureCorrectness_cert : noExternalProcedureCorrectness
  noArbitraryLawUniverseComparison : Prop
  noArbitraryLawUniverseComparison_cert : noArbitraryLawUniverseComparison
  candidateDependentFieldsNotCertified : Prop
  candidateDependentFieldsNotCertified_cert : candidateDependentFieldsNotCertified

/-- VIII.Theorem 12.3: data that enter the certified finite comparison. -/
structure AATGAGAComparisonData (M : MeasurementProfile.{u, v}) [Field M.Coeff] where
  commonData : AATGAGACommonFiniteData M
  certifiedFields : AATGAGACertifiedFields commonData

/-- VIII.Theorem 12.3: certified comparison statement. -/
def aatGAGACertifiedComparisonStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) : Prop :=
  C.coherent ∧
    F.hodgeInput.hodgeStatement ∧
      F.hodgeInput.periodStokesStatement ∧
        C.finiteCechSource.topologicalCapacityStatement ∧
          Nonempty
            (F.derivedConflictInput.lawConflict ≃ₗ[
                Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
              Derived.Intersection.mathlibTor
                (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
                F.derivedConflictInput.leftIdeal F.derivedConflictInput.rightIdeal 1) ∧
            F.derivedConflictInput.hilbertSeriesAccountingStatement

/-- Derive every certified comparison conjunct from the selected finite data. -/
theorem aatGAGACertifiedComparisonStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) :
    aatGAGACertifiedComparisonStatement F :=
  ⟨C.coherent_holds, F.hodgeInput.hodgeStatement_holds,
    F.hodgeInput.periodStokesStatement_holds,
    C.finiteCechSource.topologicalCapacityStatement_holds,
    F.derivedConflictInput.lawConflictTorReading_holds,
    F.derivedConflictInput.hilbertSeriesAccounting_holds⟩

/-- VIII.Theorem 12.3: selected finite-profile comparison statement. -/
def aatGAGAComparisonStatement {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (D : AATGAGAComparisonData M) : Prop :=
  aatGAGACertifiedComparisonStatement D.certifiedFields

/-- Derive the comparison statement from common finite data. -/
theorem aatGAGAComparisonStatement_holds {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (D : AATGAGAComparisonData M) : aatGAGAComparisonStatement D :=
  aatGAGACertifiedComparisonStatement_holds D.certifiedFields

/-- VIII.Theorem 12.3 acceptance statement. -/
abbrev AATGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (D : AATGAGAComparisonData M) : Prop :=
  aatGAGAComparisonStatement D

/-- The certified finite comparison is derived from its selected inputs. -/
theorem aatGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    (D : AATGAGAComparisonData M) : AATGAGAFiniteMeasurementComparison D :=
  aatGAGAComparisonStatement_holds D

end Measurement
end AAT.AG
