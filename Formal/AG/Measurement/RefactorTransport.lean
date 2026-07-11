import Formal.AG.Measurement.Stability

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII R5 / AC11-AC12 refactor functoriality and class transport.

The refactor transport surface is assumption-relative. It does not claim that
syntax-level refactors, external rewrites, or arbitrary profile morphisms
preserve measurement verdicts.
-/

/--
VIII.Definition 7.1: a refactor morphism between selected measurement profiles.

The morphism records only the selected comparison data used by the measurement
profile. Ringed ambient, law ideal, coefficient, witness, and axis comparison
compatibilities are explicit propositions supplied by the caller.
-/
structure RefactorMorphism (M_X M_Y : MeasurementProfile.{u, v}) where
  SiteMap : Type u
  rho : M_X.SiteObj -> M_Y.SiteObj -> Prop
  RingedAmbientComparison : Type u
  ringedAmbientComparison_cert : RingedAmbientComparison -> Prop
  LawIdealPullback : Type u
  lawIdealPullback_cert : LawIdealPullback -> Prop
  CoefficientComparison : Type v
  coefficientComparison_cert : CoefficientComparison -> Prop
  WitnessComparison : Type u
  witnessComparison_cert : WitnessComparison -> Prop
  AxisComparison : Type u
  axisComparison_cert : AxisComparison -> Prop
  selectedSiteMap : SiteMap
  selectedRingedAmbientComparison : RingedAmbientComparison
  selectedLawIdealPullback : LawIdealPullback
  selectedCoefficientComparison : CoefficientComparison
  selectedWitnessComparison : WitnessComparison
  selectedAxisComparison : AxisComparison
  selectedRingedAmbientComparison_cert :
    ringedAmbientComparison_cert selectedRingedAmbientComparison
  selectedLawIdealPullback_cert :
    lawIdealPullback_cert selectedLawIdealPullback
  selectedCoefficientComparison_cert :
    coefficientComparison_cert selectedCoefficientComparison
  selectedWitnessComparison_cert :
    witnessComparison_cert selectedWitnessComparison
  selectedAxisComparison_cert :
    axisComparison_cert selectedAxisComparison
  siteMapFinite : Prop
  siteMapFinite_cert : siteMapFinite
  lawCompatible : Prop
  lawCompatible_cert : lawCompatible
  coefficientCompatible : Prop
  coefficientCompatible_cert : coefficientCompatible
  witnessReadingCompatible : Prop
  witnessReadingCompatible_cert : witnessReadingCompatible
  axisReadingCompatible : Prop
  axisReadingCompatible_cert : axisReadingCompatible

namespace RefactorMorphism

/-- VIII.Definition 7.1: expose law compatibility for the selected morphism. -/
theorem lawCompatible_holds {M_X M_Y : MeasurementProfile.{u, v}}
    (ρ : RefactorMorphism M_X M_Y) : ρ.lawCompatible :=
  ρ.lawCompatible_cert

/-- VIII.Definition 7.1: expose coefficient compatibility for the selected morphism. -/
theorem coefficientCompatible_holds {M_X M_Y : MeasurementProfile.{u, v}}
    (ρ : RefactorMorphism M_X M_Y) : ρ.coefficientCompatible :=
  ρ.coefficientCompatible_cert

end RefactorMorphism

/--
VIII.Definition 7.2: pullback reading of selected obstruction classes.

The source and target class carriers are profile-relative handles. This records
the selected pullback `rho^*` only under an explicit coefficient comparison.
-/
structure PullbackObstructionClass {M_X M_Y : MeasurementProfile.{u, v}}
    (ρ : RefactorMorphism M_X M_Y) where
  SourceClass : Type u
  TargetClass : Type u
  pullback : TargetClass -> SourceClass
  sourceDomain : SourceClass -> M_X.Domain
  targetDomain : TargetClass -> M_Y.Domain
  coefficientComparisonFixed : Prop
  coefficientComparisonFixed_cert : coefficientComparisonFixed
  cechPullbackReading : Prop
  cechPullbackReading_cert : cechPullbackReading
  coverRelativePullbackReading : Prop
  coverRelativePullbackReading_cert : coverRelativePullbackReading
  pushforwardRequiresExtraStructure : Prop
  pushforwardRequiresExtraStructure_cert : pushforwardRequiresExtraStructure

namespace PullbackObstructionClass

/-- VIII.Definition 7.2: expose the selected Cech pullback reading. -/
theorem cechPullbackReading_holds {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y} (P : PullbackObstructionClass ρ) :
    P.cechPullbackReading :=
  P.cechPullbackReading_cert

/-- VIII.Definition 7.2: expose the boundary for pushforward readings. -/
theorem pushforwardRequiresExtraStructure_holds {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y} (P : PullbackObstructionClass ρ) :
    P.pushforwardRequiresExtraStructure :=
  P.pushforwardRequiresExtraStructure_cert

end PullbackObstructionClass

/--
VIII.Theorem 7.3 assumptions: selected equivalence data required for zero
verdict invariance.

Every preservation hypothesis is a field. The theorem below only uses the
supplied zero-preservation certificate under these explicit assumptions.
-/
structure RefactorEquivalenceAssumptions {M_X M_Y : MeasurementProfile.{u, v}}
    (ρ : RefactorMorphism M_X M_Y) where
  selectedFiniteSiteEquivalence : Prop
  selectedFiniteSiteEquivalence_cert : selectedFiniteSiteEquivalence
  ringedAmbientIso : ρ.ringedAmbientComparison_cert ρ.selectedRingedAmbientComparison -> Prop
  ringedAmbientIso_cert : ringedAmbientIso
    ρ.selectedRingedAmbientComparison_cert
  coefficientIso : ρ.coefficientComparison_cert ρ.selectedCoefficientComparison -> Prop
  coefficientIso_cert : coefficientIso
    ρ.selectedCoefficientComparison_cert
  lawIdealPullbackIso : ρ.lawIdealPullback_cert ρ.selectedLawIdealPullback -> Prop
  lawIdealPullbackIso_cert : lawIdealPullbackIso
    ρ.selectedLawIdealPullback_cert
  witnessReadingPreserved : ρ.witnessComparison_cert ρ.selectedWitnessComparison -> Prop
  witnessReadingPreserved_cert : witnessReadingPreserved
    ρ.selectedWitnessComparison_cert
  axisReadingPreserved : ρ.axisComparison_cert ρ.selectedAxisComparison -> Prop
  axisReadingPreserved_cert : axisReadingPreserved
    ρ.selectedAxisComparison_cert
  zeroPreserved :
    (P : PullbackObstructionClass ρ) ->
      (targetClass : P.TargetClass) ->
        M_Y.Zero (P.targetDomain targetClass) ->
          M_X.Zero (P.sourceDomain (P.pullback targetClass))
  zeroReflected :
    (P : PullbackObstructionClass ρ) ->
      (targetClass : P.TargetClass) ->
        M_X.Zero (P.sourceDomain (P.pullback targetClass)) ->
          M_Y.Zero (P.targetDomain targetClass)

/--
VIII.Theorem 7.3: refactor invariance under selected equivalence.

This package stores the selected target class, its pullback source class, and
the zero-iff certificate under explicit profile-equivalence assumptions.
-/
structure RefactorInvarianceUnderEquivalence {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y} (P : PullbackObstructionClass ρ)
    (E : RefactorEquivalenceAssumptions ρ) where
  targetClass : P.TargetClass
  targetInScope : M_Y.InScope (P.targetDomain targetClass)
  sourceInScope : M_X.InScope (P.sourceDomain (P.pullback targetClass))
  targetZero_iff_sourceZero :
    M_Y.Zero (P.targetDomain targetClass) ↔
      M_X.Zero (P.sourceDomain (P.pullback targetClass))

namespace RefactorInvarianceUnderEquivalence

/-- VIII.Theorem 7.3: selected zero verdict is preserved and reflected by pullback. -/
theorem zero_iff_pullback_zero {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    {E : RefactorEquivalenceAssumptions ρ}
    (T : RefactorInvarianceUnderEquivalence P E) :
    M_Y.Zero (P.targetDomain T.targetClass) ↔
      M_X.Zero (P.sourceDomain (P.pullback T.targetClass)) :=
  T.targetZero_iff_sourceZero

/-- VIII.Theorem 7.3: a measured-zero verdict transports to the selected pullback class. -/
theorem source_zero_of_target_zero {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    {E : RefactorEquivalenceAssumptions ρ}
    (T : RefactorInvarianceUnderEquivalence P E)
    (hzero : M_Y.Zero (P.targetDomain T.targetClass)) :
    M_X.Zero (P.sourceDomain (P.pullback T.targetClass)) :=
  (T.zero_iff_pullback_zero).mp hzero

/-- VIII.Theorem 7.3: reflected zero on the selected pullback class gives target zero. -/
theorem target_zero_of_source_zero {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    {E : RefactorEquivalenceAssumptions ρ}
    (T : RefactorInvarianceUnderEquivalence P E)
    (hzero : M_X.Zero (P.sourceDomain (P.pullback T.targetClass))) :
    M_Y.Zero (P.targetDomain T.targetClass) :=
  (T.zero_iff_pullback_zero).mpr hzero

end RefactorInvarianceUnderEquivalence

/-- VIII.Theorem 7.3: construct the selected refactor invariance theorem package. -/
def refactorInvarianceUnderEquivalencePackage {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    (E : RefactorEquivalenceAssumptions ρ)
    (targetClass : P.TargetClass)
    (targetInScope : M_Y.InScope (P.targetDomain targetClass))
    (sourceInScope : M_X.InScope (P.sourceDomain (P.pullback targetClass))) :
    RefactorInvarianceUnderEquivalence P E where
  targetClass := targetClass
  targetInScope := targetInScope
  sourceInScope := sourceInScope
  targetZero_iff_sourceZero :=
    ⟨E.zeroPreserved P targetClass, E.zeroReflected P targetClass⟩

/--
VIII.Theorem 7.3: selected refactor equivalence preserves and reflects zero.

The conclusion is only the selected `Zero` predicate equivalence for the
transported obstruction class. It is not a theorem about arbitrary refactors.
-/
theorem refactorInvarianceUnderEquivalence {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    (E : RefactorEquivalenceAssumptions ρ)
    (targetClass : P.TargetClass)
    (targetInScope : M_Y.InScope (P.targetDomain targetClass))
    (sourceInScope : M_X.InScope (P.sourceDomain (P.pullback targetClass))) :
    Nonempty (RefactorInvarianceUnderEquivalence P E) :=
  ⟨refactorInvarianceUnderEquivalencePackage E targetClass targetInScope sourceInScope⟩

end Measurement
end AAT.AG
