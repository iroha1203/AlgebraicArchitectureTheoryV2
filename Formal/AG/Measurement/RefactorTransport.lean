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
  [sourceClassAddCommGroup : AddCommGroup SourceClass]
  [targetClassAddCommGroup : AddCommGroup TargetClass]
  pullback : TargetClass →+ SourceClass
  sourceDomain : SourceClass -> M_X.Domain
  targetDomain : TargetClass -> M_Y.Domain
  sourceZero_iff_class_eq_zero :
    ∀ sourceClass : SourceClass,
      M_X.Zero (sourceDomain sourceClass) ↔ sourceClass = 0
  targetZero_iff_class_eq_zero :
    ∀ targetClass : TargetClass,
      M_Y.Zero (targetDomain targetClass) ↔ targetClass = 0

attribute [instance] PullbackObstructionClass.sourceClassAddCommGroup
attribute [instance] PullbackObstructionClass.targetClassAddCommGroup

namespace PullbackObstructionClass

/-- VIII.Definition 7.2: the selected pullback preserves the actual zero class. -/
theorem pullback_zero {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y} (P : PullbackObstructionClass ρ) :
    P.pullback 0 = 0 :=
  P.pullback.map_zero

end PullbackObstructionClass

/--
VIII.Theorem 7.3 assumptions: selected equivalence data required for zero
verdict invariance.

The selected site, ambient, coefficient, ideal, witness, and axis readings are
actual equivalences.  Their induced cohomology pullback is an additive
equivalence agreeing with the Definition 7.2 pullback map.
-/
structure RefactorEquivalenceAssumptions {M_X M_Y : MeasurementProfile.{u, v}}
    (ρ : RefactorMorphism M_X M_Y) (P : PullbackObstructionClass ρ) where
  selectedFiniteSiteEquivalence : M_X.SiteObj ≃ M_Y.SiteObj
  ringedAmbientIso : M_Y.ObstructionObject ≃ M_X.ObstructionObject
  coefficientIso : M_Y.Coeff ≃ M_X.Coeff
  lawIdealPullbackIso : M_Y.ObstructionIdeal ≃ M_X.ObstructionIdeal
  /-- Equivalence of the selected witness readings. -/
  witnessReadingIso : M_Y.WitnessVariables ≃ M_X.WitnessVariables
  /-- Equivalence of the selected axis representation readings. -/
  axisReadingIso : M_Y.RepresentationFamily ≃ M_X.RepresentationFamily
  /-- Additive equivalence induced on the selected obstruction cohomology classes. -/
  cohomologyPullbackIso : P.TargetClass ≃+ P.SourceClass
  cohomologyPullbackIso_apply :
    ∀ targetClass : P.TargetClass,
      cohomologyPullbackIso targetClass = P.pullback targetClass

namespace RefactorEquivalenceAssumptions

/-- VIII.Theorem 7.3: the additive pullback is injective under selected equivalence. -/
theorem pullback_injective {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    (E : RefactorEquivalenceAssumptions ρ P) :
    Function.Injective P.pullback := by
  intro a b hab
  apply E.cohomologyPullbackIso.injective
  rw [E.cohomologyPullbackIso_apply, E.cohomologyPullbackIso_apply]
  exact hab

/-- VIII.Theorem 7.3: the pullback class is zero exactly for a zero target class. -/
theorem pullback_eq_zero_iff {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    (E : RefactorEquivalenceAssumptions ρ P)
    (targetClass : P.TargetClass) :
    P.pullback targetClass = 0 ↔ targetClass = 0 := by
  constructor
  · intro hzero
    exact E.pullback_injective (by simpa using hzero)
  · rintro rfl
    exact P.pullback.map_zero

end RefactorEquivalenceAssumptions

/--
VIII.Theorem 7.3: refactor invariance under selected equivalence.

This package stores the selected target class and scope witnesses.  The zero
equivalence is derived from the induced cohomology additive equivalence.
-/
structure RefactorInvarianceUnderEquivalence {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y} (P : PullbackObstructionClass ρ)
    (E : RefactorEquivalenceAssumptions ρ P) where
  targetClass : P.TargetClass
  targetInScope : M_Y.InScope (P.targetDomain targetClass)
  sourceInScope : M_X.InScope (P.sourceDomain (P.pullback targetClass))

namespace RefactorInvarianceUnderEquivalence

/-- VIII.Theorem 7.3: selected zero verdict is preserved and reflected by pullback. -/
theorem zero_iff_pullback_zero {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    {E : RefactorEquivalenceAssumptions ρ P}
    (T : RefactorInvarianceUnderEquivalence P E) :
    M_Y.Zero (P.targetDomain T.targetClass) ↔
      M_X.Zero (P.sourceDomain (P.pullback T.targetClass)) := by
  rw [P.targetZero_iff_class_eq_zero, P.sourceZero_iff_class_eq_zero]
  exact (E.pullback_eq_zero_iff T.targetClass).symm

/-- VIII.Theorem 7.3: a measured-zero verdict transports to the selected pullback class. -/
theorem source_zero_of_target_zero {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    {E : RefactorEquivalenceAssumptions ρ P}
    (T : RefactorInvarianceUnderEquivalence P E)
    (hzero : M_Y.Zero (P.targetDomain T.targetClass)) :
    M_X.Zero (P.sourceDomain (P.pullback T.targetClass)) :=
  (T.zero_iff_pullback_zero).mp hzero

/-- VIII.Theorem 7.3: reflected zero on the selected pullback class gives target zero. -/
theorem target_zero_of_source_zero {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    {E : RefactorEquivalenceAssumptions ρ P}
    (T : RefactorInvarianceUnderEquivalence P E)
    (hzero : M_X.Zero (P.sourceDomain (P.pullback T.targetClass))) :
    M_Y.Zero (P.targetDomain T.targetClass) :=
  (T.zero_iff_pullback_zero).mpr hzero

end RefactorInvarianceUnderEquivalence

/-- VIII.Theorem 7.3: construct the selected refactor invariance theorem package. -/
def refactorInvarianceUnderEquivalencePackage {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    (E : RefactorEquivalenceAssumptions ρ P)
    (targetClass : P.TargetClass)
    (targetInScope : M_Y.InScope (P.targetDomain targetClass))
    (sourceInScope : M_X.InScope (P.sourceDomain (P.pullback targetClass))) :
    RefactorInvarianceUnderEquivalence P E where
  targetClass := targetClass
  targetInScope := targetInScope
  sourceInScope := sourceInScope

/--
VIII.Theorem 7.3: selected refactor equivalence preserves and reflects zero
for every transported obstruction class.
-/
theorem refactorZero_iff_pullbackZero {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    (E : RefactorEquivalenceAssumptions ρ P)
    (targetClass : P.TargetClass) :
    M_Y.Zero (P.targetDomain targetClass) ↔
      M_X.Zero (P.sourceDomain (P.pullback targetClass)) := by
  rw [P.targetZero_iff_class_eq_zero, P.sourceZero_iff_class_eq_zero]
  exact (E.pullback_eq_zero_iff targetClass).symm

/--
VIII.Theorem 7.3: selected refactor equivalence preserves and reflects zero.

The conclusion is only the selected `Zero` predicate equivalence for the
transported obstruction class. It is not a theorem about arbitrary refactors.
-/
theorem refactorInvarianceUnderEquivalence {M_X M_Y : MeasurementProfile.{u, v}}
    {ρ : RefactorMorphism M_X M_Y}
    {P : PullbackObstructionClass ρ}
    (E : RefactorEquivalenceAssumptions ρ P)
    (targetClass : P.TargetClass)
    (targetInScope : M_Y.InScope (P.targetDomain targetClass))
    (sourceInScope : M_X.InScope (P.sourceDomain (P.pullback targetClass))) :
    Nonempty (RefactorInvarianceUnderEquivalence P E) :=
  ⟨refactorInvarianceUnderEquivalencePackage E targetClass targetInScope sourceInScope⟩

end Measurement
end AAT.AG
