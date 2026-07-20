import Formal.AG.Measurement.RefactorTransport

noncomputable section

/-!
Fixed statement contracts for Part VIII Definition 7.2 and Theorem 7.3.
-/

namespace AAT.AG
namespace Measurement

universe u v

variable {M_X M_Y : MeasurementProfile.{u, v}}
variable {ρ : RefactorMorphism M_X M_Y}
variable {P : PullbackObstructionClass ρ}

/-- Fixed contract: obstruction-class pullback is an additive homomorphism. -/
example : P.TargetClass →+ P.SourceClass :=
  P.pullback

/-- Fixed contract: profile zero is the actual zero source class. -/
example (sourceClass : P.SourceClass) :
    M_X.Zero (P.sourceDomain sourceClass) ↔ sourceClass = 0 :=
  P.sourceZero_iff_class_eq_zero sourceClass

/-- Fixed contract: profile zero is the actual zero target class. -/
example (targetClass : P.TargetClass) :
    M_Y.Zero (P.targetDomain targetClass) ↔ targetClass = 0 :=
  P.targetZero_iff_class_eq_zero targetClass

/-- Fixed contract: selected finite sites are compared by an actual equivalence. -/
example (E : RefactorEquivalenceAssumptions ρ P) :
    M_X.SiteObj ≃ M_Y.SiteObj :=
  E.selectedFiniteSiteEquivalence

/-- Fixed contract: coefficient objects are compared by an actual equivalence. -/
example (E : RefactorEquivalenceAssumptions ρ P) :
    M_Y.Coeff ≃ M_X.Coeff :=
  E.coefficientIso

/-- Fixed contract: the induced cohomology pullback is an additive equivalence. -/
example (E : RefactorEquivalenceAssumptions ρ P) :
    P.TargetClass ≃+ P.SourceClass :=
  E.cohomologyPullbackIso

/-- Fixed contract: the induced equivalence is Definition 7.2's pullback map. -/
example (E : RefactorEquivalenceAssumptions ρ P) (targetClass : P.TargetClass) :
    E.cohomologyPullbackIso targetClass = P.pullback targetClass :=
  E.cohomologyPullbackIso_apply targetClass

/-- Fixed contract: no nonzero target class can pull back to zero. -/
example (E : RefactorEquivalenceAssumptions ρ P) (targetClass : P.TargetClass) :
    P.pullback targetClass = 0 ↔ targetClass = 0 :=
  E.pullback_eq_zero_iff targetClass

/-- Fixed contract: theorem 7.3 derives profile-zero preservation and reflection. -/
example (E : RefactorEquivalenceAssumptions ρ P) (targetClass : P.TargetClass) :
    M_Y.Zero (P.targetDomain targetClass) ↔
      M_X.Zero (P.sourceDomain (P.pullback targetClass)) :=
  refactorZero_iff_pullbackZero E targetClass

end Measurement
end AAT.AG
