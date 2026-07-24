import Formal.AG.Measurement.Computability
import Formal.AG.Measurement.LawConflict

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII theorem 4.2 connection from the computed finite support relation to
the existing relation-valued `LawConflictMeasurement` API.
-/

/-- Local common-ambient realization for the profile-selected actual equations and
the computed finite support carrier. -/
structure FiniteAATConflictRealization
    {M : MeasurementProfile.{u, v}}
    {R : FiniteMeasurementRegime M}
    (D : FiniteAATComputationData M R) where
  /-- Existing selected common ambient for the two actual equations. -/
  commonAmbient : CommonAmbientPair M
  /-- Interpret actual generated equation ideals in the common ambient. -/
  idealToAmbient :
    letI := R.geometry.coeffCommRing
    Ideal (MvPolynomial M.WitnessVariables M.Coeff) →
      commonAmbient.LawIdeal
  /-- The canonical selected left equation ideal gives the ambient left ideal. -/
  leftEquationIdeal_ambient :
    letI := R.geometry.coeffCommRing
    idealToAmbient D.profileRealization.leftIdeal =
      commonAmbient.leftLawIdeal
  /-- The canonical selected right equation ideal gives the ambient right ideal. -/
  rightEquationIdeal_ambient :
    letI := R.geometry.coeffCommRing
    idealToAmbient D.profileRealization.rightIdeal =
      commonAmbient.rightLawIdeal
  /-- Local identification of computed witness supports with the existing
  measurement support carrier. -/
  supportEquiv : Finset M.WitnessVariables ≃ commonAmbient.SupportCarrier

namespace FiniteAATConflictRealization

variable {M : MeasurementProfile.{u, v}}
variable {R : FiniteMeasurementRegime M}
variable {D : FiniteAATComputationData M R}

/-- The concrete left ideal used by the Tor computation realizes the ambient
left ideal through the canonical equation-generated presentation. -/
theorem computedLeftIdeal_ambient
    (C : FiniteAATConflictRealization D) :
    letI := R.geometry.coeffCommRing
    C.idealToAmbient D.leftIdeal = C.commonAmbient.leftLawIdeal := by
  letI := R.geometry.coeffCommRing
  rw [← D.canonicalLeftIdeal_eq]
  exact C.leftEquationIdeal_ambient

/-- The concrete right ideal used by the Tor computation realizes the ambient
right ideal through the canonical equation-generated presentation. -/
theorem computedRightIdeal_ambient
    (C : FiniteAATConflictRealization D) :
    letI := R.geometry.coeffCommRing
    C.idealToAmbient D.rightIdeal = C.commonAmbient.rightLawIdeal := by
  letI := R.geometry.coeffCommRing
  rw [← D.canonicalRightIdeal_eq]
  exact C.rightEquationIdeal_ambient

/-- Relation-valued support semantics transported to the selected common
ambient carrier. -/
def supportRelation (C : FiniteAATConflictRealization D) :
    letI := R.geometry.coeffCommRing
    D.ActualConflictClass -> C.commonAmbient.SupportCarrier -> Prop := by
  letI := R.geometry.coeffCommRing
  exact fun conflictClass support =>
    D.ComputedConflictSupport conflictClass (C.supportEquiv.symm support)

/-- Selected support in the common ambient carrier. -/
def selectedSupport (C : FiniteAATConflictRealization D) :
    C.commonAmbient.SupportCarrier :=
  C.supportEquiv D.selectedClassSupport

/-- The selected actual conflict class and selected support satisfy the
transported relation. -/
theorem selectedSupport_holds (C : FiniteAATConflictRealization D) :
    letI := R.geometry.coeffCommRing
    C.supportRelation D.selectedConflictClass C.selectedSupport := by
  letI := R.geometry.coeffCommRing
  change D.ComputedConflictSupport D.selectedConflictClass
    (C.supportEquiv.symm (C.supportEquiv D.selectedClassSupport))
  simpa using D.computedConflictSupport_selected

/-- The transported support relation assigns only the empty finite support to
the zero actual conflict class. -/
theorem supportRelation_zero
    (C : FiniteAATConflictRealization D)
    {support : C.commonAmbient.SupportCarrier}
    (h : C.supportRelation (0 : D.ActualConflictClass) support) :
    support = C.supportEquiv ∅ := by
  letI := R.geometry.coeffCommRing
  have hfinite : C.supportEquiv.symm support = ∅ :=
    D.computedConflictSupport_zero h
  apply C.supportEquiv.symm.injective
  simpa using hfinite

/-- Existing `LawConflictMeasurement` constructed from the same selected Tor
bridge, actual class, and computed relation-valued support. -/
def lawConflictMeasurement (C : FiniteAATConflictRealization D) :
    LawConflictMeasurement C.commonAmbient := by
  letI := R.geometry.coeffCommRing
  let B := Derived.Intersection.canonicalSelectedTorBridge
    (MvPolynomial M.WitnessVariables M.Coeff) D.leftIdeal D.rightIdeal
  let selectedClass : B.LawConflict D.torDegree := D.selectedConflictClass
  let relation : B.LawConflict D.torDegree ->
      C.commonAmbient.SupportCarrier -> Prop := C.supportRelation
  have hselected : relation selectedClass C.selectedSupport := by
    exact C.selectedSupport_holds
  exact @LawConflictMeasurement.ofSelectedTorBridge M C.commonAmbient
    (MvPolynomial M.WitnessVariables M.Coeff) inferInstance
    D.leftIdeal D.rightIdeal C.idealToAmbient
    C.computedLeftIdeal_ambient C.computedRightIdeal_ambient
    B D.torDegree selectedClass C.selectedSupport relation hselected

/-- The final measurement's common-ambient obligation contains the actual
equation-generated ideals used by its selected Tor bridge. -/
theorem lawConflictMeasurement_commonAmbientRequired_shape
    (C : FiniteAATConflictRealization D) :
    letI := R.geometry.coeffCommRing
    C.lawConflictMeasurement.commonAmbientRequired =
      (C.commonAmbient.commonRingedSite ∧
        C.commonAmbient.lawIdealsInCommonAmbient ∧
          C.idealToAmbient D.leftIdeal =
            C.commonAmbient.leftLawIdeal ∧
          C.idealToAmbient D.rightIdeal =
            C.commonAmbient.rightLawIdeal) :=
  rfl

/-- The final measurement exposes the selected computed-support reading. -/
theorem selectedClassSupportReading_holds
    (C : FiniteAATConflictRealization D) :
    C.lawConflictMeasurement.selectedClassSupportReading :=
  C.lawConflictMeasurement.selectedClassSupportReading_holds

end FiniteAATConflictRealization

/-- Final theorem 4.2 package after a selected common ambient has been
realized.  The base computation and relation-valued `LawConflictMeasurement`
are both conclusions; the caller supplies no class-specific support
certificate. -/
structure FiniteAATConflictComputability
    {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M)
    (D : FiniteAATComputationData M R)
    (C : FiniteAATConflictRealization D) :
    Type (max (u + 1) (v + 1)) where
  /-- The complete finite Čech, square-free, and Tor computation package. -/
  computation : FiniteAATComputability R D
  /-- Existing measurement semantics instantiated by the computed support
  relation and the actual transported conflict class. -/
  lawConflictMeasurement :
    LawConflictMeasurement.{u, v, max u v} C.commonAmbient
  /-- The exposed measurement is exactly the one constructed from the
  canonical selected Tor bridge and `ComputedConflictSupport`. -/
  lawConflictMeasurement_eq_computed :
    lawConflictMeasurement = C.lawConflictMeasurement
  /-- The final package exposes the selected class/support reading. -/
  selectedClassSupportReading :
    lawConflictMeasurement.selectedClassSupportReading

/-- Construct the final common-ambient theorem 4.2 package without accepting
any selected support correctness proof. -/
def finiteAATConflictComputabilityPackage
    {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M)
    (D : FiniteAATComputationData M R)
    (C : FiniteAATConflictRealization D) :
    FiniteAATConflictComputability R D C where
  computation := finiteAATComputabilityPackage R D
  lawConflictMeasurement := C.lawConflictMeasurement
  lawConflictMeasurement_eq_computed := rfl
  selectedClassSupportReading := C.selectedClassSupportReading_holds

/-- A finite regime, selected computation data, and local common-ambient
realization determine the final relation-valued conflict computation. -/
theorem finiteAATConflictComputability
    {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M)
    (D : FiniteAATComputationData M R)
    (C : FiniteAATConflictRealization D) :
    Nonempty (FiniteAATConflictComputability R D C) :=
  ⟨finiteAATConflictComputabilityPackage R D C⟩

end Measurement
end AAT.AG
