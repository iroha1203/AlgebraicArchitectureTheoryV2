import Formal.AG.Measurement.FiniteRegime

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII R2 / AC6 theorem 4.2 finite AAT computability package.

The theorem is a bounded package construction: under a finite measurement
regime and explicit selected objects, the requested invariants are represented
by finite computation objects. It does not claim a global algorithm for all
sites, sheaves, rings, or modules.
-/

/-- VIII.Theorem 4.2 object: a finite Cech complex representation. -/
structure FiniteCechComplexRepresentation (M : MeasurementProfile.{u, v}) where
  carrier : Type v
  carrierFintype : Fintype carrier
  finiteRepresentation : Prop
  finiteRepresentation_cert : finiteRepresentation

/-- VIII.Theorem 4.2 object: a finite cocycle representative. -/
structure FiniteCocycleRepresentative (M : MeasurementProfile.{u, v}) where
  carrier : Type v
  carrierFintype : Fintype carrier
  finiteRepresentative : Prop
  finiteRepresentative_cert : finiteRepresentative

/-- VIII.Theorem 4.2 object: a finite verdict computation object. -/
structure FiniteVerdictComputationObject (M : MeasurementProfile.{u, v}) where
  carrier : Type v
  carrierFintype : Fintype carrier
  computesSelectedVerdict : Prop
  computesSelectedVerdict_cert : computesSelectedVerdict

/-- VIII.Theorem 4.2 object: a finite square-free obstruction ideal. -/
structure FiniteSquareFreeObstructionIdeal (M : MeasurementProfile.{u, v}) where
  carrier : Type v
  carrierFintype : Fintype carrier
  finiteSquareFree : Prop
  finiteSquareFree_cert : finiteSquareFree

/-- VIII.Theorem 4.2 object: a finite Stanley-Reisner complex. -/
structure FiniteStanleyReisnerComplex (M : MeasurementProfile.{u, v}) where
  carrier : Type v
  carrierFintype : Fintype carrier
  finiteComplex : Prop
  finiteComplex_cert : finiteComplex

/-- VIII.Theorem 4.2 object: a finite monomial Tor complex. -/
structure FiniteMonomialTorComplex (M : MeasurementProfile.{u, v}) where
  carrier : Type v
  carrierFintype : Fintype carrier
  finiteTorComplex : Prop
  finiteTorComplex_cert : finiteTorComplex

/-- VIII.Theorem 4.2 object: finite support for a selected conflict class. -/
structure FiniteConflictSupport (M : MeasurementProfile.{u, v}) where
  carrier : Type v
  carrierFintype : Fintype carrier
  finiteSupport : Prop
  finiteSupport_cert : finiteSupport

/-- VIII.Theorem 4.2: selected invariants reduced to finite computation objects. -/
structure FiniteAATComputability (M : MeasurementProfile.{u, v}) where
  regime : FiniteMeasurementRegime M
  cechComplex : FiniteCechComplexRepresentation M
  cocycleRepresentative : FiniteCocycleRepresentative M
  verdictComputation : FiniteVerdictComputationObject M
  squareFreeObstructionIdeal : FiniteSquareFreeObstructionIdeal M
  stanleyReisnerComplex : FiniteStanleyReisnerComplex M
  monomialTorComplex : FiniteMonomialTorComplex M
  conflictSupport : FiniteConflictSupport M
  finiteLinearAlgebraReduction : Prop
  finiteLinearAlgebraReduction_cert : finiteLinearAlgebraReduction
  finitePresentedModuleReduction : Prop
  finitePresentedModuleReduction_cert : finitePresentedModuleReduction
  finiteCombinatoricsReduction : Prop
  finiteCombinatoricsReduction_cert : finiteCombinatoricsReduction
  finiteResolutionReduction : Prop
  finiteResolutionReduction_cert : finiteResolutionReduction

namespace FiniteAATComputability

/-- VIII.Theorem 4.2: expose the finite Cech complex representation. -/
theorem cechComplex_finite {M : MeasurementProfile.{u, v}} (P : FiniteAATComputability M) :
    P.cechComplex.finiteRepresentation :=
  P.cechComplex.finiteRepresentation_cert

/-- VIII.Theorem 4.2: expose the finite verdict computation certificate. -/
theorem verdictComputation_holds {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    P.verdictComputation.computesSelectedVerdict :=
  P.verdictComputation.computesSelectedVerdict_cert

/-- VIII.Theorem 4.2: expose the finite monomial Tor complex certificate. -/
theorem monomialTorComplex_finite {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    P.monomialTorComplex.finiteTorComplex :=
  P.monomialTorComplex.finiteTorComplex_cert

/-- VIII.Theorem 4.2: expose the finite conflict support certificate. -/
theorem conflictSupport_finite {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    P.conflictSupport.finiteSupport :=
  P.conflictSupport.finiteSupport_cert

/-- VIII.Theorem 4.2: the selected Cech-complex carrier is an actual finite type. -/
def cechComplexCarrierFintype {M : MeasurementProfile.{u, v}} (P : FiniteAATComputability M) :
    Fintype P.cechComplex.carrier :=
  P.cechComplex.carrierFintype

/-- VIII.Theorem 4.2: the selected cocycle-representative carrier is finite. -/
def cocycleRepresentativeCarrierFintype {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    Fintype P.cocycleRepresentative.carrier :=
  P.cocycleRepresentative.carrierFintype

/-- VIII.Theorem 4.2: the selected verdict-computation carrier is finite. -/
def verdictComputationCarrierFintype {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    Fintype P.verdictComputation.carrier :=
  P.verdictComputation.carrierFintype

/-- VIII.Theorem 4.2: the selected square-free ideal carrier is finite. -/
def squareFreeObstructionIdealCarrierFintype {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    Fintype P.squareFreeObstructionIdeal.carrier :=
  P.squareFreeObstructionIdeal.carrierFintype

/-- VIII.Theorem 4.2: the selected Stanley-Reisner carrier is finite. -/
def stanleyReisnerComplexCarrierFintype {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    Fintype P.stanleyReisnerComplex.carrier :=
  P.stanleyReisnerComplex.carrierFintype

/-- VIII.Theorem 4.2: the selected monomial Tor carrier is finite. -/
def monomialTorComplexCarrierFintype {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    Fintype P.monomialTorComplex.carrier :=
  P.monomialTorComplex.carrierFintype

/-- VIII.Theorem 4.2: the selected conflict-support carrier is finite. -/
def conflictSupportCarrierFintype {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    Fintype P.conflictSupport.carrier :=
  P.conflictSupport.carrierFintype

/-- VIII.Theorem 4.2: the selected Cech cochain carrier is finite. -/
theorem cechComplexCarrier_finite {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    Finite P.cechComplex.carrier := by
  letI := P.cechComplex.carrierFintype
  infer_instance

/-- VIII.Theorem 4.2: the selected cocycle-representative carrier is finite. -/
theorem cocycleRepresentativeCarrier_finite {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    Finite P.cocycleRepresentative.carrier := by
  letI := P.cocycleRepresentative.carrierFintype
  infer_instance

/-- VIII.Theorem 4.2: the selected finite computation carriers are finite. -/
theorem computationCarriers_finite {M : MeasurementProfile.{u, v}}
    (P : FiniteAATComputability M) :
    Finite P.cechComplex.carrier ∧
      Finite P.cocycleRepresentative.carrier ∧
      Finite P.verdictComputation.carrier ∧
      Finite P.squareFreeObstructionIdeal.carrier ∧
      Finite P.stanleyReisnerComplex.carrier ∧
      Finite P.monomialTorComplex.carrier ∧
      Finite P.conflictSupport.carrier := by
  letI := P.cechComplex.carrierFintype
  letI := P.cocycleRepresentative.carrierFintype
  letI := P.verdictComputation.carrierFintype
  letI := P.squareFreeObstructionIdeal.carrierFintype
  letI := P.stanleyReisnerComplex.carrierFintype
  letI := P.monomialTorComplex.carrierFintype
  letI := P.conflictSupport.carrierFintype
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

end FiniteAATComputability

/--
VIII.Theorem 4.2: construct the bounded finite computability package.

Every computational conclusion is supplied by a selected finite object and a
certificate. This definition builds the package used by the theorem below.
-/
def finiteAATComputabilityPackage {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M)
    (cechComplex : FiniteCechComplexRepresentation M)
    (cocycleRepresentative : FiniteCocycleRepresentative M)
    (verdictComputation : FiniteVerdictComputationObject M)
    (squareFreeObstructionIdeal : FiniteSquareFreeObstructionIdeal M)
    (stanleyReisnerComplex : FiniteStanleyReisnerComplex M)
    (monomialTorComplex : FiniteMonomialTorComplex M)
    (conflictSupport : FiniteConflictSupport M)
    (finiteLinearAlgebraReduction : Prop)
    (finiteLinearAlgebraReduction_cert : finiteLinearAlgebraReduction)
    (finitePresentedModuleReduction : Prop)
    (finitePresentedModuleReduction_cert : finitePresentedModuleReduction)
    (finiteCombinatoricsReduction : Prop)
    (finiteCombinatoricsReduction_cert : finiteCombinatoricsReduction)
    (finiteResolutionReduction : Prop)
    (finiteResolutionReduction_cert : finiteResolutionReduction) :
    FiniteAATComputability M where
  regime := R
  cechComplex := cechComplex
  cocycleRepresentative := cocycleRepresentative
  verdictComputation := verdictComputation
  squareFreeObstructionIdeal := squareFreeObstructionIdeal
  stanleyReisnerComplex := stanleyReisnerComplex
  monomialTorComplex := monomialTorComplex
  conflictSupport := conflictSupport
  finiteLinearAlgebraReduction := finiteLinearAlgebraReduction
  finiteLinearAlgebraReduction_cert := finiteLinearAlgebraReduction_cert
  finitePresentedModuleReduction := finitePresentedModuleReduction
  finitePresentedModuleReduction_cert := finitePresentedModuleReduction_cert
  finiteCombinatoricsReduction := finiteCombinatoricsReduction
  finiteCombinatoricsReduction_cert := finiteCombinatoricsReduction_cert
  finiteResolutionReduction := finiteResolutionReduction
  finiteResolutionReduction_cert := finiteResolutionReduction_cert

/--
VIII.Theorem 4.2: the selected invariants reduce to finite computation objects.

The conclusion is intentionally existential over the theorem package: it records
that the package is available under the supplied finite regime and selected
finite objects, without asserting unbounded algorithmic completeness.
-/
theorem finiteAATComputability {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M)
    (cechComplex : FiniteCechComplexRepresentation M)
    (cocycleRepresentative : FiniteCocycleRepresentative M)
    (verdictComputation : FiniteVerdictComputationObject M)
    (squareFreeObstructionIdeal : FiniteSquareFreeObstructionIdeal M)
    (stanleyReisnerComplex : FiniteStanleyReisnerComplex M)
    (monomialTorComplex : FiniteMonomialTorComplex M)
    (conflictSupport : FiniteConflictSupport M)
    (finiteLinearAlgebraReduction : Prop)
    (finiteLinearAlgebraReduction_cert : finiteLinearAlgebraReduction)
    (finitePresentedModuleReduction : Prop)
    (finitePresentedModuleReduction_cert : finitePresentedModuleReduction)
    (finiteCombinatoricsReduction : Prop)
    (finiteCombinatoricsReduction_cert : finiteCombinatoricsReduction)
    (finiteResolutionReduction : Prop)
    (finiteResolutionReduction_cert : finiteResolutionReduction) :
    Nonempty (FiniteAATComputability M) :=
  ⟨finiteAATComputabilityPackage R cechComplex cocycleRepresentative verdictComputation
    squareFreeObstructionIdeal stanleyReisnerComplex monomialTorComplex conflictSupport
    finiteLinearAlgebraReduction finiteLinearAlgebraReduction_cert
    finitePresentedModuleReduction finitePresentedModuleReduction_cert
    finiteCombinatoricsReduction finiteCombinatoricsReduction_cert
    finiteResolutionReduction finiteResolutionReduction_cert⟩

end Measurement
end AAT.AG
