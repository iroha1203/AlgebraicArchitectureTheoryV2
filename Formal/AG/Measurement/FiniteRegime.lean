import Formal.AG.Measurement.Profile

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
PRD-8 R2 / AC5 finite measurement regime.

The effective coefficient interface records only the selected procedures and
certificates used by a profile. It does not assert decidability for arbitrary
coefficient categories.
-/

/-- VIII.Definition 4.1: selected effective coefficient procedures. -/
structure EffCoeff (M : MeasurementProfile.{u, v}) where
  profileInterface : M.EffCoeff
  KernelObject : Type v
  ImageObject : Type v
  QuotientObject : Type v
  IdealMembershipObject : Type v
  FinitePresentationObject : Type v
  ResolutionObject : Type v
  kernelFor : M.Domain -> KernelObject -> Prop
  imageFor : M.Domain -> ImageObject -> Prop
  quotientFor : M.Domain -> QuotientObject -> Prop
  idealMembershipFor : M.Domain -> IdealMembershipObject -> Prop
  resolutionFor : M.Domain -> ResolutionObject -> Prop
  methodUsesInterface : (alpha : M.Domain) -> M.SelectedMethod alpha -> Prop
  zeroCertificateBacks : (alpha : M.Domain) -> M.CertRef alpha -> M.Zero alpha -> Prop
  nonzeroCertificateBacks : (alpha : M.Domain) -> M.CertRef alpha -> M.NonZero alpha -> Prop
  kernelCertificate : KernelObject -> Prop
  imageCertificate : ImageObject -> Prop
  quotientCertificate : QuotientObject -> Prop
  idealMembershipCertificate : IdealMembershipObject -> Prop
  finitePresentationCertificate : FinitePresentationObject -> Prop
  resolutionCertificate : ResolutionObject -> Prop

/-- VIII.Definition 4.1: a finite measurement regime for a selected profile. -/
structure FiniteMeasurementRegime (M : MeasurementProfile.{u, v}) where
  effCoeff : EffCoeff M
  finiteSite : Prop
  finiteSite_cert : finiteSite
  finiteCover : Prop
  finiteCover_cert : finiteCover
  effectiveCoefficient : Prop
  effectiveCoefficient_cert : effectiveCoefficient
  explicitRestrictionMaps : Prop
  explicitRestrictionMaps_cert : explicitRestrictionMaps
  finiteWitnessVariables : Prop
  finiteWitnessVariables_cert : finiteWitnessVariables
  finitelyGeneratedObstructionIdeal : Prop
  finitelyGeneratedObstructionIdeal_cert : finitelyGeneratedObstructionIdeal
  selectedFiniteResolutions : Prop
  selectedFiniteResolutions_cert : selectedFiniteResolutions
  zeroPredicateCertificateBacked : Prop
  zeroPredicateCertificateBacked_cert : zeroPredicateCertificateBacked
  nonzeroPredicateCertificateBacked : Prop
  nonzeroPredicateCertificateBacked_cert : nonzeroPredicateCertificateBacked

namespace FiniteMeasurementRegime

/-- VIII.R2: the selected site is finite in the regime. -/
theorem finiteSite_holds {M : MeasurementProfile.{u, v}} (R : FiniteMeasurementRegime M) :
    R.finiteSite :=
  R.finiteSite_cert

/-- VIII.R2: the selected cover or hypercover fragment is finite in the regime. -/
theorem finiteCover_holds {M : MeasurementProfile.{u, v}} (R : FiniteMeasurementRegime M) :
    R.finiteCover :=
  R.finiteCover_cert

/-- VIII.R2: the coefficient data are effective only through the selected interface. -/
theorem effectiveCoefficient_holds {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M) : R.effectiveCoefficient :=
  R.effectiveCoefficient_cert

/-- VIII.R2: the selected witness variables are finite. -/
theorem finiteWitnessVariables_holds {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M) : R.finiteWitnessVariables :=
  R.finiteWitnessVariables_cert

/-- VIII.R2: selected finite resolutions are available in the regime. -/
theorem selectedFiniteResolutions_holds {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M) : R.selectedFiniteResolutions :=
  R.selectedFiniteResolutions_cert

end FiniteMeasurementRegime

end Measurement
end AAT.AG
