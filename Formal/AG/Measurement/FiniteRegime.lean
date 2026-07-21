import Formal.AG.Measurement.Verdict

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII R2 / AC5 finite measurement regime.

The effective coefficient interface records the selected finite procedure
outputs used by a profile.  Each output is an actual function of the selected
domain element; theorem 4.2 does not receive a second copy of its result as a
`Prop` certificate.
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
  kernelObjectFintype : Fintype KernelObject
  imageObjectFintype : Fintype ImageObject
  quotientObjectFintype : Fintype QuotientObject
  idealMembershipObjectFintype : Fintype IdealMembershipObject
  finitePresentationObjectFintype : Fintype FinitePresentationObject
  resolutionObjectFintype : Fintype ResolutionObject
  kernel : M.Domain -> KernelObject
  image : M.Domain -> ImageObject
  quotient : M.Domain -> QuotientObject
  idealMembership : M.Domain -> IdealMembershipObject
  finitePresentation : M.Domain -> FinitePresentationObject
  resolution : M.Domain -> ResolutionObject
  verdict : (alpha : M.Domain) -> MeasurementVerdict M alpha

/-- VIII.Definition 4.1: a finite measurement regime for a selected profile. -/
structure FiniteMeasurementRegime (M : MeasurementProfile.{u, v}) where
  effCoeff : EffCoeff M
  [siteFintype : Fintype M.SiteObj]
  [coverFintype : Fintype M.Cover]
  [domainFintype : Fintype M.Domain]
  [witnessFintype : Fintype M.WitnessVariables]
  [witnessDecidableEq : DecidableEq M.WitnessVariables]

attribute [instance] FiniteMeasurementRegime.siteFintype
attribute [instance] FiniteMeasurementRegime.coverFintype
attribute [instance] FiniteMeasurementRegime.domainFintype
attribute [instance] FiniteMeasurementRegime.witnessFintype
attribute [instance] FiniteMeasurementRegime.witnessDecidableEq

namespace FiniteMeasurementRegime

/-- VIII.R2: the selected effective coefficient procedure computes a verdict. -/
def verdict {M : MeasurementProfile.{u, v}} (R : FiniteMeasurementRegime M)
    (alpha : M.Domain) : MeasurementVerdict M alpha :=
  R.effCoeff.verdict alpha

/-- VIII.R2/R3: the selected kernel objects form an actual finite type. -/
def kernelObjectFintype {M : MeasurementProfile.{u, v}} (R : FiniteMeasurementRegime M) :
    Fintype R.effCoeff.KernelObject :=
  R.effCoeff.kernelObjectFintype

/-- VIII.R2/R3: the selected image objects form an actual finite type. -/
def imageObjectFintype {M : MeasurementProfile.{u, v}} (R : FiniteMeasurementRegime M) :
    Fintype R.effCoeff.ImageObject :=
  R.effCoeff.imageObjectFintype

/-- VIII.R2/R3: the selected quotient objects form an actual finite type. -/
def quotientObjectFintype {M : MeasurementProfile.{u, v}} (R : FiniteMeasurementRegime M) :
    Fintype R.effCoeff.QuotientObject :=
  R.effCoeff.quotientObjectFintype

/-- VIII.R2/R3: the selected ideal-membership objects form an actual finite type. -/
def idealMembershipObjectFintype {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M) :
    Fintype R.effCoeff.IdealMembershipObject :=
  R.effCoeff.idealMembershipObjectFintype

/-- VIII.R2/R3: the selected finite-presentation objects form an actual finite type. -/
def finitePresentationObjectFintype {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M) :
    Fintype R.effCoeff.FinitePresentationObject :=
  R.effCoeff.finitePresentationObjectFintype

/-- VIII.R2/R3: the selected resolution objects form an actual finite type. -/
def resolutionObjectFintype {M : MeasurementProfile.{u, v}} (R : FiniteMeasurementRegime M) :
    Fintype R.effCoeff.ResolutionObject :=
  R.effCoeff.resolutionObjectFintype

end FiniteMeasurementRegime

end Measurement
end AAT.AG
