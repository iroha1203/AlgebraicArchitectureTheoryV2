import Formal.AG.Measurement.Bootstrap

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII R1 / AC2 measurement profile surface.

The profile is intentionally bounded: every predicate and certificate is
relative to the selected profile, and no complement relation between `Zero`
and `NonZero` is assumed.
-/

/-- VIII.Definition 2.1: architecture object and generated AAT site of a profile. -/
structure MeasurementEquationGeometry where
  U : AtomCarrier.{u}
  A : ArchitectureObject U
  site : Site.AATSite A

namespace MeasurementEquationGeometry

/-- Package an existing generated AAT site as measurement equation geometry. -/
def ofSite {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (site : Site.AATSite A) :
    MeasurementEquationGeometry.{u} where
  U := U
  A := A
  site := site

end MeasurementEquationGeometry

/--
VIII.Definition 2.1: an AAT measurement profile.

The equation geometry is an actual architecture object, equation-generated
site, and architecture signature.  The remaining fields select the cover,
coefficient, effective interface, obstruction object, witness variables,
obstruction ideal, representation family, domain, predicates, certificates,
and computation method.
-/
structure MeasurementProfile where
  equationGeometry : MeasurementEquationGeometry.{u}
  SiteObj : Type u
  Cover : Type u
  Coeff : Type v
  EffCoeff : Type (max u v)
  ObstructionObject : Type u
  WitnessVariables : Type u
  ObstructionIdeal : Type u
  RepresentationFamily : Type u
  Domain : Type u
  CertRef : Domain -> Type v
  SelectedMethod : Domain -> Type v
  InScope : Domain -> Prop
  OutOfScope : Domain -> Prop
  Zero : Domain -> Prop
  NonZero : Domain -> Prop
  Undecided : Domain -> Prop
  NotRunOrUnavailable : Domain -> Prop

namespace MeasurementProfile

/-- Equation indices are the actual indices of the profile's generated site. -/
abbrev EquationHandle (M : MeasurementProfile.{u, v}) : Type u :=
  M.equationGeometry.site.equationSystem.Index

/--
VIII.R1: bounded measurement data for a selected element of the profile domain.

Being measured includes scope, a selected method, and a certificate reference.
The structural zero / nonzero interpretation is supplied separately by the
verdict layer.
-/
structure Measured_M (M : MeasurementProfile.{u, v}) (alpha : M.Domain) where
  inScope : M.InScope alpha
  method : M.SelectedMethod alpha
  certificate : M.CertRef alpha

/-- VIII.R1: a measured element is in the profile domain scope. -/
theorem measured_inScope {M : MeasurementProfile.{u, v}} {alpha : M.Domain}
    (h : M.Measured_M alpha) : M.InScope alpha :=
  h.inScope

/-- VIII.R1: a measured element carries a selected method. -/
def measured_method {M : MeasurementProfile.{u, v}} {alpha : M.Domain}
    (h : M.Measured_M alpha) : M.SelectedMethod alpha :=
  h.method

/-- VIII.R1: a measured element carries a certificate reference. -/
def measured_certificate {M : MeasurementProfile.{u, v}} {alpha : M.Domain}
    (h : M.Measured_M alpha) : M.CertRef alpha :=
  h.certificate

end MeasurementProfile

end Measurement
end AAT.AG
