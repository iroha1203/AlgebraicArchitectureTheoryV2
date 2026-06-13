import Formal.AG.Cohomology.LocalFlatnessGap

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

open CategoryTheory
open Opposite

/--
IV.定義8.1: two-chart feature-extension cover.

`extension` is the ambient feature-extension object `C'`, `core` is
`C_core`, `feature` is `F`, and `boundary` is the overlap `B = C_core ∩ F`.
The pullback/intersection construction is selected data at this layer.
-/
structure TwoChartFeatureExtensionCover {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A) where
  extension : S.category
  core : S.category
  feature : S.category
  boundary : S.category
  coreInclusion : core ⟶ extension
  featureInclusion : feature ⟶ extension
  boundaryToCore : boundary ⟶ core
  boundaryToFeature : boundary ⟶ feature
  extension_is_union : Prop
  extension_is_union_holds : extension_is_union
  boundary_is_intersection : Prop
  boundary_is_intersection_holds : boundary_is_intersection

namespace TwoChartFeatureExtensionCover

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}

/-- IV.定義8.1: the boundary object `B = C_core ∩ F`. -/
def boundaryObject (E : TwoChartFeatureExtensionCover S) : S.category :=
  E.boundary

/-- IV.定義8.1: the ambient feature-extension object `C' = C_core ∪ F`. -/
def extensionObject (E : TwoChartFeatureExtensionCover S) : S.category :=
  E.extension

end TwoChartFeatureExtensionCover

/-- IV.定義8.2: boundary coefficient object `Ob_B`. -/
abbrev BoundaryCoefficient {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} (Ob : ObstructionSheaf S)
    (E : TwoChartFeatureExtensionCover S) :=
  Ob.carrier.toPresheaf.obj (op E.boundary)

/-- IV.定義8.3: core-side coefficient object for the two-chart Čech complex. -/
abbrev CoreCoefficient {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} (Ob : ObstructionSheaf S)
    (E : TwoChartFeatureExtensionCover S) :=
  Ob.carrier.toPresheaf.obj (op E.core)

/-- IV.定義8.3: feature-side coefficient object for the two-chart Čech complex. -/
abbrev FeatureCoefficient {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} (Ob : ObstructionSheaf S)
    (E : TwoChartFeatureExtensionCover S) :=
  Ob.carrier.toPresheaf.obj (op E.feature)

/-- IV.定義8.2: boundary mismatch section `b_U ∈ H^0(B, Ob_B)`. -/
structure BoundaryMismatchSection {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} (Ob : ObstructionSheaf S)
    (E : TwoChartFeatureExtensionCover S) where
  value : BoundaryCoefficient Ob E
  boundaryWitnessCoverage : Prop
  boundaryWitnessCoverage_holds : boundaryWitnessCoverage

namespace BoundaryMismatchSection

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {Ob : ObstructionSheaf S}
variable {E : TwoChartFeatureExtensionCover S}

/-- IV.定義8.2: read the underlying boundary mismatch value. -/
def b_U (b : BoundaryMismatchSection Ob E) : BoundaryCoefficient Ob E :=
  b.value

end BoundaryMismatchSection

/--
IV.定義8.3: concrete two-chart Čech boundary complex.

For the feature-extension cover, degree zero is
`C^0 = Ob(C_core) × Ob(F)` and degree one is `C^1 = Ob(B)`.  The selected
boundary differential is the difference of the core and feature restrictions
to the boundary object.
-/
structure TwoChartCechBoundaryComplex {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    (Ob : ObstructionSheaf S) (E : TwoChartFeatureExtensionCover S) where
  coreRestrictionToBoundary :
    CoreCoefficient Ob E →+ BoundaryCoefficient Ob E
  featureRestrictionToBoundary :
    FeatureCoefficient Ob E →+ BoundaryCoefficient Ob E

namespace TwoChartCechBoundaryComplex

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {Ob : ObstructionSheaf S}
variable {E : TwoChartFeatureExtensionCover S}

/-- IV.定義8.3: degree-zero two-chart cochains. -/
abbrev C0 (_T : TwoChartCechBoundaryComplex Ob E) : Type u :=
  CoreCoefficient Ob E × FeatureCoefficient Ob E

/-- IV.定義8.3: degree-one two-chart cochains on the boundary. -/
abbrev C1 (_T : TwoChartCechBoundaryComplex Ob E) : Type u :=
  BoundaryCoefficient Ob E

/-- IV.定義8.3: `d^0(s_core, s_feature) = s_feature|_B - s_core|_B`. -/
def d0 (T : TwoChartCechBoundaryComplex Ob E) :
    letI := Ob.addCommGroup E.core
    letI := Ob.addCommGroup E.feature
    letI := Ob.addCommGroup E.boundary
    T.C0 →+ T.C1 :=
  letI := Ob.addCommGroup E.core
  letI := Ob.addCommGroup E.feature
  letI := Ob.addCommGroup E.boundary
  {
    toFun := fun s =>
      T.featureRestrictionToBoundary s.2 - T.coreRestrictionToBoundary s.1
    map_zero' := by
      simp
    map_add' := by
      intro s t
      rcases s with ⟨s_core, s_feature⟩
      rcases t with ⟨t_core, t_feature⟩
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  }

/-- IV.定義8.3: the two-chart differential has the selected boundary-difference form. -/
theorem d0_apply (T : TwoChartCechBoundaryComplex Ob E) (s : T.C0) :
    T.d0 s = T.featureRestrictionToBoundary s.2 - T.coreRestrictionToBoundary s.1 :=
  rfl

end TwoChartCechBoundaryComplex

/--
IV.定義8.3: two-chart Čech connecting homomorphism package.

The `twoChartCech` field records the concrete `C^0 = Ob(C_core) × Ob(F)` and
`C^1 = Ob(B)` boundary differential.  The map `delta` is then supplied as a
selected Čech-level connecting map `H^0(B, Ob_B) -> C^1(C', Ob_C')`, together
with the proof that its values are 1-cocycles.  This is the concrete two-chart
Čech representation; it does not construct a derived Mayer-Vietoris triangle.
-/
structure TwoChartConnectingHomomorphism {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    (Ob : ObstructionSheaf S) (E : TwoChartFeatureExtensionCover S)
    {𝒰 : CoverRelativeCechCover S}
    (K : CoverRelativeCechComplex 𝒰 Ob) where
  extensionCover_base :
    𝒰.base = E.extension
  twoChartCech :
    TwoChartCechBoundaryComplex Ob E
  boundaryRestrictionSource :
    BoundaryCoefficient Ob E -> K.Cn 1
  deltaCochain :
    BoundaryCoefficient Ob E -> K.Cn 1
  deltaCochain_zero :
    letI := Ob.addCommGroup E.boundary
    letI := K.cochainAddCommGroup 1
    deltaCochain 0 = 0
  deltaCochain_add :
    ∀ b c : BoundaryCoefficient Ob E,
      letI := Ob.addCommGroup E.boundary
      letI := K.cochainAddCommGroup 1
      deltaCochain (b + c) = deltaCochain b + deltaCochain c
  deltaCochain_eq_boundaryRestrictionSource :
    ∀ b : BoundaryCoefficient Ob E,
      deltaCochain b = boundaryRestrictionSource b
  delta_cocycle :
    ∀ b : BoundaryCoefficient Ob E,
      letI := K.cochainAddCommGroup 1
      letI := K.cochainAddCommGroup 2
      K.d 1 (deltaCochain b) = 0
  cohomologyAddCommGroup :
    AddCommGroup (K.CoverRelativeHn 1)
  deltaCohomologyHom :
    letI := Ob.addCommGroup E.boundary
    letI := cohomologyAddCommGroup
    BoundaryCoefficient Ob E →+ K.CoverRelativeHn 1
  deltaCohomologyHom_eq_class :
    ∀ b : BoundaryCoefficient Ob E,
      letI := K.cochainAddCommGroup 1
      letI := K.cochainAddCommGroup 2
      letI := cohomologyAddCommGroup
      deltaCohomologyHom b =
        K.cohomologyClassSucc 0 ⟨deltaCochain b, delta_cocycle b⟩

namespace TwoChartConnectingHomomorphism

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {Ob : ObstructionSheaf S}
variable {E : TwoChartFeatureExtensionCover S}
variable {𝒰 : CoverRelativeCechCover S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}

/-- IV.定義8.3: connecting homomorphism on boundary sections. -/
def delta (D : TwoChartConnectingHomomorphism Ob E K) :
    letI := Ob.addCommGroup E.boundary
    letI := K.cochainAddCommGroup 1
    BoundaryCoefficient Ob E →+ K.Cn 1 :=
  letI := Ob.addCommGroup E.boundary
  letI := K.cochainAddCommGroup 1
  {
    toFun := D.deltaCochain
    map_zero' := D.deltaCochain_zero
    map_add' := D.deltaCochain_add
  }

/-- IV.定義8.3: the connecting cochain is the selected boundary restriction. -/
theorem delta_eq_boundaryRestrictionSource
    (D : TwoChartConnectingHomomorphism Ob E K) (b : BoundaryCoefficient Ob E) :
    D.delta b = D.boundaryRestrictionSource b :=
  D.deltaCochain_eq_boundaryRestrictionSource b

/-- IV.定義8.3: `delta(b)` is a selected Čech 1-cocycle. -/
def deltaCocycle (D : TwoChartConnectingHomomorphism Ob E K)
    (b : BoundaryCoefficient Ob E) :
    K.CechCocycle 1 :=
  letI := K.cochainAddCommGroup 1
  letI := K.cochainAddCommGroup 2
  ⟨D.delta b, D.delta_cocycle b⟩

/-- IV.定義8.3: `delta : H^0(B, Ob_B) -> H^1(C', Ob_C')`. -/
def deltaClass (D : TwoChartConnectingHomomorphism Ob E K)
    (b : BoundaryCoefficient Ob E) :
    K.CoverRelativeHn 1 :=
  K.cohomologyClassSucc 0 (D.deltaCocycle b)

/-- IV.定義8.3: class-level connecting homomorphism `H^0(B, Ob_B) -> H^1(C', Ob_C')`. -/
def deltaH1 (D : TwoChartConnectingHomomorphism Ob E K) :
    letI := Ob.addCommGroup E.boundary
    letI := D.cohomologyAddCommGroup
    BoundaryCoefficient Ob E →+ K.CoverRelativeHn 1 :=
  letI := Ob.addCommGroup E.boundary
  letI := D.cohomologyAddCommGroup
  D.deltaCohomologyHom

/-- IV.定義8.3: the class-level homomorphism agrees with the selected cocycle class. -/
theorem deltaH1_eq_deltaClass
    (D : TwoChartConnectingHomomorphism Ob E K) (b : BoundaryCoefficient Ob E) :
    D.deltaH1 b = D.deltaClass b := by
  exact D.deltaCohomologyHom_eq_class b

/-- IV.定義8.3: boundary holonomy `Hol_U = delta(b_U)`. -/
def boundaryHolonomy (D : TwoChartConnectingHomomorphism Ob E K)
    (b : BoundaryMismatchSection Ob E) :
    K.CoverRelativeHn 1 :=
  D.deltaH1 b.b_U

/-- IV.定義8.3: boundary holonomy agrees with the selected connecting class. -/
theorem boundaryHolonomy_eq_delta
    (D : TwoChartConnectingHomomorphism Ob E K)
    (b : BoundaryMismatchSection Ob E) :
    D.boundaryHolonomy b = D.deltaClass b.b_U :=
  D.deltaH1_eq_deltaClass b.b_U

end TwoChartConnectingHomomorphism

end Cohomology
end AAT.AG
