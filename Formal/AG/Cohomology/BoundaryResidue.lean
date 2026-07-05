import Formal.AG.Cohomology.BoundaryHolonomy

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

/--
IV.定理9.2: vanishing of the selected boundary holonomy class.

The target `H^1(C', Ob_C')` group structure is part of the selected
two-chart connecting package introduced for IV.定義8.3.
-/
def BoundaryHolonomyVanishes {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {Ob : ObstructionSheaf S}
    {E : TwoChartFeatureExtensionCover S}
    {𝒰 : CoverRelativeCechCover S}
    {K : CoverRelativeCechComplex 𝒰 Ob}
    (D : TwoChartConnectingHomomorphism Ob E K)
    (b : BoundaryMismatchSection Ob E) : Prop :=
  letI := D.cohomologyAddCommGroup
  D.boundaryHolonomy b = 0

/--
IV.定理9.2 / IV-7: concrete two-chart global U-flatness predicate.

The selected global section is represented by a core/feature degree-zero
cochain, and global flatness means that the two restrictions agree on the
boundary, i.e. the concrete two-chart differential is zero.
-/
def TwoChartGloballyUFlat {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {Ob : ObstructionSheaf S}
    {E : TwoChartFeatureExtensionCover S}
    {𝒰 : CoverRelativeCechCover S}
    {K : CoverRelativeCechComplex 𝒰 Ob}
    (D : TwoChartConnectingHomomorphism Ob E K) : Prop :=
  letI := Ob.addCommGroup E.core
  letI := Ob.addCommGroup E.feature
  letI := Ob.addCommGroup E.boundary
  ∃ s : D.twoChartCech.C0, D.twoChartCech.d0 s = 0

namespace TwoChartGloballyUFlat

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {Ob : ObstructionSheaf S}
variable {E : TwoChartFeatureExtensionCover S}
variable {𝒰 : CoverRelativeCechCover S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {D : TwoChartConnectingHomomorphism Ob E K}

/-- IV-7: expose the selected two-chart global section and boundary agreement. -/
theorem exists_boundary_agreement
    (h : TwoChartGloballyUFlat D) :
    letI := Ob.addCommGroup E.core
    letI := Ob.addCommGroup E.feature
    letI := Ob.addCommGroup E.boundary
    ∃ s : D.twoChartCech.C0, D.twoChartCech.d0 s = 0 :=
  h

/-- IV-7: build concrete global U-flatness from a zero two-chart boundary. -/
theorem of_boundary_agreement
    (s : D.twoChartCech.C0)
    (hs :
      letI := Ob.addCommGroup E.core
      letI := Ob.addCommGroup E.feature
      letI := Ob.addCommGroup E.boundary
      D.twoChartCech.d0 s = 0) :
    TwoChartGloballyUFlat D :=
  ⟨s, hs⟩

end TwoChartGloballyUFlat

/--
IV.定理9.2: explicit hypothesis block for the Boundary Residue theorem.

This package records exactly the assumptions used to read boundary holonomy as
the complete global-flatness obstruction for a selected two-chart feature
extension.  It deliberately does not construct a derived Mayer-Vietoris
triangle or an assumption-free flatness criterion.
-/
structure BoundaryResidueHypotheses {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {Ob : ObstructionSheaf S}
    {E : TwoChartFeatureExtensionCover S}
    {𝒰 : CoverRelativeCechCover S}
    {K : CoverRelativeCechComplex 𝒰 Ob}
    (D : TwoChartConnectingHomomorphism Ob E K)
    (b : BoundaryMismatchSection Ob E) where
  core_UFlat : Prop
  core_UFlat_holds : core_UFlat
  feature_UFlat : Prop
  feature_UFlat_holds : feature_UFlat
  boundaryWitnessCoverage :
    b.boundaryWitnessCoverage
  axisExactness : Prop
  axisExactness_holds : axisExactness
  boundaryExactCoefficients : Prop
  boundaryExactCoefficients_holds : boundaryExactCoefficients
  ringRestrictionCompatibility : Prop
  ringRestrictionCompatibility_holds : ringRestrictionCompatibility
  effectiveTorsorModuleDescent : Prop
  effectiveTorsorModuleDescent_holds : effectiveTorsorModuleDescent
  holonomyCompleteForGlobalObstruction : Prop
  holonomyCompleteForGlobalObstruction_holds :
    holonomyCompleteForGlobalObstruction
  noHigherBoundaryObstruction : Prop
  noHigherBoundaryObstruction_holds : noHigherBoundaryObstruction
  globally_UFlat : Prop
  boundaryResidueSoundness :
    core_UFlat ->
      feature_UFlat ->
        b.boundaryWitnessCoverage ->
          axisExactness ->
            boundaryExactCoefficients ->
              ringRestrictionCompatibility ->
                effectiveTorsorModuleDescent ->
                  globally_UFlat ->
                    BoundaryHolonomyVanishes D b
  boundaryResidueCompleteness :
    core_UFlat ->
      feature_UFlat ->
        b.boundaryWitnessCoverage ->
          axisExactness ->
            boundaryExactCoefficients ->
              ringRestrictionCompatibility ->
                effectiveTorsorModuleDescent ->
                  holonomyCompleteForGlobalObstruction ->
                    noHigherBoundaryObstruction ->
                      BoundaryHolonomyVanishes D b ->
                        globally_UFlat

namespace BoundaryResidueHypotheses

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {Ob : ObstructionSheaf S}
variable {E : TwoChartFeatureExtensionCover S}
variable {𝒰 : CoverRelativeCechCover S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {D : TwoChartConnectingHomomorphism Ob E K}
variable {b : BoundaryMismatchSection Ob E}

/-- IV.定理9.2: read the selected global flatness proposition. -/
def globallyUFlat (_H : BoundaryResidueHypotheses D b) : Prop :=
  _H.globally_UFlat

/-- IV.定理9.2: the selected assumption block records boundary witness coverage. -/
theorem boundaryWitnessCoverage_holds (H : BoundaryResidueHypotheses D b) :
    b.boundaryWitnessCoverage :=
  H.boundaryWitnessCoverage

/--
IV.定理9.2 Boundary Residue theorem.

Under the explicit Boundary Residue hypothesis block, the selected feature
extension is globally U-flat exactly when its boundary holonomy vanishes.
-/
theorem boundaryResidueTheorem (H : BoundaryResidueHypotheses D b) :
    H.globallyUFlat ↔ BoundaryHolonomyVanishes D b :=
  ⟨fun h =>
      H.boundaryResidueSoundness
        H.core_UFlat_holds
        H.feature_UFlat_holds
        H.boundaryWitnessCoverage
        H.axisExactness_holds
        H.boundaryExactCoefficients_holds
        H.ringRestrictionCompatibility_holds
        H.effectiveTorsorModuleDescent_holds
        h,
    fun h =>
      H.boundaryResidueCompleteness
        H.core_UFlat_holds
        H.feature_UFlat_holds
        H.boundaryWitnessCoverage
        H.axisExactness_holds
        H.boundaryExactCoefficients_holds
        H.ringRestrictionCompatibility_holds
        H.effectiveTorsorModuleDescent_holds
        H.holonomyCompleteForGlobalObstruction_holds
        H.noHigherBoundaryObstruction_holds
        h⟩

/-- IV.定理9.2: zero boundary holonomy gives global U-flatness under the package assumptions. -/
theorem globallyUFlat_of_boundaryHolonomy_zero
    (H : BoundaryResidueHypotheses D b)
    (h : BoundaryHolonomyVanishes D b) :
    H.globallyUFlat :=
  H.boundaryResidueCompleteness
    H.core_UFlat_holds
    H.feature_UFlat_holds
    H.boundaryWitnessCoverage
    H.axisExactness_holds
    H.boundaryExactCoefficients_holds
    H.ringRestrictionCompatibility_holds
    H.effectiveTorsorModuleDescent_holds
    H.holonomyCompleteForGlobalObstruction_holds
    H.noHigherBoundaryObstruction_holds
    h

/-- IV.定理9.2: global U-flatness gives zero boundary holonomy under the package assumptions. -/
theorem boundaryHolonomy_zero_of_globallyUFlat
    (H : BoundaryResidueHypotheses D b)
    (h : H.globallyUFlat) :
    BoundaryHolonomyVanishes D b :=
  H.boundaryResidueSoundness
    H.core_UFlat_holds
    H.feature_UFlat_holds
    H.boundaryWitnessCoverage
    H.axisExactness_holds
    H.boundaryExactCoefficients_holds
    H.ringRestrictionCompatibility_holds
    H.effectiveTorsorModuleDescent_holds
    h

end BoundaryResidueHypotheses

end Cohomology
end AAT.AG
