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
IV-7 / 定理9.2 completeness surface: the selected boundary mismatch is
resolved by a concrete core/feature degree-zero cochain.

Unlike `TwoChartGloballyUFlat`, this predicate is relative to the boundary
mismatch `b`: it records the actual equation `b_U = d0(s)` rather than only a
zero boundary agreement.
-/
def TwoChartBoundaryResolved {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {Ob : ObstructionSheaf S}
    {E : TwoChartFeatureExtensionCover S}
    {𝒰 : CoverRelativeCechCover S}
    {K : CoverRelativeCechComplex 𝒰 Ob}
    (D : TwoChartConnectingHomomorphism Ob E K)
    (b : BoundaryMismatchSection Ob E) : Prop :=
  letI := Ob.addCommGroup E.core
  letI := Ob.addCommGroup E.feature
  letI := Ob.addCommGroup E.boundary
  ∃ s : D.twoChartCech.C0, b.b_U = D.twoChartCech.d0 s

namespace TwoChartBoundaryResolved

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {Ob : ObstructionSheaf S}
variable {E : TwoChartFeatureExtensionCover S}
variable {𝒰 : CoverRelativeCechCover S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {D : TwoChartConnectingHomomorphism Ob E K}
variable {b : BoundaryMismatchSection Ob E}

/-- IV-7: expose the concrete degree-zero cochain resolving `b_U`. -/
theorem exists_boundary_coboundary
    (h : TwoChartBoundaryResolved D b) :
    letI := Ob.addCommGroup E.core
    letI := Ob.addCommGroup E.feature
    letI := Ob.addCommGroup E.boundary
    ∃ s : D.twoChartCech.C0, b.b_U = D.twoChartCech.d0 s :=
  h

/-- IV-7: build boundary-resolution from a concrete two-chart coboundary equation. -/
theorem of_boundary_coboundary
    (s : D.twoChartCech.C0)
    (hs :
      letI := Ob.addCommGroup E.core
      letI := Ob.addCommGroup E.feature
      letI := Ob.addCommGroup E.boundary
      b.b_U = D.twoChartCech.d0 s) :
    TwoChartBoundaryResolved D b :=
  ⟨s, hs⟩

end TwoChartBoundaryResolved

namespace TwoChartConnectingHomomorphism

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {Ob : ObstructionSheaf S}
variable {E : TwoChartFeatureExtensionCover S}
variable {𝒰 : CoverRelativeCechCover S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {D : TwoChartConnectingHomomorphism Ob E K}
variable {b : BoundaryMismatchSection Ob E}

/--
IV-7 / 定理9.2 completeness-side exactness predicate.

This is the concrete replacement for reading a free-form completeness package:
every boundary class with zero selected holonomy is represented by the
two-chart boundary of a core/feature degree-zero cochain.
-/
def HolonomyKernelExactAtBoundary
    (D : TwoChartConnectingHomomorphism Ob E K) : Prop :=
  letI := Ob.addCommGroup E.core
  letI := Ob.addCommGroup E.feature
  letI := Ob.addCommGroup E.boundary
  letI := D.cohomologyAddCommGroup
  ∀ c : BoundaryCoefficient Ob E, D.deltaH1 c = 0 ->
    ∃ s : D.twoChartCech.C0, c = D.twoChartCech.d0 s

/--
IV-7 / 定理9.2 soundness-side exactness predicate.

The selected class-level connecting homomorphism kills concrete two-chart
boundaries.  Together with `TwoChartBoundaryResolved`, this proves the
zero-holonomy direction without using `BoundaryResidueHypotheses`.
-/
def DeltaKillsTwoChartBoundaries
    (D : TwoChartConnectingHomomorphism Ob E K) : Prop :=
  letI := Ob.addCommGroup E.core
  letI := Ob.addCommGroup E.feature
  letI := Ob.addCommGroup E.boundary
  letI := D.cohomologyAddCommGroup
  ∀ s : D.twoChartCech.C0, D.deltaH1 (D.twoChartCech.d0 s) = 0

/--
IV-7 / 定理9.2 soundness core: if the selected boundary mismatch is the
two-chart boundary of a core/feature section whose boundary difference is zero,
then the selected boundary holonomy vanishes.

This is the theorem-level two-chart soundness route.  It does not read the
`BoundaryResidueHypotheses.boundaryResidueSoundness` field.
-/
theorem boundaryHolonomy_zero_of_twoChartBoundaryAgreement
    (s : D.twoChartCech.C0)
    (hb :
      letI := Ob.addCommGroup E.core
      letI := Ob.addCommGroup E.feature
      letI := Ob.addCommGroup E.boundary
      b.b_U = D.twoChartCech.d0 s)
    (hs :
      letI := Ob.addCommGroup E.core
      letI := Ob.addCommGroup E.feature
      letI := Ob.addCommGroup E.boundary
      D.twoChartCech.d0 s = 0) :
    BoundaryHolonomyVanishes D b := by
  letI := D.cohomologyAddCommGroup
  dsimp [BoundaryHolonomyVanishes, boundaryHolonomy]
  rw [hb, hs]
  exact map_zero D.deltaH1

/--
IV-7 / 定理9.2 soundness core: a zero boundary mismatch has zero selected
boundary holonomy.
-/
theorem boundaryHolonomy_zero_of_boundaryMismatch_zero
    (hb :
      letI := Ob.addCommGroup E.boundary
      b.b_U = 0) :
    BoundaryHolonomyVanishes D b := by
  letI := D.cohomologyAddCommGroup
  dsimp [BoundaryHolonomyVanishes, boundaryHolonomy]
  rw [hb]
  exact map_zero D.deltaH1

/--
IV-7 / 定理9.2 completeness core: if the class-level holonomy kernel is
exactly represented by concrete two-chart boundaries, then zero boundary
holonomy resolves the selected boundary mismatch by a degree-zero cochain.

This theorem does not read `BoundaryResidueHypotheses.boundaryResidueCompleteness`.
-/
theorem boundaryResolved_of_boundaryHolonomy_zero_of_kernelExact
    (hexact : D.HolonomyKernelExactAtBoundary)
    (hzero : BoundaryHolonomyVanishes D b) :
    TwoChartBoundaryResolved D b := by
  letI := Ob.addCommGroup E.core
  letI := Ob.addCommGroup E.feature
  letI := Ob.addCommGroup E.boundary
  letI := D.cohomologyAddCommGroup
  dsimp [BoundaryHolonomyVanishes, boundaryHolonomy] at hzero
  rcases hexact b.b_U hzero with ⟨s, hs⟩
  exact TwoChartBoundaryResolved.of_boundary_coboundary s hs

/--
IV-7 / 定理9.2 soundness core for the boundary-resolved predicate: if the
selected connecting map kills concrete two-chart boundaries, every resolved
boundary mismatch has zero holonomy.

This theorem does not read `BoundaryResidueHypotheses.boundaryResidueSoundness`.
-/
theorem boundaryHolonomy_zero_of_boundaryResolved_of_deltaKillsBoundaries
    (hkill : D.DeltaKillsTwoChartBoundaries)
    (hresolved : TwoChartBoundaryResolved D b) :
    BoundaryHolonomyVanishes D b := by
  letI := Ob.addCommGroup E.core
  letI := Ob.addCommGroup E.feature
  letI := Ob.addCommGroup E.boundary
  letI := D.cohomologyAddCommGroup
  rcases hresolved with ⟨s, hs⟩
  dsimp [BoundaryHolonomyVanishes, boundaryHolonomy]
  rw [hs]
  exact hkill s

/--
IV-7 / 定理9.2 nonzero core: if concrete two-chart boundaries are killed by
the selected connecting map, nonzero boundary holonomy rules out a concrete
boundary resolution.
-/
theorem not_boundaryResolved_of_boundaryHolonomy_nonzero_of_deltaKillsBoundaries
    (hkill : D.DeltaKillsTwoChartBoundaries)
    (hnonzero : ¬ BoundaryHolonomyVanishes D b) :
    ¬ TwoChartBoundaryResolved D b := by
  intro hresolved
  exact hnonzero
    (D.boundaryHolonomy_zero_of_boundaryResolved_of_deltaKillsBoundaries hkill hresolved)

end TwoChartConnectingHomomorphism

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
  boundaryResidueSoundness :
    core_UFlat ->
      feature_UFlat ->
        b.boundaryWitnessCoverage ->
          axisExactness ->
            boundaryExactCoefficients ->
              ringRestrictionCompatibility ->
                effectiveTorsorModuleDescent ->
                  TwoChartGloballyUFlat D ->
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
                        TwoChartGloballyUFlat D

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
  TwoChartGloballyUFlat D

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
