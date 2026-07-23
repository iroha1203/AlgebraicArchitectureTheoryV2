import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.CircuitLocus
import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ConormalJacobian

/-!
# Selected-chart section-module circuit locus

This file instantiates the affine C0a circuit theorem on the section module of
an actual selected chart of the generated allowed-operation sheaf. The scalar
ring is the structure-section ring of that open, the operation module is the
corresponding `allowedOperationSheaf` section module, and every required-label
response is the existing component of `labeledResponse`.

The explicit split data records only a section of the protected-response range
and a section of its cokernel. Finite/projective kernels, canonical scalar base
change, support membership, repair failure, and circuit existence are derived
from those source-level sections and the C0a theorem.

## Implementation notes

The selected chart uses the actual structure-section ring rather than
transporting sections to `chartLawQuotient`; the former is exactly the scalar
ring of `labeledResponse.app`, while the latter route would require an
additional scalar comparison unrelated to C0b. Split data stores maps and
retraction laws instead of projectivity propositions or conclusion
certificates, so the needed projectivity instances are reconstructed at each
use. The kernel comparison remains C0a's canonical `LinearMap.tensorKer` map;
the chosen source-level sections are used only to prove its bijectivity.

No abstract instance pair is added for `AffineSplitConstantRankData`: it is a
direction hypothesis on a selected actual chart, and its concrete positive or
negative realization belongs to the later witness obligations. The two
retraction laws are nevertheless used independently below, so the structure is
neither a marker nor an automatically inhabited certificate.
-/

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace IntrinsicLawResponseCircuitDescent
namespace ChartCircuitLocus

open AAT.AG AAT.AG.LawAlgebra
open LawGeneratedLabeledConormal

universe uR uE uF uk uOp uChart uState uBefore uAfter u uA

variable {R : Type uR} {M : Type uE} {F : Type uF}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup F] [Module R F]

/-- The affine split constant-rank direction data used by C0b. It records
source-level sections for the range and cokernel, without storing any
projectivity, comparison, repair, support, or circuit conclusion. -/
structure AffineSplitConstantRankData (f : M →ₗ[R] F) where
  rangeSection : f.range →ₗ[R] M
  rangeSection_spec : f.rangeRestrict ∘ₗ rangeSection = LinearMap.id
  cokernelSection : (F ⧸ f.range) →ₗ[R] F
  cokernelSection_spec : f.range.mkQ ∘ₗ cokernelSection = LinearMap.id

/-- A range split from a projective source is projective. This discharges the
first C0a regularity premise from the explicit range section. -/
theorem AffineSplitConstantRankData.range_projective
    (f : M →ₗ[R] F) (split : AffineSplitConstantRankData f)
    [Module.Projective R M] : Module.Projective R f.range :=
  Module.Projective.of_split split.rangeSection f.rangeRestrict
    split.rangeSection_spec

/-- A cokernel split from a projective target is projective. For chart
responses the target is the canonical finite product of scalar copies. -/
theorem AffineSplitConstantRankData.cokernel_projective
    (f : M →ₗ[R] F) (split : AffineSplitConstantRankData f)
    [Module.Projective R F] : Module.Projective R (F ⧸ f.range) :=
  Module.Projective.of_split split.cokernelSection f.range.mkQ
    split.cokernelSection_spec

variable {U : AtomCarrier.{u}} {Arch : ArchitectureObject U}
variable {S : Site.AATSite Arch}
variable {k : Type uk} {Op : Type uOp} {Chart : Type uChart}
variable {State : Type uState} {BeforeWitness : Type uBefore}
variable {AfterWitness : Type uAfter}
variable [Field k] [Fintype Op] [Fintype Chart]
variable (E : ArchitecturalEquationSystem S.contextPreorder) (W : S.category)
variable [Algebra k (E.Observable W)]

/-- The actual scalar ring of the selected lawful-space chart. -/
noncomputable abbrev chartRing
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) :=
  Γ(G.lawfulSpace (E.obstructionIdeal W),
    G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i)

/-- The actual selected-chart section module of the generated
allowed-operation sheaf. -/
noncomputable abbrev chartAllowedOperationModule
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) :=
  Γ(Pres.allowedOperationSheaf G (E.obstructionIdeal W),
    G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i)

/-- The required `(lawIndex, atom)` response family obtained from the
existing `labeledResponse` sheaf morphism on the selected chart. -/
noncomputable def chartLabeledResponse
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) :
    RequiredGeneratorLabel E →
      Module.Dual (chartRing E W G i)
        (chartAllowedOperationModule E W Pres G i) :=
  fun e ↦
    ((Pres.labeledResponse E W G e).val.app
      (.op (G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i))).hom

/-- The chart response is exactly the component of the previously generated
`labeledResponse`; no evaluator family is accepted as a new input. -/
theorem chartLabeledResponse_eq_labeledResponse_app
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) (e : RequiredGeneratorLabel E) :
    chartLabeledResponse E W Pres G i e =
      ((Pres.labeledResponse E W G e).val.app
        (.op (G.lawfulChartOpenOnSpace (E.obstructionIdeal W) i))).hom := rfl

/-- The protected response map formed canonically from the actual chart
response family and the finite protected-label set. -/
noncomputable def chartProtectedResponseMap
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel E)) :
    chartAllowedOperationModule E W Pres G i →ₗ[chartRing E W G i]
      (protectedLabels → chartRing E W G i) :=
  CircuitLocus.protectedResponseMap
    (chartLabeledResponse E W Pres G i) protectedLabels

/-- The target response restricted to the kernel of the actual protected
chart response map. -/
noncomputable def chartTargetOnProtectedKernel
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel E))
    (target : RequiredGeneratorLabel E) :
    (chartProtectedResponseMap E W Pres G i protectedLabels).ker
        →ₗ[chartRing E W G i] chartRing E W G i :=
  CircuitLocus.targetOnProtectedKernel
    (chartLabeledResponse E W Pres G i) protectedLabels target

/-- The response cokernel whose support measures failure of the target
response on the protected kernel. -/
noncomputable abbrev chartResponseCokernel
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel E))
    (target : RequiredGeneratorLabel E) :=
  chartRing E W G i ⧸ LinearMap.range
    (chartTargetOnProtectedKernel E W Pres G i protectedLabels target)

/-- The selected-chart section-module circuit locus generated from
support-minimal dependencies among the residue-field tensor response family. -/
noncomputable def chartCircuitLocus
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel E))
    (target : RequiredGeneratorLabel E) :
    Set (PrimeSpectrum (chartRing E W G i)) :=
  { p |
      ∃ C : Set (RequiredGeneratorLabel E),
        LinearRepair.IsSupportMinimalDependence
          (K := p.asIdeal.ResidueField)
          (CircuitLocus.fiberResponse p.asIdeal.ResidueField
            (chartLabeledResponse E W Pres G i)) C ∧
        target ∈ C ∧
        C ⊆ insert target (protectedLabels : Set (RequiredGeneratorLabel E)) }

/-- A finite projective actual operation module and its explicit range split
give a finite protected kernel through the C0a kernel theorem. -/
theorem chartProtectedKernel_finite
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel E))
    [Module.Finite (chartRing E W G i)
      (chartAllowedOperationModule E W Pres G i)]
    [Module.Projective (chartRing E W G i)
      (chartAllowedOperationModule E W Pres G i)]
    (split : AffineSplitConstantRankData
      (chartProtectedResponseMap E W Pres G i protectedLabels)) :
    Module.Finite (chartRing E W G i)
      (chartProtectedResponseMap E W Pres G i protectedLabels).ker := by
  letI : Module.Projective (chartRing E W G i)
      (chartProtectedResponseMap E W Pres G i protectedLabels).range :=
    split.range_projective _
  exact CircuitLocus.kernel_finite
    (chartProtectedResponseMap E W Pres G i protectedLabels)

/-- A projective actual operation module and its explicit range split give a
projective protected kernel through the C0a kernel theorem. -/
theorem chartProtectedKernel_projective
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel E))
    [Module.Projective (chartRing E W G i)
      (chartAllowedOperationModule E W Pres G i)]
    (split : AffineSplitConstantRankData
      (chartProtectedResponseMap E W Pres G i protectedLabels)) :
    Module.Projective (chartRing E W G i)
      (chartProtectedResponseMap E W Pres G i protectedLabels).ker := by
  letI : Module.Projective (chartRing E W G i)
      (chartProtectedResponseMap E W Pres G i protectedLabels).range :=
    split.range_projective _
  exact CircuitLocus.kernel_projective
    (chartProtectedResponseMap E W Pres G i protectedLabels)

/-- C0a's canonical tensor-to-kernel map for the actual selected-chart
protected response is an equivalence after every commutative scalar extension.
The two needed projectivity instances are reconstructed from the split data. -/
noncomputable def chartKernelBaseChangeEquiv
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel E))
    [Module.Projective (chartRing E W G i)
      (chartAllowedOperationModule E W Pres G i)]
    (split : AffineSplitConstantRankData
      (chartProtectedResponseMap E W Pres G i protectedLabels))
    (A : Type uA) [CommRing A] [Algebra (chartRing E W G i) A] :
    TensorProduct (chartRing E W G i) A
        (chartProtectedResponseMap E W Pres G i protectedLabels).ker
        ≃ₗ[A]
      ((chartProtectedResponseMap E W Pres G i protectedLabels).baseChange A).ker := by
  letI : Module.Projective (chartRing E W G i)
      (chartProtectedResponseMap E W Pres G i protectedLabels).range :=
    split.range_projective _
  letI : Module.Projective (chartRing E W G i)
      ((protectedLabels → chartRing E W G i) ⧸
        (chartProtectedResponseMap E W Pres G i protectedLabels).range) :=
    split.cokernel_projective _
  exact CircuitLocus.kernelBaseChangeEquiv A
    (chartProtectedResponseMap E W Pres G i protectedLabels)

/-- Membership in the chart circuit locus unfolds to a target-containing
support-minimal dependence in the actual residue-field response family. -/
theorem mem_chartCircuitLocus_iff
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel E))
    (target : RequiredGeneratorLabel E)
    (p : PrimeSpectrum (chartRing E W G i)) :
    p ∈ chartCircuitLocus E W Pres G i protectedLabels target ↔
      ∃ C : Set (RequiredGeneratorLabel E),
        LinearRepair.IsSupportMinimalDependence
          (K := p.asIdeal.ResidueField)
          (CircuitLocus.fiberResponse p.asIdeal.ResidueField
            (chartLabeledResponse E W Pres G i)) C ∧
        target ∈ C ∧
        C ⊆ insert target (protectedLabels : Set (RequiredGeneratorLabel E)) :=
  Iff.rfl

/-- C0a instantiated on the actual selected-chart response: response-cokernel
support is equivalent to a target-containing support-minimal circuit in the
residue-field response family. -/
theorem mem_support_chartResponseCokernel_iff_exists_supportMinimalCircuit
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel E))
    (target : RequiredGeneratorLabel E) (htarget : target ∉ protectedLabels)
    [Module.Projective (chartRing E W G i)
      (chartAllowedOperationModule E W Pres G i)]
    (split : AffineSplitConstantRankData
      (chartProtectedResponseMap E W Pres G i protectedLabels))
    (p : PrimeSpectrum (chartRing E W G i)) :
    p ∈ Module.support (chartRing E W G i)
        (chartResponseCokernel E W Pres G i protectedLabels target) ↔
      ∃ C : Set (RequiredGeneratorLabel E),
        LinearRepair.IsSupportMinimalDependence
          (K := p.asIdeal.ResidueField)
          (CircuitLocus.fiberResponse p.asIdeal.ResidueField
            (chartLabeledResponse E W Pres G i)) C ∧
        target ∈ C ∧
        C ⊆ insert target (protectedLabels : Set (RequiredGeneratorLabel E)) := by
  let response := chartLabeledResponse E W Pres G i
  let f := CircuitLocus.protectedResponseMap response protectedLabels
  letI : Module.Projective (chartRing E W G i) f.range := by
    change Module.Projective (chartRing E W G i)
      (chartProtectedResponseMap E W Pres G i protectedLabels).range
    exact split.range_projective _
  letI : Module.Projective (chartRing E W G i)
      ((protectedLabels → chartRing E W G i) ⧸ f.range) := by
    change Module.Projective (chartRing E W G i)
      ((protectedLabels → chartRing E W G i) ⧸
        (chartProtectedResponseMap E W Pres G i protectedLabels).range)
    exact split.cokernel_projective _
  simpa only [response, f, chartResponseCokernel, chartTargetOnProtectedKernel,
    chartProtectedResponseMap] using
      (CircuitLocus.mem_support_responseCokernel_iff_exists_supportMinimalCircuit
        response protectedLabels target htarget p)

/-- The selected-chart section-module circuit locus generated from actual
sheaf-response components is exactly the support of the target-response
cokernel. -/
theorem chartCircuitLocus_eq_support
    (Pres : ArchitectureOperationPresentation k (E.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (E.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel E))
    (target : RequiredGeneratorLabel E) (htarget : target ∉ protectedLabels)
    [Module.Projective (chartRing E W G i)
      (chartAllowedOperationModule E W Pres G i)]
    (split : AffineSplitConstantRankData
      (chartProtectedResponseMap E W Pres G i protectedLabels)) :
    chartCircuitLocus E W Pres G i protectedLabels target =
      Module.support (chartRing E W G i)
        (chartResponseCokernel E W Pres G i protectedLabels target) := by
  ext p
  rw [mem_chartCircuitLocus_iff]
  exact (mem_support_chartResponseCokernel_iff_exists_supportMinimalCircuit
    E W Pres G i protectedLabels target htarget split p).symm

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ChartCircuitLocus

end ChartCircuitLocus
end IntrinsicLawResponseCircuitDescent
end ResearchLean.AG.QualitySurface
