import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ChartGeometricFiber
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Actual response image sequence

This file constructs the image sequence of the target labeled response on the
kernel of the protected labeled responses. All objects and maps are obtained
from the actual allowed-operation sheaf and its existing `labeledResponse`
morphisms.

On every selected lawful-space chart, sections of the protected kernel are
identified with the linear kernel used by `ChartCircuitLocus`, and the target
map agrees with `chartTargetOnProtectedKernel` under that identification.

## Implementation notes

The chart target comparison evaluates the categorical product and then uses
product preservation followed by `ModuleCat.piIsoPi`. This route retains the
same product projections as the actual sheaf morphism, so every component can
be compared directly with the existing chart response.

The protected-kernel comparison is the composite of evaluation's canonical
kernel-preservation isomorphism, the kernel map induced by that product
comparison, and `ModuleCat.kernelIsoKer`. Consequently its compatibility with
the actual kernel inclusion is proved from universal properties. No external
kernel comparison or arbitrary linear equivalence is accepted, and the sheaf
kernel is not replaced by a separately defined pointwise kernel.
-/

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace IntrinsicLawResponseCircuitDescent
namespace ResponseImageSequence

open AAT.AG AAT.AG.LawAlgebra
open LawGeneratedLabeledConormal

universe uk uOp uChart uState uBefore uAfter u

variable {U : AtomCarrier.{u}} {Arch : ArchitectureObject U}
variable {S : Site.AATSite Arch}
variable {k : Type uk} {Op : Type uOp} {Chart : Type uChart}
variable {State : Type uState} {BeforeWitness : Type uBefore}
variable {AfterWitness : Type uAfter}
variable [Field k] [Fintype Op] [Fintype Chart]
variable (Core : SemanticLawEquationWitnessIdealCore S) (W : S.category)
variable [Algebra k (Core.Observable W)]

/-- The finite product of copies of the structure sheaf indexed by protected
required-generator labels. -/
noncomputable abbrev protectedResponseTarget
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S)) :
    (G.lawfulSpace (Core.obstructionIdeal W)).Modules :=
  ∏ᶜ fun _ : protectedLabels ↦
    SheafOfModules.unit
      ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf)

/-- The actual protected response, assembled from the existing labeled
responses by the categorical product universal property. -/
noncomputable def protectedResponse
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S)) :
    Pres.allowedOperationSheaf G (Core.obstructionIdeal W) ⟶
      protectedResponseTarget Core W G protectedLabels :=
  Pi.lift fun e ↦ Pres.labeledResponse Core W G e.1

/-- Every component of the protected response is its actual labeled response. -/
theorem protectedResponseComponent
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S))
    (e : protectedLabels) :
    protectedResponse Core W Pres G protectedLabels ≫
        Pi.π (fun _ : protectedLabels ↦
          SheafOfModules.unit
            ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf)) e =
      Pres.labeledResponse Core W G e.1 := by
  simp [protectedResponse]

/-- The kernel of all protected labeled responses. -/
noncomputable abbrev protectedKernelSheaf
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S)) :
    (G.lawfulSpace (Core.obstructionIdeal W)).Modules :=
  kernel (protectedResponse Core W Pres G protectedLabels)

/-- The actual target response restricted to the protected kernel. -/
noncomputable abbrev targetResponseOnProtectedKernel
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S))
    (target : RequiredGeneratorLabel S) :
    protectedKernelSheaf Core W Pres G protectedLabels ⟶
      SheafOfModules.unit
        ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf) :=
  kernel.ι (protectedResponse Core W Pres G protectedLabels) ≫
    Pres.labeledResponse Core W G target

/-- The kernel of the target response on the protected kernel. -/
noncomputable abbrev responseKernelSheaf
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S))
    (target : RequiredGeneratorLabel S) :
    (G.lawfulSpace (Core.obstructionIdeal W)).Modules :=
  kernel (targetResponseOnProtectedKernel
    Core W Pres G protectedLabels target)

/-- The categorical image of the target response on the protected kernel. -/
noncomputable abbrev responseImageSheaf
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S))
    (target : RequiredGeneratorLabel S) :
    (G.lawfulSpace (Core.obstructionIdeal W)).Modules :=
  Abelian.image (targetResponseOnProtectedKernel
    Core W Pres G protectedLabels target)

/-- The kernel inclusion in the response image sequence. -/
noncomputable abbrev responseKernelInclusion
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S))
    (target : RequiredGeneratorLabel S) :
    responseKernelSheaf Core W Pres G protectedLabels target ⟶
      protectedKernelSheaf Core W Pres G protectedLabels :=
  kernel.ι (targetResponseOnProtectedKernel
    Core W Pres G protectedLabels target)

/-- The canonical epimorphism from the protected kernel to the response image. -/
noncomputable abbrev responseImageProjection
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S))
    (target : RequiredGeneratorLabel S) :
    protectedKernelSheaf Core W Pres G protectedLabels ⟶
      responseImageSheaf Core W Pres G protectedLabels target :=
  Abelian.factorThruImage (targetResponseOnProtectedKernel
    Core W Pres G protectedLabels target)

/-- The canonical monomorphism from the response image to the structure sheaf. -/
noncomputable abbrev responseImageInclusion
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S))
    (target : RequiredGeneratorLabel S) :
    responseImageSheaf Core W Pres G protectedLabels target ⟶
      SheafOfModules.unit
        ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf) :=
  Abelian.image.ι (targetResponseOnProtectedKernel
    Core W Pres G protectedLabels target)

/-- The image factorization recovers the actual restricted target response. -/
theorem responseImageFactorization
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S))
    (target : RequiredGeneratorLabel S) :
    responseImageProjection Core W Pres G protectedLabels target ≫
        responseImageInclusion Core W Pres G protectedLabels target =
      targetResponseOnProtectedKernel Core W Pres G protectedLabels target := by
  exact Abelian.image.fac _

/-- The kernel-to-image short complex of the actual target response. -/
noncomputable def responseImageShortComplex
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S))
    (target : RequiredGeneratorLabel S) :
    ShortComplex ((G.lawfulSpace (Core.obstructionIdeal W)).Modules) :=
  ShortComplex.mk
    (responseKernelInclusion Core W Pres G protectedLabels target)
    (responseImageProjection Core W Pres G protectedLabels target)
    (by
      apply (cancel_mono
        (responseImageInclusion Core W Pres G protectedLabels target)).1
      simp [Category.assoc])

/-- The actual response kernel-to-image complex is short exact. -/
theorem responseImageShortComplex_shortExact
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (protectedLabels : Finset (RequiredGeneratorLabel S))
    (target : RequiredGeneratorLabel S) :
    (responseImageShortComplex Core W Pres G protectedLabels target).ShortExact := by
  let s := targetResponseOnProtectedKernel Core W Pres G protectedLabels target
  let q := Abelian.factorThruImage s
  have hzero : kernel.ι s ≫ q = 0 := by
    apply (cancel_mono (Abelian.image.ι s)).1
    simp [q, Category.assoc]
  have hKernel : IsLimit (KernelFork.ofι (kernel.ι s) hzero) :=
    KernelFork.IsLimit.ofι' (kernel.ι s) hzero fun k hk ↦ by
      have hks : k ≫ s = 0 := by
        rw [← Abelian.image.fac s]
        change k ≫ q ≫ Abelian.image.ι s = 0
        rw [← Category.assoc, hk, zero_comp]
      exact ⟨kernel.lift s k hks, kernel.lift_ι _ _ _⟩
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact ShortComplex.exact_of_f_is_kernel _ hKernel
  · change Mono (kernel.ι s)
    infer_instance
  · change Epi (Abelian.factorThruImage s)
    infer_instance

/-- Evaluation of the protected response target on a selected chart is the
concrete module of protected-label families. -/
noncomputable def chartProtectedResponseTargetIso
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel S)) :
    (SheafOfModules.evaluation
        ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf)
        (.op (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i))).obj
        (protectedResponseTarget Core W G protectedLabels) ≅
      ModuleCat.of (ChartCircuitLocus.chartRing Core W G i)
        (protectedLabels → ChartCircuitLocus.chartRing Core W G i) := by
  let ev := SheafOfModules.evaluation
    ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf)
    (.op (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i))
  let family := fun _ : protectedLabels ↦
      SheafOfModules.unit
        ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf)
  exact PreservesProduct.iso ev family ≪≫
    ModuleCat.piIsoPi (fun e : protectedLabels ↦ ev.obj (family e))

/-- On a selected chart, the protected-response component is the existing
linear protected response map. -/
theorem chartProtectedResponse_app_comp_targetIso
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel S)) :
    (protectedResponse Core W Pres G protectedLabels).val.app
        (.op (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i)) ≫
        (chartProtectedResponseTargetIso Core W G i protectedLabels).hom =
      ModuleCat.ofHom (ChartCircuitLocus.chartProtectedResponseMap
        Core W Pres G i protectedLabels) := by
  apply ConcreteCategory.hom_ext
  intro x
  funext e
  let ev := SheafOfModules.evaluation
    ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf)
    (.op (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i))
  have hcomponent :
      (((protectedResponse Core W Pres G protectedLabels).val.app
          (.op (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i)) ≫
        (chartProtectedResponseTargetIso Core W G i protectedLabels).hom) ≫
          ModuleCat.ofHom (LinearMap.proj e)) =
        (Pres.labeledResponse Core W G e.1).val.app
          (.op (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i)) := by
    change
      (ev.map (protectedResponse Core W Pres G protectedLabels) ≫
        (chartProtectedResponseTargetIso Core W G i protectedLabels).hom) ≫
          ModuleCat.ofHom (LinearMap.proj e) =
        ev.map (Pres.labeledResponse Core W G e.1)
    simp only [chartProtectedResponseTargetIso, Iso.trans_hom,
      Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
      PreservesProduct.iso_hom]
    rw [piComparison_comp_π]
    rw [← Functor.map_comp, protectedResponseComponent]
  exact ConcreteCategory.congr_hom hcomponent x

/-- Sections of the protected kernel on a selected chart agree with the
linear kernel already used by the chart circuit construction. -/
noncomputable def chartProtectedKernelSectionsEquiv
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel S)) :
    Γ(protectedKernelSheaf Core W Pres G protectedLabels,
        G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i) ≃ₗ[
          ChartCircuitLocus.chartRing Core W G i]
      (ChartCircuitLocus.chartProtectedResponseMap
        Core W Pres G i protectedLabels).ker := by
  let ev := SheafOfModules.evaluation
    ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf)
    (.op (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i))
  let f := protectedResponse Core W Pres G protectedLabels
  let chartMap := ChartCircuitLocus.chartProtectedResponseMap
    Core W Pres G i protectedLabels
  let targetIso := chartProtectedResponseTargetIso Core W G i protectedLabels
  let chartHom := ModuleCat.ofHom chartMap
  let comparison := chartProtectedResponse_app_comp_targetIso
    Core W Pres G i protectedLabels
  exact
    (PreservesKernel.iso ev f ≪≫
      kernel.mapIso (f := ev.map f) chartHom
        (Iso.refl _) targetIso (by
          simpa [ev, f, chartMap, chartHom, targetIso] using comparison) ≪≫
      ModuleCat.kernelIsoKer chartHom).toLinearEquiv

/-- The selected-chart kernel equivalence commutes with the actual protected
kernel inclusion. -/
theorem chartProtectedKernelSectionsEquiv_subtype
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel S)) :
    (ChartCircuitLocus.chartProtectedResponseMap
        Core W Pres G i protectedLabels).ker.subtype.comp
        (chartProtectedKernelSectionsEquiv
          Core W Pres G i protectedLabels).toLinearMap =
      ((kernel.ι (protectedResponse Core W Pres G protectedLabels)).val.app
        (.op (G.lawfulChartOpenOnSpace
          (Core.obstructionIdeal W) i))).hom := by
  let ev := SheafOfModules.evaluation
    ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf)
    (.op (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i))
  let f := protectedResponse Core W Pres G protectedLabels
  let chartMap := ChartCircuitLocus.chartProtectedResponseMap
    Core W Pres G i protectedLabels
  let targetIso := chartProtectedResponseTargetIso Core W G i protectedLabels
  let chartHom := ModuleCat.ofHom chartMap
  let comparison := chartProtectedResponse_app_comp_targetIso
    Core W Pres G i protectedLabels
  let kernelIso := PreservesKernel.iso ev f ≪≫
    kernel.mapIso (f := ev.map f) chartHom
      (Iso.refl _) targetIso (by
        simpa [ev, f, chartMap, chartHom, targetIso] using comparison) ≪≫
    ModuleCat.kernelIsoKer chartHom
  have hcat :
      kernelIso.hom ≫ ModuleCat.ofHom chartMap.ker.subtype =
        ev.map (kernel.ι f) := by
    have hlast :
        (ModuleCat.kernelIsoKer chartHom).hom ≫
            ModuleCat.ofHom chartMap.ker.subtype =
          kernel.ι chartHom := by
      exact ModuleCat.kernelIsoKer_hom_ker_subtype chartHom
    simp only [kernelIso, Iso.trans_hom, Category.assoc]
    rw [hlast]
    simp [kernel.mapIso, PreservesKernel.iso_hom]
  exact congrArg ModuleCat.Hom.hom hcat

/-- Under the selected-chart kernel identification, the actual target map is
the target response used by the chart circuit construction. -/
theorem chartTargetOnProtectedKernel_compatibility
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) (protectedLabels : Finset (RequiredGeneratorLabel S))
    (target : RequiredGeneratorLabel S) :
    (ChartCircuitLocus.chartTargetOnProtectedKernel
        Core W Pres G i protectedLabels target).comp
        (chartProtectedKernelSectionsEquiv
          Core W Pres G i protectedLabels).toLinearMap =
      ((targetResponseOnProtectedKernel Core W Pres G protectedLabels target).val.app
        (.op (G.lawfulChartOpenOnSpace
          (Core.obstructionIdeal W) i))).hom := by
  change
    (ChartCircuitLocus.chartLabeledResponse Core W Pres G i target).comp
        ((ChartCircuitLocus.chartProtectedResponseMap
          Core W Pres G i protectedLabels).ker.subtype.comp
          (chartProtectedKernelSectionsEquiv
            Core W Pres G i protectedLabels).toLinearMap) =
      ((Pres.labeledResponse Core W G target).val.app
        (.op (G.lawfulChartOpenOnSpace
          (Core.obstructionIdeal W) i))).hom.comp
        ((kernel.ι (protectedResponse Core W Pres G protectedLabels)).val.app
          (.op (G.lawfulChartOpenOnSpace
            (Core.obstructionIdeal W) i))).hom
  rw [chartProtectedKernelSectionsEquiv_subtype]
  rfl

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ResponseImageSequence

end ResponseImageSequence
end IntrinsicLawResponseCircuitDescent
end ResearchLean.AG.QualitySurface
