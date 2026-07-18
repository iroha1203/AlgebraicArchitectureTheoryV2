import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.AffineImageExactness
import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ChartCircuitLocus
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Selected affine chart comparison for the allowed-operation image sheaf

On a selected lawful chart, this file compares the actual restriction of the
allowed-operation sheaf with the `tilde` of its actual chart-section module.
The construction starts from the defining abelian image
`Abelian.image (operationToCoefficient ...)`.  The restricted free source and
derivation-coefficient target are placed in the affine `tilde` essential
image, naturality of the `tilde`--Gamma counit compares the restricted arrow
with the `tilde` of its section map, and the two canonical image comparisons
from `AffineImageExactness` transport the resulting abelian image.

No comparison, quasi-coherence conclusion, or `fromTildeΓ` isomorphism is
accepted as an input.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

set_option maxHeartbeats 1000000

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace IntrinsicLawResponseCircuitDescent
namespace ChartGeometricFiber

open AAT.AG AAT.AG.LawAlgebra
open LawGeneratedLabeledConormal

universe uk uOp uChart uState uBefore uAfter u uA

variable {U : AtomCarrier.{u}} {Arch : ArchitectureObject U}
variable {S : Site.AATSite Arch}
variable {k : Type uk} {Op : Type uOp} {Chart : Type uChart}
variable {State : Type uState} {BeforeWitness : Type uBefore}
variable {AfterWitness : Type uAfter}
variable [Field k] [Fintype Op] [Fintype Chart]
variable (Core : SemanticLawEquationWitnessIdealCore S) (W : S.category)
variable [Algebra k (Core.Observable W)]

private theorem presentation_mem_tilde_essImage
    {R : CommRingCat.{uA}} {M : (Spec R).Modules}
    (P : M.Presentation) :
    (tilde.functor R).essImage M := by
  apply ObjectProperty.prop_of_isColimit
    (P := (tilde.functor R).essImage) P.isColimit
  rintro (_ | _)
  · exact ⟨ModuleCat.of R (P.relations.I →₀ R), ⟨tildeFinsupp _⟩⟩
  · exact ⟨ModuleCat.of R (P.generators.I →₀ R), ⟨tildeFinsupp _⟩⟩

private noncomputable def restrictUnitIso
    {X Y : Scheme.{uA}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).obj
        (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : (TopologicalSpace.Opens.map j.base).IsRightAdjoint :=
    j.isOpenEmbedding.isOpenMap.adjunction.isRightAdjoint
  letI : (TopologicalSpace.Opens.map j.base).Final := inferInstance
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (F := TopologicalSpace.Opens.map j.base) j.toRingCatSheafHom) := by
    infer_instance
  exact (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit
      (F := TopologicalSpace.Opens.map j.base) j.toRingCatSheafHom)

private noncomputable def restrictPresentation
    {X Y : Scheme.{uA}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} (P : M.Presentation) :
    ((Scheme.Modules.restrictFunctor j).obj M).Presentation := by
  let F := Scheme.Modules.restrictFunctor j
  letI : F.IsLeftAdjoint := inferInstance
  letI : PreservesColimitsOfSize.{uA, uA} F := by infer_instance
  exact P.map F (restrictUnitIso j)

private noncomputable def tildeRestrictFreeIso
    {R : CommRingCat.{uA}} {Y : Scheme.{uA}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (I : Type uA) :
    tilde (ModuleCat.of R (I →₀ R)) ≅
      (Scheme.Modules.restrictFunctor j).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) I) := by
  letI : (TopologicalSpace.Opens.map j.base).IsRightAdjoint :=
    j.isOpenEmbedding.isOpenMap.adjunction.isRightAdjoint
  letI : (TopologicalSpace.Opens.map j.base).Final := inferInstance
  exact tildeFinsupp I ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫
      SheafOfModules.pullbackObjFreeIso j.toRingCatSheafHom I).symm

/-- Every selected lawful-space chart is affine: its image under the lawful
open immersion is the corresponding principal basic open. -/
theorem lawfulChartOpenOnSpace_isAffineOpen
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    AlgebraicGeometry.IsAffineOpen
      (G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i) := by
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion
    (G.lawfulOpen (Core.obstructionIdeal W)).ι).mp
  rw [G.image_lawfulChartOpenOnSpace]
  exact IsAffineOpen.Spec_basicOpen _

/-- The actual allowed-operation image sheaf restricted along the affine
spectrum presentation of a selected lawful-space chart. -/
noncomputable abbrev chartAllowedOperationOnSpec
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    (AlgebraicGeometry.Spec
      (.of (ChartCircuitLocus.chartRing Core W G i))).Modules :=
  let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
  (Pres.allowedOperationSheaf G (Core.obstructionIdeal W)).restrict hU.fromSpec

private noncomputable def chartSectionsToRestrictedTop
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    ModuleCat.of (ChartCircuitLocus.chartRing Core W G i)
        (ChartCircuitLocus.chartAllowedOperationModule Core W Pres G i) ⟶
      moduleSpecΓFunctor.obj (chartAllowedOperationOnSpec Core W Pres G i) := by
  let U0 := G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i
  let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
  let j := hU.fromSpec
  let M := Pres.allowedOperationSheaf G (Core.obstructionIdeal W)
  let eU : j ''ᵁ (⊤ : (Spec (.of (ChartCircuitLocus.chartRing Core W G i))).Opens) = U0 :=
    j.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  let R0 := ChartCircuitLocus.chartRing Core W G i
  let T := chartAllowedOperationOnSpec Core W Pres G i
  let Q := ((SheafOfModules.forgetToSheafModuleCat
    (Spec (.of R0)).ringCatSheaf (.op ⊤)
    (initialOpOfTerminal isTerminalTop)).obj T).val.obj (.op ⊤)
  letI : Module R0 Q :=
    Module.compHom Q (StructureSheaf.globalSectionsIso R0).hom.hom
  have hscalar :
      (G.lawfulSpace (Core.obstructionIdeal W)).presheaf.map
          (eqToHom eU).op =
        (Scheme.ΓSpecIso R0).inv ≫
          (j.appIso (⊤ : (Spec (.of R0)).Opens)).inv := by
    rw [← cancel_mono
      (j.appIso (⊤ : (Spec (.of R0)).Opens)).hom]
    simp only [Category.assoc]
    rw [j.appIso_hom]
    rw [j.naturality_assoc]
    rw [hU.fromSpec_app_self]
    simp only [Category.assoc, ← Functor.map_comp]
    simp only [j.appIso_inv_app_assoc, ← Functor.map_comp]
    congr 1
  change ModuleCat.of R0 _ ⟶ ModuleCat.of R0 Q
  refine ModuleCat.ofHom
    { toFun := fun x ↦ M.presheaf.map (eqToHom eU).op x
      map_add' := by simp
      map_smul' := ?_ }
  intro r x
  calc
    _ = ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf.val.map
          (eqToHom eU).op).hom r •
        (M.val.map (eqToHom eU).op).hom x := by
      exact (M.val.map (eqToHom eU).op).hom.map_smul r x
    _ = _ := by
      change ((G.lawfulSpace (Core.obstructionIdeal W)).ringCatSheaf.val.map
            (eqToHom eU).op).hom r •
          (M.val.map (eqToHom eU).op).hom x =
        (j.appIso (⊤ : (Spec (.of R0)).Opens)).inv.hom
            ((Scheme.ΓSpecIso R0).inv.hom r) •
          (M.val.map (eqToHom eU).op).hom x
      congr 1
      exact ConcreteCategory.congr_hom hscalar r

private noncomputable def chartSectionsIso
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    ModuleCat.of (ChartCircuitLocus.chartRing Core W G i)
        (ChartCircuitLocus.chartAllowedOperationModule Core W Pres G i) ≅
      moduleSpecΓFunctor.obj (chartAllowedOperationOnSpec Core W Pres G i) :=
  LinearEquiv.toModuleIso <| LinearEquiv.ofBijective
    (chartSectionsToRestrictedTop Core W Pres G i).hom (by
      let U0 := G.lawfulChartOpenOnSpace (Core.obstructionIdeal W) i
      let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
      let j := hU.fromSpec
      let M := Pres.allowedOperationSheaf G (Core.obstructionIdeal W)
      let eU : j ''ᵁ
          (⊤ : (Spec (.of (ChartCircuitLocus.chartRing Core W G i))).Opens) = U0 :=
        j.image_top_eq_opensRange.trans hU.opensRange_fromSpec
      change Function.Bijective
        (M.presheaf.map (eqToHom eU).op).hom
      exact ConcreteCategory.bijective_of_isIso
        (M.presheaf.map (eqToHom eU).op))

private noncomputable def chartDerivationCoefficientPresentation
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
    ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
      (G.derivationCoefficientSheaf (Core.obstructionIdeal W))).Presentation := by
  let I0 := Core.obstructionIdeal W
  let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
  let P0 := AlgebraicGeometry.presentationTilde
    (R := .of (TypedLocalizationGeometry.ambientLawQuotient I0))
    (M := TypedLocalizationGeometry.ambientDerivationModule
      (k := k) I0)
    Set.univ (by simp) _ (Submodule.span_eq _)
  change ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
    ((Scheme.Modules.restrictFunctor (G.lawfulOpen I0).ι).obj
      (TypedLocalizationGeometry.ambientDerivationSheaf
        (k := k) I0))).Presentation
  exact restrictPresentation hU.fromSpec
    (restrictPresentation (G.lawfulOpen I0).ι P0)

private theorem restrictedOperationFree_mem_essImage
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
    (tilde.functor (ChartCircuitLocus.chartRing Core W G i)).essImage
      ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
        (ArchitectureOperationPresentation.operationFreeSheaf Op G
          (Core.obstructionIdeal W))) := by
  let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
  exact ⟨ModuleCat.of (ChartCircuitLocus.chartRing Core W G i)
      (ArchitectureOperationPresentation.operationIndex
        (Core.Observable W) Op →₀ ChartCircuitLocus.chartRing Core W G i),
    ⟨tildeRestrictFreeIso hU.fromSpec
      (ArchitectureOperationPresentation.operationIndex
        (Core.Observable W) Op)⟩⟩

private theorem restrictedDerivationCoefficient_mem_essImage
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
    (tilde.functor (ChartCircuitLocus.chartRing Core W G i)).essImage
      ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
        (G.derivationCoefficientSheaf (Core.obstructionIdeal W))) := by
  exact presentation_mem_tilde_essImage
    (chartDerivationCoefficientPresentation Core W G i)

private instance restrictedOperationFree_fromTildeΓ_isIso
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
    IsIso (Scheme.Modules.fromTildeΓ
      (R := ChartCircuitLocus.chartRing Core W G i)
      ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
        (ArchitectureOperationPresentation.operationFreeSheaf Op G
          (Core.obstructionIdeal W)))) := by
  exact isIso_fromTildeΓ_iff.mpr
    (restrictedOperationFree_mem_essImage Core W G i)

private instance restrictedDerivationCoefficient_fromTildeΓ_isIso
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
    IsIso (Scheme.Modules.fromTildeΓ
      (R := ChartCircuitLocus.chartRing Core W G i)
      ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
        (G.derivationCoefficientSheaf (Core.obstructionIdeal W)))) := by
  exact isIso_fromTildeΓ_iff.mpr
    (restrictedDerivationCoefficient_mem_essImage Core W G i)

private noncomputable def restrictedOperationArrowIso
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
    let F := Scheme.Modules.restrictFunctor hU.fromSpec
    let f := Pres.operationToCoefficient G (Core.obstructionIdeal W)
    Arrow.mk ((tilde.functor
      (ChartCircuitLocus.chartRing Core W G i)).map
        ((moduleSpecΓFunctor
          (R := ChartCircuitLocus.chartRing Core W G i)).map (F.map f))) ≅
      Arrow.mk (F.map f) := by
  let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
  let F := Scheme.Modules.restrictFunctor hU.fromSpec
  let f := Pres.operationToCoefficient G (Core.obstructionIdeal W)
  exact Arrow.isoMk'
    ((tilde.functor (ChartCircuitLocus.chartRing Core W G i)).map
      ((moduleSpecΓFunctor
        (R := ChartCircuitLocus.chartRing Core W G i)).map (F.map f)))
    (F.map f)
    (asIso (Scheme.Modules.fromTildeΓ
      (R := ChartCircuitLocus.chartRing Core W G i)
      (F.obj (ArchitectureOperationPresentation.operationFreeSheaf Op G
        (Core.obstructionIdeal W)))))
    (asIso (Scheme.Modules.fromTildeΓ
      (R := ChartCircuitLocus.chartRing Core W G i)
      (F.obj (G.derivationCoefficientSheaf (Core.obstructionIdeal W)))))
    ((Scheme.Modules.fromTildeΓNatTrans
      (R := ChartCircuitLocus.chartRing Core W G i)).naturality
        (F.map f)).symm

private noncomputable def chartAllowedOperationImageTildeIso
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
    let F := Scheme.Modules.restrictFunctor hU.fromSpec
    let f := Pres.operationToCoefficient G (Core.obstructionIdeal W)
    let g := (moduleSpecΓFunctor
      (R := ChartCircuitLocus.chartRing Core W G i)).map (F.map f)
    tilde (R := ChartCircuitLocus.chartRing Core W G i)
      (Abelian.image g) ≅ F.obj (Abelian.image f) := by
  let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
  let F := Scheme.Modules.restrictFunctor hU.fromSpec
  let f := Pres.operationToCoefficient G (Core.obstructionIdeal W)
  let g := (moduleSpecΓFunctor
    (R := ChartCircuitLocus.chartRing Core W G i)).map (F.map f)
  exact AffineImageExactness.tildeAbelianImageIso g ≪≫
    Abelian.im.mapIso (restrictedOperationArrowIso Core W Pres G i) ≪≫
    (AffineImageExactness.restrictAbelianImageIso hU.fromSpec f).symm

private theorem chartAllowedOperationOnSpec_mem_essImage
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    (tilde.functor (ChartCircuitLocus.chartRing Core W G i)).essImage
      (chartAllowedOperationOnSpec Core W Pres G i) := by
  let hU := lawfulChartOpenOnSpace_isAffineOpen Core W G i
  let F := Scheme.Modules.restrictFunctor hU.fromSpec
  let f := Pres.operationToCoefficient G (Core.obstructionIdeal W)
  let g := (moduleSpecΓFunctor
    (R := ChartCircuitLocus.chartRing Core W G i)).map (F.map f)
  exact ⟨Abelian.image g,
    ⟨chartAllowedOperationImageTildeIso Core W Pres G i⟩⟩

/-- The canonical affine comparison for the actual allowed-operation image
sheaf on a selected chart.  Its image provenance is the composite
`tildeAbelianImageIso ≪≫ Abelian.im.mapIso ≪≫
restrictAbelianImageIso.symm`, applied to the defining
`operationToCoefficient` morphism. -/
noncomputable def allowedOperationChartTildeIso
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    AlgebraicGeometry.tilde
        (ModuleCat.of (ChartCircuitLocus.chartRing Core W G i)
          (ChartCircuitLocus.chartAllowedOperationModule Core W Pres G i)) ≅
      chartAllowedOperationOnSpec Core W Pres G i := by
  let T := chartAllowedOperationOnSpec Core W Pres G i
  letI : IsIso (Scheme.Modules.fromTildeΓ T) :=
    isIso_fromTildeΓ_iff.mpr
      (chartAllowedOperationOnSpec_mem_essImage Core W Pres G i)
  exact (tilde.functor
      (ChartCircuitLocus.chartRing Core W G i)).mapIso
        (chartSectionsIso Core W Pres G i) ≪≫
      asIso (Scheme.Modules.fromTildeΓ T)

/-- The `tilde`--Gamma counit of the actual selected-chart
allowed-operation sheaf is an isomorphism. -/
instance chartAllowedOperation_fromTildeΓ_isIso
    (Pres : ArchitectureOperationPresentation k (Core.Observable W) Op
      State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k (Core.Observable W) Chart)
    (i : Chart) :
    IsIso (AlgebraicGeometry.Scheme.Modules.fromTildeΓ
      (R := ChartCircuitLocus.chartRing Core W G i)
      (chartAllowedOperationOnSpec Core W Pres G i)) :=
  isIso_fromTildeΓ_iff.mpr
    ⟨ModuleCat.of (ChartCircuitLocus.chartRing Core W G i)
        (ChartCircuitLocus.chartAllowedOperationModule Core W Pres G i),
      ⟨allowedOperationChartTildeIso Core W Pres G i⟩⟩

end ChartGeometricFiber
end IntrinsicLawResponseCircuitDescent
end ResearchLean.AG.QualitySurface
