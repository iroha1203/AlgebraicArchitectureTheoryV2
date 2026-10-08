import ResearchLean.AG.AtlasCoefficientFiber.ZeroFiltrationCone

/-!
# G-135 B：原native spectral objectの連結射

## Implementation notes

precompの連結射を同じ原包含のmapping-cone composition triangleへ戻す。
元triangleのδとspectral objectのδを別の定義として放置する案は採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition CategoryTheory.Triangulated
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原native spectral δは同じ包含composition triangleの第三射。 -/
theorem carrierSpectralObject_delta {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k) :
    (carrierSpectralObject M A).δ f g =
      (CochainComplex.mappingConeCompTriangleh
        ((filteredCarrierFunctor M A).map f) ((filteredCarrierFunctor M A).map g)).mor₃ := by
  simp [carrierSpectralObject, SpectralObject.δ, SpectralObject.precomp,
    HomotopyCategory.spectralObjectMappingCone, HomotopyCategory.composableArrowsFunctor,
    CochainComplex.mappingConeCompTriangleh, ComposableArrows.Precomp.map,
    ComposableArrows.Precomp.obj, CochainComplex.mappingCone.map_id]

/-- 原composition triangleの第三射は標準cone δの後の原inr。 -/
theorem carrierSpectralObject_delta_inr {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k) :
    (carrierSpectralObject M A).δ f g =
      (CochainComplex.mappingCone.triangleh ((filteredCarrierFunctor M A).map g)).mor₃ ≫
        ((HomotopyCategory.quotient (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)).map
          (CochainComplex.mappingCone.inr ((filteredCarrierFunctor M A).map f)))⟦(1 : ℤ)⟧' := by
  rw [carrierSpectralObject_delta]
  simp only [CochainComplex.mappingConeCompTriangleh, Functor.mapTriangle_obj,
    CochainComplex.mappingConeCompTriangle_mor₃, Pretriangulated.Triangle.mk_mor₃]
  simp only [Functor.map_comp, Category.assoc, CochainComplex.mappingConeCompTriangle_obj₁,
    CochainComplex.mappingCone.triangle_obj₁]
  rw [Functor.commShiftIso_hom_naturality]

/-- 原native spectral triangleのhomological δは同じ標準cone δを保存する。 -/
theorem carrierSpectralObject_homology_connecting {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k)
    (n m : ℤ) (hnm : n + 1 = m) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) 0).homologySequenceδ
      ((carrierSpectralObject M A).triangle f g) n m hnm =
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingCone.triangleh ((filteredCarrierFunctor M A).map g)) n m hnm ≫
      ((HomotopyCategory.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) 0).shift m).map
        ((HomotopyCategory.quotient (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)).map
          (CochainComplex.mappingCone.inr ((filteredCarrierFunctor M A).map f))) := by
  simp only [Functor.homologySequenceδ, SpectralObject.triangle_mor₃,
    carrierSpectralObject_delta_inr, Functor.shiftMap_comp]

/-- 原native spectral objectの各arrow対象は同じ原包含のcone。 -/
@[simp] theorem carrierSpectralObject_omega {i j : Fin 4} (f : i ⟶ j) :
    (carrierSpectralObject M A).ω₁.obj (ComposableArrows.mk₁ f) =
      (HomotopyCategory.quotient (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone ((filteredCarrierFunctor M A).map f)) := rfl

/-- 原零始点から任意filtration段へのinrは全次数で標準homology同型。 -/
instance carrierSpectralObject_inr_homology_isIso (j : Fin 4)
    (f : (0 : Fin 4) ⟶ j) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr ((filteredCarrierFunctor M A).map f)) n) := by
  haveI : QuasiIso (CochainComplex.mappingCone.inr ((filteredCarrierFunctor M A).map f)) :=
    zeroFiltration_inr_quasiIso ((filteredCarrierFunctor M A).map f)
  infer_instance

/-- 原native第零gradedのδは同じ実短完全列δへ対応する全次数式。 -/
theorem firstNativeConnecting_shortExact (n m : ℤ) (hnm : n + 1 = m) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) 0).homologySequenceδ
      ((carrierSpectralObject M A).triangle
        (homOfLE (show (0 : Fin 4) ≤ 2 by decide))
        (homOfLE (show (2 : Fin 4) ≤ 3 by decide))) n m hnm =
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) n).hom.app _ ≫
      HomologicalComplex.homologyMap (firstGradedConeDesc M A) n ≫
        (firstGraded_shortExact M A).δ n m hnm ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) m).inv.app _ ≫
        ((HomotopyCategory.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) 0).shift m).map
          ((HomotopyCategory.quotient (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)).map
            (CochainComplex.mappingCone.inr ((filteredCarrierFunctor M A).map
              (homOfLE (show (0 : Fin 4) ≤ 2 by decide))))) := by
  have hh := carrierSpectralObject_homology_connecting M A
    (homOfLE (show (0 : Fin 4) ≤ 2 by decide))
    (homOfLE (show (2 : Fin 4) ≤ 3 by decide)) n m hnm
  change _ =
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) 0).homologySequenceδ
      (CochainComplex.mappingCone.triangleh (zeroExtensionMap (firstFiltrationInclusion M A))) n m hnm ≫ _ at hh
  rw [firstGradedCone_connecting] at hh
  simpa only [Category.assoc] using hh

/-- 原native第一gradedのδも同じ実短完全列δへ対応する全次数式。 -/
theorem secondNativeConnecting_shortExact (n m : ℤ) (hnm : n + 1 = m) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) 0).homologySequenceδ
      ((carrierSpectralObject M A).triangle
        (homOfLE (show (0 : Fin 4) ≤ 1 by decide))
        (homOfLE (show (1 : Fin 4) ≤ 2 by decide))) n m hnm =
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) n).hom.app _ ≫
      HomologicalComplex.homologyMap (secondGradedConeDesc M A) n ≫
        (secondGraded_shortExact M A).δ n m hnm ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) m).inv.app _ ≫
        ((HomotopyCategory.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) 0).shift m).map
          ((HomotopyCategory.quotient (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)).map
            (CochainComplex.mappingCone.inr ((filteredCarrierFunctor M A).map
              (homOfLE (show (0 : Fin 4) ≤ 1 by decide))))) := by
  have hh := carrierSpectralObject_homology_connecting M A
    (homOfLE (show (0 : Fin 4) ≤ 1 by decide))
    (homOfLE (show (1 : Fin 4) ≤ 2 by decide)) n m hnm
  change _ =
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) 0).homologySequenceδ
      (CochainComplex.mappingCone.triangleh (zeroExtensionMap (secondFiltrationInclusion M A))) n m hnm ≫ _ at hh
  rw [secondGradedCone_connecting] at hh
  simpa only [Category.assoc] using hh

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.carrierSpectralObject_delta
#print axioms AAT.AG.AtlasCoefficientFiber.carrierSpectralObject_delta_inr
#print axioms AAT.AG.AtlasCoefficientFiber.carrierSpectralObject_homology_connecting
#print axioms AAT.AG.AtlasCoefficientFiber.carrierSpectralObject_omega
#print axioms AAT.AG.AtlasCoefficientFiber.carrierSpectralObject_inr_homology_isIso
#print axioms AAT.AG.AtlasCoefficientFiber.firstNativeConnecting_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.secondNativeConnecting_shortExact
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
