import ResearchLean.AG.AtlasCoefficientFiber.SecondGradedComplex
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
# G-135 B：同じ原filtrationのnative spectral object

## Implementation notes

実包含F³→F²→F¹→F⁰をFin 4上の関手にし、標準mapping-cone spectral objectを
precompする。gradedへの射は同じ短完全列のdescShortComplexであり、擬同型性と
標準δの対応はその列の定理から得る。任意のspectral objectを入力として
受け取る案や、対象名だけをtransgressionとして扱う案は採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition CategoryTheory.Triangulated
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 三項零延長の単射性は元三成分の単射性から生成する。 -/
theorem zeroExtensionMap_mono_of_injective {C D : ThreeCochainComplex.{0,u} ℚ}
    (f : ThreeCochainComplex.Hom C D) (h0 : Function.Injective f.f0)
    (h1 : Function.Injective f.f1) (h2 : Function.Injective f.f2) : Mono (zeroExtensionMap f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  by_cases hn0 : n = 0
  · subst n
    exact h0
  · by_cases hn1 : n = 1
    · subst n
      exact h1
    · by_cases hn2 : n = 2
      · subst n
        exact h2
      · haveI : Subsingleton ((zeroExtension C).X n) :=
          ModuleCat.subsingleton_of_isZero (degreeObject_isZero C n hn0 hn1 hn2)
        intro x y _
        exact Subsingleton.elim x y

/-- 原F¹の標準包含は実部分空間包含なのでmono。 -/
instance firstFiltrationInclusion_standard_mono : Mono (zeroExtensionMap (firstFiltrationInclusion M A)) := by
  apply zeroExtensionMap_mono_of_injective
  · intro x y _
    exact Subsingleton.elim x y
  · exact Submodule.injective_subtype _
  · exact Submodule.injective_subtype _

/-- 原F²の標準包含も元cochain値を保つのでmono。 -/
instance secondFiltrationInclusion_standard_mono : Mono (zeroExtensionMap (secondFiltrationInclusion M A)) := by
  apply zeroExtensionMap_mono_of_injective
  · exact Function.injective_id
  · intro x y _
    exact Subsingleton.elim x y
  · exact secondFiltrationInclusion_f2_injective M A

/-- F³の標準包含は零加群からのmono。 -/
instance zeroFiltrationInclusion_standard_mono : Mono (zeroExtensionMap (zeroFiltrationInclusion M A)) := by
  apply zeroExtensionMap_mono_of_injective
  all_goals
    intro x y _
    exact Subsingleton.elim x y

/-- 同じ原減少filtrationを逆向きindexで読む実包含関手。 -/
def filteredCarrierFunctor : Fin 4 ⥤ CochainComplex (ModuleCat.{u} ℚ) ℤ :=
  ComposableArrows.mk₃ (zeroExtensionMap (zeroFiltrationInclusion M A))
    (zeroExtensionMap (secondFiltrationInclusion M A)) (zeroExtensionMap (firstFiltrationInclusion M A))

/-- 関手初段は原F³。 -/
@[simp] theorem filteredCarrierFunctor_obj_zero :
    (filteredCarrierFunctor M A).obj 0 = zeroExtension zeroFiltrationComplex := rfl

/-- 関手の1番は原F²。 -/
@[simp] theorem filteredCarrierFunctor_obj_one :
    (filteredCarrierFunctor M A).obj 1 = zeroExtension (secondFiltrationComplex M A) := rfl

/-- 関手の2番は原F¹。 -/
@[simp] theorem filteredCarrierFunctor_obj_two :
    (filteredCarrierFunctor M A).obj 2 = zeroExtension (firstFiltrationComplex M A) := rfl

/-- 関手終段は同じ原細cochain F⁰。 -/
@[simp] theorem filteredCarrierFunctor_obj_three :
    (filteredCarrierFunctor M A).obj 3 = zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)) := rfl

/-- 関手の0→1は原F³包含。 -/
@[simp] theorem filteredCarrierFunctor_map01 :
    (filteredCarrierFunctor M A).map (homOfLE (show (0 : Fin 4) ≤ 1 by decide)) =
      zeroExtensionMap (zeroFiltrationInclusion M A) := rfl

/-- 関手の1→2は原F²包含。 -/
@[simp] theorem filteredCarrierFunctor_map12 :
    (filteredCarrierFunctor M A).map (homOfLE (show (1 : Fin 4) ≤ 2 by decide)) =
      zeroExtensionMap (secondFiltrationInclusion M A) := rfl

/-- 関手の2→3は原F¹包含。 -/
@[simp] theorem filteredCarrierFunctor_map23 :
    (filteredCarrierFunctor M A).map (homOfLE (show (2 : Fin 4) ≤ 3 by decide)) =
      zeroExtensionMap (firstFiltrationInclusion M A) := rfl

/-- 原包含関手から独立生成するnative spectral object。 -/
def carrierSpectralObject : SpectralObject (HomotopyCategory (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)) (Fin 4) :=
  (HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} ℚ)).precomp (filteredCarrierFunctor M A)

/-- 生成native spectral objectの全composable index射に対する標準triangle。 -/
theorem carrierSpectralObject_triangle_distinguished {i j k : Fin 4} (f : i ⟶ j) (g : j ⟶ k) :
    (carrierSpectralObject M A).triangle f g ∈ distTriang
      (HomotopyCategory (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)) :=
  (carrierSpectralObject M A).triangle_distinguished f g

/-- 第一gradedへの同じ標準cone商評価。 -/
def firstGradedConeDesc : CochainComplex.mappingCone (zeroExtensionMap (firstFiltrationInclusion M A)) ⟶
    zeroExtension (firstGradedComplex M A) :=
  CochainComplex.mappingCone.descShortComplex (firstGradedShortComplex M A)

/-- 第一gradedへのcone評価は原短完全性から擬同型。 -/
instance firstGradedConeDesc_quasiIso : QuasiIso (firstGradedConeDesc M A) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex (firstGraded_shortExact M A)

/-- 第二gradedへの同じ標準cone商評価。 -/
def secondGradedConeDesc : CochainComplex.mappingCone (zeroExtensionMap (secondFiltrationInclusion M A)) ⟶
    zeroExtension (secondGradedComplex M A) :=
  CochainComplex.mappingCone.descShortComplex (secondGradedShortComplex M A)

/-- 第二gradedへのcone評価も原短完全性から擬同型。 -/
instance secondGradedConeDesc_quasiIso : QuasiIso (secondGradedConeDesc M A) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex (secondGraded_shortExact M A)

/-- 第一cone triangleの連結射と同じ原短完全列δの全次数対応。 -/
theorem firstGradedCone_connecting (n m : ℤ) (hnm : n + 1 = m) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) 0).homologySequenceδ
      (CochainComplex.mappingCone.triangleh (zeroExtensionMap (firstFiltrationInclusion M A))) n m hnm =
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) n).hom.app _ ≫
      HomologicalComplex.homologyMap (firstGradedConeDesc M A) n ≫
        (firstGraded_shortExact M A).δ n m hnm ≫
          (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) m).inv.app _ :=
  CochainComplex.mappingCone.homologySequenceδ_triangleh (firstGraded_shortExact M A) n m hnm

/-- 第二cone triangleの連結射と同じ原短完全列δの全次数対応。 -/
theorem secondGradedCone_connecting (n m : ℤ) (hnm : n + 1 = m) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) 0).homologySequenceδ
      (CochainComplex.mappingCone.triangleh (zeroExtensionMap (secondFiltrationInclusion M A))) n m hnm =
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) n).hom.app _ ≫
      HomologicalComplex.homologyMap (secondGradedConeDesc M A) n ≫
        (secondGraded_shortExact M A).δ n m hnm ≫
          (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) m).inv.app _ :=
  CochainComplex.mappingCone.homologySequenceδ_triangleh (secondGraded_shortExact M A) n m hnm

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.zeroExtensionMap_mono_of_injective
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiltrationInclusion_standard_mono
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationInclusion_standard_mono
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltrationInclusion_standard_mono
#print axioms AAT.AG.AtlasCoefficientFiber.filteredCarrierFunctor
#print axioms AAT.AG.AtlasCoefficientFiber.filteredCarrierFunctor_obj_zero
#print axioms AAT.AG.AtlasCoefficientFiber.filteredCarrierFunctor_obj_one
#print axioms AAT.AG.AtlasCoefficientFiber.filteredCarrierFunctor_obj_two
#print axioms AAT.AG.AtlasCoefficientFiber.filteredCarrierFunctor_obj_three
#print axioms AAT.AG.AtlasCoefficientFiber.filteredCarrierFunctor_map01
#print axioms AAT.AG.AtlasCoefficientFiber.filteredCarrierFunctor_map12
#print axioms AAT.AG.AtlasCoefficientFiber.filteredCarrierFunctor_map23
#print axioms AAT.AG.AtlasCoefficientFiber.carrierSpectralObject
#print axioms AAT.AG.AtlasCoefficientFiber.carrierSpectralObject_triangle_distinguished
#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedConeDesc
#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedConeDesc_quasiIso
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedConeDesc
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedConeDesc_quasiIso
#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedCone_connecting
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedCone_connecting
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
