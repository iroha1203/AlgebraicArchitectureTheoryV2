import ResearchLean.AG.AtlasCoefficientFiber.CarrierChain
import ResearchLean.AG.AtlasCoefficientFiber.ChainHomologyDual
import ResearchLean.AG.AtlasCoefficientFiber.DualShortExact

/-!
# G-135 B：原carrier鎖filtrationの双対減少複体

## Implementation notes

F¹は原垂直辺・面への評価核、F²は原none面への評価核であり、
元cochainの部分空間として生成する。F⁰は同じ細複体、F³は零複体。
微分の保存は原鎖部分複体の微分制限から導く。任意のfiltrationや
期待homologyを受け取る案は原始構成の義務を移すため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じ細cochainから原垂直辺chainへの評価制限。 -/
def verticalRestriction1 : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C1 →ₗ[ℚ]
    Module.Dual ℚ (VerticalEdge M A →₀ ℚ) :=
  (verticalEdgeInclusion M A).dualMap.comp (freeDualEquiv _).toLinearMap

/-- 同じ細cochainから原垂直面chainへの評価制限。 -/
def verticalRestriction2 : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C2 →ₗ[ℚ]
    Module.Dual ℚ (VerticalFace M A →₀ ℚ) :=
  (verticalFaceInclusion M A).dualMap.comp (freeDualEquiv _).toLinearMap

/-- 辺制限の原chain評価。 -/
@[simp] theorem verticalRestriction1_apply
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C1)
    (x : VerticalEdge M A →₀ ℚ) :
    verticalRestriction1 M A z x = freeDualEquiv _ z (verticalEdgeInclusion M A x) := rfl

/-- 面制限の原chain評価。 -/
@[simp] theorem verticalRestriction2_apply
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C2)
    (x : VerticalFace M A →₀ ℚ) :
    verticalRestriction2 M A z x = freeDualEquiv _ z (verticalFaceInclusion M A x) := rfl

/-- F¹の1次はcarrier≤0辺空間の双対annihilatorそのもの。 -/
theorem verticalRestriction1_kernel_iff
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C1) :
    z ∈ LinearMap.ker (verticalRestriction1 M A) ↔
      ∀ x ∈ carrierChain1 M A 0, freeDualEquiv _ z x = 0 := by
  change verticalRestriction1 M A z = 0 ↔ ∀ x ∈ LinearMap.range (verticalEdgeInclusion M A), _
  constructor
  · intro hz x hx
    obtain ⟨x, rfl⟩ := hx
    exact LinearMap.congr_fun hz x
  · intro hz
    exact LinearMap.ext fun x => hz _ ⟨x, rfl⟩

/-- F¹の2次はcarrier≤0面空間の双対annihilatorそのもの。 -/
theorem verticalRestriction2_kernel_iff
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C2) :
    z ∈ LinearMap.ker (verticalRestriction2 M A) ↔
      ∀ x ∈ carrierChain2 M A 0, freeDualEquiv _ z x = 0 := by
  change verticalRestriction2 M A z = 0 ↔ ∀ x ∈ LinearMap.range (verticalFaceInclusion M A), _
  constructor
  · intro hz x hx
    obtain ⟨x, rfl⟩ := hx
    exact LinearMap.congr_fun hz x
  · intro hz
    exact LinearMap.ext fun x => hz _ ⟨x, rfl⟩

/-- F²の2次はcarrier≤1面空間の同じannihilator。 -/
theorem secondFiltration_kernel_iff
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C2) :
    z ∈ LinearMap.ker (restriction2 M A) ↔
      ∀ x ∈ carrierChain2 M A 1, freeDualEquiv _ z x = 0 := by
  change (degenerateL2 M A).dualRestrict (freeDualEquiv _ z) = 0 ↔ _
  exact dualRestriction_eq_zero_iff _ _

/-- 原carrier≤0が部分複体なので、F¹の辺annihilatorは微分で面annihilatorへ入る。 -/
theorem verticalRestriction_comm1
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C1) :
    verticalRestriction2 M A ((Nf.targetSubsetComplex _).d1 z) =
      (verticalBoundary M A).dualMap (verticalRestriction1 M A z) := by
  apply LinearMap.ext
  intro x
  rw [verticalRestriction2_apply, LinearMap.dualMap_apply, verticalRestriction1_apply]
  erw [← chainD2_dual]
  exact congrArg (freeDualEquiv _ z) (LinearMap.congr_fun (verticalBoundary_inclusion M A) x).symm

/-- 同じ原微分のF¹への実制限。 -/
def firstFiltrationDifferential : LinearMap.ker (verticalRestriction1 M A) →ₗ[ℚ]
    LinearMap.ker (verticalRestriction2 M A) :=
  ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1.comp
    (LinearMap.ker (verticalRestriction1 M A)).subtype).codRestrict _ (fun z => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, verticalRestriction_comm1]
      change (verticalBoundary M A).dualMap (verticalRestriction1 M A z.1) = 0
      rw [z.2, map_zero])

/-- F¹の微分は元細cochain微分と同じ値。 -/
@[simp] theorem firstFiltrationDifferential_val (z : LinearMap.ker (verticalRestriction1 M A)) :
    (firstFiltrationDifferential M A z).1 = (Nf.targetSubsetComplex _).d1 z.1 := rfl

/-- 原carrier≤0鎖filtrationの双対F¹。 -/
abbrev firstFiltrationComplex : ThreeCochainComplex ℚ where
  C0 := PUnit.{u+1}
  C1 := LinearMap.ker (verticalRestriction1 M A)
  C2 := LinearMap.ker (verticalRestriction2 M A)
  d0 := 0
  d1 := firstFiltrationDifferential M A
  d1_comp_d0 := by intro z; simp

/-- 原carrier≤1鎖filtrationの双対F²。 -/
abbrev secondFiltrationComplex : ThreeCochainComplex ℚ where
  C0 := PUnit.{u+1}
  C1 := PUnit.{u+1}
  C2 := LinearMap.ker (restriction2 M A)
  d0 := 0
  d1 := 0
  d1_comp_d0 := by intro z; simp

/-- 全原carrier≤2のannihilatorであるF³零複体。 -/
abbrev zeroFiltrationComplex : ThreeCochainComplex.{0,u} ℚ where
  C0 := PUnit.{u+1}
  C1 := PUnit.{u+1}
  C2 := PUnit.{u+1}
  d0 := 0
  d1 := 0
  d1_comp_d0 := by intro z; rfl

/-- F¹から同じ原F⁰への部分複体包含。 -/
def firstFiltrationInclusion : ThreeCochainComplex.Hom (firstFiltrationComplex M A)
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)) where
  f0 := 0
  f1 := (LinearMap.ker (verticalRestriction1 M A)).subtype
  f2 := (LinearMap.ker (verticalRestriction2 M A)).subtype
  comm0 := by intro z; simp
  comm1 := by intro z; rfl

/-- 全none面をannihilateする元は原垂直面もannihilateする。 -/
theorem secondFiltration_le_first (z : LinearMap.ker (restriction2 M A)) :
    z.1 ∈ LinearMap.ker (verticalRestriction2 M A) := by
  apply LinearMap.ext
  intro x
  have hx : verticalFaceInclusion M A x ∈ degenerateL2 M A :=
    verticalFaceInclusion_range_le_degenerate M A ⟨x, rfl⟩
  have he := LinearMap.congr_fun z.2 (⟨verticalFaceInclusion M A x, hx⟩ : degenerateL2 M A)
  exact he

/-- F²から原F¹への部分空間包含。 -/
def secondFiltrationInclusion : ThreeCochainComplex.Hom (secondFiltrationComplex M A)
    (firstFiltrationComplex M A) where
  f0 := LinearMap.id
  f1 := 0
  f2 := ((LinearMap.ker (restriction2 M A)).subtype).codRestrict _ (secondFiltration_le_first M A)
  comm0 := by intro z; rfl
  comm1 := by intro z; simp

/-- F²の0次包含は零加群の恒等射。 -/
@[simp] theorem secondFiltrationInclusion_f0 : (secondFiltrationInclusion M A).f0 = LinearMap.id := rfl

/-- F²の1次包含は零加群からの零射。 -/
@[simp] theorem secondFiltrationInclusion_f1 : (secondFiltrationInclusion M A).f1 = 0 := rfl

/-- F³からF²への零部分複体包含。 -/
def zeroFiltrationInclusion : ThreeCochainComplex.Hom zeroFiltrationComplex (secondFiltrationComplex M A) where
  f0 := 0
  f1 := 0
  f2 := 0
  comm0 := by intro z; rfl
  comm1 := by intro z; rfl

/-- F¹の0次包含は零加群からの零射。 -/
@[simp] theorem firstFiltrationInclusion_f0 : (firstFiltrationInclusion M A).f0 = 0 := rfl

/-- 三つの包含の成分は原部分空間包含または零加群からの射。 -/
@[simp] theorem firstFiltrationInclusion_f1 :
    (firstFiltrationInclusion M A).f1 = (LinearMap.ker (verticalRestriction1 M A)).subtype := rfl

/-- F¹の2次包含の所有API。 -/
@[simp] theorem firstFiltrationInclusion_f2 :
    (firstFiltrationInclusion M A).f2 = (LinearMap.ker (verticalRestriction2 M A)).subtype := rfl

/-- F²の2次包含は同じ元cochain値を保つ。 -/
@[simp] theorem secondFiltrationInclusion_f2_val (z : (secondFiltrationComplex M A).C2) :
    ((secondFiltrationInclusion M A).f2 z).1 = z.1 := rfl

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.verticalRestriction1
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRestriction2
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRestriction1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRestriction2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRestriction1_kernel_iff
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRestriction2_kernel_iff
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltration_kernel_iff
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRestriction_comm1
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiltrationDifferential
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiltrationDifferential_val
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiltrationComplex
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationComplex
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltrationComplex
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiltrationInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltration_le_first
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationInclusion_f0
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationInclusion_f1
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltrationInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiltrationInclusion_f0
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiltrationInclusion_f1
#print axioms AAT.AG.AtlasCoefficientFiber.firstFiltrationInclusion_f2
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationInclusion_f2_val
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
