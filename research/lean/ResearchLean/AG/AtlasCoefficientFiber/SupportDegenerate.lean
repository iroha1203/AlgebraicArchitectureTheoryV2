import ResearchLean.AG.AtlasCoefficientFiber.SupportCells
import ResearchLean.AG.AtlasCoefficientFiber.DegenerateSubcomplex

/-!
# G-135 D：原細chainの台包含による退化部分複体の包含

## Implementation notes

none/someの原始分類はセル名のまま保持し、同じ自由chain包含をLへ制限する。
L₀の垂直辺像、L₁の混在面全微分、L₂の退化面をすべて保持する。
選択後のhomology同型を入力にする案は、混在面の実像の包含を証明しないため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 同じ原辺名の台包含は、原宣言noneの垂直辺を保つ。 -/
def supportVerticalEdgeInclude (e : VerticalEdge M A) : VerticalEdge M B :=
  ⟨supportCellInclude Nf.edgeSupport (fun _ ht => hab ht) e.1, e.2⟩

/-- 全三辺noneの垂直面も元の名前のまま含める。 -/
def supportVerticalFaceInclude (f : VerticalFace M A) : VerticalFace M B :=
  ⟨supportCellInclude Nf.faceSupport (fun _ ht => hab ht) f.1, f.2⟩

/-- 負符号辺someの混在面も同じOption像で含める。 -/
def supportMixedFaceInclude (f : MixedFace M A) : MixedFace M B :=
  ⟨supportCellInclude Nf.faceSupport (fun _ ht => hab ht) f.1, f.2⟩

/-- 元のfaceMap noneの退化面全部を含める。 -/
def supportDegenerateFaceInclude (f : DegenerateFace M A) : DegenerateFace M B :=
  ⟨supportCellInclude Nf.faceSupport (fun _ ht => hab ht) f.1, f.2⟩

/-- 垂直辺包含の元細辺は同じ支持セル包含。 -/
@[simp] theorem supportVerticalEdgeInclude_val (e : VerticalEdge M A) :
    (supportVerticalEdgeInclude M hab e).1 =
      supportCellInclude Nf.edgeSupport (fun _ ht => hab ht) e.1 := rfl
/-- 垂直面包含の元細面は同じ支持セル包含。 -/
@[simp] theorem supportVerticalFaceInclude_val (f : VerticalFace M A) :
    (supportVerticalFaceInclude M hab f).1 =
      supportCellInclude Nf.faceSupport (fun _ ht => hab ht) f.1 := rfl
/-- 混在面包含の元細面は同じ支持セル包含。 -/
@[simp] theorem supportMixedFaceInclude_val (f : MixedFace M A) :
    (supportMixedFaceInclude M hab f).1 =
      supportCellInclude Nf.faceSupport (fun _ ht => hab ht) f.1 := rfl
/-- 全退化面包含の元細面は同じ支持セル包含。 -/
@[simp] theorem supportDegenerateFaceInclude_val (f : DegenerateFace M A) :
    (supportDegenerateFaceInclude M hab f).1 =
      supportCellInclude Nf.faceSupport (fun _ ht => hab ht) f.1 := rfl

/-- 原VerticalEdge自由chainを同じ名前の線形延長で含める。 -/
def supportVerticalEdgeChainInclude : (VerticalEdge M A →₀ ℚ) →ₗ[ℚ] (VerticalEdge M B →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (supportVerticalEdgeInclude M hab)

/-- 原VerticalEdgechain包含の全基底値。 -/
@[simp] theorem supportVerticalEdgeChainInclude_single (x : VerticalEdge M A) (r : ℚ) :
    supportVerticalEdgeChainInclude M hab (Finsupp.single x r) =
      Finsupp.single (supportVerticalEdgeInclude M hab x) r := Finsupp.mapDomain_single

/-- 同じVerticalEdgechainの原細chainへの包含は支持包含と可換。 -/
theorem supportVerticalEdgeChainInclude_inclusion (x : VerticalEdge M A →₀ ℚ) :
    verticalEdgeInclusion M B (supportVerticalEdgeChainInclude M hab x) =
      selectedInclude Nf.edgeSupport (fun _ ht => hab ht) (verticalEdgeInclusion M A x) := by
  have hh : (verticalEdgeInclusion M B).comp (supportVerticalEdgeChainInclude M hab) =
      (selectedInclude Nf.edgeSupport (fun _ ht => hab ht)).comp (verticalEdgeInclusion M A) := by
    apply Finsupp.lhom_ext
    intro i r
    change verticalEdgeInclusion M B (supportVerticalEdgeChainInclude M hab (Finsupp.single i r)) =
      selectedInclude Nf.edgeSupport (fun _ ht => hab ht) (verticalEdgeInclusion M A (Finsupp.single i r))
    rw [supportVerticalEdgeChainInclude_single, verticalEdgeInclusion_single, verticalEdgeInclusion_single,
      supportChainInclude_single, supportVerticalEdgeInclude_val]
  exact LinearMap.congr_fun hh x

/-- 原VerticalFace自由chainを同じ名前の線形延長で含める。 -/
def supportVerticalFaceChainInclude : (VerticalFace M A →₀ ℚ) →ₗ[ℚ] (VerticalFace M B →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (supportVerticalFaceInclude M hab)

/-- 原VerticalFacechain包含の全基底値。 -/
@[simp] theorem supportVerticalFaceChainInclude_single (x : VerticalFace M A) (r : ℚ) :
    supportVerticalFaceChainInclude M hab (Finsupp.single x r) =
      Finsupp.single (supportVerticalFaceInclude M hab x) r := Finsupp.mapDomain_single

/-- 同じVerticalFacechainの原細chainへの包含は支持包含と可換。 -/
theorem supportVerticalFaceChainInclude_inclusion (x : VerticalFace M A →₀ ℚ) :
    verticalFaceInclusion M B (supportVerticalFaceChainInclude M hab x) =
      selectedInclude Nf.faceSupport (fun _ ht => hab ht) (verticalFaceInclusion M A x) := by
  have hh : (verticalFaceInclusion M B).comp (supportVerticalFaceChainInclude M hab) =
      (selectedInclude Nf.faceSupport (fun _ ht => hab ht)).comp (verticalFaceInclusion M A) := by
    apply Finsupp.lhom_ext
    intro i r
    change verticalFaceInclusion M B (supportVerticalFaceChainInclude M hab (Finsupp.single i r)) =
      selectedInclude Nf.faceSupport (fun _ ht => hab ht) (verticalFaceInclusion M A (Finsupp.single i r))
    rw [supportVerticalFaceChainInclude_single, verticalFaceInclusion_single, verticalFaceInclusion_single,
      supportChainInclude_single, supportVerticalFaceInclude_val]
  exact LinearMap.congr_fun hh x

/-- 原MixedFace自由chainを同じ名前の線形延長で含める。 -/
def supportMixedFaceChainInclude : (MixedFace M A →₀ ℚ) →ₗ[ℚ] (MixedFace M B →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (supportMixedFaceInclude M hab)

/-- 原MixedFacechain包含の全基底値。 -/
@[simp] theorem supportMixedFaceChainInclude_single (x : MixedFace M A) (r : ℚ) :
    supportMixedFaceChainInclude M hab (Finsupp.single x r) =
      Finsupp.single (supportMixedFaceInclude M hab x) r := Finsupp.mapDomain_single

/-- 同じMixedFacechainの原細chainへの包含は支持包含と可換。 -/
theorem supportMixedFaceChainInclude_inclusion (x : MixedFace M A →₀ ℚ) :
    mixedFaceInclusion M B (supportMixedFaceChainInclude M hab x) =
      selectedInclude Nf.faceSupport (fun _ ht => hab ht) (mixedFaceInclusion M A x) := by
  have hh : (mixedFaceInclusion M B).comp (supportMixedFaceChainInclude M hab) =
      (selectedInclude Nf.faceSupport (fun _ ht => hab ht)).comp (mixedFaceInclusion M A) := by
    apply Finsupp.lhom_ext
    intro i r
    change mixedFaceInclusion M B (supportMixedFaceChainInclude M hab (Finsupp.single i r)) =
      selectedInclude Nf.faceSupport (fun _ ht => hab ht) (mixedFaceInclusion M A (Finsupp.single i r))
    rw [supportMixedFaceChainInclude_single, mixedFaceInclusion_single, mixedFaceInclusion_single,
      supportChainInclude_single, supportMixedFaceInclude_val]
  exact LinearMap.congr_fun hh x

/-- 原DegenerateFace自由chainを同じ名前の線形延長で含める。 -/
def supportDegenerateFaceChainInclude : (DegenerateFace M A →₀ ℚ) →ₗ[ℚ] (DegenerateFace M B →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (supportDegenerateFaceInclude M hab)

/-- 原DegenerateFacechain包含の全基底値。 -/
@[simp] theorem supportDegenerateFaceChainInclude_single (x : DegenerateFace M A) (r : ℚ) :
    supportDegenerateFaceChainInclude M hab (Finsupp.single x r) =
      Finsupp.single (supportDegenerateFaceInclude M hab x) r := Finsupp.mapDomain_single

/-- 同じDegenerateFacechainの原細chainへの包含は支持包含と可換。 -/
theorem supportDegenerateFaceChainInclude_inclusion (x : DegenerateFace M A →₀ ℚ) :
    degenerateFaceInclusion M B (supportDegenerateFaceChainInclude M hab x) =
      selectedInclude Nf.faceSupport (fun _ ht => hab ht) (degenerateFaceInclusion M A x) := by
  have hh : (degenerateFaceInclusion M B).comp (supportDegenerateFaceChainInclude M hab) =
      (selectedInclude Nf.faceSupport (fun _ ht => hab ht)).comp (degenerateFaceInclusion M A) := by
    apply Finsupp.lhom_ext
    intro i r
    change degenerateFaceInclusion M B (supportDegenerateFaceChainInclude M hab (Finsupp.single i r)) =
      selectedInclude Nf.faceSupport (fun _ ht => hab ht) (degenerateFaceInclusion M A (Finsupp.single i r))
    rw [supportDegenerateFaceChainInclude_single, degenerateFaceInclusion_single, degenerateFaceInclusion_single,
      supportChainInclude_single, supportDegenerateFaceInclude_val]
  exact LinearMap.congr_fun hh x

/-- L₀の原垂直辺微分像は同じchain包含でL₀へ入る。 -/
theorem supportDegenerateL0_mem (x : K0 Nf (comparisonFactor qc qf h ⁻¹' A))
    (hx : x ∈ degenerateL0 M A) :
    selectedInclude Nf.chartSupport (fun _ ht => hab ht) x ∈ degenerateL0 M B := by
  obtain ⟨v, rfl⟩ := (mem_degenerateL0 M A x).mp hx
  apply (mem_degenerateL0 M B _).mpr
  refine ⟨supportVerticalEdgeChainInclude M hab v, ?_⟩
  rw [supportVerticalEdgeChainInclude_inclusion]
  exact (LinearMap.congr_fun (supportChainInclude_boundary1 Nf (fun _ ht => hab ht))
    (verticalEdgeInclusion M A v)).symm

/-- L₁の垂直辺と混在面の全微分は同じchain包含で保たれる。 -/
theorem supportDegenerateL1_mem (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A))
    (hx : x ∈ degenerateL1 M A) :
    selectedInclude Nf.edgeSupport (fun _ ht => hab ht) x ∈ degenerateL1 M B := by
  obtain ⟨v, m, rfl⟩ := (mem_degenerateL1 M A x).mp hx
  apply (mem_degenerateL1 M B _).mpr
  refine ⟨supportVerticalEdgeChainInclude M hab v, supportMixedFaceChainInclude M hab m, ?_⟩
  rw [supportVerticalEdgeChainInclude_inclusion, supportMixedFaceChainInclude_inclusion, map_add]
  congr 1
  exact (LinearMap.congr_fun (supportChainInclude_boundary2 Nf (fun _ ht => hab ht))
    (mixedFaceInclusion M A m)).symm

/-- L₂の全退化面像は同じ原chain包含でL₂へ入る。 -/
theorem supportDegenerateL2_mem (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A))
    (hx : x ∈ degenerateL2 M A) :
    selectedInclude Nf.faceSupport (fun _ ht => hab ht) x ∈ degenerateL2 M B := by
  obtain ⟨f, rfl⟩ := (mem_degenerateL2 M A x).mp hx
  exact (mem_degenerateL2 M B _).mpr
    ⟨supportDegenerateFaceChainInclude M hab f, supportDegenerateFaceChainInclude_inclusion M hab f⟩

/-- 原L₀の包含は同じ細chart自由chain包含の実制限。 -/
def supportL0Include : degenerateL0 M A →ₗ[ℚ] degenerateL0 M B :=
  (selectedInclude Nf.chartSupport (fun _ ht => hab ht)).restrict (supportDegenerateL0_mem M hab)
/-- 原L₁の包含は同じ細辺自由chain包含の実制限。 -/
def supportL1Include : degenerateL1 M A →ₗ[ℚ] degenerateL1 M B :=
  (selectedInclude Nf.edgeSupport (fun _ ht => hab ht)).restrict (supportDegenerateL1_mem M hab)
/-- 原L₂の包含は同じ細面自由chain包含の実制限。 -/
def supportL2Include : degenerateL2 M A →ₗ[ℚ] degenerateL2 M B :=
  (selectedInclude Nf.faceSupport (fun _ ht => hab ht)).restrict (supportDegenerateL2_mem M hab)

/-- L₀包含の原chart chain値。 -/
@[simp] theorem supportL0Include_val (x : degenerateL0 M A) :
    (supportL0Include M hab x).1 = selectedInclude Nf.chartSupport (fun _ ht => hab ht) x.1 := rfl
/-- L₁包含の原辺chain値。 -/
@[simp] theorem supportL1Include_val (x : degenerateL1 M A) :
    (supportL1Include M hab x).1 = selectedInclude Nf.edgeSupport (fun _ ht => hab ht) x.1 := rfl
/-- L₂包含の原面chain値。 -/
@[simp] theorem supportL2Include_val (x : degenerateL2 M A) :
    (supportL2Include M hab x).1 = selectedInclude Nf.faceSupport (fun _ ht => hab ht) x.1 := rfl

/-- 原Lの第一微分と制限は、元の細chainの全可換式に一致する。 -/
theorem supportLInclude_boundary1 (x : degenerateL1 M A) :
    supportL0Include M hab (degenerateBoundary1 M A x) =
      degenerateBoundary1 M B (supportL1Include M hab x) := by
  apply Subtype.ext
  simp only [supportL0Include_val, supportL1Include_val, degenerateBoundary1_val]
  exact LinearMap.congr_fun (supportChainInclude_boundary1 Nf (fun _ ht => hab ht)) x.1

/-- 原Lの第二微分も同じ符号・三辺出現を保持して可換。 -/
theorem supportLInclude_boundary2 (x : degenerateL2 M A) :
    supportL1Include M hab (degenerateBoundary2 M A x) =
      degenerateBoundary2 M B (supportL2Include M hab x) := by
  apply Subtype.ext
  simp only [supportL1Include_val, supportL2Include_val, degenerateBoundary2_val]
  exact LinearMap.congr_fun (supportChainInclude_boundary2 Nf (fun _ ht => hab ht)) x.1

/-- 原L0包含の恒等則は同じ細chain包含の恒等から従う。 -/
theorem supportL0Include_refl (A : Set qc.Target) :
    supportL0Include M (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [supportL0Include_val, selectedInclude_refl]
  rfl

/-- 原L0包含の合成則は同じ細chain包含の合成から従う。 -/
theorem supportL0Include_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportL0Include M hbc).comp (supportL0Include M hab) =
      supportL0Include M (hab.trans hbc) := by
  apply LinearMap.ext
  intro x
  change supportL0Include M hbc (supportL0Include M hab x) = _
  apply Subtype.ext
  rw [supportL0Include_val, supportL0Include_val, supportL0Include_val]
  exact (LinearMap.congr_fun (selectedInclude_comp Nf.chartSupport
    (fun _ ht => hab ht) (fun _ ht => hbc ht)) x.1).symm

/-- 原L1包含の恒等則は同じ細chain包含の恒等から従う。 -/
theorem supportL1Include_refl (A : Set qc.Target) :
    supportL1Include M (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [supportL1Include_val, selectedInclude_refl]
  rfl

/-- 原L1包含の合成則は同じ細chain包含の合成から従う。 -/
theorem supportL1Include_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportL1Include M hbc).comp (supportL1Include M hab) =
      supportL1Include M (hab.trans hbc) := by
  apply LinearMap.ext
  intro x
  change supportL1Include M hbc (supportL1Include M hab x) = _
  apply Subtype.ext
  rw [supportL1Include_val, supportL1Include_val, supportL1Include_val]
  exact (LinearMap.congr_fun (selectedInclude_comp Nf.edgeSupport
    (fun _ ht => hab ht) (fun _ ht => hbc ht)) x.1).symm

/-- 原L2包含の恒等則は同じ細chain包含の恒等から従う。 -/
theorem supportL2Include_refl (A : Set qc.Target) :
    supportL2Include M (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [supportL2Include_val, selectedInclude_refl]
  rfl

/-- 原L2包含の合成則は同じ細chain包含の合成から従う。 -/
theorem supportL2Include_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportL2Include M hbc).comp (supportL2Include M hab) =
      supportL2Include M (hab.trans hbc) := by
  apply LinearMap.ext
  intro x
  change supportL2Include M hbc (supportL2Include M hab x) = _
  apply Subtype.ext
  rw [supportL2Include_val, supportL2Include_val, supportL2Include_val]
  exact (LinearMap.congr_fun (selectedInclude_comp Nf.faceSupport
    (fun _ ht => hab ht) (fun _ ht => hbc ht)) x.1).symm

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalEdgeInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalFaceInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportMixedFaceInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateFaceInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalEdgeInclude_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalFaceInclude_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportMixedFaceInclude_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateFaceInclude_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalEdgeChainInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalEdgeChainInclude_single
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalEdgeChainInclude_inclusion
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalFaceChainInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalFaceChainInclude_single
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalFaceChainInclude_inclusion
#print axioms AAT.AG.AtlasCoefficientFiber.supportMixedFaceChainInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportMixedFaceChainInclude_single
#print axioms AAT.AG.AtlasCoefficientFiber.supportMixedFaceChainInclude_inclusion
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateFaceChainInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateFaceChainInclude_single
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateFaceChainInclude_inclusion
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateL0_mem
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateL1_mem
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateL2_mem
#print axioms AAT.AG.AtlasCoefficientFiber.supportL0Include
#print axioms AAT.AG.AtlasCoefficientFiber.supportL1Include
#print axioms AAT.AG.AtlasCoefficientFiber.supportL2Include
#print axioms AAT.AG.AtlasCoefficientFiber.supportL0Include.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportL0Include_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportL1Include.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportL1Include_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportL2Include.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportL2Include_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportLInclude_boundary1
#print axioms AAT.AG.AtlasCoefficientFiber.supportLInclude_boundary2
#print axioms AAT.AG.AtlasCoefficientFiber.supportL0Include_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportL0Include_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportL1Include_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportL1Include_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportL2Include_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportL2Include_comp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
