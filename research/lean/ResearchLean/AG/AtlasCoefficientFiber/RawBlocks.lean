import ResearchLean.AG.AtlasCoefficientFiber.DegenerateSubcomplex
import Mathlib.LinearAlgebra.Finsupp.SumProd

/-!
# G-135 B §1：原支持chainのセル分類と二つの辺block

Optionのnoneとその補集合で元の名前付きセルを分割する。
射影は自由係数の実制限であり、期待するrankや完全性を入力にしない。

## Implementation notes

原基底の部分型へのlcomapDomainと包含を使い、二つの補集合への直積同型を作る。
面では既存の原始Fv/Fm分類も合成する。係数の像だけをblockとする案は
原セルの両方向分類を与えないため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u

/-- 自由部分基底の係数への射影。 -/
def cellProjection {I : Type u} (p : I → Prop) :
    (I →₀ ℚ) →ₗ[ℚ] ({i // p i} →₀ ℚ) :=
  Finsupp.lcomapDomain Subtype.val Subtype.val_injective

/-- 射影は同じセル名の係数を読む。 -/
@[simp] theorem cellProjection_apply {I : Type u} (p : I → Prop)
    (x : I →₀ ℚ) (i : {i // p i}) : cellProjection p x i = x i.1 := rfl

/-- 部分基底包含はその部分の各係数を保つ。 -/
@[simp] theorem cellInclusion_apply {I : Type u} (p : I → Prop)
    (x : {i // p i} →₀ ℚ) (i : {i // p i}) : cellInclusion p x i.1 = x i :=
  Finsupp.mapDomain_apply Subtype.val_injective x i

/-- 包含の像は選択外セルの係数を持たない。 -/
theorem cellInclusion_apply_notmem {I : Type u} (p : I → Prop)
    (x : {i // p i} →₀ ℚ) (i : I) (hi : ¬ p i) : cellInclusion p x i = 0 :=
  Finsupp.mapDomain_notin_range x i (by
    rintro ⟨j, rfl⟩
    exact hi j.2)

/-- 部分基底への射影と包含の合成は恒等。 -/
@[simp] theorem cellProjection_cellInclusion {I : Type u} (p : I → Prop)
    (x : {i // p i} →₀ ℚ) : cellProjection p (cellInclusion p x) = x := by
  ext i
  exact cellInclusion_apply p x i

/-- 相補的な部分基底の包含は、他方の射影で零になる。 -/
@[simp] theorem cellProjection_complementInclusion {I : Type u} (p : I → Prop)
    (x : {i // ¬ p i} →₀ ℚ) : cellProjection p (cellInclusion (fun i => ¬ p i) x) = 0 := by
  ext i
  exact cellInclusion_apply_notmem (fun i => ¬ p i) x i.1 (not_not.mpr i.2)

/-- none側とその補集合の係数から元のchainを復元する。 -/
theorem cell_recombination {I : Type u} (p : I → Prop) (x : I →₀ ℚ) :
    cellInclusion p (cellProjection p x) +
      cellInclusion (fun i => ¬ p i) (cellProjection (fun i => ¬ p i) x) = x := by
  classical
  ext i
  by_cases hi : p i
  · have hp := cellInclusion_apply p (cellProjection p x) ⟨i, hi⟩
    have hn := cellInclusion_apply_notmem (fun i => ¬ p i)
      (cellProjection (fun i => ¬ p i) x) i (not_not.mpr hi)
    simp only [Finsupp.add_apply, cellProjection_apply, hp, hn, add_zero]
  · have hp := cellInclusion_apply_notmem p (cellProjection p x) i hi
    have hn := cellInclusion_apply (fun i => ¬ p i)
      (cellProjection (fun i => ¬ p i) x) ⟨i, hi⟩
    simp only [Finsupp.add_apply, cellProjection_apply, hp, hn, zero_add]

/-- 以前の公開名を同じstatementの互換aliasとして保持する。 -/
theorem cellRecombination {I : Type u} (p : I → Prop) (x : I →₀ ℚ) :
    cellInclusion p (cellProjection p x) +
      cellInclusion (fun i => ¬ p i) (cellProjection (fun i => ¬ p i) x) = x :=
  cell_recombination p x

/-- 相補的な原始セル分類は元自由chainの両方向分解を与える。 -/
def cellDecomposition {I : Type u} (p : I → Prop) :
    (I →₀ ℚ) ≃ₗ[ℚ] ({i // p i} →₀ ℚ) × ({i // ¬ p i} →₀ ℚ) where
  toFun x := (cellProjection p x, cellProjection (fun i => ¬ p i) x)
  invFun x := cellInclusion p x.1 + cellInclusion (fun i => ¬ p i) x.2
  left_inv x := cellRecombination p x
  right_inv x := by
    apply Prod.ext
    · simp only [map_add, cellProjection_cellInclusion,
        cellProjection_complementInclusion, add_zero]
    · ext i
      simp only [map_add, Finsupp.add_apply, cellProjection_apply, cellInclusion_apply]
      rw [cellInclusion_apply_notmem p x.1 i.1 i.2, zero_add]
  map_add' x y := by simp only [map_add, Prod.mk_add_mk]
  map_smul' r x := by simp only [map_smul, Prod.smul_mk, RingHom.id_apply]

/-- 分解の垂直座標は実係数射影。 -/
@[simp] theorem cellDecomposition_fst {I : Type u} (p : I → Prop) (x : I →₀ ℚ) :
    (cellDecomposition p x).1 = cellProjection p x := rfl

/-- 分解の水平座標は相補部分への実係数射影。 -/
@[simp] theorem cellDecomposition_snd {I : Type u} (p : I → Prop) (x : I →₀ ℚ) :
    (cellDecomposition p x).2 = cellProjection (fun i => ¬ p i) x := rfl

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- E_hは元の選択細辺のmapped像。粗loopもここに保持する。 -/
abbrev HorizontalEdge :=
  {e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) // ¬ M.edgeMap e.1 = none}

/-- F_hは元の選択細面のmapped像。 -/
abbrev HorizontalFace :=
  {f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) // ¬ M.faceMap f.1 = none}

/-- 元K′₁の垂直・水平セルによる両方向分解。 -/
def edgeBlockEquiv : K1 Nf (comparisonFactor qc qf h ⁻¹' A) ≃ₗ[ℚ]
    (VerticalEdge M A →₀ ℚ) × (HorizontalEdge M A →₀ ℚ) := cellDecomposition _

/-- 垂直辺blockへの実係数射影。 -/
def verticalEdgeProjection : K1 Nf (comparisonFactor qc qf h ⁻¹' A) →ₗ[ℚ]
    (VerticalEdge M A →₀ ℚ) := cellProjection _

/-- 水平辺blockへの実係数射影。 -/
def horizontalEdgeProjection : K1 Nf (comparisonFactor qc qf h ⁻¹' A) →ₗ[ℚ]
    (HorizontalEdge M A →₀ ℚ) := cellProjection _

/-- 水平辺の元K′₁への包含。 -/
def horizontalEdgeInclusion : (HorizontalEdge M A →₀ ℚ) →ₗ[ℚ]
    K1 Nf (comparisonFactor qc qf h ⁻¹' A) := cellInclusion _

/-- 水平面の元K′₂への包含。 -/
def horizontalFaceInclusion : (HorizontalFace M A →₀ ℚ) →ₗ[ℚ]
    K2 Nf (comparisonFactor qc qf h ⁻¹' A) := cellInclusion _

/-- 指定aは原第一微分の垂直辺への制限。 -/
def verticalEdgeBoundary : (VerticalEdge M A →₀ ℚ) →ₗ[ℚ]
    K0 Nf (comparisonFactor qc qf h ⁻¹' A) :=
  (chainD1 Nf _).comp (verticalEdgeInclusion M A)

/-- 原支持微分を通すaの値を返す所有API。 -/
theorem verticalEdgeBoundary_apply (x : VerticalEdge M A →₀ ℚ) :
    verticalEdgeBoundary M A x = chainD1 Nf _ (verticalEdgeInclusion M A x) := rfl

/-- aの各列は同じ原細辺の右端点と左端点の差。 -/
@[simp] theorem verticalEdgeBoundary_single (e : VerticalEdge M A) (r : ℚ) :
    verticalEdgeBoundary M A (Finsupp.single e r) = r •
      (Finsupp.single (Nf.targetSubsetEdgeRight _ e.1) 1 -
        Finsupp.single (Nf.targetSubsetEdgeLeft _ e.1) 1) := by
  rw [verticalEdgeBoundary_apply, verticalEdgeInclusion_single, chainD1_single]

/-- 指定bは原第一微分の水平辺への制限。 -/
def horizontalEdgeBoundary : (HorizontalEdge M A →₀ ℚ) →ₗ[ℚ]
    K0 Nf (comparisonFactor qc qf h ⁻¹' A) :=
  (chainD1 Nf _).comp (horizontalEdgeInclusion M A)

/-- 指定Dは混在面の元微分の垂直成分。 -/
def mixedVerticalBoundary : (MixedFace M A →₀ ℚ) →ₗ[ℚ] (VerticalEdge M A →₀ ℚ) :=
  (verticalEdgeProjection M A).comp ((chainD2 Nf _).comp (mixedFaceInclusion M A))

/-- 指定Bは混在面の元微分の水平成分。後で同じΓ incidenceへ同定する。 -/
def mixedHorizontalBoundary : (MixedFace M A →₀ ℚ) →ₗ[ℚ] (HorizontalEdge M A →₀ ℚ) :=
  (horizontalEdgeProjection M A).comp ((chainD2 Nf _).comp (mixedFaceInclusion M A))

/-- 原支持微分と水平射影を通すBの値を返す所有API。 -/
theorem mixedHorizontalBoundary_apply (x : MixedFace M A →₀ ℚ) :
    mixedHorizontalBoundary M A x =
      horizontalEdgeProjection M A (chainD2 Nf _ (mixedFaceInclusion M A x)) := rfl

/-- 指定Hはmapped面の元微分の水平成分。 -/
def horizontalFaceBoundary : (HorizontalFace M A →₀ ℚ) →ₗ[ℚ] (HorizontalEdge M A →₀ ℚ) :=
  (horizontalEdgeProjection M A).comp ((chainD2 Nf _).comp (horizontalFaceInclusion M A))

/-- 垂直包含を垂直座標へ戻す所有API。 -/
@[simp] theorem verticalEdgeProjection_inclusion (x : VerticalEdge M A →₀ ℚ) :
    verticalEdgeProjection M A (verticalEdgeInclusion M A x) = x :=
  cellProjection_cellInclusion _ x

/-- 水平包含の垂直座標は零。 -/
@[simp] theorem verticalEdgeProjection_horizontal (x : HorizontalEdge M A →₀ ℚ) :
    verticalEdgeProjection M A (horizontalEdgeInclusion M A x) = 0 :=
  cellProjection_complementInclusion _ x

/-- 水平包含を水平座標へ戻す所有API。 -/
@[simp] theorem horizontalEdgeProjection_inclusion (x : HorizontalEdge M A →₀ ℚ) :
    horizontalEdgeProjection M A (horizontalEdgeInclusion M A x) = x :=
  cellProjection_cellInclusion _ x

/-- 垂直包含の水平座標は零。 -/
@[simp] theorem horizontalEdgeProjection_vertical (x : VerticalEdge M A →₀ ℚ) :
    horizontalEdgeProjection M A (verticalEdgeInclusion M A x) = 0 := by
  ext i
  exact cellInclusion_apply_notmem _ x i.1 i.2

/-- 原K′₁の二blockの和は、同じchainそのもの。 -/
theorem edgeBlock_recombination (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    verticalEdgeInclusion M A (verticalEdgeProjection M A x) +
      horizontalEdgeInclusion M A (horizontalEdgeProjection M A x) = x :=
  cellRecombination _ x

/-- 混在面微分の実二blockを足すと原支持微分を復元する。 -/
theorem mixedBoundary_recombination (x : MixedFace M A →₀ ℚ) :
    verticalEdgeInclusion M A (mixedVerticalBoundary M A x) +
      horizontalEdgeInclusion M A (mixedHorizontalBoundary M A x) =
    chainD2 Nf (comparisonFactor qc qf h ⁻¹' A) (mixedFaceInclusion M A x) :=
  edgeBlock_recombination M A _

/-- Vの像のa微分は、元のsquare-zeroから零。 -/
theorem verticalEdgeBoundary_comp_verticalBoundary :
    (verticalEdgeBoundary M A).comp (verticalBoundary M A) = 0 := by
  rw [verticalEdgeBoundary, LinearMap.comp_assoc, verticalBoundary_inclusion,
    ← LinearMap.comp_assoc, chainD1_comp_chainD2, LinearMap.zero_comp]

/-- 同じ混在面の実微分からaD+bB=0を導く。 -/
theorem mixedBoundary_square :
    (verticalEdgeBoundary M A).comp (mixedVerticalBoundary M A) +
      (horizontalEdgeBoundary M A).comp (mixedHorizontalBoundary M A) = 0 := by
  apply LinearMap.ext
  intro x
  change chainD1 Nf _ (verticalEdgeInclusion M A (mixedVerticalBoundary M A x)) +
    chainD1 Nf _ (horizontalEdgeInclusion M A (mixedHorizontalBoundary M A x)) = 0
  rw [← map_add, mixedBoundary_recombination]
  exact LinearMap.congr_fun (chainD1_comp_chainD2 Nf _) _

/-- mapped面の全三辺出現は水平辺に属する。 -/
theorem horizontalFace_edge_mapped (f : HorizontalFace M A) (i : Fin 3) :
    ¬ M.edgeMap (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i).1 = none := by
  cases hf : M.faceMap f.1.1 with
  | none => exact False.elim (f.2 hf)
  | some F =>
    fin_cases i
    · change ¬ M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = none
      rw [M.face_some_edge0 f.1.1 F hf]
      exact Option.some_ne_none _
    · change ¬ M.edgeMap (Nf.nerve.faceEdge1 f.1.1) = none
      rw [M.face_some_edge1 f.1.1 F hf]
      exact Option.some_ne_none _
    · change ¬ M.edgeMap (Nf.nerve.faceEdge2 f.1.1) = none
      rw [M.face_some_edge2 f.1.1 F hf]
      exact Option.some_ne_none _

/-- mapped面微分の垂直成分は原始face_some incidenceから零。 -/
theorem horizontalFace_vertical_zero :
    (verticalEdgeProjection M A).comp
      ((chainD2 Nf _).comp (horizontalFaceInclusion M A)) = 0 := by
  apply Finsupp.lhom_ext
  intro f r
  simp only [LinearMap.comp_apply, horizontalFaceInclusion, cellInclusion_single,
    chainD2_single, map_smul, map_add, map_sub, LinearMap.zero_apply]
  have hz (i : Fin 3) : verticalEdgeProjection M A (Finsupp.single (faceEdge Nf _ f.1 i) 1) = 0 := by
    ext e
    change Finsupp.single (faceEdge Nf _ f.1 i) (1 : ℚ) e.1 = 0
    apply Finsupp.single_eq_of_ne
    intro he
    have hh := horizontalFace_edge_mapped M A f i
    exact hh (he ▸ e.2)
  change r • ((verticalEdgeProjection M A) (Finsupp.single (faceEdge Nf _ f.1 0) 1) -
    (verticalEdgeProjection M A) (Finsupp.single (faceEdge Nf _ f.1 1) 1) +
    (verticalEdgeProjection M A) (Finsupp.single (faceEdge Nf _ f.1 2) 1)) = 0
  rw [hz 0, hz 1, hz 2]
  simp

/-- 原mapped面微分は水平Hの包含と一致する。 -/
theorem horizontalFaceBoundary_inclusion :
    (horizontalEdgeInclusion M A).comp (horizontalFaceBoundary M A) =
      (chainD2 Nf _).comp (horizontalFaceInclusion M A) := by
  apply LinearMap.ext
  intro x
  have hr := edgeBlock_recombination M A
    (chainD2 Nf _ (horizontalFaceInclusion M A x))
  have hz := LinearMap.congr_fun (horizontalFace_vertical_zero M A) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  rw [hz, map_zero, zero_add] at hr
  exact hr

/-- bH=0も同じ原支持chainのsquare-zeroによる。 -/
theorem horizontalEdgeBoundary_comp_horizontalFaceBoundary :
    (horizontalEdgeBoundary M A).comp (horizontalFaceBoundary M A) = 0 := by
  rw [horizontalEdgeBoundary, LinearMap.comp_assoc, horizontalFaceBoundary_inclusion,
    ← LinearMap.comp_assoc, chainD1_comp_chainD2, LinearMap.zero_comp]

/-- 水平射影はmapped辺の元基底係数をそのまま保つ。 -/
@[simp] theorem horizontalEdgeProjection_single (e : HorizontalEdge M A) (r : ℚ) :
    horizontalEdgeProjection M A (Finsupp.single e.1 r) = Finsupp.single e r := by
  classical
  ext w
  change Finsupp.single e.1 r w.1 = Finsupp.single e r w
  simp only [Finsupp.single_apply, Subtype.ext_iff]

/-- 水平射影は原垂直辺の基底を零に送る。 -/
@[simp] theorem horizontalEdgeProjection_vertical_single (e : VerticalEdge M A) (r : ℚ) :
    horizontalEdgeProjection M A (Finsupp.single e.1 r) = 0 := by
  simpa only [verticalEdgeInclusion_single] using
    horizontalEdgeProjection_vertical M A (Finsupp.single e r)

/-- 退化面の非交和分類を同じ自由基底の両方向線形分解へ移す。 -/
def degenerateFaceSplitEquiv : (DegenerateFace M A →₀ ℚ) ≃ₗ[ℚ]
    (VerticalFace M A →₀ ℚ) × (MixedFace M A →₀ ℚ) :=
  (Finsupp.domLCongr (degenerateFaceEquiv M A)).trans
    (Finsupp.sumFinsuppLEquivProdFinsupp ℚ)

/-- 原K′₂の三つの原始セルclassによる両方向分解。 -/
def faceBlockEquiv : K2 Nf (comparisonFactor qc qf h ⁻¹' A) ≃ₗ[ℚ]
    ((VerticalFace M A →₀ ℚ) × (MixedFace M A →₀ ℚ)) × (HorizontalFace M A →₀ ℚ) :=
  (cellDecomposition (fun f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) =>
    M.faceMap f.1 = none)).trans
      (LinearEquiv.prodCongr (degenerateFaceSplitEquiv M A) (LinearEquiv.refl _ _))

/-- 三面blockの垂直係数は、元の同じ細面の係数。 -/
@[simp] theorem faceBlockEquiv_vertical (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A))
    (f : VerticalFace M A) : (faceBlockEquiv M A x).1.1 f = x f.1 := by
  simp [faceBlockEquiv, degenerateFaceSplitEquiv, Finsupp.domCongr_apply,
    cellProjection_apply,
    cellDecomposition_fst]

/-- 三面blockの混在係数は、元の同じ細面の係数。 -/
@[simp] theorem faceBlockEquiv_mixed (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A))
    (f : MixedFace M A) : (faceBlockEquiv M A x).1.2 f = x f.1 := by
  simp [faceBlockEquiv, degenerateFaceSplitEquiv, Finsupp.domCongr_apply,
    cellProjection_apply,
    cellDecomposition_fst]

/-- 三面blockのmapped係数は、元の同じ細面の係数。 -/
@[simp] theorem faceBlockEquiv_horizontal (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A))
    (f : HorizontalFace M A) : (faceBlockEquiv M A x).2 f = x f.1 := rfl

attribute [deprecated cell_recombination (since := "2026-10-08")] cellRecombination

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.cellProjection
#print axioms AAT.AG.AtlasCoefficientFiber.cellProjection_apply
#print axioms AAT.AG.AtlasCoefficientFiber.cellInclusion_apply
#print axioms AAT.AG.AtlasCoefficientFiber.cellInclusion_apply_notmem
#print axioms AAT.AG.AtlasCoefficientFiber.cellProjection_cellInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.cellProjection_complementInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.cell_recombination
#print axioms AAT.AG.AtlasCoefficientFiber.cellRecombination
#print axioms AAT.AG.AtlasCoefficientFiber.cellDecomposition
#print axioms AAT.AG.AtlasCoefficientFiber.cellDecomposition_fst
#print axioms AAT.AG.AtlasCoefficientFiber.cellDecomposition_snd
#print axioms AAT.AG.AtlasCoefficientFiber.HorizontalEdge
#print axioms AAT.AG.AtlasCoefficientFiber.HorizontalFace
#print axioms AAT.AG.AtlasCoefficientFiber.edgeBlockEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdgeProjection
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeProjection
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalFaceInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdgeBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdgeBoundary_apply
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdgeBoundary_single
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.mixedVerticalBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.mixedHorizontalBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.mixedHorizontalBoundary_apply
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalFaceBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdgeProjection_inclusion
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdgeProjection_horizontal
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeProjection_inclusion
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeProjection_vertical
#print axioms AAT.AG.AtlasCoefficientFiber.edgeBlock_recombination
#print axioms AAT.AG.AtlasCoefficientFiber.mixedBoundary_recombination
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdgeBoundary_comp_verticalBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.mixedBoundary_square
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalFace_edge_mapped
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalFace_vertical_zero
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalFaceBoundary_inclusion
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeBoundary_comp_horizontalFaceBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeProjection_single
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeProjection_vertical_single
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateFaceSplitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.faceBlockEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.faceBlockEquiv_vertical
#print axioms AAT.AG.AtlasCoefficientFiber.faceBlockEquiv_mixed
#print axioms AAT.AG.AtlasCoefficientFiber.faceBlockEquiv_horizontal

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
