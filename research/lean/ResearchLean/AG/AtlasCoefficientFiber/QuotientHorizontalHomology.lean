import ResearchLean.AG.AtlasCoefficientFiber.RawBlocks
import ResearchLean.AG.AtlasCoefficientFiber.QuotientDual
import ResearchLean.AG.AtlasCoefficientFiber.QuotientChain
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# G-135 B：原K′/Lの水平座標

元のliteral quotientを、水平辺のB像商と水平面へ両方向に同定する。

## Implementation notes

係数射影と実Lの生成式から核を計算し、第一同型定理へ渡す。
水平空間を新たな商複体の定義に採る案は、指定K′/Lとの接続を残すため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 元mapped面係数の実射影。 -/
def horizontalFaceProjection : K2 Nf (comparisonFactor qc qf h ⁻¹' A) →ₗ[ℚ]
    (HorizontalFace M A →₀ ℚ) := cellProjection _

/-- mapped面の係数は同じ原セル値。 -/
@[simp] theorem horizontalFaceProjection_apply
    (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A)) (f : HorizontalFace M A) :
    horizontalFaceProjection M A x f = x f.1 := cellProjection_apply _ _ _

/-- 水平面包含への射影は恒等。 -/
@[simp] theorem horizontalFaceProjection_inclusion (x : HorizontalFace M A →₀ ℚ) :
    horizontalFaceProjection M A (horizontalFaceInclusion M A x) = x :=
  cellProjection_cellInclusion _ x

/-- 原退化面包含への水平射影は零。 -/
@[simp] theorem horizontalFaceProjection_degenerate (x : DegenerateFace M A →₀ ℚ) :
    horizontalFaceProjection M A (degenerateFaceInclusion M A x) = 0 := by
  ext f
  exact cellInclusion_apply_notmem _ x f.1 f.2

/-- 元の全細面は退化係数とmapped係数の和へ戻る。 -/
theorem face_recombination (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    degenerateFaceInclusion M A (cellProjection (fun f => M.faceMap f.1 = none) x) +
      horizontalFaceInclusion M A (horizontalFaceProjection M A x) = x :=
  cell_recombination _ x

/-- 全mapped面自由空間への射影は全射。 -/
theorem horizontalFaceProjection_surjective : Function.Surjective (horizontalFaceProjection M A) :=
  fun x => ⟨horizontalFaceInclusion M A x, horizontalFaceProjection_inclusion M A x⟩

/-- 原面射影の核は指定L₂そのもの。 -/
theorem horizontalFaceProjection_ker : LinearMap.ker (horizontalFaceProjection M A) =
    degenerateL2 M A := by
  ext x
  rw [LinearMap.mem_ker, mem_degenerateL2]
  constructor
  · intro hx
    refine ⟨cellProjection (fun f => M.faceMap f.1 = none) x, ?_⟩
    have hh := face_recombination M A x
    simpa only [hx, map_zero, add_zero] using hh
  · rintro ⟨y, rfl⟩
    exact horizontalFaceProjection_degenerate M A y

/-- 指定literal quotientの面空間と原mapped面の両方向同型。 -/
def quotientFaceEquiv : (K2 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL2 M A) ≃ₗ[ℚ]
    (HorizontalFace M A →₀ ℚ) :=
  (Submodule.quotEquivOfEq _ _ (horizontalFaceProjection_ker M A).symm).trans
    ((horizontalFaceProjection M A).quotKerEquivOfSurjective (horizontalFaceProjection_surjective M A))

/-- 指定面商の同定は元の水平係数を読む。 -/
@[simp] theorem quotientFaceEquiv_mk (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    quotientFaceEquiv M A (Submodule.Quotient.mk x) = horizontalFaceProjection M A x := rfl

/-- 逆同定は同じ原水平面の商類を返す。 -/
@[simp] theorem quotientFaceEquiv_symm_apply (x : HorizontalFace M A →₀ ℚ) :
    (quotientFaceEquiv M A).symm x = Submodule.Quotient.mk (horizontalFaceInclusion M A x) := by
  apply (quotientFaceEquiv M A).injective
  rw [LinearEquiv.apply_symm_apply, quotientFaceEquiv_mk, horizontalFaceProjection_inclusion]

/-- 原B像による水平辺商。 -/
abbrev HorizontalEdgeQuotient := (HorizontalEdge M A →₀ ℚ) ⧸ LinearMap.range (mixedHorizontalBoundary M A)

/-- 原Hを同じB像の商へ降ろしたHbar。 -/
def horizontalQuotientBoundary : (HorizontalFace M A →₀ ℚ) →ₗ[ℚ] HorizontalEdgeQuotient M A :=
  (LinearMap.range (mixedHorizontalBoundary M A)).mkQ.comp (horizontalFaceBoundary M A)

/-- Hbarの値は同じ原Hxの商類。 -/
@[simp] theorem horizontalQuotientBoundary_apply (x : HorizontalFace M A →₀ ℚ) :
    horizontalQuotientBoundary M A x = Submodule.Quotient.mk (horizontalFaceBoundary M A x) := rfl

/-- 原商二次閉路の水平表示。 -/
abbrev HorizontalFaceCycles := LinearMap.ker (horizontalQuotientBoundary M A)

/-- Hbar閉性は同じ原行列By=Hxを解けることと必要十分。 -/
theorem mem_horizontalFaceCycles_iff (x : HorizontalFace M A →₀ ℚ) :
    x ∈ HorizontalFaceCycles M A ↔ ∃ y : MixedFace M A →₀ ℚ,
      mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x := by
  rw [LinearMap.mem_ker, horizontalQuotientBoundary_apply, Submodule.Quotient.mk_eq_zero]
  rfl

/-- 元細辺を同じB像商へ射影する。 -/
def horizontalEdgeQuotientProjection : K1 Nf (comparisonFactor qc qf h ⁻¹' A) →ₗ[ℚ]
    HorizontalEdgeQuotient M A :=
  (LinearMap.range (mixedHorizontalBoundary M A)).mkQ.comp (horizontalEdgeProjection M A)

/-- 元細辺の射影は原水平係数のB像商類。 -/
@[simp] theorem horizontalEdgeQuotientProjection_apply
    (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    horizontalEdgeQuotientProjection M A x = Submodule.Quotient.mk (horizontalEdgeProjection M A x) := rfl

/-- 同じ水平辺商への射影は全射。 -/
theorem horizontalEdgeQuotientProjection_surjective :
    Function.Surjective (horizontalEdgeQuotientProjection M A) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    refine ⟨horizontalEdgeInclusion M A x, ?_⟩
    rw [horizontalEdgeQuotientProjection_apply, horizontalEdgeProjection_inclusion]

/-- 元細辺の水平商射影の核は、混在全微分を含む指定L₁そのもの。 -/
theorem horizontalEdgeQuotientProjection_ker :
    LinearMap.ker (horizontalEdgeQuotientProjection M A) = degenerateL1 M A := by
  ext x
  rw [LinearMap.mem_ker, horizontalEdgeQuotientProjection_apply,
    Submodule.Quotient.mk_eq_zero, mem_degenerateL1]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨verticalEdgeProjection M A x - mixedVerticalBoundary M A y, y, ?_⟩
    have hm := mixedBoundary_recombination M A y
    have hx := edgeBlock_recombination M A x
    calc
      _ = verticalEdgeInclusion M A (verticalEdgeProjection M A x) +
          horizontalEdgeInclusion M A (horizontalEdgeProjection M A x) := by
        rw [← hm, hy, map_sub]
        abel
      _ = x := hx
  · rintro ⟨v, m, rfl⟩
    refine ⟨m, ?_⟩
    rw [← mixedBoundary_recombination]
    simp only [map_add, horizontalEdgeProjection_vertical, horizontalEdgeProjection_inclusion, zero_add]

/-- 指定literal quotientの辺空間と原B像商の両方向同型。 -/
def quotientEdgeEquiv : (K1 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL1 M A) ≃ₗ[ℚ]
    HorizontalEdgeQuotient M A :=
  (Submodule.quotEquivOfEq _ _ (horizontalEdgeQuotientProjection_ker M A).symm).trans
    ((horizontalEdgeQuotientProjection M A).quotKerEquivOfSurjective
      (horizontalEdgeQuotientProjection_surjective M A))

/-- 指定辺商の同定は同じ水平係数のB像商類。 -/
@[simp] theorem quotientEdgeEquiv_mk (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    quotientEdgeEquiv M A (Submodule.Quotient.mk x) =
      horizontalEdgeQuotientProjection M A x := rfl

/-- 指定L₁の元は同じ水平B像商への射影で零になる。 -/
theorem horizontalEdgeQuotientProjection_degenerate (x : degenerateL1 M A) :
    horizontalEdgeQuotientProjection M A x.1 = 0 := by
  rw [← LinearMap.mem_ker, horizontalEdgeQuotientProjection_ker]
  exact x.2

/-- 指定L₂の原微分は同じ水平B像商で零になる。 -/
theorem horizontalEdgeQuotientProjection_boundary_degenerate (x : degenerateL2 M A) :
    horizontalEdgeQuotientProjection M A (chainD2 Nf _ x.1) = 0 := by
  exact horizontalEdgeQuotientProjection_degenerate M A (degenerateBoundary2 M A x)

/-- 原mapped面の微分を水平B像商へ読むと同じHbarになる。 -/
theorem horizontalEdgeQuotientProjection_boundary_horizontal (x : HorizontalFace M A →₀ ℚ) :
    horizontalEdgeQuotientProjection M A (chainD2 Nf _ (horizontalFaceInclusion M A x)) =
      horizontalQuotientBoundary M A x := by
  rw [horizontalEdgeQuotientProjection_apply, horizontalQuotientBoundary_apply]
  have he := LinearMap.congr_fun (horizontalFaceBoundary_inclusion M A) x
  simp only [LinearMap.comp_apply] at he
  rw [← he, horizontalEdgeProjection_inclusion]

/-- literal quotient第二微分は両座標同型の下で原Hbarそのもの。 -/
theorem quotientBoundary2_horizontal (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL2 M A) :
    quotientEdgeEquiv M A (quotientBoundary2 M A x) =
      horizontalQuotientBoundary M A (quotientFaceEquiv M A x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change quotientEdgeEquiv M A (quotientBoundary2 M A ((degenerateL2 M A).mkQ x)) = _
    rw [quotientBoundary2_mk]
    change quotientEdgeEquiv M A (Submodule.Quotient.mk (chainD2 Nf _ x)) = _
    rw [quotientEdgeEquiv_mk, quotientFaceEquiv_mk]
    have hx := face_recombination M A x
    let v : degenerateL2 M A := ⟨degenerateFaceInclusion M A
      (cellProjection (fun f => M.faceMap f.1 = none) x), ⟨_, rfl⟩⟩
    have hd := horizontalEdgeQuotientProjection_boundary_degenerate M A v
    calc
      _ = horizontalEdgeQuotientProjection M A (chainD2 Nf _ v.1) +
          horizontalEdgeQuotientProjection M A (chainD2 Nf _
            (horizontalFaceInclusion M A (horizontalFaceProjection M A x))) := by
        rw [← map_add, ← map_add]
        exact congrArg (fun t => horizontalEdgeQuotientProjection M A (chainD2 Nf _ t)) hx.symm
      _ = _ := by rw [hd, zero_add, horizontalEdgeQuotientProjection_boundary_horizontal]

/-- 元商chainの二次閉路。次数3は零なのでこの核がH₂を与える。 -/
abbrev QuotientSecondCycles := LinearMap.ker (quotientBoundary2 M A)

/-- 元K′/Lの二次閉路と原Hbarの核の同じ代表による両方向同定。 -/
def quotientSecondCyclesEquiv : QuotientSecondCycles M A ≃ₗ[ℚ] HorizontalFaceCycles M A where
  toFun x := ⟨quotientFaceEquiv M A x.1, by
    rw [LinearMap.mem_ker, ← quotientBoundary2_horizontal, x.2, map_zero]⟩
  invFun x := ⟨(quotientFaceEquiv M A).symm x.1, by
    rw [LinearMap.mem_ker]
    apply (quotientEdgeEquiv M A).injective
    rw [map_zero, quotientBoundary2_horizontal, LinearEquiv.apply_symm_apply]
    exact x.2⟩
  left_inv x := Subtype.ext ((quotientFaceEquiv M A).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((quotientFaceEquiv M A).apply_symm_apply x.1)
  map_add' x y := Subtype.ext ((quotientFaceEquiv M A).map_add x.1 y.1)
  map_smul' r x := Subtype.ext ((quotientFaceEquiv M A).map_smul r x.1)

/-- 二次閉路の両方向同定は元面商の水平係数を返す。 -/
@[simp] theorem quotientSecondCyclesEquiv_val (x : QuotientSecondCycles M A) :
    (quotientSecondCyclesEquiv M A x).1 = quotientFaceEquiv M A x.1 := rfl

/-- 閉路同型の逆方向も同じ次数2の原商同型で代表を戻す。 -/
@[simp] theorem quotientSecondCyclesEquiv_symm_val (x : HorizontalFaceCycles M A) :
    ((quotientSecondCyclesEquiv M A).symm x).1 = (quotientFaceEquiv M A).symm x.1 := by
  apply (quotientFaceEquiv M A).injective
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg Subtype.val ((quotientSecondCyclesEquiv M A).apply_symm_apply x)

/-- 元標準商chainの次数2短複体と同じ微分核を置く。 -/
def quotientSecondShort : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.moduleCatMk
    (0 : PUnit.{u+1} →ₗ[ℚ] (K2 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL2 M A))
    (quotientBoundary2 M A) (by simp)

/-- 標準商chainの次数2短複体を同じ零始域・原微分へ同定する。 -/
def quotientSecondScIso : (quotientChain M A).sc (2 : ℤ) ≅ quotientSecondShort M A :=
  (quotientChain M A).isoSc' (i := 3) (j := 2) (k := 1) (by simp) (by simp) ≪≫
    eqToIso (by rfl)

/-- 原商二次閉路は、同じ標準商chainのH₂に両方向同型。 -/
def quotientSecondStandardEquiv : QuotientSecondCycles M A ≃ₗ[ℚ]
    (quotientChain M A).homology (2 : ℤ) :=
  ((quotientSecondShort M A).moduleCatCyclesIso.symm ≪≫
    (quotientSecondShort M A).asIsoHomologyπ (by rfl) ≪≫
    (ShortComplex.homologyMapIso (quotientSecondScIso M A)).symm).toLinearEquiv

/-- 元の標準商chain H₂そのものを同じker Hbarへ両方向同定する。 -/
def quotientStandardH2HorizontalEquiv :
    (quotientChain M A).homology (2 : ℤ) ≃ₗ[ℚ] HorizontalFaceCycles M A :=
  (quotientSecondStandardEquiv M A).symm.trans (quotientSecondCyclesEquiv M A)

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.horizontalFaceProjection
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalFaceProjection_apply
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalFaceProjection_inclusion
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalFaceProjection_degenerate
#print axioms AAT.AG.AtlasCoefficientFiber.face_recombination
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalFaceProjection_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalFaceProjection_ker
#print axioms AAT.AG.AtlasCoefficientFiber.quotientFaceEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.quotientFaceEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.quotientFaceEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.HorizontalEdgeQuotient
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalQuotientBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalQuotientBoundary_apply
#print axioms AAT.AG.AtlasCoefficientFiber.HorizontalFaceCycles
#print axioms AAT.AG.AtlasCoefficientFiber.mem_horizontalFaceCycles_iff
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeQuotientProjection
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeQuotientProjection_apply
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeQuotientProjection_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeQuotientProjection_ker
#print axioms AAT.AG.AtlasCoefficientFiber.quotientEdgeEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.quotientEdgeEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeQuotientProjection_degenerate
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeQuotientProjection_boundary_degenerate
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdgeQuotientProjection_boundary_horizontal
#print axioms AAT.AG.AtlasCoefficientFiber.quotientBoundary2_horizontal
#print axioms AAT.AG.AtlasCoefficientFiber.QuotientSecondCycles
#print axioms AAT.AG.AtlasCoefficientFiber.quotientSecondCyclesEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.quotientSecondCyclesEquiv_val
#print axioms AAT.AG.AtlasCoefficientFiber.quotientSecondCyclesEquiv_symm_val
#print axioms AAT.AG.AtlasCoefficientFiber.quotientSecondShort
#print axioms AAT.AG.AtlasCoefficientFiber.quotientSecondScIso
#print axioms AAT.AG.AtlasCoefficientFiber.quotientSecondStandardEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.quotientStandardH2HorizontalEquiv
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
