import ResearchLean.AG.AtlasCoefficientFiber.Kappa
import ResearchLean.AG.AtlasCoefficientFiber.DegenerateChain
import ResearchLean.AG.AtlasCoefficientFiber.ChainHomologyDual

/-!
# G-135 B §1：実Lの一次homologyと混在関係の商

指定された原支持部分複体Lの閉路・微分像を使う。
垂直包含による商写像は全射であり、その核はVとD(ker B)の和である。

## Implementation notes

指定Lの微分で作るker/range商と標準ShortComplex homologyの同定を使う。
垂直包含の核計算では元L₂をFv/Fmへ分解する。Lを垂直fiberだけへ置き換える案は
混在面の関係を失うため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じLの一次閉路。 -/
abbrev degenerateCycles : Submodule ℚ (degenerateL1 M A) := LinearMap.ker (degenerateBoundary1 M A)

/-- 同じLの第二微分を一次閉路へ制限する。 -/
abbrev degenerateBoundaryToCycles : degenerateL2 M A →ₗ[ℚ] degenerateCycles M A :=
  chainBoundaryToCycles (degenerateBoundary1 M A) (degenerateBoundary2 M A)
    (degenerateBoundary_square M A)

/-- 元のK′上で読むと、同じ原支持第二微分。 -/
@[simp] theorem degenerateBoundaryToCycles_val (x : degenerateL2 M A) :
    (degenerateBoundaryToCycles M A x).1.1 = chainD2 Nf _ x.1 := rfl

/-- 実Lの閉路を実Lの微分像で割った一次homology。 -/
abbrev DegenerateHomology : Type u :=
  ChainFirstHomology (degenerateBoundary1 M A) (degenerateBoundary2 M A)
    (degenerateBoundary_square M A)

/-- 垂直閉路は実L₁の閉路として包含される。 -/
def verticalCycleInclusion : verticalCycles M A →ₗ[ℚ] degenerateCycles M A :=
  { toFun := fun z => ⟨⟨verticalEdgeInclusion M A z.1,
      verticalEdge_range_le_L1 M A ⟨z.1, rfl⟩⟩, by
      apply Subtype.ext
      exact z.2⟩
    map_add' := fun x y => by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
    map_smul' := fun r x => by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _ }

/-- 垂直閉路の包含は元の同じ名前付き辺包含。 -/
@[simp] theorem verticalCycleInclusion_val (z : verticalCycles M A) :
    (verticalCycleInclusion M A z).1.1 = verticalEdgeInclusion M A z.1 := rfl

/-- 垂直閉路から実L一次homologyへの指定写像。 -/
def verticalCycleHomologyMap : verticalCycles M A →ₗ[ℚ] DegenerateHomology M A where
  toFun z := Submodule.Quotient.mk (verticalCycleInclusion M A z)
  map_add' x y := by rw [map_add]; rfl
  map_smul' r x := by rw [map_smul]; rfl

/-- 代表式は垂直包含の実L類。 -/
@[simp] theorem verticalCycleHomologyMap_apply (z : verticalCycles M A) :
    verticalCycleHomologyMap M A z = Submodule.Quotient.mk (verticalCycleInclusion M A z) := rfl

/-- 実Lの任意の一次閉路は、垂直閉路と混在面の微分の和である。 -/
theorem degenerateCycle_vertical_representative (z : degenerateCycles M A) :
    ∃ (v : verticalCycles M A) (m : degenerateL2 M A),
      verticalCycleInclusion M A v + degenerateBoundaryToCycles M A m = z := by
  obtain ⟨v, m, hm⟩ := (mem_degenerateL1 M A z.1.1).mp z.1.2
  have hv : verticalEdgeBoundary M A v = 0 := by
    have hz := congrArg Subtype.val z.2
    rw [degenerateBoundary1_val] at hz
    rw [← hm, map_add] at hz
    have hs := LinearMap.congr_fun (chainD1_comp_chainD2 Nf _) (mixedFaceInclusion M A m)
    change chainD1 Nf _ (chainD2 Nf _ (mixedFaceInclusion M A m)) = 0 at hs
    rw [hs, add_zero] at hz
    exact hz
  refine ⟨⟨v, hv⟩, ⟨mixedFaceInclusion M A m,
    mixedFaceInclusion_range_le_degenerate M A ⟨m, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hm

/-- 垂直包含は実Lの一次homologyを全て生成する。 -/
theorem verticalCycleHomologyMap_surjective : Function.Surjective (verticalCycleHomologyMap M A) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    obtain ⟨v, m, hm⟩ := degenerateCycle_vertical_representative M A z
    refine ⟨v, ?_⟩
    rw [verticalCycleHomologyMap_apply, ← hm, Submodule.Quotient.mk_add]
    have hz : Submodule.Quotient.mk (degenerateBoundaryToCycles M A m) =
        (0 : DegenerateHomology M A) :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨m, rfl⟩
    rw [hz, add_zero]

/-- 実L₂の微分を垂直閉路の代表へ照合すると、水平成分がker Bを強制する。 -/
theorem verticalCycleHomologyMap_ker :
    LinearMap.ker (verticalCycleHomologyMap M A) = verticalRelations M A := by
  ext z
  rw [LinearMap.mem_ker, verticalCycleHomologyMap_apply, Submodule.Quotient.mk_eq_zero,
    mem_verticalRelations]
  constructor
  · rintro ⟨f, hf⟩
    have hfv := congrArg (fun w : degenerateCycles M A => w.1.1) hf
    have hmem : f.1 ∈ LinearMap.range (verticalFaceInclusion M A) ⊔
        LinearMap.range (mixedFaceInclusion M A) := by
      rw [← degenerateL2_vertical_mixed]
      exact f.2
    obtain ⟨t, ⟨v, hv⟩, s, ⟨m, hm⟩, he⟩ := Submodule.mem_sup.mp hmem
    have he' : verticalFaceInclusion M A v + mixedFaceInclusion M A m = f.1 := by
      simpa only [← hv, ← hm] using he
    change (degenerateBoundaryToCycles M A f).1.1 = (verticalCycleInclusion M A z).1.1 at hfv
    rw [degenerateBoundaryToCycles_val, verticalCycleInclusion_val] at hfv
    rw [← he', map_add, ← LinearMap.comp_apply (chainD2 Nf _) (verticalFaceInclusion M A),
      ← verticalBoundary_inclusion, LinearMap.comp_apply] at hfv
    have hb : mixedHorizontalBoundary M A m = 0 := by
      have hh := congrArg (horizontalEdgeProjection M A) hfv
      simp only [map_add, horizontalEdgeProjection_vertical, zero_add] at hh
      exact hh
    refine ⟨v, ⟨m, hb⟩, ?_⟩
    have hh := congrArg (verticalEdgeProjection M A) hfv
    simpa only [map_add, verticalEdgeProjection_inclusion] using hh
  · rintro ⟨v, y, hz⟩
    have hfmem : verticalFaceInclusion M A v + mixedFaceInclusion M A y.1 ∈
        degenerateL2 M A :=
      (degenerateL2 M A).add_mem
        (verticalFaceInclusion_range_le_degenerate M A ⟨v, rfl⟩)
        (mixedFaceInclusion_range_le_degenerate M A ⟨y.1, rfl⟩)
    refine ⟨⟨_, hfmem⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [degenerateBoundaryToCycles_val, verticalCycleInclusion_val]
    rw [map_add, ← LinearMap.comp_apply (chainD2 Nf _) (verticalFaceInclusion M A),
      ← verticalBoundary_inclusion, LinearMap.comp_apply]
    have hm := mixedBoundary_recombination M A y.1
    rw [show mixedHorizontalBoundary M A y.1 = 0 from y.2, map_zero, add_zero] at hm
    rw [← hm, ← map_add, hz]

/-- 実垂直包含が、指定関係商と同じLの一次homologyの両方向同型を与える。 -/
def verticalRelationsHomologyEquiv :
    (verticalCycles M A ⧸ verticalRelations M A) ≃ₗ[ℚ] DegenerateHomology M A :=
  (Submodule.quotEquivOfEq _ _ (verticalCycleHomologyMap_ker M A).symm).trans
    ((verticalCycleHomologyMap M A).quotKerEquivOfSurjective
      (verticalCycleHomologyMap_surjective M A))

/-- 関係商の同定は同じ垂直代表の実L類を返す。 -/
@[simp] theorem verticalRelationsHomologyEquiv_mk (z : verticalCycles M A) :
    verticalRelationsHomologyEquiv M A (Submodule.Quotient.mk z) =
      verticalCycleHomologyMap M A z := rfl

/-- 指定Lの一次homologyは同じ原始κの余核に同型。 -/
def rawKappaCokernelHomologyEquiv :
    (VerticalHomology M A ⧸ LinearMap.range (rawKappa M A)) ≃ₗ[ℚ] DegenerateHomology M A :=
  (rawKappaCokernelEquiv M A).trans (verticalRelationsHomologyEquiv M A)

/-- 実Lの次数1短複体。 -/
def degenerateOneShort : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.moduleCatMk (degenerateBoundary2 M A) (degenerateBoundary1 M A)
    (degenerateBoundary_square M A)

/-- 実Lの標準chainから同じ一次短複体への同型。 -/
def degenerateOneScIso : (degenerateChain M A).sc (1 : ℤ) ≅ degenerateOneShort M A :=
  (degenerateChain M A).isoSc' (i := 2) (j := 1) (k := 0) (by simp) (by simp) ≪≫
    eqToIso (by rfl)

/-- 閉路・微分像の商と標準ℤ homologyの実同定。 -/
def degenerateHomologyStandardEquiv : DegenerateHomology M A ≃ₗ[ℚ]
    (degenerateChain M A).homology (1 : ℤ) :=
  ((degenerateOneShort M A).moduleCatHomologyIso.symm ≪≫
    (ShortComplex.homologyMapIso (degenerateOneScIso M A)).symm).toLinearEquiv

/-- 同じ原始κの余核を標準H₁Lへ移す両方向同型。 -/
def rawKappaCokernelStandardEquiv :
    (VerticalHomology M A ⧸ LinearMap.range (rawKappa M A)) ≃ₗ[ℚ]
      (degenerateChain M A).homology (1 : ℤ) :=
  (rawKappaCokernelHomologyEquiv M A).trans (degenerateHomologyStandardEquiv M A)

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.degenerateCycles
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateBoundaryToCycles
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateBoundaryToCycles_val
#print axioms AAT.AG.AtlasCoefficientFiber.DegenerateHomology
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCycleInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCycleInclusion_val
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCycleHomologyMap
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCycleHomologyMap_apply
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateCycle_vertical_representative
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCycleHomologyMap_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCycleHomologyMap_ker
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRelationsHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRelationsHomologyEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappaCokernelHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateOneShort
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateOneScIso
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateHomologyStandardEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappaCokernelStandardEquiv
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
