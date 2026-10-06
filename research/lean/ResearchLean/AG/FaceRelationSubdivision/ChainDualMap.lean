import ResearchLean.AG.FaceRelationSubdivision.RawSupportedChain
import ResearchLean.AG.FaceRelationSubdivision.ThreeHomotopy
import Mathlib.LinearAlgebra.Dual.Defs
import Formal.Util.AssertStandardAxioms

/-!
# 原始chain有限和の実cochain化

## Implementation notes

mathlibのLinearMap.dualMapを自由加群の双対同定で共役する。
関数の各点を手書きで定義する案は線形性と合成式を重複させるため採らない。
chain-map式はこの一般bridgeの方向仮定であり、基本変形では原始基底像から生成する。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {I J L : Type u}

/-- セルchainの同じ線形射を、関数cochain間の双対射へ送る。 -/
def dualCellMap (f : (I →₀ ℚ) →ₗ[ℚ] (J →₀ ℚ)) : (J → ℚ) →ₗ[ℚ] (I → ℚ) :=
  (freeDualEquiv I).symm.toLinearMap.comp
    (f.dualMap.comp (freeDualEquiv J).toLinearMap)

/-- 双対生成射の全chain上の評価。 -/
theorem dualCellMap_dual (f : (I →₀ ℚ) →ₗ[ℚ] (J →₀ ℚ))
    (z : J → ℚ) (x : I →₀ ℚ) :
    freeDualEquiv I (dualCellMap f z) x = freeDualEquiv J z (f x) := by
  simp [dualCellMap, LinearMap.comp_apply, LinearMap.dualMap_apply]

/-- 双対生成射は原始基底像の有限和を同じcochainで評価する。 -/
theorem dualCellMap_apply (f : (I →₀ ℚ) →ₗ[ℚ] (J →₀ ℚ)) (z : J → ℚ) (i : I) :
    dualCellMap f z i = freeDualEquiv J z (f (Finsupp.single i 1)) := by
  simpa using dualCellMap_dual f z (Finsupp.single i 1)

/-- 原始有限和の直接合成を双対化すると、逆順の実cochain合成に一致する。 -/
theorem dualCellMap_comp (f : (I →₀ ℚ) →ₗ[ℚ] (J →₀ ℚ))
    (g : (J →₀ ℚ) →ₗ[ℚ] (L →₀ ℚ)) :
    dualCellMap (g.comp f) = (dualCellMap f).comp (dualCellMap g) := by
  apply LinearMap.ext
  intro z
  apply (freeDualEquiv I).injective
  apply LinearMap.ext
  intro x
  simp only [dualCellMap_dual, LinearMap.comp_apply]

/-- 同じchain恒等を双対化した射は実cochain恒等。 -/
theorem dualCellMap_identity : dualCellMap (LinearMap.id : (I →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) =
    LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply (freeDualEquiv I).injective
  apply LinearMap.ext
  intro x
  simp only [dualCellMap_dual, LinearMap.id_apply]

/-- 同じchain射の和を双対化すると実cochain射の和となる。 -/
theorem dualCellMap_add (f g : (I →₀ ℚ) →ₗ[ℚ] (J →₀ ℚ)) :
    dualCellMap (f + g) = dualCellMap f + dualCellMap g := by
  apply LinearMap.ext
  intro z
  apply (freeDualEquiv I).injective
  apply LinearMap.ext
  intro x
  rw [dualCellMap_dual, LinearMap.add_apply, map_add]
  change _ = freeDualEquiv I (dualCellMap f z + dualCellMap g z) x
  rw [map_add, LinearMap.add_apply, dualCellMap_dual, dualCellMap_dual]

variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (Ac : Set qc.Target) (Af : Set qf.Target)

/-- 具体的支持chain-mapの三成分を同じ既存subset複体のHomへ双対化する。 -/
def dualSubsetHom
    (r0 : K0 Nf Af →ₗ[ℚ] K0 Nc Ac) (r1 : K1 Nf Af →ₗ[ℚ] K1 Nc Ac)
    (r2 : K2 Nf Af →ₗ[ℚ] K2 Nc Ac)
    (h01 : (chainD1 Nc Ac).comp r1 = r0.comp (chainD1 Nf Af))
    (h12 : (chainD2 Nc Ac).comp r2 = r1.comp (chainD2 Nf Af)) :
    ThreeCochainComplex.Hom (Nc.targetSubsetComplex Ac) (Nf.targetSubsetComplex Af) where
  f0 := dualCellMap r0
  f1 := dualCellMap r1
  f2 := dualCellMap r2
  comm0 := by
    intro z
    apply (freeDualEquiv (Nf.EdgeInTargetSubset Af)).injective
    apply LinearMap.ext
    intro x
    change freeDualEquiv _ (dualCellMap r1 (Nc.targetSubsetD0 Ac z)) x =
      freeDualEquiv _ (Nf.targetSubsetD0 Af (dualCellMap r0 z)) x
    rw [dualCellMap_dual, ← chainD1_dual, ← chainD1_dual, dualCellMap_dual]
    exact congrArg (freeDualEquiv _ z) (LinearMap.congr_fun h01 x)
  comm1 := by
    intro z
    apply (freeDualEquiv (Nf.FaceInTargetSubset Af)).injective
    apply LinearMap.ext
    intro x
    change freeDualEquiv _ (dualCellMap r2 (Nc.targetSubsetD1 Ac z)) x =
      freeDualEquiv _ (Nf.targetSubsetD1 Af (dualCellMap r1 z)) x
    rw [dualCellMap_dual, ← chainD2_dual, ← chainD2_dual, dualCellMap_dual]
    exact congrArg (freeDualEquiv _ z) (LinearMap.congr_fun h12 x)


/-- 支持辺微分の実双対は既存subsetの同じd0射。 -/
theorem dualCellMap_chainD1 (N : TargetSupportedNerve qc) (A : Set qc.Target) :
    dualCellMap (chainD1 N A) = N.targetSubsetD0 A := by
  apply LinearMap.ext
  intro z
  apply (freeDualEquiv _).injective
  apply LinearMap.ext
  intro x
  rw [dualCellMap_dual, chainD1_dual]

/-- 支持面微分の実双対は既存subsetの同じd1射。 -/
theorem dualCellMap_chainD2 (N : TargetSupportedNerve qc) (A : Set qc.Target) :
    dualCellMap (chainD2 N A) = N.targetSubsetD1 A := by
  apply LinearMap.ext
  intro z
  apply (freeDualEquiv _).injective
  apply LinearMap.ext
  intro x
  rw [dualCellMap_dual, chainD2_dual]

variable (r0 : K0 Nf Af →ₗ[ℚ] K0 Nc Ac) (r1 : K1 Nf Af →ₗ[ℚ] K1 Nc Ac)
  (r2 : K2 Nf Af →ₗ[ℚ] K2 Nc Ac)
  (h01 : (chainD1 Nc Ac).comp r1 = r0.comp (chainD1 Nf Af))
  (h12 : (chainD2 Nc Ac).comp r2 = r1.comp (chainD2 Nf Af))

/-- 同じchain射から生成した実Homの次数0成分。 -/
@[simp] theorem dualSubsetHom_f0 :
    (dualSubsetHom Ac Af r0 r1 r2 h01 h12).f0 = dualCellMap r0 := rfl

/-- 同じchain射から生成した実Homの次数1成分。 -/
@[simp] theorem dualSubsetHom_f1 :
    (dualSubsetHom Ac Af r0 r1 r2 h01 h12).f1 = dualCellMap r1 := rfl

/-- 同じchain射から生成した実Homの次数2成分。 -/
@[simp] theorem dualSubsetHom_f2 :
    (dualSubsetHom Ac Af r0 r1 r2 h01 h12).f2 = dualCellMap r2 := rfl

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
