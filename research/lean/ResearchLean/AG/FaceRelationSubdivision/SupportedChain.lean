import ResearchLean.AG.FaceRelationSubdivision.SubsetComparison
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import ResearchLean.AG.AtlasDefectComposition.ZeroExtension
import Formal.Util.AssertStandardAxioms

/-!
# 支持セルの自由chainと実subset複体の双対

G-134 T0・A・D。原始incidenceから有限自由ℚ加群と微分を作る。

## Implementation notes

chainは支持セル名上のFinsuppであり、cochainとの同定はmathlibの自由加群の
線形普遍性を使う。微分と比較は基底像から先に定め、双対の式を検証する。
有限基底を番号付けして行列へ移す表現は、任意のセル名・支持部分集合ごとに
番号付けとtransportを追加するため採らず、セル名を直接基底とするFinsuppを用いる。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase
universe u

/-- セル基底の像を線形延長する。 -/
def freeMap {I J : Type u} (f : I → (J →₀ ℚ)) : (I →₀ ℚ) →ₗ[ℚ] (J →₀ ℚ) :=
  Finsupp.linearCombination ℚ f

/-- 線形延長の基底評価。定義の所有API。 -/
@[simp] theorem freeMap_single {I J : Type u} (f : I → (J →₀ ℚ)) (i : I) (a : ℚ) :
    freeMap f (Finsupp.single i a) = a • f i := by simp [freeMap]

/-- 自由chainの線形双対と同じセル上の関数の標準同定。 -/
def freeDualEquiv (I : Type u) : (I → ℚ) ≃ₗ[ℚ] ((I →₀ ℚ) →ₗ[ℚ] ℚ) :=
  Finsupp.llift ℚ ℚ ℚ I

/-- 双対同定の基底評価。 -/
@[simp] theorem freeDualEquiv_single {I : Type u} (z : I → ℚ) (i : I) (a : ℚ) :
    freeDualEquiv I z (Finsupp.single i a) = a * z i := by
  simp [freeDualEquiv, Finsupp.lift_apply]

/-- 全双対評価によって自由chainの等号を検査できる。 -/
theorem freeDual_separates {I : Type u} {x y : I →₀ ℚ}
    (h : ∀ z : I → ℚ, freeDualEquiv I z x = freeDualEquiv I z y) : x = y := by
  classical
  ext i
  have hi := h (Pi.single i 1)
  change Finsupp.linearCombination ℚ (Pi.single i 1) x =
    Finsupp.linearCombination ℚ (Pi.single i 1) y at hi
  simpa using hi

variable {Source : Type u} {q : Reading Source}

/-- 支持頂点の有限自由chain。 -/
abbrev K0 (N : TargetSupportedNerve q) (A : Set q.Target) := N.ChartInTargetSubset A →₀ ℚ
/-- 支持辺の有限自由chain。 -/
abbrev K1 (N : TargetSupportedNerve q) (A : Set q.Target) := N.EdgeInTargetSubset A →₀ ℚ
/-- 支持面の有限自由chain。 -/
abbrev K2 (N : TargetSupportedNerve q) (A : Set q.Target) := N.FaceInTargetSubset A →₀ ℚ

/-- K1からK0への原始端点差分。 -/
def chainD1 (N : TargetSupportedNerve q) (A : Set q.Target) : K1 N A →ₗ[ℚ] K0 N A :=
  freeMap fun e => Finsupp.single (N.targetSubsetEdgeRight A e) 1 -
    Finsupp.single (N.targetSubsetEdgeLeft A e) 1

/-- K2からK1への原始三辺の符号付き和。 -/
def chainD2 (N : TargetSupportedNerve q) (A : Set q.Target) : K2 N A →ₗ[ℚ] K1 N A :=
  freeMap fun f => Finsupp.single (N.targetSubsetFaceEdge0 A f) 1 -
    Finsupp.single (N.targetSubsetFaceEdge1 A f) 1 +
      Finsupp.single (N.targetSubsetFaceEdge2 A f) 1

/-- 支持辺の基底微分。 -/
@[simp] theorem chainD1_single (N : TargetSupportedNerve q) (A : Set q.Target)
    (e : N.EdgeInTargetSubset A) (a : ℚ) :
    chainD1 N A (Finsupp.single e a) = a •
      (Finsupp.single (N.targetSubsetEdgeRight A e) 1 -
        Finsupp.single (N.targetSubsetEdgeLeft A e) 1) := freeMap_single _ _ _

/-- 支持面の基底微分。 -/
@[simp] theorem chainD2_single (N : TargetSupportedNerve q) (A : Set q.Target)
    (f : N.FaceInTargetSubset A) (a : ℚ) :
    chainD2 N A (Finsupp.single f a) = a •
      (Finsupp.single (N.targetSubsetFaceEdge0 A f) 1 -
        Finsupp.single (N.targetSubsetFaceEdge1 A f) 1 +
          Finsupp.single (N.targetSubsetFaceEdge2 A f) 1) := freeMap_single _ _ _

/-- 原始chain微分の双対は既存subsetの実degree 0微分。 -/
theorem chainD1_dual (N : TargetSupportedNerve q) (A : Set q.Target)
    (z : N.ChartInTargetSubset A → ℚ) (x : K1 N A) :
    freeDualEquiv _ z (chainD1 N A x) = freeDualEquiv _ (N.targetSubsetD0 A z) x := by
  have h : (freeDualEquiv _ z).comp (chainD1 N A) = freeDualEquiv _ (N.targetSubsetD0 A z) := by
    apply Finsupp.lhom_ext
    intro e a
    simp only [LinearMap.comp_apply, chainD1_single, map_smul, map_sub,
      freeDualEquiv_single, one_mul, smul_eq_mul]
    change a * (z (N.targetSubsetEdgeRight A e) - z (N.targetSubsetEdgeLeft A e)) =
      a * (N.targetSubsetComplex A).d0 z e
    rw [N.targetSubsetComplex_d0_apply]
  exact LinearMap.congr_fun h x

/-- 原始chain微分の双対は既存subsetの実degree 1微分。 -/
theorem chainD2_dual (N : TargetSupportedNerve q) (A : Set q.Target)
    (z : N.EdgeInTargetSubset A → ℚ) (x : K2 N A) :
    freeDualEquiv _ z (chainD2 N A x) = freeDualEquiv _ (N.targetSubsetD1 A z) x := by
  have h : (freeDualEquiv _ z).comp (chainD2 N A) = freeDualEquiv _ (N.targetSubsetD1 A z) := by
    apply Finsupp.lhom_ext
    intro f a
    simp only [LinearMap.comp_apply, chainD2_single, map_smul, map_sub, map_add,
      freeDualEquiv_single, one_mul, smul_eq_mul]
    change a * (z (N.targetSubsetFaceEdge0 A f) - z (N.targetSubsetFaceEdge1 A f) +
      z (N.targetSubsetFaceEdge2 A f)) = a * (N.targetSubsetComplex A).d1 z f
    rw [N.targetSubsetComplex_d1_apply]
  exact LinearMap.congr_fun h x

/-- 原始支持chainの二微分は零に合成される。 -/
theorem chainD1_comp_chainD2 (N : TargetSupportedNerve q) (A : Set q.Target) :
    (chainD1 N A).comp (chainD2 N A) = 0 := by
  apply Finsupp.lhom_ext
  intro f a
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, chainD2_single, map_smul,
    map_add, map_sub, chainD1_single, one_smul]
  rw [N.targetSubset_left_faceEdge0_eq_left_faceEdge1,
    N.targetSubset_right_faceEdge0_eq_left_faceEdge2,
    N.targetSubset_right_faceEdge1_eq_right_faceEdge2]
  simp

/-- 診断係数ℚでの部分セル基底像。 -/
def rationalOptionCell {I : Type u} (a : Option I) : I →₀ ℚ :=
  a.elim 0 (fun i => Finsupp.single i 1)

/-- 部分セル基底像の双対評価は零延長pullbackの式と一致する。 -/
@[simp] theorem rationalOptionCell_dual {I : Type u} (z : I → ℚ) (a : Option I) :
    freeDualEquiv I z (rationalOptionCell a) = a.elim 0 z := by
  cases a <;> simp [rationalOptionCell]

open CategoryTheory

/-- 支持chainの標準ℤ次数加群。次数外は零加群。 -/
def chainDegreeObject (N : TargetSupportedNerve q) (A : Set q.Target) (n : ℤ) : ModuleCat.{u} ℚ :=
  if n = 0 then ModuleCat.of ℚ (K0 N A)
  else if n = 1 then ModuleCat.of ℚ (K1 N A)
  else if n = 2 then ModuleCat.of ℚ (K2 N A)
  else ModuleCat.of ℚ PUnit.{u+1}

/-- 二つの原始微分の標準chain次数表示。 -/
def chainDegreeDifferential (N : TargetSupportedNerve q) (A : Set q.Target) (n : ℤ) :
    chainDegreeObject N A (n + 1) ⟶ chainDegreeObject N A n :=
  if h0 : n = 0 then by subst n; exact ModuleCat.ofHom (chainD1 N A)
  else if h1 : n = 1 then by subst n; exact ModuleCat.ofHom (chainD2 N A)
  else 0

/-- 原始微分から標準chainのsquare-zeroを放電する。 -/
theorem chainDegreeDifferential_square (N : TargetSupportedNerve q) (A : Set q.Target) (n : ℤ) :
    chainDegreeDifferential N A (n + 1) ≫ chainDegreeDifferential N A n = 0 := by
  by_cases h0 : n = 0
  · subst n
    change ModuleCat.ofHom (chainD2 N A) ≫ ModuleCat.ofHom (chainD1 N A) = 0
    apply ModuleCat.hom_ext
    exact chainD1_comp_chainD2 N A
  · by_cases h1 : n = 1
    · subst n
      simp [chainDegreeDifferential]
    · simp [chainDegreeDifferential, h0, h1]

/-- T0の支持セルchainをmathlibの標準ChainComplexへ接続する。 -/
def supportedChain (N : TargetSupportedNerve q) (A : Set q.Target) :
    ChainComplex (ModuleCat.{u} ℚ) ℤ :=
  ChainComplex.of (chainDegreeObject N A) (chainDegreeDifferential N A)
    (chainDegreeDifferential_square N A)

namespace IncidenceSupportedComparison
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (Ac : Set qc.Target) (Af : Set qf.Target)
variable (hs : ∀ t, t ∈ Af → comparisonFactor qc qf h t ∈ Ac)

/-- degree 0の支持chain比較を原始セル像から線形延長する。 -/
def supportedChainMap0 : K0 Nf Af →ₗ[ℚ] K0 Nc Ac :=
  freeMap fun c => Finsupp.single (M.targetSubsetChartMap Ac Af hs c) 1

/-- degree 0の支持chain比較の基底評価。 -/
@[simp] theorem supportedChainMap0_single (c : Nf.ChartInTargetSubset Af) (a : ℚ) :
    M.supportedChainMap0 Ac Af hs (Finsupp.single c a) = a • (Finsupp.single (M.targetSubsetChartMap Ac Af hs c) 1) :=
  freeMap_single _ _ _

/-- degree 0のchain比較の双対は独立生成した既存subset上の同じ比較。 -/
theorem supportedChainMap0_dual (z : Nc.ChartInTargetSubset Ac → ℚ) (x : K0 Nf Af) :
    freeDualEquiv _ z (M.supportedChainMap0 Ac Af hs x) =
      freeDualEquiv _ (M.targetSubsetPullback0 Ac Af hs z) x := by
  have heq : (freeDualEquiv _ z).comp (M.supportedChainMap0 Ac Af hs) =
      freeDualEquiv _ (M.targetSubsetPullback0 Ac Af hs z) := by
    apply Finsupp.lhom_ext
    intro c a
    simp [LinearMap.comp_apply, targetSubsetPullback0_apply]
  exact LinearMap.congr_fun heq x

/-- degree 1の支持chain比較を原始セル像から線形延長する。 -/
def supportedChainMap1 : K1 Nf Af →ₗ[ℚ] K1 Nc Ac :=
  freeMap fun c => rationalOptionCell (M.targetSubsetEdgeMapOption Ac Af hs c)

/-- degree 1の支持chain比較の基底評価。 -/
@[simp] theorem supportedChainMap1_single (c : Nf.EdgeInTargetSubset Af) (a : ℚ) :
    M.supportedChainMap1 Ac Af hs (Finsupp.single c a) = a • (rationalOptionCell (M.targetSubsetEdgeMapOption Ac Af hs c)) :=
  freeMap_single _ _ _

/-- degree 1のchain比較の双対は独立生成した既存subset上の同じ比較。 -/
theorem supportedChainMap1_dual (z : Nc.EdgeInTargetSubset Ac → ℚ) (x : K1 Nf Af) :
    freeDualEquiv _ z (M.supportedChainMap1 Ac Af hs x) =
      freeDualEquiv _ (M.targetSubsetPullback1 Ac Af hs z) x := by
  have heq : (freeDualEquiv _ z).comp (M.supportedChainMap1 Ac Af hs) =
      freeDualEquiv _ (M.targetSubsetPullback1 Ac Af hs z) := by
    apply Finsupp.lhom_ext
    intro c a
    simp [LinearMap.comp_apply, targetSubsetPullback1_apply]
  exact LinearMap.congr_fun heq x

/-- degree 2の支持chain比較を原始セル像から線形延長する。 -/
def supportedChainMap2 : K2 Nf Af →ₗ[ℚ] K2 Nc Ac :=
  freeMap fun c => rationalOptionCell (M.targetSubsetFaceMapOption Ac Af hs c)

/-- degree 2の支持chain比較の基底評価。 -/
@[simp] theorem supportedChainMap2_single (c : Nf.FaceInTargetSubset Af) (a : ℚ) :
    M.supportedChainMap2 Ac Af hs (Finsupp.single c a) = a • (rationalOptionCell (M.targetSubsetFaceMapOption Ac Af hs c)) :=
  freeMap_single _ _ _

/-- degree 2のchain比較の双対は独立生成した既存subset上の同じ比較。 -/
theorem supportedChainMap2_dual (z : Nc.FaceInTargetSubset Ac → ℚ) (x : K2 Nf Af) :
    freeDualEquiv _ z (M.supportedChainMap2 Ac Af hs x) =
      freeDualEquiv _ (M.targetSubsetPullback2 Ac Af hs z) x := by
  have heq : (freeDualEquiv _ z).comp (M.supportedChainMap2 Ac Af hs) =
      freeDualEquiv _ (M.targetSubsetPullback2 Ac Af hs z) := by
    apply Finsupp.lhom_ext
    intro c a
    simp [LinearMap.comp_apply, targetSubsetPullback2_apply]
  exact LinearMap.congr_fun heq x

/-- degree 1のchain-map式を、原始生成済み双対の同じ微分へ接続する。 -/
theorem supportedChainMap_comm1 (x : K1 Nf Af) :
    M.supportedChainMap0 Ac Af hs (chainD1 Nf Af x) =
      chainD1 Nc Ac (M.supportedChainMap1 Ac Af hs x) := by
  apply freeDual_separates
  intro z
  rw [supportedChainMap0_dual, chainD1_dual, chainD1_dual]
  have hc := M.targetSubsetPullback_comm0 Ac Af hs z
  exact (congrArg (fun y => freeDualEquiv _ y x) hc).symm.trans
    (M.supportedChainMap1_dual Ac Af hs (Nc.targetSubsetD0 Ac z) x).symm

/-- degree 2のchain-map式。退化面の零和を同じsubset微分で用いる。 -/
theorem supportedChainMap_comm2 (x : K2 Nf Af) :
    M.supportedChainMap1 Ac Af hs (chainD2 Nf Af x) =
      chainD2 Nc Ac (M.supportedChainMap2 Ac Af hs x) := by
  apply freeDual_separates
  intro z
  rw [supportedChainMap1_dual, chainD2_dual, chainD2_dual]
  have hc := M.targetSubsetPullback_comm1 Ac Af hs z
  exact (congrArg (fun y => freeDualEquiv _ y x) hc).symm.trans
    (M.supportedChainMap2_dual Ac Af hs (Nc.targetSubsetD1 Ac z) x).symm

/-- 原始支持chain比較の標準次数表示。 -/
def supportedChainDegreeMap (n : ℤ) : chainDegreeObject Nf Af n ⟶ chainDegreeObject Nc Ac n :=
  if h0 : n = 0 then by subst n; exact ModuleCat.ofHom (M.supportedChainMap0 Ac Af hs)
  else if h1 : n = 1 then by subst n; exact ModuleCat.ofHom (M.supportedChainMap1 Ac Af hs)
  else if h2 : n = 2 then by subst n; exact ModuleCat.ofHom (M.supportedChainMap2 Ac Af hs)
  else 0

/-- 標準chainの全次数で同じ原始比較が微分と可換。 -/
theorem supportedChainDegreeMap_comm (n : ℤ) :
    M.supportedChainDegreeMap Ac Af hs (n + 1) ≫ chainDegreeDifferential Nc Ac n =
      chainDegreeDifferential Nf Af n ≫ M.supportedChainDegreeMap Ac Af hs n := by
  by_cases h0 : n = 0
  · subst n
    change ModuleCat.ofHom (M.supportedChainMap1 Ac Af hs) ≫ ModuleCat.ofHom (chainD1 Nc Ac) =
      ModuleCat.ofHom (chainD1 Nf Af) ≫ ModuleCat.ofHom (M.supportedChainMap0 Ac Af hs)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (M.supportedChainMap_comm1 Ac Af hs x).symm
  · by_cases h1 : n = 1
    · subst n
      change ModuleCat.ofHom (M.supportedChainMap2 Ac Af hs) ≫ ModuleCat.ofHom (chainD2 Nc Ac) =
        ModuleCat.ofHom (chainD2 Nf Af) ≫ ModuleCat.ofHom (M.supportedChainMap1 Ac Af hs)
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (M.supportedChainMap_comm2 Ac Af hs x).symm
    · simp [chainDegreeDifferential, h0, h1]

/-- 全Aの原始比較から標準chain-mapを出力する。 -/
def supportedChainHom : supportedChain Nf Af ⟶ supportedChain Nc Ac :=
  ChainComplex.ofHom _ _ _ _ _ _ (M.supportedChainDegreeMap Ac Af hs)
    (M.supportedChainDegreeMap_comm Ac Af hs)

end IncidenceSupportedComparison

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
