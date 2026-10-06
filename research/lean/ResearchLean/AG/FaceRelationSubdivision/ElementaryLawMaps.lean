import ResearchLean.AG.FaceRelationSubdivision.LawFiniteOption
import ResearchLean.AG.FaceRelationSubdivision.TriangleContraction
import ResearchLean.AG.FaceRelationSubdivision.EdgeContraction
import Formal.Util.AssertStandardAxioms

/-!
# 正操作の同じ原始r/s/hを実Lawへ送る

## Implementation notes

両正操作の受理済み原始基底表とchain式を具体適用し、汎用bridgeの方向仮定を放電する。
原始Option比較との射等号と、同じ既存subset収縮の実射との可換式を閉じる。
全次数のLaw収縮式・有限操作列は後続義務として、このmoduleで代替しない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}

namespace TriangleAddition
variable (N : ResolutionInvariance.TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 原始collapse有限和から独立生成する同じ実Law比較。 -/
def lawR := lawFiniteHom (r0 N e) (r1 N e) (r2 N e)
  (r_comm01 N e) (r_comm12 N e) laws ha
/-- 原始sectionの辺・面有限和から独立生成する同じ逆Law射。 -/
def lawS := lawFiniteHom (s0 N e) (s1 N e) (s2 N e)
  (s_comm01 N e) (s_comm12 N e) laws ha
/-- 同じ原始h0有限和のLaw補正。 -/
def lawH0 := (h0 N e).lawDual laws ha
/-- 同じ原始h1有限和のLaw補正。 -/
def lawH1 := (h1 N e).lawDual laws ha

/-- 同じ実Law比較は受理済みOption生成Homに全三成分一致。 -/
theorem lawR_eq_generated : lawR N e laws ha = (collapse N e).generatedComparisonHom laws ha ha :=
  (collapse N e).basisLawHom_eq_generated laws ha (r_comm01 N e) (r_comm12 N e)

omit [Fintype Source] in
/-- 原始collapseを選択した同じHomは受理済み収縮のrHom。 -/
theorem rSubsetFiniteHom_eq (A : Set q.Target) :
    subsetFiniteHom (r0 N e) (r1 N e) (r2 N e) (r_comm01 N e) (r_comm12 N e) A =
      (chainContraction N e A).rHom := by
  apply cochain_ext
  · rw [subsetFiniteHom_f0, SubsetChainContraction.rHom_f0, chainContraction_r0]
  · rw [subsetFiniteHom_f1, SubsetChainContraction.rHom_f1, chainContraction_r1]
  · rw [subsetFiniteHom_f2, SubsetChainContraction.rHom_f2, chainContraction_r2]

omit [Fintype Source] in
/-- 原始section有限和を選択した同じHomは受理済み収縮のsHom。 -/
theorem sSubsetFiniteHom_eq (A : Set q.Target) :
    subsetFiniteHom (s0 N e) (s1 N e) (s2 N e) (s_comm01 N e) (s_comm12 N e) A =
      (chainContraction N e A).sHom := by
  apply cochain_ext
  · rw [subsetFiniteHom_f0, SubsetChainContraction.sHom_f0, chainContraction_s0]
  · rw [subsetFiniteHom_f1, SubsetChainContraction.sHom_f1, chainContraction_s1]
  · rw [subsetFiniteHom_f2, SubsetChainContraction.sHom_f2, chainContraction_s2]

/-- 原始Law比較の同じ実三成分はlabel fiber収縮rへ着地。 -/
theorem lawR_fiber (l : LawValueLabel laws) :
    cochainComp (lawR N e laws ha) (lawFiberHom laws ha (supported N e) l) =
      cochainComp (lawFiberHom laws ha N l)
        (chainContraction N e (labelValueFiber laws q ha l)).rHom := by
  have h := lawFiniteFiber_square (r0 N e) (r1 N e) (r2 N e)
    (r_comm01 N e) (r_comm12 N e) laws ha l
  rw [rSubsetFiniteHom_eq] at h
  exact h

/-- 原始有限和逆Law射はlabel fiber収縮sの同じ実三成分へ着地。 -/
theorem lawS_fiber (l : LawValueLabel laws) :
    cochainComp (lawS N e laws ha) (lawFiberHom laws ha N l) =
      cochainComp (lawFiberHom laws ha (supported N e) l)
        (chainContraction N e (labelValueFiber laws q ha l)).sHom := by
  have h := lawFiniteFiber_square (s0 N e) (s1 N e) (s2 N e)
    (s_comm01 N e) (s_comm12 N e) laws ha l
  rw [sSubsetFiniteHom_eq] at h
  exact h

/-- 同じLaw比較の既存H1は同じ実fiber収縮のh1Mapと可換。 -/
theorem lawR_h1_fiber (l : LawValueLabel laws) :
    (lawFiberHom laws ha (supported N e) l).h1Map.comp (lawR N e laws ha).h1Map =
      (chainContraction N e (labelValueFiber laws q ha l)).rHom.h1Map.comp
        (lawFiberHom laws ha N l).h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map (lawR_fiber N e laws ha l)
  simpa only [cochainComp_h1Map] using h
/-- 同じ逆Law射の既存H1も同じfiber射へ着地。 -/
theorem lawS_h1_fiber (l : LawValueLabel laws) :
    (lawFiberHom laws ha N l).h1Map.comp (lawS N e laws ha).h1Map =
      (chainContraction N e (labelValueFiber laws q ha l)).sHom.h1Map.comp
        (lawFiberHom laws ha (supported N e) l).h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map (lawS_fiber N e laws ha l)
  simpa only [cochainComp_h1Map] using h

/-- 実比較の次数0有限和を公開する。 -/
@[simp] theorem lawR_f0 : (lawR N e laws ha).f0 = (r0 N e).lawDual laws ha := rfl
/-- 実比較の次数1有限和を公開する。 -/
@[simp] theorem lawR_f1 : (lawR N e laws ha).f1 = (r1 N e).lawDual laws ha := rfl
/-- 実比較の次数2有限和を公開する。 -/
@[simp] theorem lawR_f2 : (lawR N e laws ha).f2 = (r2 N e).lawDual laws ha := rfl
/-- 実逆射の次数0有限和を公開する。 -/
@[simp] theorem lawS_f0 : (lawS N e laws ha).f0 = (s0 N e).lawDual laws ha := rfl
/-- 実逆射の次数1有限和を公開する。 -/
@[simp] theorem lawS_f1 : (lawS N e laws ha).f1 = (s1 N e).lawDual laws ha := rfl
/-- 実逆射の次数2有限和を公開する。 -/
@[simp] theorem lawS_f2 : (lawS N e laws ha).f2 = (s2 N e).lawDual laws ha := rfl
omit [Fintype Source] in
/-- 実h0の同じ有限和。 -/
@[simp] theorem lawH0_eq : lawH0 N e laws ha = (h0 N e).lawDual laws ha := rfl
omit [Fintype Source] in
/-- 実h1の同じ有限和。 -/
@[simp] theorem lawH1_eq : lawH1 N e laws ha = (h1 N e).lawDual laws ha := rfl

/-- 同じ実Law比較のH1商はG-133標準homology自然性へ接続する。 -/
theorem lawR_h1_standard (x : (N.lawGeneratedComplex laws ha).H1) :
    oldH1Equiv ((supported N e).lawGeneratedComplex laws ha)
        ((lawR N e laws ha).h1Map x) =
      HomologicalComplex.homologyMap (zeroExtensionMap (lawR N e laws ha)) 1
        (oldH1Equiv (N.lawGeneratedComplex laws ha) x) :=
  oldH1Equiv_natural (lawR N e laws ha) x
/-- 同じ実逆Law射のH1商も標準homology自然性へ接続する。 -/
theorem lawS_h1_standard (x : ((supported N e).lawGeneratedComplex laws ha).H1) :
    oldH1Equiv (N.lawGeneratedComplex laws ha) ((lawS N e laws ha).h1Map x) =
      HomologicalComplex.homologyMap (zeroExtensionMap (lawS N e laws ha)) 1
        (oldH1Equiv ((supported N e).lawGeneratedComplex laws ha) x) :=
  oldH1Equiv_natural (lawS N e laws ha) x

end TriangleAddition

namespace EdgeSubdivision
variable (N : ResolutionInvariance.TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 原始collapse有限和から独立生成する同じ実Law比較。 -/
def lawR := lawFiniteHom (r0 N e) (r1 N e) (r2 N e)
  (r_comm01 N e) (r_comm12 N e) laws ha
/-- 原始sectionの辺・面有限和から独立生成する同じ逆Law射。 -/
def lawS := lawFiniteHom (s0 N e) (s1 N e) (s2 N e)
  (s_comm01 N e) (s_comm12 N e) laws ha
/-- 同じ原始h0有限和のLaw補正。 -/
def lawH0 := (h0 N e).lawDual laws ha
/-- 同じ原始h1有限和のLaw補正。 -/
def lawH1 := (h1 N e).lawDual laws ha

/-- 同じ実Law比較は受理済みOption生成Homに全三成分一致。 -/
theorem lawR_eq_generated : lawR N e laws ha = (collapse N e).generatedComparisonHom laws ha ha :=
  (collapse N e).basisLawHom_eq_generated laws ha (r_comm01 N e) (r_comm12 N e)

omit [Fintype Source] in
/-- 原始collapseを選択した同じHomは受理済み収縮のrHom。 -/
theorem rSubsetFiniteHom_eq (A : Set q.Target) :
    subsetFiniteHom (r0 N e) (r1 N e) (r2 N e) (r_comm01 N e) (r_comm12 N e) A =
      (chainContraction N e A).rHom := by
  apply cochain_ext
  · rw [subsetFiniteHom_f0, SubsetChainContraction.rHom_f0, chainContraction_r0]
  · rw [subsetFiniteHom_f1, SubsetChainContraction.rHom_f1, chainContraction_r1]
  · rw [subsetFiniteHom_f2, SubsetChainContraction.rHom_f2, chainContraction_r2]

omit [Fintype Source] in
/-- 原始section有限和を選択した同じHomは受理済み収縮のsHom。 -/
theorem sSubsetFiniteHom_eq (A : Set q.Target) :
    subsetFiniteHom (s0 N e) (s1 N e) (s2 N e) (s_comm01 N e) (s_comm12 N e) A =
      (chainContraction N e A).sHom := by
  apply cochain_ext
  · rw [subsetFiniteHom_f0, SubsetChainContraction.sHom_f0, chainContraction_s0]
  · rw [subsetFiniteHom_f1, SubsetChainContraction.sHom_f1, chainContraction_s1]
  · rw [subsetFiniteHom_f2, SubsetChainContraction.sHom_f2, chainContraction_s2]

/-- 原始Law比較の同じ実三成分はlabel fiber収縮rへ着地。 -/
theorem lawR_fiber (l : LawValueLabel laws) :
    cochainComp (lawR N e laws ha) (lawFiberHom laws ha (supported N e) l) =
      cochainComp (lawFiberHom laws ha N l)
        (chainContraction N e (labelValueFiber laws q ha l)).rHom := by
  have h := lawFiniteFiber_square (r0 N e) (r1 N e) (r2 N e)
    (r_comm01 N e) (r_comm12 N e) laws ha l
  rw [rSubsetFiniteHom_eq] at h
  exact h

/-- 原始有限和逆Law射はlabel fiber収縮sの同じ実三成分へ着地。 -/
theorem lawS_fiber (l : LawValueLabel laws) :
    cochainComp (lawS N e laws ha) (lawFiberHom laws ha N l) =
      cochainComp (lawFiberHom laws ha (supported N e) l)
        (chainContraction N e (labelValueFiber laws q ha l)).sHom := by
  have h := lawFiniteFiber_square (s0 N e) (s1 N e) (s2 N e)
    (s_comm01 N e) (s_comm12 N e) laws ha l
  rw [sSubsetFiniteHom_eq] at h
  exact h

/-- 同じLaw比較の既存H1は同じ実fiber収縮のh1Mapと可換。 -/
theorem lawR_h1_fiber (l : LawValueLabel laws) :
    (lawFiberHom laws ha (supported N e) l).h1Map.comp (lawR N e laws ha).h1Map =
      (chainContraction N e (labelValueFiber laws q ha l)).rHom.h1Map.comp
        (lawFiberHom laws ha N l).h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map (lawR_fiber N e laws ha l)
  simpa only [cochainComp_h1Map] using h
/-- 同じ逆Law射の既存H1も同じfiber射へ着地。 -/
theorem lawS_h1_fiber (l : LawValueLabel laws) :
    (lawFiberHom laws ha N l).h1Map.comp (lawS N e laws ha).h1Map =
      (chainContraction N e (labelValueFiber laws q ha l)).sHom.h1Map.comp
        (lawFiberHom laws ha (supported N e) l).h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map (lawS_fiber N e laws ha l)
  simpa only [cochainComp_h1Map] using h

/-- 実比較の次数0有限和を公開する。 -/
@[simp] theorem lawR_f0 : (lawR N e laws ha).f0 = (r0 N e).lawDual laws ha := rfl
/-- 実比較の次数1有限和を公開する。 -/
@[simp] theorem lawR_f1 : (lawR N e laws ha).f1 = (r1 N e).lawDual laws ha := rfl
/-- 実比較の次数2有限和を公開する。 -/
@[simp] theorem lawR_f2 : (lawR N e laws ha).f2 = (r2 N e).lawDual laws ha := rfl
/-- 実逆射の次数0有限和を公開する。 -/
@[simp] theorem lawS_f0 : (lawS N e laws ha).f0 = (s0 N e).lawDual laws ha := rfl
/-- 実逆射の次数1有限和を公開する。 -/
@[simp] theorem lawS_f1 : (lawS N e laws ha).f1 = (s1 N e).lawDual laws ha := rfl
/-- 実逆射の次数2有限和を公開する。 -/
@[simp] theorem lawS_f2 : (lawS N e laws ha).f2 = (s2 N e).lawDual laws ha := rfl
omit [Fintype Source] in
/-- 実h0の同じ有限和。 -/
@[simp] theorem lawH0_eq : lawH0 N e laws ha = (h0 N e).lawDual laws ha := rfl
omit [Fintype Source] in
/-- 実h1の同じ有限和。 -/
@[simp] theorem lawH1_eq : lawH1 N e laws ha = (h1 N e).lawDual laws ha := rfl

/-- 同じ実Law比較のH1商はG-133標準homology自然性へ接続する。 -/
theorem lawR_h1_standard (x : (N.lawGeneratedComplex laws ha).H1) :
    oldH1Equiv ((supported N e).lawGeneratedComplex laws ha)
        ((lawR N e laws ha).h1Map x) =
      HomologicalComplex.homologyMap (zeroExtensionMap (lawR N e laws ha)) 1
        (oldH1Equiv (N.lawGeneratedComplex laws ha) x) :=
  oldH1Equiv_natural (lawR N e laws ha) x
/-- 同じ実逆Law射のH1商も標準homology自然性へ接続する。 -/
theorem lawS_h1_standard (x : ((supported N e).lawGeneratedComplex laws ha).H1) :
    oldH1Equiv (N.lawGeneratedComplex laws ha) ((lawS N e laws ha).h1Map x) =
      HomologicalComplex.homologyMap (zeroExtensionMap (lawS N e laws ha)) 1
        (oldH1Equiv ((supported N e).lawGeneratedComplex laws ha) x) :=
  oldH1Equiv_natural (lawS N e laws ha) x

end EdgeSubdivision

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
