import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationGeometry
import ResearchLean.AG.FaceRelationSubdivision.HereditarySpecialization
import Formal.Util.AssertStandardAxioms

/-!
# 面複製の同じ支持比較

原始hereditary表の新比較クラスへの埋め込みを使い、全三成分を実subsetに生成する。

## Implementation notes

H¹の逆は旧面を選ぶsectionから作る。次数1の合成恒等だけを商へ降ろし、
複製面上の次数2合成を恒等とする主張は置かない。
抽象H¹同型を入力として受け取る方式は生成比較との接続を失うので採らない。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace FaceDuplication
variable (N : TargetSupportedNerve q) (F : N.nerve.FaceComponent)

/-- 旧原始collapseを新混在比較クラスへ埋め込む。 -/
def comparison : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) N (supported N F) :=
  IncidenceSupportedComparison.ofHereditary (collapse N F)
/-- 原始sectionを同じ新比較クラスへ埋め込む。 -/
def reverseComparison : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) (supported N F) N :=
  IncidenceSupportedComparison.ofHereditary (sectionMap N F)
/-- 同じ原始hereditary表からの埋め込みとの等号。 -/
theorem comparison_eq_ofHereditary : comparison N F = IncidenceSupportedComparison.ofHereditary (collapse N F) := rfl
/-- 同じreadingで任意の支持選択を保つ。 -/
theorem subset_compatible (A : Set q.Target) :
    ∀ t, t ∈ A → comparisonFactor q q (Reading.coarserThan_refl q) t ∈ A := by
  intro t ht
  rw [TriangleAddition.self_factor]
  exact ht
/-- 任意Aに生成した実subset比較。 -/
def subsetHom (A : Set q.Target) :
    ThreeCochainComplex.Hom (N.targetSubsetComplex A) ((supported N F).targetSubsetComplex A) :=
  (comparison N F).targetSubsetComparisonHom A A (subset_compatible A)
/-- 任意Aに生成した実逆向きsubset射。 -/
def reverseSubsetHom (A : Set q.Target) :
    ThreeCochainComplex.Hom ((supported N F).targetSubsetComplex A) (N.targetSubsetComplex A) :=
  (reverseComparison N F).targetSubsetComparisonHom A A (subset_compatible A)
/-- 原始新比較のchartは恒等。 -/
@[simp] theorem comparison_chart (v : N.nerve.Chart) : (comparison N F).chartMap v = v := rfl
/-- 原始新比較のedgeは同じ旧辺。 -/
@[simp] theorem comparison_edge (e : N.nerve.EdgeComponent) : (comparison N F).edgeMap e = some e := rfl
/-- 原始新比較のfaceはfold。 -/
@[simp] theorem comparison_face (f : (supported N F).nerve.FaceComponent) :
    (comparison N F).faceMap f = some (fold N F f) := rfl
/-- 原始新sectionのchartは恒等。 -/
@[simp] theorem reverseComparison_chart (v : N.nerve.Chart) : (reverseComparison N F).chartMap v = v := rfl
/-- 原始新sectionのedgeは同じ旧辺。 -/
@[simp] theorem reverseComparison_edge (e : N.nerve.EdgeComponent) : (reverseComparison N F).edgeMap e = some e := rfl
/-- 原始新sectionのfaceは旧面包含。 -/
@[simp] theorem reverseComparison_face (f : N.nerve.FaceComponent) :
    (reverseComparison N F).faceMap f = some (.inl f) := rfl
/-- 実subset比較の次数0は同じ頂点座標の恒等。 -/
@[simp] theorem subsetHom_f0 (A : Set q.Target) (z : (N.targetSubsetComplex A).C0) :
    (subsetHom N F A).f0 z = z := by
  funext v
  exact ((comparison N F).targetSubsetPullback0_apply A A (subset_compatible A) z v).trans (by rfl)
/-- 実逆subset射の次数0も同じ頂点座標の恒等。 -/
@[simp] theorem reverseSubsetHom_f0 (A : Set q.Target)
    (z : ((supported N F).targetSubsetComplex A).C0) :
    (reverseSubsetHom N F A).f0 z = z := by
  funext v
  exact ((reverseComparison N F).targetSubsetPullback0_apply A A (subset_compatible A) z v).trans (by rfl)
/-- 実subset比較の次数1は同じ辺座標の恒等。 -/
@[simp] theorem subsetHom_f1 (A : Set q.Target) (z : (N.targetSubsetComplex A).C1) :
    (subsetHom N F A).f1 z = z := by
  funext e
  exact ((comparison N F).targetSubsetPullback1_apply A A (subset_compatible A) z e).trans (by
    rw [(comparison N F).targetSubsetEdgeMapOption_eq_some A A (subset_compatible A) e e.val
      (comparison_edge N F e.val)]
    rfl)
/-- 実逆subset射の次数1も同じ辺座標の恒等。 -/
@[simp] theorem reverseSubsetHom_f1 (A : Set q.Target)
    (z : ((supported N F).targetSubsetComplex A).C1) :
    (reverseSubsetHom N F A).f1 z = z := by
  funext e
  exact ((reverseComparison N F).targetSubsetPullback1_apply A A (subset_compatible A) z e).trans (by
    rw [(reverseComparison N F).targetSubsetEdgeMapOption_eq_some A A (subset_compatible A) e e.val
      (reverseComparison_edge N F e.val)]
    rfl)
/-- 実subset比較の次数2成分を原始生成pullbackへ接続する公開API。 -/
@[simp] theorem subsetHom_f2_eq (A : Set q.Target) :
    (subsetHom N F A).f2 = (comparison N F).targetSubsetPullback2 A A (subset_compatible A) := rfl
/-- 旧側H¹で実二射の合成が恒等になる。 -/
theorem reverse_h1Map_comp (A : Set q.Target) :
    (reverseSubsetHom N F A).h1Map.comp (subsetHom N F A).h1Map = LinearMap.id := by
  rw [← cochainComp_h1Map]
  rw [ThreeCochainComplex.Hom.h1Map_eq_of_f1_eq _ (cochainId (N.targetSubsetComplex A))]
  · exact cochainId_h1Map _
  · ext z
    simp only [cochainComp_f1, subsetHom_f1, reverseSubsetHom_f1, cochainId_f1]
/-- 複製側H¹でも実二射の合成が恒等になる。 -/
theorem h1Map_reverse_comp (A : Set q.Target) :
    (subsetHom N F A).h1Map.comp (reverseSubsetHom N F A).h1Map = LinearMap.id := by
  rw [← cochainComp_h1Map]
  rw [ThreeCochainComplex.Hom.h1Map_eq_of_f1_eq _ (cochainId ((supported N F).targetSubsetComplex A))]
  · exact cochainId_h1Map _
  · ext z
    simp only [cochainComp_f1, subsetHom_f1, reverseSubsetHom_f1, cochainId_f1]
/-- 全Aの同じ実生成H¹比較から得た線形同値。 -/
def subsetH1Equiv (A : Set q.Target) :
    (N.targetSubsetComplex A).H1 ≃ₗ[ℚ] ((supported N F).targetSubsetComplex A).H1 :=
  LinearEquiv.ofLinear (subsetHom N F A).h1Map (reverseSubsetHom N F A).h1Map
    (h1Map_reverse_comp N F A) (reverse_h1Map_comp N F A)
/-- 線形同値の正方向は同じ実H¹比較。 -/
@[simp] theorem subsetH1Equiv_toLinearMap (A : Set q.Target) :
    (subsetH1Equiv N F A).toLinearMap = (subsetHom N F A).h1Map := rfl
/-- 全三成分で旧hereditary比較と同じ実subset射になる。 -/
theorem subsetHom_eq_hereditary (A : Set q.Target) :
    subsetHom N F A = (collapse N F).targetSubsetComparisonHom A A (subset_compatible A) :=
  ofHereditary_targetSubsetComparisonHom _ A A _

end FaceDuplication
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
