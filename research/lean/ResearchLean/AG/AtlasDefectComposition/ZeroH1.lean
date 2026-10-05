import ResearchLean.AG.AtlasDefectComposition.GeneratedDefect
import Formal.Util.AssertStandardAxioms
/-! # 実三項複体の零次数1からの H¹ 零性 API

Implementation notes: 商の内部表現はこの基本 API で扱い、具体例の利用者は
次数1の零性だけから旧 H¹ の零性を得る。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
open TwoPhase
universe u v
variable {k : Type u} [Field k] (C : ThreeCochainComplex.{u,v} k)
/-- 旧 H¹ 商の基本零性 API。次数1が零なら実 cocycle とその商も零である。 -/
theorem h1_subsingleton_of_C1 [Subsingleton C.C1] : Subsingleton C.H1 := by
  unfold ThreeCochainComplex.H1
  infer_instance
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
