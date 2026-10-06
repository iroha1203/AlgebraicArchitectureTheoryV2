import ResearchLean.AG.FaceRelationSubdivision.SourceSupportedBasis
import ResearchLean.AG.FaceRelationSubdivision.LawFiniteFunctor

/-!
# 同じLaw座標をSource台へ読む

## Implementation notes

セル名・Law・値を保つ座標全単射をSourceの全射性から構成する。
後続の混在reading有限和は原始係数で独立生成し、この全単射は一致の検査にだけ使う。
Law値型全体の有限性や選択済み診断同型を入力にする案は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I : Type u}

/-- 台のSource表示を検査する恒等reading。 -/
def sourceReading (Source : Type u) : Reading Source where
  Target := Source
  read := id
  surjective := Function.surjective_id

/-- 恒等reading値は元のSource。 -/
@[simp] theorem sourceReading_read (x : Source) : (sourceReading Source).read x = x := rfl

/-- 任意LawのSource表示adequacyを元評価から構成する。 -/
theorem sourceAdequate (laws : FiniteLawFamily Source) : laws.Adequate (sourceReading Source) :=
  fun l => ⟨laws.eval l, fun _ => rfl⟩

/-- Source表示のLaw降下は元評価。 -/
@[simp] theorem lawDescend_sourceReading (laws : FiniteLawFamily Source) (l) (x : Source) :
    lawDescend laws (sourceReading Source) (sourceAdequate laws) l x = laws.eval l x :=
  lawDescend_commutes laws (sourceReading Source) (sourceAdequate laws) l x

variable (laws : FiniteLawFamily Source) {q : Reading Source} (ha : laws.Adequate q)
variable (s : I → Set q.Target)

/-- 同じセル名・Law・値のSource発生座標と実座標の全単射。 -/
def sourceCoordinateEquiv :
    CellCoordinate laws (sourceReading Source) (sourceAdequate laws) I (sourceSupport q s) ≃
      CellCoordinate laws q ha I s where
  toFun x := ⟨x.cell, x.law, x.value, by
    obtain ⟨a, ha, hv⟩ := x.generated
    exact ⟨q.read a, ha, (lawDescend_commutes laws q _ _ a).trans
      ((lawDescend_sourceReading laws _ a).symm.trans hv)⟩⟩
  invFun x := ⟨x.cell, x.law, x.value, by
    obtain ⟨t, ht, hv⟩ := x.generated
    obtain ⟨a, rfl⟩ := q.surjective t
    exact ⟨a, ht, (lawDescend_sourceReading laws _ a).trans
      ((lawDescend_commutes laws q _ _ a).symm.trans hv)⟩⟩
  left_inv x := by apply CellCoordinate.ext <;> rfl
  right_inv x := by apply CellCoordinate.ext <;> rfl

/-- Source座標表示でも同じ原始セル名。 -/
@[simp] theorem sourceCoordinateEquiv_cell (x) :
    (sourceCoordinateEquiv laws ha s x).cell = x.cell := rfl
/-- Source座標表示でも同じLaw名。 -/
@[simp] theorem sourceCoordinateEquiv_law (x) :
    (sourceCoordinateEquiv laws ha s x).law = x.law := rfl
/-- Source座標表示でも同じLaw値。 -/
@[simp] theorem sourceCoordinateEquiv_value (x) :
    (sourceCoordinateEquiv laws ha s x).value = x.value := rfl

/-- 実Law cochainを同じSource発生座標へ読む。 -/
def sourceCoordinateRead := cochainEquivOfIndexEquiv (sourceCoordinateEquiv laws ha s)

/-- Source座標読み取りは同じ実座標の評価。 -/
@[simp] theorem sourceCoordinateRead_apply (z) (x) :
    sourceCoordinateRead laws ha s z x = z (sourceCoordinateEquiv laws ha s x) :=
  cochainEquivOfIndexEquiv_apply _ _ _

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
