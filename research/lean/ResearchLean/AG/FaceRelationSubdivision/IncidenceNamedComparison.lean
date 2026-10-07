import ResearchLean.AG.FaceRelationSubdivision.IncidenceFullSupportPullback
import ResearchLean.AG.AtlasDefectComposition.FullSupportIncidence
import ResearchLean.AG.AtlasDefectComposition.GeneratedComposition
import Formal.Util.AssertStandardAxioms
/-!
# 混在比較の原始名付き射と実 block 正方形

## Implementation notes

名付き射も原始 chart/Option セル表から生成する。
独立に生成済みの実 block と全三成分で一致する正方形を証明する。
旧 hereditary 型への置換や H¹ 座標だけの一致を採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
/-- 原始部分セル像を cochain に反変評価する線形写像。 -/
def namedOptionPullback {I J : Type u} (m : J → Option I) : (I → ℚ) →ₗ[ℚ] (J → ℚ) where
  toFun z j := (m j).elim 0 z
  map_add' z w := by funext j; cases he : m j <;> simp [he]
  map_smul' a z := by funext j; cases he : m j <;> simp [he]
/-- 原始 Option 射の公開評価。 -/
@[simp] theorem namedOptionPullback_apply {I J : Type u} (m : J → Option I) (z : I → ℚ) (j : J) :
    namedOptionPullback m z j = (m j).elim 0 z := rfl
variable {Source : Type u} {q r : Reading Source} {h : q.CoarserThan r}
variable {D : TargetSupportedNerve q} {E : TargetSupportedNerve r}
variable (M : IncidenceSupportedComparison q r h D E)
/-- 原始 incidence の符号から名付き全三成分 Hom を生成する。 -/
def incidenceNamedHom : ThreeCochainComplex.Hom (namedComplex D) (namedComplex E) where
  f0 := { toFun z c := z (M.chartMap c), map_add' _ _ := rfl, map_smul' _ _ := rfl }
  f1 := namedOptionPullback M.edgeMap
  f2 := namedOptionPullback M.faceMap
  comm0 := by
    intro z
    funext e
    rw [namedComplex_d0_apply]
    change (M.edgeMap e).elim 0 ((namedComplex D).d0 z) =
      z (M.chartMap (E.nerve.edgeRight e)) - z (M.chartMap (E.nerve.edgeLeft e))
    cases he : M.edgeMap e with
    | none => rw [M.edge_none_fiber e he]; exact (sub_self _).symm
    | some d => rw [Option.elim_some,namedComplex_d0_apply,M.edge_some_left e d he,M.edge_some_right e d he]
  comm1 := by
    intro z
    funext f
    rw [namedComplex_d1_apply]
    change (M.faceMap f).elim 0 ((namedComplex D).d1 z) =
      (M.edgeMap (E.nerve.faceEdge0 f)).elim 0 z -
      (M.edgeMap (E.nerve.faceEdge1 f)).elim 0 z +
      (M.edgeMap (E.nerve.faceEdge2 f)).elim 0 z
    cases hf : M.faceMap f with
    | some d =>
        rw [Option.elim_some,namedComplex_d1_apply]
        simp only [M.face_some_edge0 f d hf,M.face_some_edge1 f d hf,M.face_some_edge2 f d hf,Option.elim_some]
    | none =>
        rcases (optionCell_incidence_iff _ _ _).mp (M.face_none_incidence f hf) with ⟨ha,hbc⟩ | ⟨hc,hab⟩
        · rw [ha,hbc]; simp
        · rw [hc,hab]; simp
/-- 名付き次数0射の原始評価。 -/
@[simp] theorem incidenceNamedHom_f0 (z) (c) : (incidenceNamedHom M).f0 z c = z (M.chartMap c) := rfl
/-- 名付き次数1射の原始評価。 -/
@[simp] theorem incidenceNamedHom_f1 (z) (e) : (incidenceNamedHom M).f1 z e = (M.edgeMap e).elim 0 z := rfl
/-- 名付き次数2射の原始評価。 -/
@[simp] theorem incidenceNamedHom_f2 (z) (f) : (incidenceNamedHom M).f2 z f = (M.faceMap f).elim 0 z := rfl
variable [Fintype Source]
variable (laws : FiniteLawFamily Source) (hq : laws.Adequate q) (hr : laws.Adequate r)
variable (hD0 : ∀ c, D.chartSupport c = Set.univ) (hD1 : ∀ e, D.edgeSupport e = Set.univ)
variable (hD2 : ∀ f, D.faceSupport f = Set.univ)
variable (hE0 : ∀ c, E.chartSupport c = Set.univ) (hE1 : ∀ e, E.edgeSupport e = Set.univ)
variable (hE2 : ∀ f, E.faceSupport f = Set.univ) (label : LawValueLabel laws)
/-- 独立実生成 block と原始名付き射の全三成分正方形。 -/
theorem incidenceNamedHom_square :
    cochainComp (M.generatedBlockComparisonHom laws hq hr label)
      (fullBlockNamedEquivalence E laws hr hE0 hE1 hE2 label).toHom =
    cochainComp (fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label).toHom (incidenceNamedHom M) := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro z <;> funext x
  · exact fullBlock_pullback0 M laws hq hr label hD0 hE0 z x
  · rw [cochainComp_f1,cochainComp_f1,incidenceNamedHom_f1]
    cases he : M.edgeMap x with
    | none => simp only [Option.elim_none]; exact fullBlock_pullback1_none M laws hq hr hE1 label z x he
    | some e => simp only [Option.elim_some]; exact fullBlock_pullback1_some M laws hq hr hD1 hE1 label z x e he
  · rw [cochainComp_f2,cochainComp_f2,incidenceNamedHom_f2]
    cases hf : M.faceMap x with
    | none => simp only [Option.elim_none]; exact fullBlock_pullback2_none M laws hq hr label hE2 z x hf
    | some f => simp only [Option.elim_some]; exact fullBlock_pullback2_some M laws hq hr label hD2 hE2 z x f hf
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
