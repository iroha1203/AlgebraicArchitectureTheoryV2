import ResearchLean.AG.AtlasDefectComposition.ComparisonLaws
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Formal.Util.AssertStandardAxioms
/-! # 同じ Source の原始比較の圏

Implementation notes: 射は元の reading 順序と chart/Option edge/Option face 比較だけを持つ。
cochain 比較や完全性を field に追加しない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance
universe u
/-- 同じ Source の reading と元の支持付き nerve。 -/
structure RawResolution (Source : Type u) where
  reading : Reading Source
  nerve : TargetSupportedNerve.{u,u} reading
/-- reading 順序と全原始セル比較を持つ射。 -/
abbrev RawResolution.Hom {Source : Type u} (X Y : RawResolution Source) :=
  PSigma fun h : X.reading.CoarserThan Y.reading =>
    TargetSupportedNerveMorphism X.reading Y.reading h X.nerve Y.nerve
/-- 元の恒等セル比較。 -/
def RawResolution.identity {Source : Type u} (X : RawResolution Source) : X.Hom X :=
  ⟨Reading.coarserThan_refl X.reading,
    TargetSupportedNerveMorphism.identityMorphism X.reading X.nerve⟩
/-- 全 incidence 条件を満たす原始比較の合成。 -/
def RawResolution.compose {Source : Type u} {X Y Z : RawResolution Source}
    (f : X.Hom Y) (g : Y.Hom Z) : X.Hom Z :=
  ⟨Reading.coarserThan_trans f.1 g.1,comparisonComp f.2 g.2⟩
/-- 原始比較だけで構成する圏。 -/
instance rawResolutionCategory (Source : Type u) : Category (RawResolution Source) where
  Hom := RawResolution.Hom
  id := RawResolution.identity
  comp := RawResolution.compose
  id_comp f := by
    cases f with | mk h M =>
    refine PSigma.ext (Subsingleton.elim _ _) ?_
    exact heq_of_eq (comparisonComp_id_left M)
  comp_id f := by
    cases f with | mk h M =>
    refine PSigma.ext (Subsingleton.elim _ _) ?_
    exact heq_of_eq (comparisonComp_id_right M)
  assoc f g h := by
    refine PSigma.ext (Subsingleton.elim _ _) ?_
    exact heq_of_eq (comparisonComp_assoc f.2 g.2 h.2)
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
