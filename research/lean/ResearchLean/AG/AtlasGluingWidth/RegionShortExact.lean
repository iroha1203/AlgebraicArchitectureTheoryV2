import ResearchLean.AG.AtlasGluingWidth.CellwiseShortExact

/-! # 元セル和と交差の複体短完全列

G-136 A。一般選択に対する評価射から構成し、領域選択へ特殊化する。

## Implementation notes

直和は二つの線形空間の積として表示する。完全性の証拠は
Cellwise の零延長と貼り合わせであり、cochain 射の field には含めない。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth
open ResolutionInvariance CanonicalResolution TwoPhase
universe u
variable {Source : Type u} {q : Reading Source} {D : TargetSupportedNerve q}

/-- 二つの三項複体の次数別直和。 -/
def pairComplex (C E : ThreeCochainComplex ℚ) : ThreeCochainComplex ℚ where
  C0 := C.C0 × E.C0
  C1 := C.C1 × E.C1
  C2 := C.C2 × E.C2
  d0 := C.d0.prodMap E.d0
  d1 := C.d1.prodMap E.d1
  d1_comp_d0 x := by
    apply Prod.ext
    · exact C.d1_comp_d0 x.1
    · exact E.d1_comp_d0 x.2

namespace CellSelection
variable (S T : CellSelection D)

/-- 元セル和から二つの選択への制限。 -/
def unionInclusion : ThreeCochainComplex.Hom (S.union T).complex
    (pairComplex S.complex T.complex) where
  f0 := Cellwise.inclusion S.chart T.chart
  f1 := Cellwise.inclusion S.edge T.edge
  f2 := Cellwise.inclusion S.face T.face
  comm0 x := by
    apply Prod.ext <;> funext e <;> rfl
  comm1 x := by
    apply Prod.ext <;> funext f <;> rfl

/-- 真の交差への二つの制限の差。 -/
def intersectionDifference : ThreeCochainComplex.Hom
    (pairComplex S.complex T.complex) (S.inter T).complex where
  f0 := Cellwise.difference S.chart T.chart
  f1 := Cellwise.difference S.edge T.edge
  f2 := Cellwise.difference S.face T.face
  comm0 x := by
    funext e
    change (x.1 (S.right ⟨e.1, e.2.1⟩) - x.1 (S.left ⟨e.1, e.2.1⟩)) -
      (x.2 (T.right ⟨e.1, e.2.2⟩) - x.2 (T.left ⟨e.1, e.2.2⟩)) =
      (x.1 (S.right ⟨e.1, e.2.1⟩) - x.2 (T.right ⟨e.1, e.2.2⟩)) -
      (x.1 (S.left ⟨e.1, e.2.1⟩) - x.2 (T.left ⟨e.1, e.2.2⟩))
    ring
  comm1 x := by
    funext f
    change (x.1 (S.face0 ⟨f.1, f.2.1⟩) - x.1 (S.face1 ⟨f.1, f.2.1⟩) +
      x.1 (S.face2 ⟨f.1, f.2.1⟩)) -
      (x.2 (T.face0 ⟨f.1, f.2.2⟩) - x.2 (T.face1 ⟨f.1, f.2.2⟩) +
      x.2 (T.face2 ⟨f.1, f.2.2⟩)) =
      (x.1 (S.face0 ⟨f.1, f.2.1⟩) - x.2 (T.face0 ⟨f.1, f.2.2⟩)) -
      (x.1 (S.face1 ⟨f.1, f.2.1⟩) - x.2 (T.face1 ⟨f.1, f.2.2⟩)) +
      (x.1 (S.face2 ⟨f.1, f.2.1⟩) - x.2 (T.face2 ⟨f.1, f.2.2⟩))
    ring

/-- 真のセル交差複体は原始領域の二つの所属を持つセルで作る。 -/
def intersectionComplex (D : TargetSupportedNerve q) (A B : Set q.Target) :
    ThreeCochainComplex ℚ := ((region D A).inter (region D B)).complex

/-- 領域和からの射は元セル和からの制限射と一致する。 -/
def regionInclusion (D : TargetSupportedNerve q) (A B : Set q.Target) :
    ThreeCochainComplex.Hom (D.targetSubsetComplex (A ∪ B))
      (pairComplex (D.targetSubsetComplex A) (D.targetSubsetComplex B)) := by
  rw [← region_complex D (A ∪ B), region_union,
    ← region_complex D A, ← region_complex D B]
  exact unionInclusion _ _

/-- 次数0 の制限対は単射。 -/
theorem unionInclusion_injective0 : Function.Injective (unionInclusion S T).f0 :=
  Cellwise.inclusion_injective S.chart T.chart

/-- 次数0 の差制限は全射。 -/
theorem intersectionDifference_surjective0 :
    Function.Surjective (intersectionDifference S T).f0 :=
  Cellwise.difference_surjective S.chart T.chart

/-- 次数0 の像は同じ元セル交差における差制限の核。 -/
theorem union_intersection_exact0 :
    Function.Exact (unionInclusion S T).f0 (intersectionDifference S T).f0 :=
  Cellwise.exact S.chart T.chart

/-- 次数1 の制限対は単射。 -/
theorem unionInclusion_injective1 : Function.Injective (unionInclusion S T).f1 :=
  Cellwise.inclusion_injective S.edge T.edge

/-- 次数1 の差制限は全射。 -/
theorem intersectionDifference_surjective1 :
    Function.Surjective (intersectionDifference S T).f1 :=
  Cellwise.difference_surjective S.edge T.edge

/-- 次数1 の像は同じ元セル交差における差制限の核。 -/
theorem union_intersection_exact1 :
    Function.Exact (unionInclusion S T).f1 (intersectionDifference S T).f1 :=
  Cellwise.exact S.edge T.edge

/-- 次数2 の制限対は単射。 -/
theorem unionInclusion_injective2 : Function.Injective (unionInclusion S T).f2 :=
  Cellwise.inclusion_injective S.face T.face

/-- 次数2 の差制限は全射。 -/
theorem intersectionDifference_surjective2 :
    Function.Surjective (intersectionDifference S T).f2 :=
  Cellwise.difference_surjective S.face T.face

/-- 次数2 の像は同じ元セル交差における差制限の核。 -/
theorem union_intersection_exact2 :
    Function.Exact (unionInclusion S T).f2 (intersectionDifference S T).f2 :=
  Cellwise.exact S.face T.face

end CellSelection
end AAT.AG.AtlasGluingWidth
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
