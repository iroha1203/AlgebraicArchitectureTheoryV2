import ResearchLean.AG.AtlasCoefficientFiber.ConstrainedRank

/-!
# G-135 B：元τ消滅と原始block rankの必要十分

同じB/D/H/Vから制約と出力を生成する。κの核を失うfiber直和へ置き換えない。

## Implementation notes

WBは関係像の出力とそのBt制約を、Giantは追加Dy出力と二つの独立制約を保持する。
積射のrank-nullityで元の像包含をrank加法へ移すため、この形を採る。
核基底を供給して包含を調べる方法は原始入力以外の選択を増やし、
BtとBy-Hxを一つの和にする方法は相殺によって別の制約になるため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision Module
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原By-Hxを保持する制約射。 -/
def primitiveConstraint := (mixedHorizontalBoundary M A).coprod (-horizontalFaceBoundary M A)

/-- 制約射の所有API。積元への適用を原By-Hxへ正規化する。 -/
@[simp] theorem primitiveConstraint_apply (y : MixedFace M A →₀ ℚ)
    (x : HorizontalFace M A →₀ ℚ) :
    primitiveConstraint M A (y, x) =
      mixedHorizontalBoundary M A y - horizontalFaceBoundary M A x := by
  simp only [primitiveConstraint, LinearMap.coprod_apply, LinearMap.neg_apply, sub_eq_add_neg]

/-- 原Vv+Dtを生成する出力射。 -/
def primitiveBaseOutput := (verticalBoundary M A).coprod (mixedVerticalBoundary M A)

/-- 関係出力射の所有API。積元への適用を原Vv+Dtへ正規化する。 -/
@[simp] theorem primitiveBaseOutput_apply (v : VerticalFace M A →₀ ℚ)
    (t : MixedFace M A →₀ ℚ) : primitiveBaseOutput M A (v, t) =
      verticalBoundary M A v + mixedVerticalBoundary M A t := rfl

/-- 基底関係の制約は同じ元Bt。 -/
def primitiveBaseConstraint := (mixedHorizontalBoundary M A).comp
  (LinearMap.snd ℚ (VerticalFace M A →₀ ℚ) (MixedFace M A →₀ ℚ))

/-- 関係制約射の所有API。積元への適用を原Btへ正規化する。 -/
@[simp] theorem primitiveBaseConstraint_apply (v : VerticalFace M A →₀ ℚ)
    (t : MixedFace M A →₀ ℚ) : primitiveBaseConstraint M A (v, t) =
      mixedHorizontalBoundary M A t := rfl

/-- 制約By=Hxから残る実Dy。 -/
def primitiveLiftOutput := (mixedVerticalBoundary M A).comp
  (LinearMap.fst ℚ (MixedFace M A →₀ ℚ) (HorizontalFace M A →₀ ℚ))

/-- 追加出力射の所有API。積元への適用を原Dyへ正規化する。 -/
@[simp] theorem primitiveLiftOutput_apply (y : MixedFace M A →₀ ℚ)
    (x : HorizontalFace M A →₀ ℚ) : primitiveLiftOutput M A (y, x) =
      mixedVerticalBoundary M A y := rfl

/-- 元WB(v,t)=(Vv+Dt,Bt)。 -/
def primitiveBaseBlock := (primitiveBaseOutput M A).prod (primitiveBaseConstraint M A)

/-- WBの所有API。積元への適用を元出力とBtの二座標へ正規化する。 -/
@[simp] theorem primitiveBaseBlock_apply (v : VerticalFace M A →₀ ℚ)
    (t : MixedFace M A →₀ ℚ) : primitiveBaseBlock M A (v, t) =
      (verticalBoundary M A v + mixedVerticalBoundary M A t,
        mixedHorizontalBoundary M A t) := rfl

/-- 元Giant(v,t,y,x)は二つの制約を別座標に保持する。 -/
def primitiveGiantBlock :=
  ((primitiveBaseOutput M A).coprod (primitiveLiftOutput M A)).prod
    ((primitiveBaseConstraint M A).prodMap (primitiveConstraint M A))

/-- Giantの所有API。積元への適用を元出力と独立二制約の三座標へ正規化する。 -/
@[simp] theorem primitiveGiantBlock_apply (v : VerticalFace M A →₀ ℚ)
    (t y : MixedFace M A →₀ ℚ) (x : HorizontalFace M A →₀ ℚ) :
    primitiveGiantBlock M A ((v, t), (y, x)) =
      (verticalBoundary M A v + mixedVerticalBoundary M A t + mixedVerticalBoundary M A y,
        (mixedHorizontalBoundary M A t,
          mixedHorizontalBoundary M A y - horizontalFaceBoundary M A x)) := by
  simp only [primitiveGiantBlock, LinearMap.prod_apply, Pi.prod, LinearMap.coprod_apply,
    LinearMap.prodMap_apply, primitiveBaseOutput_apply, primitiveLiftOutput_apply,
    primitiveBaseConstraint_apply, primitiveConstraint_apply]

/-- Giantの所有APIは任意の積元（零積を含む）の全三座標を返す。 -/
theorem primitiveGiantBlock_apply_all (z : ((VerticalFace M A →₀ ℚ) ×
    (MixedFace M A →₀ ℚ)) × ((MixedFace M A →₀ ℚ) × (HorizontalFace M A →₀ ℚ))) :
    primitiveGiantBlock M A z =
      (verticalBoundary M A z.1.1 + mixedVerticalBoundary M A z.1.2 + mixedVerticalBoundary M A z.2.1,
        (mixedHorizontalBoundary M A z.1.2,
          mixedHorizontalBoundary M A z.2.1 - horizontalFaceBoundary M A z.2.2)) := by
  rcases z with ⟨⟨v, t⟩, ⟨y, x⟩⟩
  exact primitiveGiantBlock_apply M A v t y x

/-- 元関係部分空間の同じVv+Dt代表による所属API。 -/
theorem mem_primitiveBaseImage (z : VerticalEdge M A →₀ ℚ) :
    z ∈ (LinearMap.ker (primitiveBaseConstraint M A)).map (primitiveBaseOutput M A) ↔
      ∃ (v : VerticalFace M A →₀ ℚ) (t : mixedCycles M A),
        verticalBoundary M A v + mixedVerticalBoundary M A t.1 = z := by
  constructor
  · rintro ⟨⟨v, t⟩, ht, hz⟩
    exact ⟨v, ⟨t, ht⟩, hz⟩
  · rintro ⟨v, t, hz⟩
    exact ⟨(v, t.1), t.2, hz⟩

/-- 原τ零の像包含は、元By=Hx制約核のDy像と同じ関係空間の包含。 -/
theorem primitiveVanishing_iff_image_le : PrimitiveTransgressionVanishing M A ↔
    (LinearMap.ker (primitiveConstraint M A)).map (primitiveLiftOutput M A) ≤
      (LinearMap.ker (primitiveBaseConstraint M A)).map (primitiveBaseOutput M A) := by
  rw [primitiveTransgressionVanishing_iff]
  constructor
  · intro hh z hz
    obtain ⟨⟨y, x⟩, he, rfl⟩ := hz
    have he' : mixedHorizontalBoundary M A y - horizontalFaceBoundary M A x = 0 :=
      (primitiveConstraint_apply M A y x).symm.trans he
    apply (mem_primitiveBaseImage M A _).mpr
    exact hh x y (sub_eq_zero.mp he')
  · intro hh x y he
    apply (mem_primitiveBaseImage M A _).mp
    apply hh
    refine ⟨(y, x), ?_, rfl⟩
    exact (primitiveConstraint_apply M A y x).trans (sub_eq_zero.mpr he)

/-- 一般混在の原τ零は、二つの原始blockと原By-Hxのrank等式と必要十分。 -/
theorem connectingTau_zero_iff_block_rank : connectingTau M A = 0 ↔
    finrank ℚ (LinearMap.range (primitiveGiantBlock M A)) =
      finrank ℚ (LinearMap.range (primitiveBaseBlock M A)) +
        finrank ℚ (LinearMap.range (primitiveConstraint M A)) := by
  rw [connectingTau_zero_iff_primitive, primitiveVanishing_iff_image_le]
  have hb := ConstrainedRank.range_prod_finrank
    (primitiveBaseOutput M A) (primitiveBaseConstraint M A)
  have hg := ConstrainedRank.range_prod_finrank
    ((primitiveBaseOutput M A).coprod (primitiveLiftOutput M A))
    ((primitiveBaseConstraint M A).prodMap (primitiveConstraint M A))
  rw [ConstrainedRank.constrainedCoprod_range, ConstrainedRank.range_prodMap_finrank] at hg
  constructor
  · intro hl
    rw [sup_eq_left.mpr hl] at hg
    change finrank ℚ (LinearMap.range (primitiveGiantBlock M A)) = _ at hg
    change finrank ℚ (LinearMap.range (primitiveBaseBlock M A)) = _ at hb
    omega
  · intro hr
    have he :
        finrank ℚ (((LinearMap.ker (primitiveBaseConstraint M A)).map
          (primitiveBaseOutput M A) ⊔
            (LinearMap.ker (primitiveConstraint M A)).map (primitiveLiftOutput M A)) :
              Submodule ℚ (VerticalEdge M A →₀ ℚ)) =
        finrank ℚ ((LinearMap.ker (primitiveBaseConstraint M A)).map
          (primitiveBaseOutput M A)) := by
      change finrank ℚ (LinearMap.range (primitiveGiantBlock M A)) = _ at hg
      change finrank ℚ (LinearMap.range (primitiveBaseBlock M A)) = _ at hb
      omega
    have hs := Submodule.eq_of_le_of_finrank_eq le_sup_left he.symm
    exact sup_le_iff.mp (le_of_eq hs.symm) |>.2

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.primitiveConstraint
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveConstraint_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBaseOutput
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBaseOutput_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBaseConstraint
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBaseConstraint_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveLiftOutput
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveLiftOutput_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBaseBlock
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveBaseBlock_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveGiantBlock
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveGiantBlock_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveGiantBlock_apply_all
#print axioms AAT.AG.AtlasCoefficientFiber.mem_primitiveBaseImage
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveVanishing_iff_image_le
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_zero_iff_block_rank
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
