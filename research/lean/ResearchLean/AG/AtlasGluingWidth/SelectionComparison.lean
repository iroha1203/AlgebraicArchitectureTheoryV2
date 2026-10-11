import ResearchLean.AG.AtlasGluingWidth.RegionShortExact
import ResearchLean.AG.FaceRelationSubdivision.SubsetComparison

/-! # 原始部分比較のセル選択への制限

G-136 A の交差比較を作る。二つの所属点は K1 台輸送で別々に移す。

## Implementation notes

選択の輸送は元の chart/Option edge/Option face に相対的な性質として記録する。
領域・和・交差の輸送は原始台から証明する。線形可換性を field に持たせず、
元端点等式と符号付き退化条件から微分の可換性を導く。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth
open ResolutionInvariance CanonicalResolution Cohomology TwoPhase FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)

/-- 選択の所属を原始セル像へ輸送する条件。 -/
structure SelectionCompatible (Sc : CellSelection Nc) (Sf : CellSelection Nf) : Prop where
  chart : ∀ c, Sf.chart c → Sc.chart (M.chartMap c)
  edge : ∀ e c, Sf.edge e → M.edgeMap e = some c → Sc.edge c
  face : ∀ f c, Sf.face f → M.faceMap f = some c → Sc.face c

namespace SelectionCompatible

/-- 領域選択の輸送は K1 台輸送から導出する。 -/
theorem region (A : Set qc.Target) :
    SelectionCompatible M (CellSelection.region Nc A)
      (CellSelection.region Nf (comparisonFactor qc qf h ⁻¹' A)) where
  chart := by
    rintro c ⟨t, ht, ha⟩
    exact ⟨comparisonFactor qc qf h t, M.chartSupport_compatible c t ht, ha⟩
  edge := by
    rintro e c ⟨t, ht, ha⟩ hm
    exact ⟨comparisonFactor qc qf h t, M.edgeSupport_compatible hm ht, ha⟩
  face := by
    rintro f c ⟨t, ht, ha⟩ hm
    exact ⟨comparisonFactor qc qf h t, M.faceSupport_compatible hm ht, ha⟩

/-- 真のセル交差の両所属を別々に輸送する。 -/
theorem inter {Sc Tc : CellSelection Nc} {Sf Tf : CellSelection Nf}
    (hs : SelectionCompatible M Sc Sf) (ht : SelectionCompatible M Tc Tf) :
    SelectionCompatible M (Sc.inter Tc) (Sf.inter Tf) where
  chart c hc := ⟨hs.chart c hc.1, ht.chart c hc.2⟩
  edge e c he hm := ⟨hs.edge e c he.1 hm, ht.edge e c he.2 hm⟩
  face f c hf hm := ⟨hs.face f c hf.1 hm, ht.face f c hf.2 hm⟩

/-- 元セル和の所属輸送。 -/
theorem union {Sc Tc : CellSelection Nc} {Sf Tf : CellSelection Nf}
    (hs : SelectionCompatible M Sc Sf) (ht : SelectionCompatible M Tc Tf) :
    SelectionCompatible M (Sc.union Tc) (Sf.union Tf) where
  chart c := Or.imp (hs.chart c) (ht.chart c)
  edge e c he hm := he.elim (fun he => Or.inl (hs.edge e c he hm))
    (fun he => Or.inr (ht.edge e c he hm))
  face f c hf hm := hf.elim (fun hf => Or.inl (hs.face f c hf hm))
    (fun hf => Or.inr (ht.face f c hf hm))

variable {M} {Sc : CellSelection Nc} {Sf : CellSelection Nf}
variable (hs : SelectionCompatible M Sc Sf)

/-- 選択された chart の原始像。 -/
def chartMap (c : Sf.Chart) : Sc.Chart := ⟨M.chartMap c.1, hs.chart c.1 c.2⟩

/-- 選択された edge の原始部分像。 -/
def edgeMap (e : Sf.Edge) : Option Sc.Edge :=
  match hm : M.edgeMap e.1 with
  | none => none
  | some c => some ⟨c, hs.edge e.1 c e.2 hm⟩

/-- 選択された face の原始部分像。 -/
def faceMap (f : Sf.Face) : Option Sc.Face :=
  match hm : M.faceMap f.1 with
  | none => none
  | some c => some ⟨c, hs.face f.1 c f.2 hm⟩

/-- 選択 chart 像の元セル名を読む API。 -/
@[simp] theorem chartMap_val (c : Sf.Chart) : (hs.chartMap c).1 = M.chartMap c.1 := rfl

/-- 退化 edge を零へ正規化する API。 -/
@[simp] theorem edgeMap_none (e : Sf.Edge) (hm : M.edgeMap e.1 = none) :
    hs.edgeMap e = none := by
  unfold edgeMap
  split <;> simp_all

/-- mapped edge を元セル名へ正規化する API。 -/
@[simp] theorem edgeMap_some (e : Sf.Edge) (c : Nc.nerve.EdgeComponent)
    (hm : M.edgeMap e.1 = some c) :
    hs.edgeMap e = some ⟨c, hs.edge e.1 c e.2 hm⟩ := by
  unfold edgeMap
  split
  · simp_all
  · rename_i mapped heq
    have he : mapped = c := Option.some.inj (heq.symm.trans hm)
    subst mapped
    rfl

/-- 退化 face を零へ正規化する API。 -/
@[simp] theorem faceMap_none (f : Sf.Face) (hm : M.faceMap f.1 = none) :
    hs.faceMap f = none := by
  unfold faceMap
  split <;> simp_all

/-- mapped face を元セル名へ正規化する API。 -/
@[simp] theorem faceMap_some (f : Sf.Face) (c : Nc.nerve.FaceComponent)
    (hm : M.faceMap f.1 = some c) :
    hs.faceMap f = some ⟨c, hs.face f.1 c f.2 hm⟩ := by
  unfold faceMap
  split
  · simp_all
  · rename_i mapped heq
    have he : mapped = c := Option.some.inj (heq.symm.trans hm)
    subst mapped
    rfl

/-- 同じ原始部分像は同じ選択部分像へ移る。 -/
theorem edgeMap_eq_of_raw_eq {e e' : Sf.Edge} (hm : M.edgeMap e.1 = M.edgeMap e'.1) :
    hs.edgeMap e = hs.edgeMap e' := by
  cases he : M.edgeMap e.1 with
  | none => rw [hs.edgeMap_none e he, hs.edgeMap_none e' (hm.symm.trans he)]
  | some c => rw [hs.edgeMap_some e c he, hs.edgeMap_some e' c (hm.symm.trans he)]

/-- 次数零の原始引き戻し。 -/
def pull0 : (Sc.Chart → ℚ) →ₗ[ℚ] (Sf.Chart → ℚ) where
  toFun x c := x (hs.chartMap c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 次数一の原始部分引き戻し。退化セルでは零。 -/
def pull1 : (Sc.Edge → ℚ) →ₗ[ℚ] (Sf.Edge → ℚ) where
  toFun x e := (hs.edgeMap e).elim 0 x
  map_add' x y := by funext e; cases hm : hs.edgeMap e <;> simp [hm]
  map_smul' r x := by funext e; cases hm : hs.edgeMap e <;> simp [hm]

/-- 次数二の原始部分引き戻し。退化セルでは零。 -/
def pull2 : (Sc.Face → ℚ) →ₗ[ℚ] (Sf.Face → ℚ) where
  toFun x f := (hs.faceMap f).elim 0 x
  map_add' x y := by funext f; cases hm : hs.faceMap f <;> simp [hm]
  map_smul' r x := by funext f; cases hm : hs.faceMap f <;> simp [hm]

/-- 次数零の評価式。 -/
@[simp] theorem pull0_apply (x : Sc.Chart → ℚ) (c : Sf.Chart) :
    hs.pull0 x c = x (hs.chartMap c) := rfl

/-- 次数一の評価式。 -/
@[simp] theorem pull1_apply (x : Sc.Edge → ℚ) (e : Sf.Edge) :
    hs.pull1 x e = (hs.edgeMap e).elim 0 x := rfl

/-- 次数二の評価式。 -/
@[simp] theorem pull2_apply (x : Sc.Face → ℚ) (f : Sf.Face) :
    hs.pull2 x f = (hs.faceMap f).elim 0 x := rfl

/-- 原始端点条件から d0 の可換性を導く。 -/
theorem pull_comm0 (x : Sc.Chart → ℚ) : hs.pull1 (Sc.d0 x) = Sf.d0 (hs.pull0 x) := by
  funext e
  rw [hs.pull1_apply, Sf.d0_apply, hs.pull0_apply, hs.pull0_apply]
  cases hm : M.edgeMap e.1 with
  | none =>
    have hc : hs.chartMap (Sf.left e) = hs.chartMap (Sf.right e) :=
      Subtype.ext (M.edge_none_fiber e.1 hm)
    rw [hs.edgeMap_none e hm, hc]
    simp
  | some c =>
    let ce : Sc.Edge := ⟨c, hs.edge e.1 c e.2 hm⟩
    have hl : hs.chartMap (Sf.left e) = Sc.left ce :=
      Subtype.ext (M.edge_some_left e.1 c hm)
    have hr : hs.chartMap (Sf.right e) = Sc.right ce :=
      Subtype.ext (M.edge_some_right e.1 c hm)
    rw [hs.edgeMap_some e c hm, hl, hr]
    exact Sc.d0_apply x ce

/-- 退化面の原始符号付き零和を選択 edge 値へ移す。 -/
theorem degenerate_face_sum (f : Sf.Face) (hm : M.faceMap f.1 = none)
    (x : Sc.Edge → ℚ) :
    hs.pull1 x (Sf.face0 f) - hs.pull1 x (Sf.face1 f) +
      hs.pull1 x (Sf.face2 f) = 0 := by
  rcases (optionCell_incidence_iff _ _ _).1 (M.face_none_incidence f.1 hm) with
    ⟨he0, he12⟩ | ⟨he2, he01⟩
  · have h12 := hs.edgeMap_eq_of_raw_eq (e := Sf.face1 f) (e' := Sf.face2 f) he12
    rw [hs.pull1_apply, hs.pull1_apply, hs.pull1_apply,
      hs.edgeMap_none (Sf.face0 f) he0, h12]
    simp
  · have h01 := hs.edgeMap_eq_of_raw_eq (e := Sf.face0 f) (e' := Sf.face1 f) he01
    rw [hs.pull1_apply, hs.pull1_apply, hs.pull1_apply,
      hs.edgeMap_none (Sf.face2 f) he2, h01]
    simp

/-- 原始面 incidence と退化零和から d1 の可換性を導く。 -/
theorem pull_comm1 (x : Sc.Edge → ℚ) : hs.pull2 (Sc.d1 x) = Sf.d1 (hs.pull1 x) := by
  funext f
  rw [hs.pull2_apply, Sf.d1_apply]
  cases hm : M.faceMap f.1 with
  | none =>
    rw [hs.faceMap_none f hm, hs.degenerate_face_sum f hm x]
    rfl
  | some c =>
    let cf : Sc.Face := ⟨c, hs.face f.1 c f.2 hm⟩
    have h0 : hs.edgeMap (Sf.face0 f) = some (Sc.face0 cf) := by
      rw [hs.edgeMap_some (Sf.face0 f) _ (M.face_some_edge0 f.1 c hm)]
      rfl
    have h1 : hs.edgeMap (Sf.face1 f) = some (Sc.face1 cf) := by
      rw [hs.edgeMap_some (Sf.face1 f) _ (M.face_some_edge1 f.1 c hm)]
      rfl
    have h2 : hs.edgeMap (Sf.face2 f) = some (Sc.face2 cf) := by
      rw [hs.edgeMap_some (Sf.face2 f) _ (M.face_some_edge2 f.1 c hm)]
      rfl
    rw [hs.faceMap_some f c hm, hs.pull1_apply, hs.pull1_apply, hs.pull1_apply, h0, h1, h2]
    exact Sc.d1_apply x cf

/-- 選択された原始比較の cochain 射。可換性は原始入力からの出力。 -/
def hom : ThreeCochainComplex.Hom Sc.complex Sf.complex where
  f0 := hs.pull0
  f1 := hs.pull1
  f2 := hs.pull2
  comm0 := hs.pull_comm0
  comm1 := hs.pull_comm1

/-- 選択比較の次数0 成分を評価射へ正規化する API。 -/
@[simp] theorem hom_f0 : hs.hom.f0 = hs.pull0 := rfl

/-- 選択比較の次数1 成分を評価射へ正規化する API。 -/
@[simp] theorem hom_f1 : hs.hom.f1 = hs.pull1 := rfl

/-- 選択比較の次数2 成分を評価射へ正規化する API。 -/
@[simp] theorem hom_f2 : hs.hom.f2 = hs.pull2 := rfl

variable {Tc : CellSelection Nc} {Tf : CellSelection Nf}
variable (ht : SelectionCompatible M Tc Tf)

/-- 次数0 の制限対は原始比較と可換。 -/
theorem union_square0 :
    ((hs.hom.f0).prodMap ht.hom.f0).comp (CellSelection.unionInclusion Sc Tc).f0 =
      (CellSelection.unionInclusion Sf Tf).f0.comp ((hs.union M ht).hom.f0) := by
  apply LinearMap.ext
  intro x
  simp only [hom_f0, CellSelection.unionInclusion_f0]
  simp only [LinearMap.comp_apply, LinearMap.prodMap_apply]
  erw [Cellwise.inclusion_apply Sc.chart Tc.chart x]
  erw [LinearMap.comp_apply]
  erw [Cellwise.inclusion_apply Sf.chart Tf.chart ((hs.union M ht).pull0 x)]
  apply Prod.ext
  · funext c
    rfl
  · funext c
    rfl

/-- 次数0 の差制限は原始比較と可換。 -/
theorem inter_square0 :
    ((hs.inter M ht).hom.f0).comp (CellSelection.intersectionDifference Sc Tc).f0 =
      (CellSelection.intersectionDifference Sf Tf).f0.comp
        ((hs.hom.f0).prodMap ht.hom.f0) := by
  apply LinearMap.ext
  intro x
  funext c
  simp only [hom_f0, CellSelection.intersectionDifference_f0]
  simp only [LinearMap.comp_apply]
  erw [Cellwise.difference_apply Sf.chart Tf.chart ((hs.pull0.prodMap ht.pull0) x) c]

/-- 次数1 の制限対は原始比較と可換。 -/
theorem union_square1 :
    ((hs.hom.f1).prodMap ht.hom.f1).comp (CellSelection.unionInclusion Sc Tc).f1 =
      (CellSelection.unionInclusion Sf Tf).f1.comp ((hs.union M ht).hom.f1) := by
  apply LinearMap.ext
  intro x
  simp only [hom_f1, CellSelection.unionInclusion_f1]
  simp only [LinearMap.comp_apply, LinearMap.prodMap_apply]
  erw [Cellwise.inclusion_apply Sc.edge Tc.edge x]
  erw [LinearMap.comp_apply]
  erw [Cellwise.inclusion_apply Sf.edge Tf.edge ((hs.union M ht).pull1 x)]
  apply Prod.ext
  · funext c
    dsimp only
    erw [hs.pull1_apply, (hs.union M ht).pull1_apply]
    cases hm : M.edgeMap c.1 with
    | none => rw [hs.edgeMap_none c hm, (hs.union M ht).edgeMap_none _ hm]; rfl
    | some e => rw [hs.edgeMap_some c e hm, (hs.union M ht).edgeMap_some _ e hm]; rfl
  · funext c
    dsimp only
    erw [ht.pull1_apply, (hs.union M ht).pull1_apply]
    cases hm : M.edgeMap c.1 with
    | none => rw [ht.edgeMap_none c hm, (hs.union M ht).edgeMap_none _ hm]; rfl
    | some e => rw [ht.edgeMap_some c e hm, (hs.union M ht).edgeMap_some _ e hm]; rfl

/-- 次数1 の差制限は原始比較と可換。 -/
theorem inter_square1 :
    ((hs.inter M ht).hom.f1).comp (CellSelection.intersectionDifference Sc Tc).f1 =
      (CellSelection.intersectionDifference Sf Tf).f1.comp
        ((hs.hom.f1).prodMap ht.hom.f1) := by
  apply LinearMap.ext
  intro x
  funext c
  simp only [hom_f1, CellSelection.intersectionDifference_f1]
  simp only [LinearMap.comp_apply]
  erw [Cellwise.difference_apply Sf.edge Tf.edge ((hs.pull1.prodMap ht.pull1) x) c]
  erw [(hs.inter M ht).pull1_apply]
  erw [LinearMap.prodMap_apply]
  dsimp only
  erw [hs.pull1_apply, ht.pull1_apply]
  cases hm : M.edgeMap c.1 with
  | none =>
    rw [(hs.inter M ht).edgeMap_none c hm, hs.edgeMap_none _ hm, ht.edgeMap_none _ hm]
    simp
  | some e =>
    rw [(hs.inter M ht).edgeMap_some c e hm, hs.edgeMap_some _ e hm, ht.edgeMap_some _ e hm]
    simp only [Option.elim_some]
    erw [Cellwise.difference_apply]

/-- 次数2 の制限対は原始比較と可換。 -/
theorem union_square2 :
    ((hs.hom.f2).prodMap ht.hom.f2).comp (CellSelection.unionInclusion Sc Tc).f2 =
      (CellSelection.unionInclusion Sf Tf).f2.comp ((hs.union M ht).hom.f2) := by
  apply LinearMap.ext
  intro x
  simp only [hom_f2, CellSelection.unionInclusion_f2]
  simp only [LinearMap.comp_apply, LinearMap.prodMap_apply]
  erw [Cellwise.inclusion_apply Sc.face Tc.face x]
  erw [LinearMap.comp_apply]
  erw [Cellwise.inclusion_apply Sf.face Tf.face ((hs.union M ht).pull2 x)]
  apply Prod.ext
  · funext c
    dsimp only
    erw [hs.pull2_apply, (hs.union M ht).pull2_apply]
    cases hm : M.faceMap c.1 with
    | none => rw [hs.faceMap_none c hm, (hs.union M ht).faceMap_none _ hm]; rfl
    | some e => rw [hs.faceMap_some c e hm, (hs.union M ht).faceMap_some _ e hm]; rfl
  · funext c
    dsimp only
    erw [ht.pull2_apply, (hs.union M ht).pull2_apply]
    cases hm : M.faceMap c.1 with
    | none => rw [ht.faceMap_none c hm, (hs.union M ht).faceMap_none _ hm]; rfl
    | some e => rw [ht.faceMap_some c e hm, (hs.union M ht).faceMap_some _ e hm]; rfl

/-- 次数2 の差制限は原始比較と可換。 -/
theorem inter_square2 :
    ((hs.inter M ht).hom.f2).comp (CellSelection.intersectionDifference Sc Tc).f2 =
      (CellSelection.intersectionDifference Sf Tf).f2.comp
        ((hs.hom.f2).prodMap ht.hom.f2) := by
  apply LinearMap.ext
  intro x
  funext c
  simp only [hom_f2, CellSelection.intersectionDifference_f2]
  simp only [LinearMap.comp_apply]
  erw [Cellwise.difference_apply Sf.face Tf.face ((hs.pull2.prodMap ht.pull2) x) c]
  erw [(hs.inter M ht).pull2_apply]
  erw [LinearMap.prodMap_apply]
  dsimp only
  erw [hs.pull2_apply, ht.pull2_apply]
  cases hm : M.faceMap c.1 with
  | none =>
    rw [(hs.inter M ht).faceMap_none c hm, hs.faceMap_none _ hm, ht.faceMap_none _ hm]
    simp
  | some e =>
    rw [(hs.inter M ht).faceMap_some c e hm, hs.faceMap_some _ e hm, ht.faceMap_some _ e hm]
    simp only [Option.elim_some]
    erw [Cellwise.difference_apply]

/-- 通常領域の比較は G-134 の同じ原始比較 Hom。 -/
theorem region_hom_eq (A : Set qc.Target) :
    (region M A).hom = M.aSubnerveComparisonHom A := by
  rfl

/-- 非空 chart を持つ細選択は空粗領域へ輸送できない。
SelectionCompatible の非成立例を任意の原始比較上で生成する API。 -/
theorem not_empty_coarse_univ_fine (c : Nf.nerve.Chart) :
    ¬ SelectionCompatible M (CellSelection.region Nc ∅) (CellSelection.region Nf Set.univ) := by
  intro hc
  obtain ⟨t, ht⟩ := Nf.chartSupport_nonempty c
  obtain ⟨s, _, hs⟩ := hc.chart c ⟨t, ht, Set.mem_univ t⟩
  exact hs

/-- 真のセル交差における原始粗細比較。 -/
def intersectionHom (A B : Set qc.Target) : ThreeCochainComplex.Hom
    (CellSelection.intersectionComplex Nc A B)
    (CellSelection.intersectionComplex Nf
      (comparisonFactor qc qf h ⁻¹' A) (comparisonFactor qc qf h ⁻¹' B)) :=
  ((region M A).inter M (region M B)).hom

end SelectionCompatible
end AAT.AG.AtlasGluingWidth
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
