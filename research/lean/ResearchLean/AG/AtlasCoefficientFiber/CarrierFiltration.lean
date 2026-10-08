import ResearchLean.AG.AtlasCoefficientFiber.RawBlocks
import ResearchLean.AG.AtlasCoefficientFiber.CarrierFunctor

/-!
# G-135 B：原carrier次元の鎖filtration

## Implementation notes

次元は原carrier関手の対象をchart/edge/faceとして読む。次元零の鎖0次は
元の全chart加群とする。Lの0次微分像を使う案はcarrier filtrationと異なる
対象になるため採用しない。鎖1次・2次は同じ原包含の実像から生成する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 出現を保つincidence対象のセル次元。 -/
def incDimension {q : Reading Source} {N : TargetSupportedNerve q} {S : Set q.Target} :
    Inc N S → ℕ
  | .chart _ => 0
  | .edge _ => 1
  | .face _ => 2

/-- 原carrier関手が生成するセル次元。 -/
def carrierDimension (x : Inc Nf (comparisonFactor qc qf h ⁻¹' A)) : ℕ :=
  incDimension ((Carrier.preimageFunctor M A).obj x)

/-- 全chartのcarrier次元は零。 -/
@[simp] theorem carrierDimension_chart (c : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) :
    carrierDimension M A (.chart c) = 0 := by
  rw [carrierDimension, Carrier.preimageFunctor_obj_chart]
  rfl

/-- 辺のcarrier次元零は宣言上のnone像と同値。 -/
theorem carrierDimension_edge_zero_iff
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) :
    carrierDimension M A (.edge e) = 0 ↔ M.edgeMap e.1 = none := by
  cases he : M.edgeMap e.1 with
  | none => rw [carrierDimension, Carrier.preimageFunctor_obj_edge_of_none M A e he]; simp [incDimension]
  | some a => rw [carrierDimension, Carrier.preimageFunctor_obj_edge_of_some M A e a he]; simp [incDimension]

/-- 全辺のcarrier次元は高々一。 -/
theorem carrierDimension_edge_le_one
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) :
    carrierDimension M A (.edge e) ≤ 1 := by
  cases he : M.edgeMap e.1 with
  | none => rw [carrierDimension, Carrier.preimageFunctor_obj_edge_of_none M A e he]; simp [incDimension]
  | some a => rw [carrierDimension, Carrier.preimageFunctor_obj_edge_of_some M A e a he]; simp [incDimension]

/-- 面のcarrier次元零は原垂直面分類と同値。 -/
theorem carrierDimension_face_zero_iff
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) :
    carrierDimension M A (.face f) = 0 ↔
      M.faceMap f.1 = none ∧ M.edgeMap (Nf.nerve.faceEdge0 f.1) = none ∧
      M.edgeMap (Nf.nerve.faceEdge1 f.1) = none ∧ M.edgeMap (Nf.nerve.faceEdge2 f.1) = none := by
  cases hf : M.faceMap f.1 with
  | some F =>
    rw [carrierDimension, Carrier.preimageFunctor_obj_face_of_some M A f F hf]
    simp [incDimension]
  | none =>
    rw [carrierDimension, Carrier.preimageFunctor_obj_face]
    rcases degenerate_face_cases M f.1 hf with hv | ⟨e, h0, h1, h2⟩ | ⟨e, h0, h1, h2⟩
    · rw [Carrier.face_of_vertical M A _ _ f hf hv.1 hv.2.1]
      simp [incDimension, hv.1, hv.2.1, hv.2.2]
    · rw [Carrier.face_of_mixed_left M A _ _ f hf h0 e h1]
      simp [incDimension, h0, h1]
    · rw [Carrier.face_of_mixed_right M A _ _ f hf e h0]
      simp [incDimension, h0]

/-- 面のcarrier次元高々一は原none面分類と同値。 -/
theorem carrierDimension_face_le_one_iff
    (f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) :
    carrierDimension M A (.face f) ≤ 1 ↔ M.faceMap f.1 = none := by
  cases hf : M.faceMap f.1 with
  | some F =>
    rw [carrierDimension, Carrier.preimageFunctor_obj_face_of_some M A f F hf]
    simp [incDimension]
  | none =>
    rw [carrierDimension, Carrier.preimageFunctor_obj_face]
    rcases degenerate_face_cases M f.1 hf with hv | ⟨e, h0, h1, h2⟩ | ⟨e, h0, h1, h2⟩
    · rw [Carrier.face_of_vertical M A _ _ f hf hv.1 hv.2.1]; simp [incDimension]
    · rw [Carrier.face_of_mixed_left M A _ _ f hf h0 e h1]; simp [incDimension]
    · rw [Carrier.face_of_mixed_right M A _ _ f hf e h0]; simp [incDimension]

/-- 全セルのcarrier次元は高々二。 -/
theorem carrierDimension_le_two (x : Inc Nf (comparisonFactor qc qf h ⁻¹' A)) :
    carrierDimension M A x ≤ 2 := by
  unfold carrierDimension
  cases (Carrier.preimageFunctor M A).obj x <;> simp [incDimension]

/-- 次元高々pの鎖0次は元の全chart加群。 -/
def carrierChain0 (_p : ℕ) : Submodule ℚ (K0 Nf (comparisonFactor qc qf h ⁻¹' A)) := ⊤

/-- 次元零の辺だけを垂直辺実像として選ぶ。 -/
def carrierChain1 (p : ℕ) : Submodule ℚ (K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :=
  if p = 0 then LinearMap.range (verticalEdgeInclusion M A) else ⊤

/-- 次元零面・高々一面・全原面による三段の鎖2次。 -/
def carrierChain2 (p : ℕ) : Submodule ℚ (K2 Nf (comparisonFactor qc qf h ⁻¹' A)) :=
  if p = 0 then LinearMap.range (verticalFaceInclusion M A)
  else if p = 1 then degenerateL2 M A else ⊤

/-- carrier≤0の元面微分はcarrier≤0の垂直辺実像へ入る。 -/
theorem carrierChain2_boundary_le (p : ℕ) :
    (carrierChain2 M A p).map (chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)) ≤ carrierChain1 M A p := by
  by_cases hp : p = 0
  · subst p
    change (LinearMap.range (verticalFaceInclusion M A)).map (chainD2 Nf _) ≤
      LinearMap.range (verticalEdgeInclusion M A)
    rw [← LinearMap.range_comp, ← verticalBoundary_inclusion]
    exact LinearMap.range_comp_le_range _ _
  · simp only [carrierChain1, if_neg hp]
    exact le_top

/-- 原辺微分は元chart加群に入る。 -/
theorem carrierChain1_boundary_le (p : ℕ) :
    (carrierChain1 M A p).map (chainD1 Nf (comparisonFactor qc qf h ⁻¹' A)) ≤ carrierChain0 (Nf := Nf) A p :=
  le_top

/-- 鎖辺部分空間の増大性はpの原順序から導く。 -/
theorem carrierChain1_mono {p r : ℕ} (hpr : p ≤ r) : carrierChain1 M A p ≤ carrierChain1 M A r := by
  by_cases hr : r = 0
  · subst r
    have hp : p = 0 := Nat.eq_zero_of_le_zero hpr
    subst p
    exact le_refl _
  · simp only [carrierChain1, if_neg hr]
    exact le_top

/-- 鎖面部分空間の増大性。垂直面像から全none面像への包含は原分類。 -/
theorem carrierChain2_mono {p r : ℕ} (hpr : p ≤ r) : carrierChain2 M A p ≤ carrierChain2 M A r := by
  by_cases hr0 : r = 0
  · subst r
    have hp : p = 0 := Nat.eq_zero_of_le_zero hpr
    subst p
    exact le_refl _
  · by_cases hr1 : r = 1
    · subst r
      have hp : p = 0 ∨ p = 1 := by omega
      rcases hp with rfl | rfl
      · simpa only [carrierChain2, if_pos rfl, if_neg (by decide : (1 : ℕ) ≠ 0)] using
          verticalFaceInclusion_range_le_degenerate M A
      · exact le_refl _
    · simp only [carrierChain2, if_neg hr0, if_neg hr1]
      exact le_top

/-- 自由chainの実像は原基底像が生成するspanである。 -/
theorem freeRange_eq_span {I X : Type u} [AddCommGroup X] [Module ℚ X]
    (f : (I →₀ ℚ) →ₗ[ℚ] X) :
    LinearMap.range f = Submodule.span ℚ (Set.range fun i => f (Finsupp.single i 1)) := by
  apply le_antisymm
  · rw [freeRange_le_iff]
    intro i
    exact Submodule.subset_span ⟨i, rfl⟩
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact ⟨Finsupp.single i 1, rfl⟩

/-- 原carrier次元条件で選ぶ辺基底の集合。 -/
def carrierEdgeBasis (p : ℕ) : Set (K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :=
  {x | ∃ e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A),
    carrierDimension M A (.edge e) ≤ p ∧ Finsupp.single e 1 = x}

/-- 原carrier次元条件で選ぶ面基底の集合。 -/
def carrierFaceBasis (p : ℕ) : Set (K2 Nf (comparisonFactor qc qf h ⁻¹' A)) :=
  {x | ∃ f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A),
    carrierDimension M A (.face f) ≤ p ∧ Finsupp.single f 1 = x}

/-- 鎖carrier≤0の辺空間は同じ原carrier条件の基底span。 -/
theorem carrierChain1_zero_eq_span :
    carrierChain1 M A 0 = Submodule.span ℚ (carrierEdgeBasis M A 0) := by
  change LinearMap.range (verticalEdgeInclusion M A) = _
  rw [freeRange_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.1, (Nat.le_zero).mpr ((carrierDimension_edge_zero_iff M A e.1).mpr e.2),
      (verticalEdgeInclusion_single M A e 1).symm⟩
  · rintro ⟨e, he, rfl⟩
    have hn := (carrierDimension_edge_zero_iff M A e).mp ((Nat.le_zero).mp he)
    exact ⟨⟨e, hn⟩, verticalEdgeInclusion_single M A ⟨e, hn⟩ 1⟩

/-- 鎖carrier≤0の面空間は原垂直面を選ぶ同じ基底span。 -/
theorem carrierChain2_zero_eq_span :
    carrierChain2 M A 0 = Submodule.span ℚ (carrierFaceBasis M A 0) := by
  change LinearMap.range (verticalFaceInclusion M A) = _
  rw [freeRange_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.1, (Nat.le_zero).mpr ((carrierDimension_face_zero_iff M A f.1).mpr f.2),
      (verticalFaceInclusion_single M A f 1).symm⟩
  · rintro ⟨f, hf, rfl⟩
    have hn := (carrierDimension_face_zero_iff M A f).mp ((Nat.le_zero).mp hf)
    exact ⟨⟨f, hn⟩, verticalFaceInclusion_single M A ⟨f, hn⟩ 1⟩

/-- 鎖carrier≤1の面空間は原none面を選ぶ同じ基底span。 -/
theorem carrierChain2_one_eq_span :
    carrierChain2 M A 1 = Submodule.span ℚ (carrierFaceBasis M A 1) := by
  change LinearMap.range (degenerateFaceInclusion M A) = _
  rw [freeRange_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.1, (carrierDimension_face_le_one_iff M A f.1).mpr f.2,
      (degenerateFaceInclusion_single M A f 1).symm⟩
  · rintro ⟨f, hf, rfl⟩
    have hn := (carrierDimension_face_le_one_iff M A f).mp hf
    exact ⟨⟨f, hn⟩, degenerateFaceInclusion_single M A ⟨f, hn⟩ 1⟩

/-- 自由chain全体は全原セルの係数一基底で生成される。 -/
theorem freeChain_eq_span {I : Type u} :
    (⊤ : Submodule ℚ (I →₀ ℚ)) = Submodule.span ℚ (Set.range fun i : I => Finsupp.single i (1 : ℚ)) := by
  simpa only [LinearMap.range_id, LinearMap.id_apply] using
    freeRange_eq_span (LinearMap.id : (I →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ))

/-- 次元高々一で全原辺を得る。 -/
theorem carrierChain1_one_eq_span :
    carrierChain1 M A 1 = Submodule.span ℚ (carrierEdgeBasis M A 1) := by
  change (⊤ : Submodule ℚ _) = _
  rw [freeChain_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e, carrierDimension_edge_le_one M A e, rfl⟩
  · rintro ⟨e, _, rfl⟩
    exact ⟨e, rfl⟩

/-- 次元高々二で全原面を得る。 -/
theorem carrierChain2_two_eq_span :
    carrierChain2 M A 2 = Submodule.span ℚ (carrierFaceBasis M A 2) := by
  change (⊤ : Submodule ℚ _) = _
  rw [freeChain_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, carrierDimension_le_two M A (.face f), rfl⟩
  · rintro ⟨f, _, rfl⟩
    exact ⟨f, rfl⟩

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.incDimension
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDimension
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDimension_chart
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDimension_edge_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDimension_edge_le_one
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDimension_face_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDimension_face_le_one_iff
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDimension_le_two
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain0
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain1
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain2
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain2_boundary_le
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain1_boundary_le
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain1_mono
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain2_mono
#print axioms AAT.AG.AtlasCoefficientFiber.freeRange_eq_span
#print axioms AAT.AG.AtlasCoefficientFiber.carrierEdgeBasis
#print axioms AAT.AG.AtlasCoefficientFiber.carrierFaceBasis
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain1_zero_eq_span
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain2_zero_eq_span
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain2_one_eq_span
#print axioms AAT.AG.AtlasCoefficientFiber.freeChain_eq_span
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain1_one_eq_span
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain2_two_eq_span
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
