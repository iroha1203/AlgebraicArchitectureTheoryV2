import ResearchLean.AG.AtlasCoefficientFiber.LocalFiber

/-!
# G-135 A §4：原始退化セルの自由部分空間

## Implementation notes

垂直辺、垂直面、混在面は同じ選択済み細セルのOption像から分類する。
包含は元のセル名の自由線形延長であり、混在面の境界を消去しない。
Lを先にΦの直和と定義する経路は、混在面が生成する追加境界を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u, u} qc} {Nf : TargetSupportedNerve.{u, u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- E_vは選択済み細辺の宣言上のnone逆像。粗loopへのmapped辺を含めない。 -/
abbrev VerticalEdge :=
  {e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) // M.edgeMap e.1 = none}

/-- F_vは面と全三辺の原始Option像がnoneである細面。 -/
abbrev VerticalFace :=
  {f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) //
    M.faceMap f.1 = none ∧ M.edgeMap (Nf.nerve.faceEdge0 f.1) = none ∧
      M.edgeMap (Nf.nerve.faceEdge1 f.1) = none ∧
      M.edgeMap (Nf.nerve.faceEdge2 f.1) = none}

/-- F_mは面がnone、負符号の辺出現がsomeである細面。二パターンは原始零和から導く。 -/
abbrev MixedFace :=
  {f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) //
    M.faceMap f.1 = none ∧ ∃ e, M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e}

/-- 退化面全体は原始faceMapのnone逆像。L₂の基底。 -/
abbrev DegenerateFace :=
  {f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) // M.faceMap f.1 = none}

/-- 退化面の負辺もnoneなら、残る二辺もnoneである。分類の所有API。 -/
theorem degenerateFace_vertical (f : DegenerateFace M A)
    (he : M.edgeMap (Nf.nerve.faceEdge1 f.1.1) = none) :
    M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = none ∧
      M.edgeMap (Nf.nerve.faceEdge1 f.1.1) = none ∧
      M.edgeMap (Nf.nerve.faceEdge2 f.1.1) = none := by
  rcases degenerate_face_cases M f.1.1 f.2 with hv | hl | hr
  · exact hv
  · rcases hl with ⟨e, _, h1, _⟩; cases he.symm.trans h1
  · rcases hr with ⟨e, _, h1, _⟩; cases he.symm.trans h1

/-- 混在面の正符号側の二つの原始パターン。面名と重複出現を保持する。 -/
theorem mixedFace_patterns (f : MixedFace M A) :
    ∃ e, M.edgeMap (Nf.nerve.faceEdge1 f.1.1) = some e ∧
      ((M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = none ∧
        M.edgeMap (Nf.nerve.faceEdge2 f.1.1) = some e) ∨
      (M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = some e ∧
        M.edgeMap (Nf.nerve.faceEdge2 f.1.1) = none)) := by
  rcases degenerate_face_cases M f.1.1 f.2.1 with hv | hl | hr
  · obtain ⟨e, he⟩ := f.2.2
    cases hv.2.1.symm.trans he
  · rcases hl with ⟨e, h0, h1, h2⟩
    exact ⟨e, h1, Or.inl ⟨h0, h2⟩⟩
  · rcases hr with ⟨e, h0, h1, h2⟩
    exact ⟨e, h1, Or.inr ⟨h0, h2⟩⟩

/-- 原始分類により退化面全体は垂直面と混在面の非交和。入力fieldにしない。 -/
def degenerateFaceEquiv : DegenerateFace M A ≃ VerticalFace M A ⊕ MixedFace M A where
  toFun f := if he : M.edgeMap (Nf.nerve.faceEdge1 f.1.1) = none then
    .inl ⟨f.1, f.2, degenerateFace_vertical M A f he⟩
  else .inr ⟨f.1, f.2, by
    cases hm : M.edgeMap (Nf.nerve.faceEdge1 f.1.1) with
    | none => exact False.elim (he hm)
    | some e => exact ⟨e, rfl⟩⟩
  invFun x := match x with
    | .inl f => ⟨f.1, f.2.1⟩
    | .inr f => ⟨f.1, f.2.1⟩
  left_inv f := by
    by_cases he : M.edgeMap (Nf.nerve.faceEdge1 f.1.1) = none
    · simp only [dif_pos he]
    · simp only [dif_neg he]
  right_inv x := by
    rcases x with f | f
    · simp only [dif_pos f.2.2.2.1]
    · have hn : ¬ M.edgeMap (Nf.nerve.faceEdge1 f.1.1) = none := by
        obtain ⟨e, he⟩ := f.2.2
        rw [he]; exact Option.some_ne_none _
      simp only [dif_neg hn]

/-- 分類同値の逆は元の同じ細面名を返す。下流で分類の実装を展開しないためのAPI。 -/
@[simp] theorem degenerateFaceEquiv_symm_val (x : VerticalFace M A ⊕ MixedFace M A) :
    ((degenerateFaceEquiv M A).symm x).1 = Sum.elim Subtype.val Subtype.val x := by
  cases x <;> rfl

/-- 垂直面の全辺出現はE_vへ属する。定義所有者API。 -/
theorem verticalFace_edge_none (f : VerticalFace M A) (i : Fin 3) :
    M.edgeMap (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i).1 = none := by
  fin_cases i
  · exact f.2.2.1
  · exact f.2.2.2.1
  · exact f.2.2.2.2

/-- 垂直面の原始三辺を垂直辺として読む。 -/
def verticalFaceEdge (f : VerticalFace M A) (i : Fin 3) : VerticalEdge M A :=
  ⟨faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i, verticalFace_edge_none M A f i⟩

/-- E_v所属の証明を剥かずに元の三辺出現を返すAPI。 -/
@[simp] theorem verticalFaceEdge_val (f : VerticalFace M A) (i : Fin 3) :
    (verticalFaceEdge M A f i).1 = faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i := rfl

/-- 元のセル名を保つ自由部分基底の包含。部分空間生成の共通所有API。 -/
def cellInclusion {I : Type u} (p : I → Prop) : ({i // p i} →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ Subtype.val

/-- 自由部分基底包含の基底像。 -/
@[simp] theorem cellInclusion_single {I : Type u} (p : I → Prop) (i : {i // p i}) (r : ℚ) :
    cellInclusion p (Finsupp.single i r) = Finsupp.single i.1 r :=
  Finsupp.mapDomain_single

/-- 自由部分基底の包含は、名前付きセルを同一視しないので単射。 -/
theorem cellInclusion_injective {I : Type u} (p : I → Prop) :
    Function.Injective (cellInclusion p) := Finsupp.mapDomain_injective Subtype.val_injective

/-- 自由加群からの線形像包含は、係数1の各原始基底像で検査できる。 -/
theorem freeRange_le_iff {I V : Type u} [AddCommGroup V] [Module ℚ V]
    (f : (I →₀ ℚ) →ₗ[ℚ] V) (S : Submodule ℚ V) :
    LinearMap.range f ≤ S ↔ ∀ i, f (Finsupp.single i 1) ∈ S := by
  constructor
  · intro hh i; exact hh ⟨_, rfl⟩
  · intro hh x hx
    rcases hx with ⟨x, rfl⟩
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
    | single i r =>
        rw [← Finsupp.smul_single_one, map_smul]
        exact S.smul_mem r (hh i)

/-- 原始基底集合の包含は同じ自由部分空間の包含を与える。 -/
theorem cellInclusion_range_mono {I : Type u} {p r : I → Prop}
    (hp : ∀ i, p i → r i) : LinearMap.range (cellInclusion p) ≤ LinearMap.range (cellInclusion r) := by
  rw [freeRange_le_iff]
  intro i
  exact ⟨Finsupp.single ⟨i.1, hp i.1 i.2⟩ 1, by simp⟩

/-- 原始基底の線形像をannihilateすることは、全基底像での零評価と同値。 -/
theorem annihilates_freeRange_iff {I V : Type u} [AddCommGroup V] [Module ℚ V]
    (f : (I →₀ ℚ) →ₗ[ℚ] V) (z : V →ₗ[ℚ] ℚ) :
    (∀ x ∈ LinearMap.range f, z x = 0) ↔ ∀ i, z (f (Finsupp.single i 1)) = 0 := by
  constructor
  · intro hh i; exact hh _ ⟨_, rfl⟩
  · intro hh x hx
    have hc : z.comp f = 0 := by
      apply Finsupp.lhom_ext
      intro i r
      rw [LinearMap.comp_apply, ← Finsupp.smul_single_one, map_smul, map_smul, hh]
      simp
    rcases hx with ⟨x, rfl⟩
    exact LinearMap.congr_fun hc x

/-- E_vの原支持K′₁への包含。 -/
def verticalEdgeInclusion : (VerticalEdge M A →₀ ℚ) →ₗ[ℚ]
    K1 Nf (comparisonFactor qc qf h ⁻¹' A) := cellInclusion _

/-- F_vの原支持K′₂への包含。 -/
def verticalFaceInclusion : (VerticalFace M A →₀ ℚ) →ₗ[ℚ]
    K2 Nf (comparisonFactor qc qf h ⁻¹' A) := cellInclusion _

/-- F_mの原支持K′₂への包含。 -/
def mixedFaceInclusion : (MixedFace M A →₀ ℚ) →ₗ[ℚ]
    K2 Nf (comparisonFactor qc qf h ⁻¹' A) := cellInclusion _

/-- F_v⊔F_mの原支持K′₂への包含。 -/
def degenerateFaceInclusion : (DegenerateFace M A →₀ ℚ) →ₗ[ℚ]
    K2 Nf (comparisonFactor qc qf h ⁻¹' A) := cellInclusion _

/-- 垂直辺包含の原始基底像。 -/
@[simp] theorem verticalEdgeInclusion_single (e : VerticalEdge M A) (r : ℚ) :
    verticalEdgeInclusion M A (Finsupp.single e r) = Finsupp.single e.1 r := cellInclusion_single _ _ _
/-- 垂直面包含の原始基底像。 -/
@[simp] theorem verticalFaceInclusion_single (f : VerticalFace M A) (r : ℚ) :
    verticalFaceInclusion M A (Finsupp.single f r) = Finsupp.single f.1 r := cellInclusion_single _ _ _
/-- 混在面包含の原始基底像。 -/
@[simp] theorem mixedFaceInclusion_single (f : MixedFace M A) (r : ℚ) :
    mixedFaceInclusion M A (Finsupp.single f r) = Finsupp.single f.1 r := cellInclusion_single _ _ _
/-- 全退化面包含の原始基底像。 -/
@[simp] theorem degenerateFaceInclusion_single (f : DegenerateFace M A) (r : ℚ) :
    degenerateFaceInclusion M A (Finsupp.single f r) = Finsupp.single f.1 r := cellInclusion_single _ _ _

/-- 垂直面の境界は元の三辺と同じ符号でE_v内に生成される。 -/
def verticalBoundary : (VerticalFace M A →₀ ℚ) →ₗ[ℚ] (VerticalEdge M A →₀ ℚ) :=
  freeMap fun f => Finsupp.single (verticalFaceEdge M A f 0) 1 -
    Finsupp.single (verticalFaceEdge M A f 1) 1 + Finsupp.single (verticalFaceEdge M A f 2) 1

/-- 垂直境界の基底評価。 -/
@[simp] theorem verticalBoundary_single (f : VerticalFace M A) (r : ℚ) :
    verticalBoundary M A (Finsupp.single f r) = r •
      (Finsupp.single (verticalFaceEdge M A f 0) 1 -
        Finsupp.single (verticalFaceEdge M A f 1) 1 + Finsupp.single (verticalFaceEdge M A f 2) 1) :=
  freeMap_single _ _ _

/-- E_v内の垂直境界を含めると、元の同じ支持chain微分になる。 -/
theorem verticalBoundary_inclusion :
    (verticalEdgeInclusion M A).comp (verticalBoundary M A) =
      (chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)).comp (verticalFaceInclusion M A) := by
  apply Finsupp.lhom_ext
  intro f r
  simp only [LinearMap.comp_apply, verticalBoundary_single, map_smul, map_sub, map_add,
    verticalEdgeInclusion_single, verticalFaceInclusion_single, chainD2_single, verticalFaceEdge_val]
  rfl

/-- 垂直辺の包含は元の細セル名を同一視しない。 -/
theorem verticalEdgeInclusion_injective : Function.Injective (verticalEdgeInclusion M A) := cellInclusion_injective _

/-- 垂直面の包含は元の細セル名を同一視しない。 -/
theorem verticalFaceInclusion_injective : Function.Injective (verticalFaceInclusion M A) := cellInclusion_injective _

/-- 混在面の包含は元の細セル名を同一視しない。 -/
theorem mixedFaceInclusion_injective : Function.Injective (mixedFaceInclusion M A) := cellInclusion_injective _

/-- 全退化面の包含は元の細セル名を同一視しない。 -/
theorem degenerateFaceInclusion_injective : Function.Injective (degenerateFaceInclusion M A) := cellInclusion_injective _

/-- 垂直面の自由部分空間は全退化面の部分空間へ含まれる。 -/
theorem verticalFaceInclusion_range_le_degenerate :
    LinearMap.range (verticalFaceInclusion M A) ≤ LinearMap.range (degenerateFaceInclusion M A) :=
  cellInclusion_range_mono (fun _ hf => hf.1)

/-- 混在面の自由部分空間は全退化面の部分空間へ含まれる。 -/
theorem mixedFaceInclusion_range_le_degenerate :
    LinearMap.range (mixedFaceInclusion M A) ≤ LinearMap.range (degenerateFaceInclusion M A) :=
  cellInclusion_range_mono (fun _ hf => hf.1)

/-- 全退化面の自由部分空間は、垂直面と混在面の和そのものである。 -/
theorem degenerateFaceInclusion_range_eq :
    LinearMap.range (degenerateFaceInclusion M A) =
      LinearMap.range (verticalFaceInclusion M A) ⊔ LinearMap.range (mixedFaceInclusion M A) := by
  apply le_antisymm
  · rw [freeRange_le_iff]
    intro f
    rw [degenerateFaceInclusion_single]
    cases he : M.edgeMap (Nf.nerve.faceEdge1 f.1.1) with
    | none =>
        let v : VerticalFace M A := ⟨f.1, f.2, degenerateFace_vertical M A f he⟩
        exact (le_sup_left : LinearMap.range (verticalFaceInclusion M A) ≤
          LinearMap.range (verticalFaceInclusion M A) ⊔ LinearMap.range (mixedFaceInclusion M A))
            ⟨Finsupp.single v 1, verticalFaceInclusion_single M A v 1⟩
    | some e =>
        let m : MixedFace M A := ⟨f.1, f.2, e, he⟩
        exact (le_sup_right : LinearMap.range (mixedFaceInclusion M A) ≤
          LinearMap.range (verticalFaceInclusion M A) ⊔ LinearMap.range (mixedFaceInclusion M A))
            ⟨Finsupp.single m 1, mixedFaceInclusion_single M A m 1⟩
  · exact sup_le (verticalFaceInclusion_range_le_degenerate M A)
      (mixedFaceInclusion_range_le_degenerate M A)

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.VerticalEdge
#print axioms AAT.AG.AtlasCoefficientFiber.VerticalFace
#print axioms AAT.AG.AtlasCoefficientFiber.MixedFace
#print axioms AAT.AG.AtlasCoefficientFiber.DegenerateFace
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateFace_vertical
#print axioms AAT.AG.AtlasCoefficientFiber.mixedFace_patterns
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateFaceEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateFaceEquiv_symm_val
#print axioms AAT.AG.AtlasCoefficientFiber.verticalFace_edge_none
#print axioms AAT.AG.AtlasCoefficientFiber.verticalFaceEdge
#print axioms AAT.AG.AtlasCoefficientFiber.verticalFaceEdge_val
#print axioms AAT.AG.AtlasCoefficientFiber.cellInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.cellInclusion_single
#print axioms AAT.AG.AtlasCoefficientFiber.cellInclusion_injective
#print axioms AAT.AG.AtlasCoefficientFiber.freeRange_le_iff
#print axioms AAT.AG.AtlasCoefficientFiber.cellInclusion_range_mono
#print axioms AAT.AG.AtlasCoefficientFiber.annihilates_freeRange_iff
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdgeInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.verticalFaceInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.mixedFaceInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateFaceInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdgeInclusion_single
#print axioms AAT.AG.AtlasCoefficientFiber.verticalFaceInclusion_single
#print axioms AAT.AG.AtlasCoefficientFiber.mixedFaceInclusion_single
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateFaceInclusion_single
#print axioms AAT.AG.AtlasCoefficientFiber.verticalBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.verticalBoundary_single
#print axioms AAT.AG.AtlasCoefficientFiber.verticalBoundary_inclusion
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdgeInclusion_injective
#print axioms AAT.AG.AtlasCoefficientFiber.verticalFaceInclusion_injective
#print axioms AAT.AG.AtlasCoefficientFiber.mixedFaceInclusion_injective
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateFaceInclusion_injective
#print axioms AAT.AG.AtlasCoefficientFiber.verticalFaceInclusion_range_le_degenerate
#print axioms AAT.AG.AtlasCoefficientFiber.mixedFaceInclusion_range_le_degenerate
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateFaceInclusion_range_eq
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
