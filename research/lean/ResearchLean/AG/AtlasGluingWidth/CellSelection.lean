import ResearchLean.AG.UniformInvariance.ASubnerveReduction
import Formal.Util.AssertStandardAxioms

/-! # 元セルの選択と真のセル交差

G-136 A の選択を、元のセル名の述語として構成する。
閉性は K1 の支持から生成し、和と交差で保存する。

## Implementation notes

セルは元セルの subtype とし、所属点をセル名に含めない。
一般選択の incidence 閉性を記録し、通常領域・和・交差では入力台から生成する。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth
open ResolutionInvariance CanonicalResolution Cohomology TwoPhase
universe u
variable {Source : Type u} {q : Reading Source}

/-- 元の incidence に閉じた三次数のセル選択。 -/
structure CellSelection (D : TargetSupportedNerve q) where
  chart : D.nerve.Chart → Prop
  edge : D.nerve.EdgeComponent → Prop
  face : D.nerve.FaceComponent → Prop
  edge_left : ∀ e, edge e → chart (D.nerve.edgeLeft e)
  edge_right : ∀ e, edge e → chart (D.nerve.edgeRight e)
  face_edge0 : ∀ f, face f → edge (D.nerve.faceEdge0 f)
  face_edge1 : ∀ f, face f → edge (D.nerve.faceEdge1 f)
  face_edge2 : ∀ f, face f → edge (D.nerve.faceEdge2 f)

namespace CellSelection
variable {D : TargetSupportedNerve q}

/-- 選択は三つの元セル述語によって決まる。 -/
@[ext] theorem ext {S T : CellSelection D}
    (h0 : S.chart = T.chart) (h1 : S.edge = T.edge) (h2 : S.face = T.face) : S = T := by
  cases S
  cases T
  cases h0
  cases h1
  cases h2
  rfl

/-- 各次数の K1 台が領域と交わる選択。閉性は台の包含から導く。 -/
def region (D : TargetSupportedNerve q) (A : Set q.Target) : CellSelection D where
  chart c := ∃ t, t ∈ D.chartSupport c ∧ t ∈ A
  edge e := ∃ t, t ∈ D.edgeSupport e ∧ t ∈ A
  face f := ∃ t, t ∈ D.faceSupport f ∧ t ∈ A
  edge_left := by
    rintro e ⟨t, ht, ha⟩
    exact ⟨t, ht.1, ha⟩
  edge_right := by
    rintro e ⟨t, ht, ha⟩
    exact ⟨t, ht.2, ha⟩
  face_edge0 := by
    rintro f ⟨t, ht, ha⟩
    exact ⟨t, ht.1, ha⟩
  face_edge1 := by
    rintro f ⟨t, ht, ha⟩
    exact ⟨t, ht.2.1, ha⟩
  face_edge2 := by
    rintro f ⟨t, ht, ha⟩
    exact ⟨t, ht.2.2, ha⟩

/-- 同じ元セルが両方に属する交差。所属の証拠点は別々に保持する。 -/
def inter (S T : CellSelection D) : CellSelection D where
  chart c := S.chart c ∧ T.chart c
  edge e := S.edge e ∧ T.edge e
  face f := S.face f ∧ T.face f
  edge_left e h := ⟨S.edge_left e h.1, T.edge_left e h.2⟩
  edge_right e h := ⟨S.edge_right e h.1, T.edge_right e h.2⟩
  face_edge0 f h := ⟨S.face_edge0 f h.1, T.face_edge0 f h.2⟩
  face_edge1 f h := ⟨S.face_edge1 f h.1, T.face_edge1 f h.2⟩
  face_edge2 f h := ⟨S.face_edge2 f h.1, T.face_edge2 f h.2⟩

/-- 元セルの和選択。 -/
def union (S T : CellSelection D) : CellSelection D where
  chart c := S.chart c ∨ T.chart c
  edge e := S.edge e ∨ T.edge e
  face f := S.face f ∨ T.face f
  edge_left e := Or.imp (S.edge_left e) (T.edge_left e)
  edge_right e := Or.imp (S.edge_right e) (T.edge_right e)
  face_edge0 f := Or.imp (S.face_edge0 f) (T.face_edge0 f)
  face_edge1 f := Or.imp (S.face_edge1 f) (T.face_edge1 f)
  face_edge2 f := Or.imp (S.face_edge2 f) (T.face_edge2 f)

/-- 任意の台と領域和の交わりを、二つの所属へ分解する。 -/
theorem meets_union {α : Type*} (support A B : Set α) :
    (∃ t, t ∈ support ∧ t ∈ A ∪ B) ↔
      (∃ t, t ∈ support ∧ t ∈ A) ∨ (∃ t, t ∈ support ∧ t ∈ B) := by
  constructor
  · rintro ⟨t, ht, ha | hb⟩
    · exact Or.inl ⟨t, ht, ha⟩
    · exact Or.inr ⟨t, ht, hb⟩
  · rintro (⟨t, ht, ha⟩ | ⟨t, ht, hb⟩)
    · exact ⟨t, ht, Or.inl ha⟩
    · exact ⟨t, ht, Or.inr hb⟩

/-- 領域和が選ぶ chart は二つの元セル選択の和。 -/
@[simp] theorem region_union_chart (D : TargetSupportedNerve q) (A B : Set q.Target)
    (c : D.nerve.Chart) :
    (region D (A ∪ B)).chart c ↔
      ((region D A).union (region D B)).chart c :=
  meets_union (D.chartSupport c) A B

/-- 領域和が選ぶ edge は二つの元セル選択の和。 -/
@[simp] theorem region_union_edge (D : TargetSupportedNerve q) (A B : Set q.Target)
    (c : D.nerve.EdgeComponent) :
    (region D (A ∪ B)).edge c ↔
      ((region D A).union (region D B)).edge c :=
  meets_union (D.edgeSupport c) A B

/-- 領域和が選ぶ face は二つの元セル選択の和。 -/
@[simp] theorem region_union_face (D : TargetSupportedNerve q) (A B : Set q.Target)
    (c : D.nerve.FaceComponent) :
    (region D (A ∪ B)).face c ↔
      ((region D A).union (region D B)).face c :=
  meets_union (D.faceSupport c) A B

/-- 全三次数で領域和と元セル和を同定する。 -/
theorem region_union (D : TargetSupportedNerve q) (A B : Set q.Target) :
    region D (A ∪ B) = (region D A).union (region D B) := by
  apply ext
  · funext c; exact propext (region_union_chart D A B c)
  · funext c; exact propext (region_union_edge D A B c)
  · funext c; exact propext (region_union_face D A B c)

/-- 選択された元 chart 型。 -/
abbrev Chart (S : CellSelection D) := {c // S.chart c}
/-- 選択された元 edge 型。 -/
abbrev Edge (S : CellSelection D) := {e // S.edge e}
/-- 選択された元 face 型。 -/
abbrev Face (S : CellSelection D) := {f // S.face f}

/-- 選択されたセルの元 incidence。 -/
def left (S : CellSelection D) (c : S.Edge) : S.Chart :=
  ⟨D.nerve.edgeLeft c.1, S.edge_left c.1 c.2⟩

/-- 選択されたセルの元 incidence。 -/
def right (S : CellSelection D) (c : S.Edge) : S.Chart :=
  ⟨D.nerve.edgeRight c.1, S.edge_right c.1 c.2⟩

/-- 選択されたセルの元 incidence。 -/
def face0 (S : CellSelection D) (c : S.Face) : S.Edge :=
  ⟨D.nerve.faceEdge0 c.1, S.face_edge0 c.1 c.2⟩

/-- 選択されたセルの元 incidence。 -/
def face1 (S : CellSelection D) (c : S.Face) : S.Edge :=
  ⟨D.nerve.faceEdge1 c.1, S.face_edge1 c.1 c.2⟩

/-- 選択されたセルの元 incidence。 -/
def face2 (S : CellSelection D) (c : S.Face) : S.Edge :=
  ⟨D.nerve.faceEdge2 c.1, S.face_edge2 c.1 c.2⟩

/-- 元の右端値−左端値。 -/
def d0 (S : CellSelection D) : (S.Chart → ℚ) →ₗ[ℚ] (S.Edge → ℚ) where
  toFun x e := x (S.right e) - x (S.left e)
  map_add' x y := by ext e; simp; ring
  map_smul' a x := by ext e; simp; ring

/-- 三つの元面 incidence の符号付き和。 -/
def d1 (S : CellSelection D) : (S.Edge → ℚ) →ₗ[ℚ] (S.Face → ℚ) where
  toFun x f := x (S.face0 f) - x (S.face1 f) + x (S.face2 f)
  map_add' x y := by ext f; simp; ring
  map_smul' a x := by ext f; simp; ring

/-- 原始 d0 を右端値−左端値へ正規化する評価 API。 -/
@[simp] theorem d0_apply (S : CellSelection D) (x : S.Chart → ℚ) (e : S.Edge) :
    S.d0 x e = x (S.right e) - x (S.left e) := rfl

/-- 原始 d1 を三 incidence の符号付き和へ正規化する評価 API。 -/
@[simp] theorem d1_apply (S : CellSelection D) (x : S.Edge → ℚ) (f : S.Face) :
    S.d1 x f = x (S.face0 f) - x (S.face1 f) + x (S.face2 f) := rfl

/-- 原始面端点等式から微分の合成が零。 -/
theorem d1_d0 (S : CellSelection D) (x : S.Chart → ℚ) : S.d1 (S.d0 x) = 0 := by
  funext f
  have h0 : S.left (S.face0 f) = S.left (S.face1 f) :=
    Subtype.ext (D.faceEdge0_left f.1)
  have h1 : S.right (S.face0 f) = S.left (S.face2 f) :=
    Subtype.ext (D.faceEdge0_right f.1)
  have h2 : S.right (S.face1 f) = S.right (S.face2 f) :=
    Subtype.ext (D.faceEdge1_right f.1)
  change (x (S.right (S.face0 f)) - x (S.left (S.face0 f))) -
    (x (S.right (S.face1 f)) - x (S.left (S.face1 f))) +
    (x (S.right (S.face2 f)) - x (S.left (S.face2 f))) = 0
  rw [h0, h1, h2]
  ring

/-- 選択した元セル上の有限有理係数複体。 -/
def complex (S : CellSelection D) : ThreeCochainComplex ℚ := by
  classical
  letI : Fintype S.Chart := Fintype.ofFinite _
  letI : Fintype S.Edge := Fintype.ofFinite _
  letI : Fintype S.Face := Fintype.ofFinite _
  exact {
    C0 := S.Chart → ℚ
    C1 := S.Edge → ℚ
    C2 := S.Face → ℚ
    d0 := S.d0
    d1 := S.d1
    d1_comp_d0 := S.d1_d0 }

/-- 選択複体の d0 は元端点の値の差。 -/
@[simp] theorem complex_d0_apply (S : CellSelection D) (x : S.complex.C0) (e : S.Edge) :
    S.complex.d0 x e = x (S.right e) - x (S.left e) := rfl

/-- 選択複体の d1 は元面の三 incidence の符号付き和。 -/
@[simp] theorem complex_d1_apply (S : CellSelection D) (x : S.complex.C1) (f : S.Face) :
    S.complex.d1 x f = x (S.face0 f) - x (S.face1 f) + x (S.face2 f) := rfl

/-- 通常領域では既存 targetSubsetComplex と同じ三次数・微分を持つ。 -/
theorem region_complex (D : TargetSupportedNerve q) (A : Set q.Target) :
    (region D A).complex = D.targetSubsetComplex A := by
  rfl

end CellSelection
end AAT.AG.AtlasGluingWidth
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
