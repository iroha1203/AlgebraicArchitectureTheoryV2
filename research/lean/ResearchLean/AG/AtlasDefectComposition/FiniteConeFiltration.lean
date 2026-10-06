import ResearchLean.AG.AtlasDefectComposition.CumulativeConeTower
import Mathlib.CategoryTheory.Subobject.Lattice
import Formal.Util.AssertStandardAxioms
/-! # 有限単射列と terminal model の実部分複体 filtration

Implementation notes: 元の非単射 tower を部分複体と宣言せず、構成済みモデルの実単射を使う。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
open scoped ZeroObject
namespace AAT.AG.AtlasDefectComposition.ConeTower
universe w
variable (C : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ)
/-- モデル tower の任意の順方向射は合成された実単射である。 -/
theorem modelDiagram_map_mono {i j : ℕ} (hij : i ≤ j) :
    Mono ((modelDiagram C).map (homOfLE hij)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero =>
    have he : (modelDiagram C).map (homOfLE hij) = 𝟙 (model C i) := by
      simpa only [Nat.add_zero,show homOfLE hij = 𝟙 i from Subsingleton.elim _ _]
        using (modelDiagram C).map_id i
    rw [he]
    constructor
    intro Z f g h
    simpa using h
  | succ k ih =>
    have hs : (modelDiagram C).map (homOfLE (show i ≤ i+(k+1) by omega)) =
        (modelDiagram C).map (homOfLE (show i ≤ i+k by omega)) ≫ inclusion C (i+k) := by
      rw [← Functor.ofSequence_map_homOfLE_succ (inclusion C)]
      exact (modelDiagram C).map_comp _ _
    rw [hs]
    letI := ih
    infer_instance
/-- 任意の有限段数で terminal model への実埋め込み。 -/
def embedding (n : ℕ) (i : Fin (n+1)) : model C i.val ⟶ model C n :=
  (modelDiagram C).map (homOfLE (Nat.le_of_lt_succ i.isLt))
/-- terminal model への全埋め込みは単射である。 -/
instance embedding_mono (n : ℕ) (i : Fin (n+1)) : Mono (embedding C n i) :=
  modelDiagram_map_mono C _
/-- terminal model の全有限段の実部分複体。 -/
def filtration (n : ℕ) (i : Fin (n+1)) : Subobject (model C n) := Subobject.mk (embedding C n i)
/-- 実filtrationの終段への射は指定underlying同型と実モデル埋め込みである。 -/
theorem filtration_arrow (n : ℕ) (i : Fin (n+1)) :
    (filtration C n i).arrow = (Subobject.underlyingIso (embedding C n i)).hom ≫ embedding C n i :=
  (Subobject.underlyingIso_hom_comp_eq_mk (embedding C n i)).symm
/-- 実部分複体は有限段順序に沿って包含する。 -/
theorem filtration_monotone (n : ℕ) : Monotone (filtration C n) := by
  intro i j hij
  exact Subobject.mk_le_mk_of_comm
    ((modelDiagram C).map (homOfLE (Fin.le_def.mp hij)))
    ((modelDiagram C).map_comp _ _).symm
/-- 有限filtrationの初段は実零部分複体である。 -/
theorem filtration_zero (n : ℕ) : filtration C n 0 = ⊥ := by
  apply Subobject.mk_eq_bot_iff_zero.mpr
  exact (isZero_zero _).eq_of_src _ _
/-- 有限filtrationの終段は terminal model 全体である。 -/
theorem filtration_last (n : ℕ) : filtration C n (Fin.last n) = ⊤ := by
  have hi : embedding C n (Fin.last n) = 𝟙 (model C n) := by
    simpa only [embedding,Fin.val_last,show homOfLE (Nat.le_refl n) = 𝟙 n from Subsingleton.elim _ _]
      using (modelDiagram C).map_id n
  haveI : IsIso (embedding C n (Fin.last n)) := by
    rw [hi]
    exact ⟨⟨𝟙 _,by simp⟩⟩
  exact Subobject.mk_eq_top_of_isIso _
/-- 有限部分複体 filtration の実隣接包含。 -/
def filtrationInclusion (n : ℕ) (i : Fin n) :
    (filtration C n i.castSucc : CochainComplex (ModuleCat.{w} ℚ) ℤ) ⟶
      (filtration C n i.succ : CochainComplex (ModuleCat.{w} ℚ) ℤ) :=
  Subobject.ofLE _ _ (filtration_monotone C n (Fin.le_def.mpr (Nat.le_succ i.val)))
/-- 実隣接包含はモデル包含を指定 underlying 同型で移した射である。 -/
theorem filtrationInclusion_eq (n : ℕ) (i : Fin n) :
    filtrationInclusion C n i =
      (Subobject.underlyingIso (embedding C n i.castSucc)).hom ≫ inclusion C i.val ≫
        (Subobject.underlyingIso (embedding C n i.succ)).inv := by
  apply Subobject.ofLE_mk_le_mk_of_comm
  simpa only [embedding,modelDiagram,Fin.val_castSucc,Fin.val_succ,
    Functor.ofSequence_map_homOfLE_succ] using
      ((modelDiagram C).map_comp (homOfLE (Nat.le_succ i.val))
        (homOfLE (show i.val+1 ≤ n by omega))).symm
/-- 実部分複体 filtration の実逐次商と指定隣接錐との同値。 -/
def filtrationQuotientEquiv (n : ℕ) (i : Fin n) :
    HomotopyEquiv (cokernel (filtrationInclusion C n i)) (mappingCone (adjacent C i.val)) :=
  (HomotopyEquiv.ofIso (cokernel.mapIso (inclusion C i.val) (filtrationInclusion C n i)
    (Subobject.underlyingIso (embedding C n i.castSucc)).symm
    (Subobject.underlyingIso (embedding C n i.succ)).symm
    (by simp [filtrationInclusion_eq])).symm).trans (successiveQuotientEquiv C i.val)
/-- 実filtration商の指定同値の公開射の式。underlying同型と実モデル商を保持する。 -/
theorem filtrationQuotientEquiv_hom (n : ℕ) (i : Fin n) :
    (filtrationQuotientEquiv C n i).hom =
      cokernel.map (filtrationInclusion C n i) (inclusion C i.val)
        (Subobject.underlyingIso (embedding C n i.castSucc)).hom
        (Subobject.underlyingIso (embedding C n i.succ)).hom
        (by simp [filtrationInclusion_eq]) ≫ (successiveQuotientEquiv C i.val).hom := rfl
/-- 有限 reading diagram を最後の段以後で一定にする指定 index functor。 -/
def clamp (n : ℕ) : ℕ ⥤ Fin (n+1) :=
  (show Monotone (fun k : ℕ => (⟨min k n,by omega⟩ : Fin (n+1))) from
    fun _ _ h => Fin.le_def.mpr (min_le_min_right n h)).functor
/-- 実有限 diagram の指定延長。 -/
def extend {n : ℕ} (D : Fin (n+1) ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) := clamp n ⋙ D
/-- 延長しても全有限段の元の複体そのものに一致する。 -/
@[simp] theorem extend_obj {n : ℕ}
    (D : Fin (n+1) ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ) (i : Fin (n+1)) :
    (extend D).obj i.val = D.obj i := by
  change D.obj ⟨min i.val n,_⟩ = D.obj i
  congr 1
  apply Fin.ext
  exact min_eq_left (Nat.le_of_lt_succ i.isLt)
end AAT.AG.AtlasDefectComposition.ConeTower
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ConeTower
