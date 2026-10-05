import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyFreeMonoid
import Formal.Util.AssertStandardAxioms
/-! # 任意の有限署名多重度からの selected block 族

Implementation notes: 非零署名ごとに指定回数の Fin 添字を取り、標準 gamma
代表を割り当てる。有限型の Fin 同値で添字 universe を保つ。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SelectedFamilies
universe u v
variable {T : Type u} {Ω : Type v} (S : T → Set Ω) [Finite Ω]
/-- 指定多重度の元の署名・回数の添字。 -/
abbrev MultiplicityIndex (m : NonzeroSignature S →₀ ℕ) := Σ s, Fin (m s)
/-- 有限セルと各有限回数から元の署名回数添字の有限性を導く。 -/
instance multiplicityIndexFinite (m : NonzeroSignature S →₀ ℕ) : Finite (MultiplicityIndex S m) := by
  classical
  letI := Fintype.ofFinite (NonzeroSignature S)
  infer_instance
/-- 同じ署名・回数添字を元の target universe の有限添字へ同定する。 -/
def multiplicityIndexEquiv (m : NonzeroSignature S →₀ ℕ) :
    ULift.{u} (Fin (Nat.card (MultiplicityIndex S m))) ≃ MultiplicityIndex S m := by
  classical
  letI := Fintype.ofFinite (MultiplicityIndex S m)
  exact Equiv.ulift.trans ((Equiv.cast (by rw [Nat.card_eq_fintype_card])).trans (Fintype.equivFin _).symm)
/-- 任意の署名多重度から作る指定代表 block 族。 -/
def canonicalFamily (m : NonzeroSignature S →₀ ℕ) : Family S where
  Index := ULift.{u} (Fin (Nat.card (MultiplicityIndex S m)))
  finite := inferInstance
  subset i := SignatureGeometry.gamma S ((multiplicityIndexEquiv S m i).1).val
/-- 各元の指定代表の署名は指定非零署名そのものである。 -/
theorem canonical_sigma (m : NonzeroSignature S →₀ ℕ) (i : (canonicalFamily S m).Index) :
    SignatureGeometry.sigma S ((canonicalFamily S m).subset i) = ((multiplicityIndexEquiv S m i).1).val :=
  SignatureGeometry.sigma_gamma_signature S _
/-- 全 canonical 添字が非零であり、零 block の排除で多重度を失わない。 -/
def canonicalActiveEquiv (m : NonzeroSignature S →₀ ℕ) :
    Active S (canonicalFamily S m) ≃ MultiplicityIndex S m where
  toFun i := multiplicityIndexEquiv S m i.1
  invFun i := ⟨(multiplicityIndexEquiv S m).symm i,by
    rw [canonical_sigma,Equiv.apply_symm_apply]
    exact i.1.2⟩
  left_inv i := Subtype.ext ((multiplicityIndexEquiv S m).symm_apply_apply i.1)
  right_inv i := (multiplicityIndexEquiv S m).apply_symm_apply i
/-- canonical 非零添字同値は元の全署名を保持する。 -/
theorem canonical_active_signature (m : NonzeroSignature S →₀ ℕ) (i : Active S (canonicalFamily S m)) :
    activeSignature S (canonicalFamily S m) i = (canonicalActiveEquiv S m i).1 :=
  Subtype.ext (canonical_sigma S m i.1)
/-- 各署名の sigma 添字 fiber は指定回数の Fin と同値である。 -/
def multiplicityFiberEquiv (m : NonzeroSignature S →₀ ℕ) (s : NonzeroSignature S) :
    {i : MultiplicityIndex S m // i.1 = s} ≃ Fin (m s) where
  toFun i := i.2 ▸ i.1.2
  invFun j := ⟨⟨s,j⟩,rfl⟩
  left_inv := by rintro ⟨⟨t,j⟩,h⟩; cases h; rfl
  right_inv _ := rfl
/-- canonical block 族の各実署名 fiber から指定回数の Fin への同値。 -/
def canonicalFiberEquiv (m : NonzeroSignature S →₀ ℕ) (s : NonzeroSignature S) :
    Fiber S (canonicalFamily S m) s ≃ Fin (m s) :=
  (Equiv.subtypeEquiv (canonicalActiveEquiv S m)
    (fun i => by rw [canonical_active_signature])).trans (multiplicityFiberEquiv S m s)
/-- 指定回数から生成した block 族の多重度は元の関数に戻る。 -/
theorem canonical_multiplicity (m : NonzeroSignature S →₀ ℕ) : multiplicity S (canonicalFamily S m) = m := by
  ext s
  rw [multiplicity_apply,Nat.card_congr (canonicalFiberEquiv S m s),Nat.card_fin]
/-- 非零署名多重度の分類は任意の有限 support 関数を実現する。 -/
theorem multiplicity_surjective : Function.Surjective (multiplicity S) :=
  fun m => ⟨canonicalFamily S m,canonical_multiplicity S m⟩
/-- 同型類は自由可換モノイドの任意の元をちょうど実現する。 -/
theorem canonical_classifies (F : Family S) : Nonempty (Hom S F (canonicalFamily S (multiplicity S F))) :=
  (multiplicity_classifies S _ _).mp (canonical_multiplicity S _).symm
end AAT.AG.AtlasDefectComposition.SelectedFamilies
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilies
