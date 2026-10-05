import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyUniversal
import Mathlib.Algebra.Group.Nat.Hom
import Formal.Util.AssertStandardAxioms
/-! # 署名多重度の自由可換モノイド

Implementation notes: 非零署名の Finsupp ℕ に標準 liftAddHom を適用する。
元の selected block 評価へは実添字 fiber の濃度で接続する。
-/
noncomputable section
open scoped BigOperators
namespace AAT.AG.AtlasDefectComposition.SelectedFamilies
universe u v w
variable {T : Type u} {Ω : Type v} (S : T → Set Ω)
variable {B : Type w} [AddCommMonoid B]
/-- 非零署名値から自由可換モノイドの評価準同型を生成する。 -/
def freeEvaluation (v : NonzeroSignature S → B) : (NonzeroSignature S →₀ ℕ) →+ B :=
  Finsupp.liftAddHom (fun s => multiplesHom B (v s))
/-- 一つの非零署名を一回数えた評価は元の署名値である。 -/
@[simp] theorem freeEvaluation_single (v : NonzeroSignature S → B) (s : NonzeroSignature S) :
    freeEvaluation S v (Finsupp.single s 1) = v s := by
  rw [freeEvaluation,Finsupp.liftAddHom_apply_single,multiplesHom_apply,one_nsmul]
/-- 標準自由可換モノイドの準同型は全一重署名の評価で一意に決まる。 -/
theorem freeEvaluation_unique (v : NonzeroSignature S → B)
    (f : (NonzeroSignature S →₀ ℕ) →+ B) (hf : ∀ s, f (Finsupp.single s 1) = v s) :
    f = freeEvaluation S v := by
  apply Finsupp.liftAddHom.symm.injective
  funext s
  apply AddMonoidHom.ext_nat
  simpa only [Finsupp.liftAddHom_symm_apply_apply,freeEvaluation_single] using hf s
/-- 任意の可換加法モノイド値への一意延長という標準普遍性。 -/
theorem freeMonoid_universal (v : NonzeroSignature S → B) :
    ∃! f : (NonzeroSignature S →₀ ℕ) →+ B, ∀ s, f (Finsupp.single s 1) = v s :=
  ⟨freeEvaluation S v,freeEvaluation_single S v,fun f hf => freeEvaluation_unique S v f hf⟩
/-- 元の署名多重度の評価は selected block の元の添字和と一致する。 -/
theorem freeEvaluation_multiplicity [Finite Ω] (v : SignatureGeometry.Signature S → B)
    (hv : v ⊥ = 0) (F : Family S) :
    freeEvaluation S (fun s => v s.val) (multiplicity S F) = valueSum S v F := by
  classical
  letI := Fintype.ofFinite F.Index
  letI := Fintype.ofFinite (Active S F)
  letI := Fintype.ofFinite (NonzeroSignature S)
  rw [freeEvaluation,Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_fintype _ _ (fun s => by simp)]
  simp only [multiplesHom_apply,multiplicity_apply]
  rw [valueSum_active S v hv]
  have hsplit := Fintype.sum_fiberwise' (activeSignature S F) (fun s => v s.val)
  have hi (s : NonzeroSignature S) :
      (∑ _i : Fiber S F s, v s.val) = Nat.card (Fiber S F s) • v s.val := by
    simp only [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card]
  simpa only [hi] using hsplit
end AAT.AG.AtlasDefectComposition.SelectedFamilies
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilies
