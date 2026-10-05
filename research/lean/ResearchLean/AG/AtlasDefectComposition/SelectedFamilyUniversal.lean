import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyAdditive
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Formal.Util.AssertStandardAxioms
/-! # selected block の加法的普遍性

Implementation notes: 単独 selected block の評価から署名の値を取り、
有限族の評価をその和として復元する。全 Law の合計からの一意性は主張しない。
-/
noncomputable section
open scoped BigOperators
namespace AAT.AG.AtlasDefectComposition.SelectedFamilies
universe u v w
variable {T : Type u} {Ω : Type v} (S : T → Set Ω)
variable {B : Type w} [AddCommMonoid B]
variable (v : SignatureGeometry.Signature S → B) (hv : v ⊥ = 0)
/-- 署名値を元の全有限添字で加算した評価。 -/
def valueSum (F : Family S) : B :=
  letI := Fintype.ofFinite F.Index
  ∑ i, v (SignatureGeometry.sigma S (F.subset i))
/-- valueSum の公開全添字評価 API。元の有限添字の和を表示する。 -/
theorem valueSum_eq_sum (F : Family S) : valueSum S v F =
    letI := Fintype.ofFinite F.Index; ∑ i, v (SignatureGeometry.sigma S (F.subset i)) := rfl
include hv in
/-- bottom 値零により、全添字の和は非零添字の和と一致する。 -/
theorem valueSum_active (F : Family S) : valueSum S v F =
    letI := Fintype.ofFinite F.Index; letI := Fintype.ofFinite (Active S F); ∑ i : Active S F, v (activeSignature S F i).val := by
  classical
  letI := Fintype.ofFinite F.Index
  letI := Fintype.ofFinite (Active S F)
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i => SignatureGeometry.sigma S (F.subset i) ≠ ⊥)
    (fun i => v (SignatureGeometry.sigma S (F.subset i)))
  have hz : (∑ i : {i : F.Index // ¬ SignatureGeometry.sigma S (F.subset i) ≠ ⊥},
      v (SignatureGeometry.sigma S (F.subset i.1))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [not_not.mp i.2,hv]
  rw [hz,add_zero] at hsplit
  have hi : Subtype.fintype (fun i : F.Index => SignatureGeometry.sigma S (F.subset i) ≠ ⊥) =
      Fintype.ofFinite (Active S F) := Subsingleton.elim _ _
  rw [hi] at hsplit
  exact hsplit.symm
include hv in
/-- 指定添字全単射は同じ全署名値の和を保存する。 -/
theorem valueSum_invariant {F G : Family S} (f : Hom S F G) : valueSum S v F = valueSum S v G := by
  classical
  letI := Fintype.ofFinite F.Index
  letI := Fintype.ofFinite G.Index
  letI := Fintype.ofFinite (Active S F)
  letI := Fintype.ofFinite (Active S G)
  rw [valueSum_active S v hv,valueSum_active S v hv]
  exact Fintype.sum_equiv f.equiv (fun i => v (activeSignature S F i).val)
    (fun i => v (activeSignature S G i).val)
    (fun i => congrArg (fun s : NonzeroSignature S => v s.val) (f.signature_eq i).symm)
/-- 元の添字非交和の署名値評価は加法である。 -/
theorem valueSum_sum (F G : Family S) : valueSum S v (sum S F G) = valueSum S v F + valueSum S v G := by
  classical
  letI := Fintype.ofFinite F.Index
  letI := Fintype.ofFinite G.Index
  have hi : Fintype.ofFinite (sum S F G).Index =
      inferInstanceAs (Fintype (F.Index ⊕ G.Index)) := Subsingleton.elim _ _
  unfold valueSum
  rw [hi]
  exact Fintype.sum_sum_type _
/-- 任意の bottom 値零の署名値から指定加法的評価を生成する。 -/
def evaluationOfValues : AdditiveEvaluation S B where
  eval := valueSum S v
  invariant := valueSum_invariant S v hv
  sum := valueSum_sum S v
  empty := by
    classical
    simp [valueSum,empty]
  zero_single A hA := by
    classical
    simp [valueSum,single,hA,hv]
/-- evaluationOfValues の公開評価 API。構成した署名値の和へ接続する。 -/
theorem evaluationOfValues_eval (F : Family S) : (evaluationOfValues S v hv).eval F = valueSum S v F := rfl
variable (I : AdditiveEvaluation S B)
/-- 加法的評価を単独 selected block の指定代表で読む。 -/
def signatureValue (s : SignatureGeometry.Signature S) : B :=
  I.eval (single S (SignatureGeometry.gamma S s.val))
/-- 加法的評価から得た bottom 値は零である。 -/
theorem signatureValue_bot : signatureValue S I ⊥ = 0 :=
  I.zero_single _ (SignatureGeometry.sigma_gamma_signature S ⊥)
/-- 任意の単独 subset block の値は元の実署名の値である。 -/
theorem signatureValue_sigma (A : Set T) : signatureValue S I (SignatureGeometry.sigma S A) = I.eval (single S A) :=
  single_eval_eq S I (SignatureGeometry.sigma_gamma_signature S (SignatureGeometry.sigma S A))
/-- すべての加法的評価は単独 selected block で決まる署名値の和である。 -/
theorem signatureValue_represents (F : Family S) : I.eval F = valueSum S (signatureValue S I) F := by
  classical
  letI := Fintype.ofFinite F.Index
  rw [eval_family S I F]
  apply Finset.sum_congr rfl
  intro i _
  exact (signatureValue_sigma S I (F.subset i)).symm
/-- 元の単独 selected block の値は指定値 v に戻る。 -/
theorem valueSum_single (A : Set T) : valueSum S v (single S A) = v (SignatureGeometry.sigma S A) := by
  classical
  simp [valueSum,single]
  exact one_nsmul _
/-- 署名値の一意性は全署名の実現と単独 selected block による。 -/
theorem signatureValue_unique (hrep : ∀ F, I.eval F = valueSum S v F) : v = signatureValue S I := by
  funext s
  obtain ⟨A,rfl⟩ := SignatureGeometry.sigma_surjective S s
  rw [signatureValue_sigma S I A,← valueSum_single S v A,← hrep]
/-- Eの固定した加法的普遍性。署名値は単独 selected block で一意に決まる。 -/
theorem additive_universal : ∃! v : SignatureGeometry.Signature S → B,
    v ⊥ = 0 ∧ ∀ F, I.eval F = valueSum S v F :=
  ⟨signatureValue S I,⟨signatureValue_bot S I,signatureValue_represents S I⟩,
    fun v h => signatureValue_unique S v I h.2⟩
end AAT.AG.AtlasDefectComposition.SelectedFamilies
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilies
