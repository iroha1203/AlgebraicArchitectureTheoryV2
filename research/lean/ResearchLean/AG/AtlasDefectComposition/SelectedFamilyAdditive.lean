import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyMultiplicity
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Formal.Util.AssertStandardAxioms
/-! # selected block 評価の単独 block 展開

Implementation notes: 指定射不変性と非交和加法性だけを評価の条件とする。
有限添字の empty/option 帰納法で単独 block の評価の和へ展開する。
-/
noncomputable section
open scoped BigOperators
namespace AAT.AG.AtlasDefectComposition.SelectedFamilies
universe u v w
variable {T : Type u} {Ω : Type v} (S : T → Set Ω)
/-- 指定圏における任意の可換加法モノイド値の加法的評価。 -/
structure AdditiveEvaluation (B : Type w) [AddCommMonoid B] where
  /-- 有限 selected block 族の評価。 -/
  eval : Family S → B
  /-- 非零署名を保つ指定添字射で評価は不変である。 -/
  invariant : ∀ {F G}, Hom S F G → eval F = eval G
  /-- 元の添字の非交和は加法へ移る。 -/
  sum : ∀ F G, eval (SelectedFamilies.sum S F G) = eval F + eval G
  /-- 空族の評価。 -/
  empty : eval (SelectedFamilies.empty S) = 0
  /-- 零署名の単独 selected block の評価。 -/
  zero_single : ∀ A, SignatureGeometry.sigma S A = ⊥ → eval (single S A) = 0
/-- 有限 subset 関数からの元の添字を保った selected block 族。 -/
def ofBlocks {ι : Type u} [Finite ι] (A : ι → Set T) : Family S where
  Index := ι
  finite := inferInstance
  subset := A
variable {B : Type w} [AddCommMonoid B] (I : AdditiveEvaluation S B)
/-- 同署名の単独 block の評価は指定射不変性で一致する。 -/
theorem single_eval_eq {A C : Set T} (he : SignatureGeometry.sigma S A = SignatureGeometry.sigma S C) :
    I.eval (single S A) = I.eval (single S C) := I.invariant (singleHom S he)
/-- 任意の有限添字の評価は単独 selected block 評価の和である。 -/
theorem eval_ofBlocks (ι : Type u) [Fintype ι] (A : ι → Set T) :
    I.eval (ofBlocks S A) = ∑ i, I.eval (single S (A i)) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ C : α → Set T, I.eval (ofBlocks S C) = ∑ i, I.eval (single S (C i)))
    ?_ ?_ ?_ ι A
  · intro α β _ e ih C
    letI := Fintype.ofEquiv β e.symm
    have hI := I.invariant (reindexHom S (F := ofBlocks S (C ∘ e)) (G := ofBlocks S C) e (fun _ => rfl))
    rw [← hI,ih]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  · intro C
    have hI := I.invariant (reindexHom S (F := ofBlocks S C) (G := empty S)
      (Equiv.refl _) (fun i => i.elim))
    rw [hI,I.empty]
    simp
  · intro α _ ih C
    have hI := I.invariant (reindexHom S
      (F := sum S (ofBlocks S (fun i => C (some i))) (single S (C none)))
      (G := ofBlocks S C) (Equiv.optionEquivSumPUnit α).symm
      (by rintro (a | b) <;> rfl))
    rw [← hI,I.sum,ih]
    simp only [Fintype.sum_option]
    exact add_comm _ _
/-- 任意の指定族を元の有限添字で単独 block 和へ展開する。 -/
theorem eval_family (F : Family S) :
    I.eval F = letI := Fintype.ofFinite F.Index; ∑ i, I.eval (single S (F.subset i)) := by
  classical
  letI := Fintype.ofFinite F.Index
  exact eval_ofBlocks S I F.Index F.subset
end AAT.AG.AtlasDefectComposition.SelectedFamilies
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilies
