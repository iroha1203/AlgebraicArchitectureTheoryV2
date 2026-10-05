import ResearchLean.AG.AtlasDefectComposition.SupportReconstruction
import ResearchLean.AG.AtlasDefectComposition.IndicatorSelectedBlock
import Formal.Util.AssertStandardAxioms
/-! # 非 bottom 署名の非空台と selected true Law block

Implementation notes: 非 bottom 署名の指定代表が非空であることを商の定義から放電し、
元の指示 Law の true block 同型へ接続する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SupportSignature
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r) (h : q.CoarserThan r)
/-- 非 bottom の実署名は元の非空 subset でしか実現されない。 -/
theorem nonbottom_nonempty {A : Set q.Target} (hA : sigma N E h A ≠ ⊥) : A.Nonempty := by
  by_contra he
  have hz : A = ∅ := Set.not_nonempty_iff_eq_empty.mp he
  apply hA
  rw [hz]
  exact map_bot (SignatureGeometry.sigmaHom _)
/-- 非 bottom 署名の canonical 閉集合代表は非空である。 -/
theorem representative_nonempty (s : Signature N E h) (hs : s ≠ ⊥) :
    (SupportFunctor.representative N E h s).Nonempty := by
  apply nonbottom_nonempty N E h
  change SignatureGeometry.sigma (family N E h) (SignatureGeometry.gamma (family N E h) s.val) ≠ ⊥
  rwa [SignatureGeometry.sigma_gamma_signature]
variable [Fintype Source] (M : TargetSupportedNerveMorphism q r h N E)
/-- 各非 bottom 署名の実比較錐は、同じ指定代表の指示 Law true block で実現する。 -/
def nonbottomIndicatorConeIso (s : Signature N E h) (hs : s ≠ ⊥) :=
  indicatorSelectedConeIso N E M (SupportFunctor.representative N E h s) (representative_nonempty N E h s hs)
end AAT.AG.AtlasDefectComposition.SupportSignature
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportSignature
