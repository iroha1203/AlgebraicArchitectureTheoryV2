import ResearchLean.AG.SafeCoarseningOrder.Factorization
import ResearchLean.AG.AtlasDefectComposition.SubsetComposition
import ResearchLean.AG.AtlasDefectComposition.ComparisonLaws
import ResearchLean.AG.FaceRelationSubdivision.HereditarySpecialization

/-!
# G-137 原始商比較の実 cochain と H¹合成

A の任意の商と包含から生成した直接比較を、同じG-133/G-134の実比較へ接続する。
最粗側のAを中間側へ引き戻す。等号は元の三項複体の Hom と実 H¹写像である。

## Implementation notes

逆像合成の型輸送には既存 transportHom を用いる。任意の同次元同型を選ばず、
Cycle 1 の原始全record等号から直接比較の合成を導く。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
variable {S T V : Type} [Fintype V]
namespace PrimitiveInput
variable (M : PrimitiveInput S T V) {R R' : Coarsening T V} (h : R ≤ R')

/-- 任意商の恒等原始比較は既存恒等比較と全recordで一致。 -/
theorem factorMorphism_refl : M.factorMorphism (le_refl R) =
    TargetSupportedNerveMorphism.identityMorphism (M.quotientReading R) (M.quotientSupported R) := by
  apply morphism_ext
  · funext b
    exact M.factorMorphism_refl_chart b
  · funext e
    exact M.factorMorphism_refl_edge e
  · funext f
    exact f.elim

/-- 恒等比較のcanonical逆像は同じA。 -/
theorem identity_subset_preimage {S : Type} (q : Reading S) (A : Set q.Target) :
    comparisonFactor q q q.coarserThan_refl ⁻¹' A = A := by
  ext t
  simp only [Set.mem_preimage, TargetSupportedNerveMorphism.comparisonFactor_refl_apply]

/-- 任意商の恒等比較は実cochain Homでも恒等、canonical逆像の型を移送する。 -/
theorem factor_cochain_refl (A : Set (Quotient R.1)) :
    transportHom (congrArg (M.quotientSupported R).targetSubsetComplex
      (identity_subset_preimage (M.quotientReading R) A))
      ((M.factorMorphism (le_refl R)).aSubnerveComparisonHom A) =
      cochainId ((M.quotientSupported R).targetSubsetComplex A) := by
  rw [M.factorMorphism_refl]
  let q := M.quotientReading R
  let N := M.quotientSupported R
  let m := TargetSupportedNerveMorphism.identityMorphism q N
  have ht := targetSubsetComparisonHom_transport m A _ A (identity_subset_preimage q A)
    (fun _ ht => ht) (TargetSupportedNerveMorphism.identitySubsetMapsTo q A)
  change transportHom _ (m.targetSubsetComparisonHom A _ (fun _ ht => ht)) = _
  apply ht.trans
  apply cochain_ext
  · apply LinearMap.ext; intro x
    exact TargetSupportedNerveMorphism.identityMorphism_targetSubsetComparisonHom_f0 (q := q) (D := N) A x
  · apply LinearMap.ext; intro x
    exact TargetSupportedNerveMorphism.identityMorphism_targetSubsetComparisonHom_f1 (q := q) (D := N) A x
  · apply LinearMap.ext; intro x
    exact TargetSupportedNerveMorphism.identityMorphism_targetSubsetComparisonHom_f2 (q := q) (D := N) A x

/-- 同じ恒等Homは実H¹商で線形恒等写像となる。 -/
theorem factor_h1_refl (A : Set (Quotient R.1)) :
    (transportHom (congrArg (M.quotientSupported R).targetSubsetComplex
      (identity_subset_preimage (M.quotientReading R) A))
      ((M.factorMorphism (le_refl R)).aSubnerveComparisonHom A)).h1Map = LinearMap.id := by
  rw [M.factor_cochain_refl]
  exact cochainId_h1Map _

/-- fine→商の incidence 埋め込みは旧比較と全Homが一致する。 -/
theorem quotient_actualHom_old (A : Set (Quotient R.1)) :
    (M.quotientComparison R).aSubnerveComparisonHom A =
      (M.quotientMorphism R).aSubnerveComparisonHom A :=
  ofHereditary_aSubnerveComparisonHom _ _

/-- 同じfine→商比較のH¹商でも埋め込みは同じ線形写像。 -/
theorem quotient_actualH1_old (A : Set (Quotient R.1)) :
    ((M.quotientComparison R).aSubnerveComparisonHom A).h1Map =
      ((M.quotientMorphism R).aSubnerveComparisonHom A).h1Map :=
  ofHereditary_aSubnerveComparisonHom_h1Map _ _

/-- 直接商と二段商の実cochain合成。全三次数とcanonical逆像を保持する。 -/
theorem quotient_cochain_comp (A : Set (Quotient R'.1)) :
    transportHom (congrArg M.supported.targetSubsetComplex
      (comparisonFactor_preimage_comp (M.factor_coarser h) (M.quotient_coarser R) A))
      ((M.quotientMorphism R').aSubnerveComparisonHom A) =
    cochainComp ((M.factorMorphism h).aSubnerveComparisonHom A)
      ((M.quotientMorphism R).aSubnerveComparisonHom
        (comparisonFactor (M.quotientReading R') (M.quotientReading R)
          (M.factor_coarser h) ⁻¹' A)) := by
  rw [M.quotientMorphism_factor h]
  exact aSubnerveComparisonHom_comp (M.factorMorphism h) (M.quotientMorphism R) A

/-- 直接商比較の実H¹合成。次数0/1/2の同じHomから商へ降ろす。 -/
theorem quotient_h1_comp (A : Set (Quotient R'.1)) :
    (transportHom (congrArg M.supported.targetSubsetComplex
      (comparisonFactor_preimage_comp (M.factor_coarser h) (M.quotient_coarser R) A))
      ((M.quotientComparison R').aSubnerveComparisonHom A)).h1Map =
      ((M.quotientComparison R).aSubnerveComparisonHom
        (comparisonFactor (M.quotientReading R') (M.quotientReading R)
          (M.factor_coarser h) ⁻¹' A)).h1Map.comp
          ((M.factorMorphism h).aSubnerveComparisonHom A).h1Map := by
  rw [M.quotient_actualHom_old, M.quotient_actualHom_old]
  rw [M.quotientMorphism_factor h]
  exact aSubnerveComparisonHom_h1Map_comp (M.factorMorphism h) (M.quotientMorphism R) A

/-- 三分割間の実cochain合成も全三次数で一致。 -/
theorem factor_cochain_comp {R'' : Coarsening T V} (k : R' ≤ R'')
    (A : Set (Quotient R''.1)) :
    transportHom (congrArg (M.quotientSupported R).targetSubsetComplex
      (comparisonFactor_preimage_comp (M.factor_coarser k) (M.factor_coarser h) A))
      ((M.factorMorphism (le_trans h k)).aSubnerveComparisonHom A) =
    cochainComp ((M.factorMorphism k).aSubnerveComparisonHom A)
      ((M.factorMorphism h).aSubnerveComparisonHom
        (comparisonFactor (M.quotientReading R'') (M.quotientReading R')
          (M.factor_coarser k) ⁻¹' A)) := by
  rw [M.factorMorphism_comp h k]
  exact aSubnerveComparisonHom_comp (M.factorMorphism k) (M.factorMorphism h) A

/-- 三分割間の実H¹比較は同じ中間逆像で合成する。 -/
theorem factor_h1_comp {R'' : Coarsening T V} (k : R' ≤ R'')
    (A : Set (Quotient R''.1)) :
    (transportHom (congrArg (M.quotientSupported R).targetSubsetComplex
      (comparisonFactor_preimage_comp (M.factor_coarser k) (M.factor_coarser h) A))
      ((M.factorMorphism (le_trans h k)).aSubnerveComparisonHom A)).h1Map =
    ((M.factorMorphism h).aSubnerveComparisonHom
      (comparisonFactor (M.quotientReading R'') (M.quotientReading R')
        (M.factor_coarser k) ⁻¹' A)).h1Map.comp
          ((M.factorMorphism k).aSubnerveComparisonHom A).h1Map := by
  rw [M.factorMorphism_comp h k]
  exact aSubnerveComparisonHom_h1Map_comp (M.factorMorphism k) (M.factorMorphism h) A

end PrimitiveInput
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
