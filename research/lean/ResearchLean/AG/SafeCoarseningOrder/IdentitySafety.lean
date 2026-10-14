import ResearchLean.AG.SafeCoarseningOrder.IsomorphismCochains

/-!
# 恒等分割の同じ実比較の安全性

元primitiveと等号関係商の原始同型から実cochain同型を生成し、
その逆Homが原始商比較の全0/1/2成分と一致することを示す。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
variable {S T V : Type} [Fintype V]
namespace PrimitiveInput
variable (M : PrimitiveInput S T V)
omit [Fintype V] in
/-- 恒等商のcanonical逆像は生成原始同型のtarget逆像と同じ。 -/
theorem bot_preimage (A : Set (Quotient (⊥ : Setoid T))) :
    comparisonFactor (M.quotientReading (⊥ : Coarsening T V)) M.reading
      (M.quotient_coarser _) ⁻¹' A = M.botIso.target ⁻¹' A := by
  ext t
  simp only [Set.mem_preimage, M.quotient_factor]
  rfl
/-- 恒等粗化の元の実H¹比較は全Aで全単射。 -/
theorem safe_bot : M.Safe (⊥ : Coarsening T V) := by
  letI : Fintype (Quotient (⊥ : Setoid V)) := (M.quotientSupported (⊥ : Coarsening T V)).chartFintype
  intro B
  let a := M.botIso
  let e := a.subsetCochainEquiv B
  have ht := targetSubsetComparisonHom_transport (M.quotientMorphism (⊥ : Coarsening T V)) B _
    (a.target ⁻¹' B) (M.bot_preimage B) (fun _ h => h) (by
      intro t ht; rw [M.quotient_factor]; exact ht)
  have hh : (M.quotientMorphism (⊥ : Coarsening T V)).targetSubsetComparisonHom B
      (a.target ⁻¹' B) (by intro t ht; rw [M.quotient_factor]; exact ht) = e.symm.toHom := by
    apply cochain_ext
    · apply LinearMap.ext; intro x; funext v
      change (M.quotientMorphism (⊥ : Coarsening T V)).targetSubsetPullback0 B
        (a.target ⁻¹' B) _ x v = e.symm.toHom.f0 x v
      rw [TargetSupportedNerveMorphism.targetSubsetPullback0_apply,
        PrimitiveIso.subsetCochainEquiv_symm_f0_apply]
      rfl
    · apply LinearMap.ext; intro x; funext f
      change (M.quotientMorphism (⊥ : Coarsening T V)).targetSubsetPullback1 B
        (a.target ⁻¹' B) _ x f =
          e.symm.toHom.f1 x f
      rw [TargetSupportedNerveMorphism.targetSubsetPullback1_apply,
        PrimitiveIso.subsetCochainEquiv_symm_f1_apply]
      have hm : (M.quotientMorphism (⊥ : Coarsening T V)).edgeMap f.1 =
          some (a.edgeEquiv f.1) := by
        apply (M.quotientEdgeMap_eq_some _ _ _).mpr
        exact ⟨rfl,rfl⟩
      rw [TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_some _ _ _ _ _ _ hm,
        Option.elim_some]
      congr 1
    · apply LinearMap.ext; intro x; funext f; exact f.1.elim
  have hb := e.symm.toHom_h1Map_bijective
  rw [M.quotient_actualHom_old]
  rw [← hh, ← ht] at hb
  have htransport : ∀ {C D E : ThreeCochainComplex ℚ} (h : D = E)
      (f : ThreeCochainComplex.Hom C D),
      Function.Bijective (transportHom h f).h1Map ↔ Function.Bijective f.h1Map := by
    intro C D E h f; cases h; rfl
  exact (htransport _ _).mp hb
end PrimitiveInput
end AAT.AG.SafeCoarseningOrder

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
