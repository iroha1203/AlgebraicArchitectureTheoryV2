import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-! # Descent and covering refinements -/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Pseudofunctor Opposite

universe u v a b

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a,b}) (J : GrothendieckTopology C)

/-- Descent of morphisms can be checked on covering refinements. Every
pullback of a refinement is again covering, so the same criterion gives
uniqueness on the overlaps used in the sheaf condition. -/
theorem isPrestack_of_covering_refinements
    (refineCover : ∀ ⦃X : C⦄ (R : Sieve X), R ∈ J X →
      ∃ S : Sieve X, S ∈ J X ∧ S ≤ R ∧ F.IsPrestackFor S.arrows) :
    F.IsPrestack J where
  isSheaf {X} M N := by
    rw [isSheaf_iff_isSheaf_of_type]
    intro Y R covering
    have baseCovering : Sieve.overEquiv Y R ∈ J Y.left := (J.mem_over_iff R).mp covering
    obtain ⟨S, coverS, leS, descentS⟩ := refineCover (Sieve.overEquiv Y R) baseCovering
    let T := (Sieve.overEquiv Y).symm S
    have restrict : T ≤ R := by
      apply (Sieve.overEquiv_le_overEquiv_iff T R).mp
      simpa only [T, Equiv.apply_symm_apply] using leS
    have sheafT : Presieve.IsSheafFor (F.presheafHom M N) T.arrows :=
      (show F.IsPrestackFor (Sieve.overEquiv Y T).arrows by simpa [T] using descentS).isSheafFor' Y M N
    apply Presieve.isSheafFor_subsieve_aux _ restrict sheafT
    intro Z f _
    obtain ⟨U, _, leU, descentU⟩ := refineCover (S.pullback f.left) (J.pullback_stable f.left coverS)
    let V := (Sieve.overEquiv Z).symm U
    have smaller : V ≤ T.pullback f := by
      rw [← Sieve.overEquiv_symm_pullback]
      intro W g hg
      exact leU _ hg
    have sheafV : Presieve.IsSheafFor (F.presheafHom M N) V.arrows :=
      (show F.IsPrestackFor (Sieve.overEquiv Z V).arrows by simpa [V] using descentU).isSheafFor' Z M N
    intro x t₁ t₂ h₁ h₂
    exact sheafV.isSeparatedFor _ _ _ (Presieve.isAmalgamation_restrict smaller x t₁ h₁)
      (Presieve.isAmalgamation_restrict smaller x t₂ h₂)

/-- Effective descent on a covering refinement of each covering sieve
implies effective descent for the full Grothendieck topology. -/
theorem isStack_of_effective_refinements
    (refineCover : ∀ ⦃X : C⦄ (R : Sieve X), R ∈ J X →
      ∃ S : Sieve X, S ∈ J X ∧ S ≤ R ∧ F.IsStackFor S.arrows) :
    F.IsStack J := by
  letI : F.IsPrestack J := isPrestack_of_covering_refinements F J (fun {_} R cover => by
    obtain ⟨S, covering, smaller, desc⟩ := refineCover R cover
    exact ⟨S, covering, smaller, desc.isPrestackFor⟩)
  refine ⟨fun R cover => ?_⟩
  obtain ⟨S, covering, smaller, desc⟩ := refineCover R cover
  exact (IsStackFor.of_le' F desc covering smaller).essSurj

/-- A descent comparison on a sieve still descends morphisms after refining
each of its arrows by a cover for a topology on which the fibers are a prestack. -/
theorem isPrestackFor_refining_arrows [F.IsPrestack J] {X : C} {R S : Sieve X}
    (smaller : S ≤ R) (base : F.IsPrestackFor R.arrows)
    (localCover : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → S.pullback f ∈ J Y) :
    F.IsPrestackFor S.arrows := by
  rw [F.isPrestackFor_iff_isSheafFor]
  intro M N
  let X' : Over X := Over.mk (𝟙 X)
  let R' := (Sieve.overEquiv X').symm R
  let S' := (Sieve.overEquiv X').symm S
  have sheafR : Presieve.IsSheafFor (F.presheafHom M N) R'.arrows :=
    (F.isPrestackFor_iff_isSheafFor R).1 base M N
  apply Presieve.isSheafFor_trans _ R' S' sheafR
  · intro Y f hf
    have inR : R' f := smaller _ hf
    rw [(Sieve.mem_iff_pullback_eq_top f).1 inR]
    exact (Presieve.isSheafFor_top _).isSeparatedFor
  · intro Y f hf
    have h := localCover f.left hf
    have descent := F.isPrestackFor' (J := J) _ h
    rw [← Sieve.overEquiv_symm_pullback]
    apply Pseudofunctor.IsPrestackFor.isSheafFor' Y _ M N
    simpa using descent

section BasisArrows

variable {X : C}

/-- Morphisms can be glued by checking a sieve locally on a generating family.
Uniqueness on pullbacks of the sieve guarantees compatibility of the local
amalgamations on overlaps of the generating arrows. -/
theorem isSheafFor_from_basis_arrows (P : Cᵒᵖ ⥤ Type a) (R : Presieve X) (S : Sieve X)
    (base : Presieve.IsSheafFor P R)
    (baseSeparated : ∀ ⦃Y : C⦄ (f : Y ⟶ X),
      Presieve.IsSeparatedFor P ((Sieve.generate R).pullback f).arrows)
    (localSheaf : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → Presieve.IsSheafFor P (S.pullback f).arrows)
    (separated : ∀ ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSeparatedFor P (S.pullback f).arrows) :
    Presieve.IsSheafFor P S.arrows := by
  have sep : Presieve.IsSeparatedFor P S.arrows := by
    simpa only [Sieve.pullback_id] using separated (𝟙 X)
  apply sep.isSheafFor
  intro x hx
  have same {Y : C} {f g : Y ⟶ X} (hf : S f) (hg : S g) (eq : f = g) :
      x f hf = x g hg := by
    subst g
    rfl
  let localFamily {Y : C} (f : Y ⟶ X) : Presieve.FamilyOfElements P (S.pullback f).arrows :=
    fun _ g hg => x (g ≫ f) hg
  have localCompatible {Y : C} (f : Y ⟶ X) : (localFamily f).Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro U V g k hg
    have step := hx.to_sieveCompatible (g ≫ f) k hg
    exact (same _ _ (Category.assoc k g f)).trans step
  let t : R.FamilyOfElements P := fun _ f hf => (localSheaf f hf).amalgamate _ (localCompatible f)
  have restrict {Y W : C} (f : Y ⟶ X) (hf : R f) (g : W ⟶ Y) (hg : S (g ≫ f)) :
      P.map g.op (t f hf) = x (g ≫ f) hg := (localSheaf f hf).valid_glue (localCompatible f) g hg
  have compatible : t.Compatible := by
    intro Y₀ Y₁ Z g₀ g₁ f₀ f₁ hf₀ hf₁ eq
    apply (separated (g₀ ≫ f₀)).ext
    intro W k hk
    have left : S ((k ≫ g₀) ≫ f₀) := by
      rw [Category.assoc]
      exact hk
    have right : S ((k ≫ g₁) ≫ f₁) := by
      rw [Category.assoc, ← eq]
      exact hk
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← FunctorToTypes.map_comp_apply, ← op_comp,
      restrict f₀ hf₀ _ left, restrict f₁ hf₁ _ right]
    exact same left right ((Category.assoc k g₀ f₀).trans
      ((congrArg (k ≫ ·) eq).trans (Category.assoc k g₁ f₁).symm))
  let m := base.amalgamate t compatible
  refine ⟨m, ?_⟩
  intro Y f hf
  apply (baseSeparated f).ext
  intro W k hk
  obtain ⟨V, g, r, hr, equal⟩ := hk
  have inS : S (g ≫ r) := equal.symm ▸ S.downward_closed hf k
  calc
    P.map k.op (P.map f.op m) = P.map (k ≫ f).op m := by
      rw [op_comp, FunctorToTypes.map_comp_apply]
    _ = P.map g.op (P.map r.op m) := by
      rw [← equal, op_comp, FunctorToTypes.map_comp_apply]
    _ = P.map g.op (t r hr) := congrArg (P.map g.op) (base.valid_glue compatible r hr)
    _ = x (g ≫ r) inS := restrict r hr g inS
    _ = P.map k.op (x f hf) :=
      (same inS (S.downward_closed hf k) equal).trans (hx.to_sieveCompatible f k hf)

end BasisArrows

end SHIGURE.SchemeDescent
