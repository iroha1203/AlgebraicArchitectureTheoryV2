import ResearchLean.AG.RelativeRepairComposition.C17SplitRepairCounts
import Mathlib.CategoryTheory.IsomorphismClasses

/-! # W4's actual isomorphism classes and the separately fixed new vertex
## Implementation notes

Classes are Mathlib isIsomorphicSetoid quotients of the actual native action categories. The generic unit and counit prove the quotient comparison, while full Hom uniqueness proves every actual automorphism is identity. A coordinate equivalence alone does not establish isomorphism classes.
-/
namespace AAT.AG.RelativeRepairComposition.C17SubdivisionInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction NativeAffine

/-- The original actual groupoid fixes the original vertex. -/
abbrev OldCategory := RepairGroupoid originalTower Set.univ ∅
/-- The actual subdivided groupoid fixes only the original vertex. -/
abbrev NewCategory := RepairGroupoid splitTower (Sum.inl '' (Set.univ : Set geometry.Vertex))
  (Subdivision.oldEdgeSet geometry chosen ∅)
/-- Every original actual categorical object has its full original F3 repair parameter. -/
noncomputable def oldObjectEquiv : OldCategory ≃ ZMod 3 where
  toFun R := oldRepairEquiv R.back
  invFun h := ⟨(),oldRepairEquiv.symm h⟩
  left_inv R := by
    rcases R with ⟨u,R⟩
    cases u
    exact congrArg (fun R : OldRepairs => (⟨(),R⟩ : OldCategory)) (oldRepairEquiv.symm_apply_apply R)
  right_inv h := oldRepairEquiv.apply_symm_apply h

/-- The actual original isomorphism classes are all three original repair parameters. -/
noncomputable def oldClassEquiv : Quotient (isIsomorphicSetoid OldCategory) ≃ ZMod 3 where
  toFun := Quotient.lift oldObjectEquiv (by
    intro R Q h
    exact congrArg oldObjectEquiv ((old_hom_iff R Q).mp ⟨h.some.hom⟩))
  invFun h := Quotient.mk _ (oldObjectEquiv.symm h)
  left_inv R := Quotient.inductionOn R (fun R => by
    change Quotient.mk _ (oldObjectEquiv.symm (oldObjectEquiv R)) = Quotient.mk _ R
    rw [Equiv.symm_apply_apply])
  right_inv h := oldObjectEquiv.apply_symm_apply h

/-- The same generic actual subdivision equivalence, with the new intermediate vertex free. -/
noncomputable abbrev actualEquivalence : OldCategory ≌ NewCategory :=
  Subdivision.equivalence originalTower chosen factors Set.univ ∅ (by exact not_false)

/-- The full actual unit and counit induce the bijection of all new and old isomorphism classes. -/
noncomputable def subdivisionClassEquiv : Quotient (isIsomorphicSetoid NewCategory) ≃
    Quotient (isIsomorphicSetoid OldCategory) where
  toFun := Quotient.map actualEquivalence.inverse.obj (fun _ _ h => ⟨actualEquivalence.inverse.mapIso h.some⟩)
  invFun := Quotient.map actualEquivalence.functor.obj (fun _ _ h => ⟨actualEquivalence.functor.mapIso h.some⟩)
  left_inv R := Quotient.inductionOn R (fun R => Quotient.sound ⟨actualEquivalence.counitIso.app R⟩)
  right_inv R := Quotient.inductionOn R (fun R => Quotient.sound ⟨(actualEquivalence.unitIso.app R).symm⟩)

/-- Original actual repair classes number three. -/
theorem old_class_card : Nat.card (Quotient (isIsomorphicSetoid OldCategory)) = 3 := by
  rw [Nat.card_congr oldClassEquiv,Nat.card_eq_fintype_card,ZMod.card]
/-- New actual repair classes also number three, despite nine actual repairs. -/
theorem new_class_card : Nat.card (Quotient (isIsomorphicSetoid NewCategory)) = 3 := by
  rw [Nat.card_congr subdivisionClassEquiv,old_class_card]

/-- The separate fixed-new-vertex input has the same nine actual repairs but fixes both vertices. -/
abbrev FixedNewCategory := RepairGroupoid splitTower Set.univ (Subdivision.oldEdgeSet geometry chosen ∅)
/-- Every full label in the separate fixed-new-vertex input vanishes at every actual vertex. -/
theorem fixed_new_label_zero
    (b : supportedC0 splitTower Set.univ (Subdivision.oldEdgeSet geometry chosen ∅)) : b = 0 := by
  apply Subtype.ext
  funext v
  exact supportedC0_vertex_zero splitTower Set.univ _ b v (Set.mem_univ v)
/-- Every full actual arrow of the fixed-new-vertex input has the identity full label. -/
theorem fixed_new_hom_label_zero {R Q : FixedNewCategory} (f : R ⟶ Q) :
    f.1 = (1 : Multiplicative (supportedC0 splitTower Set.univ (Subdivision.oldEdgeSet geometry chosen ∅))) := by
  apply Multiplicative.toAdd.injective
  exact fixed_new_label_zero (Multiplicative.toAdd f.1)
/-- The separate fixed-new-vertex input makes every actual repair its own isomorphism class. -/
theorem fixed_new_hom_iff (R Q : FixedNewCategory) : Nonempty (R ⟶ Q) ↔ R = Q := by
  constructor
  · rintro ⟨f⟩
    have hf := f.2
    rw [fixed_new_hom_label_zero f] at hf
    change (1 : Multiplicative (supportedC0 splitTower Set.univ
      (Subdivision.oldEdgeSet geometry chosen ∅))) • R.back = Q.back at hf
    rw [one_smul] at hf
    cases R
    cases Q
    cases hf
    rfl
  · intro h
    subst Q
    exact ⟨𝟙 R⟩

/-- The separate fixed-new-vertex input retains the complete nine actual repair parameters. -/
noncomputable def fixedNewObjectEquiv : FixedNewCategory ≃ (ZMod 3) × (ZMod 3) where
  toFun R := splitRepairEquiv R.back
  invFun h := ⟨(),splitRepairEquiv.symm h⟩
  left_inv R := by
    rcases R with ⟨u,R⟩
    cases u
    exact congrArg (fun R : NewRepairs => (⟨(),R⟩ : FixedNewCategory)) (splitRepairEquiv.symm_apply_apply R)
  right_inv h := splitRepairEquiv.apply_symm_apply h
/-- The actual classes of the separate fixed-new-vertex input are all nine full split parameters. -/
noncomputable def fixedNewClassEquiv : Quotient (isIsomorphicSetoid FixedNewCategory) ≃
    (ZMod 3) × (ZMod 3) where
  toFun := Quotient.lift fixedNewObjectEquiv (by
    intro R Q h
    exact congrArg fixedNewObjectEquiv ((fixed_new_hom_iff R Q).mp ⟨h.some.hom⟩))
  invFun h := Quotient.mk _ (fixedNewObjectEquiv.symm h)
  left_inv R := Quotient.inductionOn R (fun R => by
    change Quotient.mk _ (fixedNewObjectEquiv.symm (fixedNewObjectEquiv R)) = Quotient.mk _ R
    rw [Equiv.symm_apply_apply])
  right_inv h := fixedNewObjectEquiv.apply_symm_apply h
/-- Fixing the new vertex gives nine actual isomorphism classes, showing why the free-vertex condition is necessary. -/
theorem fixed_new_class_card : Nat.card (Quotient (isIsomorphicSetoid FixedNewCategory)) = 9 := by
  rw [Nat.card_congr fixedNewClassEquiv,Nat.card_prod]
  simp only [Nat.card_eq_fintype_card,ZMod.card]

/-- Every original actual automorphism is the actual identity, with its full native label. -/
theorem old_aut_identity (R : OldCategory) (f : R ≅ R) : f = Iso.refl R := by
  apply Iso.ext
  exact old_hom_unique _ _
/-- Every new actual automorphism is the actual identity, with its entire fresh and original native label. -/
theorem new_aut_identity (R : NewCategory) (f : R ≅ R) : f = Iso.refl R := by
  apply Iso.ext
  exact new_hom_unique _ _

end AAT.AG.RelativeRepairComposition.C17SubdivisionInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C17SubdivisionInput
