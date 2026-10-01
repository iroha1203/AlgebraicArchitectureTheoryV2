import ResearchLean.AG.RelativeRepairComposition.C17OriginalRepairs

/-! # Full actual W4 repair counts from the same generic subdivision maps
## Implementation notes

The cardinalities are transported along the generic equivalence of all actual repairs with the old repairs times the entire new kernel. Counting only a generated family would not establish the cardinality of the independent repair type.
-/
namespace AAT.AG.RelativeRepairComposition.C17SubdivisionInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction NativeAffine

/-- The entire new-object kernel has the same full F3 coordinate as the native affine projection kernel. -/
noncomputable def middleCoefficient :
    Additive (Kernel (GroupExtension.projection (projection (k := ZMod 3) (A := ZMod 3)))
      (GroupExtension.terminal (ZMod 3 ≃ₗ[ZMod 3] ZMod 3)) factors.middle) ≃+ ZMod 3 :=
  NativeAffine.coefficient geometry reference reference comparison linear_faces ()

/-- The independent new actual repair type has only retained original fixed names and both factors free. -/
abbrev NewRepairs := SupportedRepair splitTower (Subdivision.oldEdgeSet geometry chosen ∅)
/-- Every full actual split repair corresponds to its actual original h and arbitrary full first correction r. -/
noncomputable def splitRepairEquiv : NewRepairs ≃ (ZMod 3) × (ZMod 3) :=
  (Subdivision.supportedSolutionEquiv originalTower chosen factors ∅ (by exact not_false)).trans
    (Equiv.prodCongr oldRepairEquiv middleCoefficient.toEquiv)

/-- Every original actual repair parameter is restored with every full first-factor correction. -/
theorem all_split_restorations (h r : ZMod 3) :
    splitRepairEquiv.symm (h,r) =
      Subdivision.expandSupported originalTower chosen factors ∅
        (oldRepairEquiv.symm h) (middleCoefficient.symm r) := rfl

/-- All three independent actual old repairs are counted. -/
theorem old_repair_card : Nat.card OldRepairs = 3 := by
  rw [Nat.card_congr oldRepairEquiv,Nat.card_eq_fintype_card,ZMod.card]
/-- All nine independent actual new repairs are counted, including every first-factor restoration. -/
theorem new_repair_card : Nat.card NewRepairs = 9 := by
  rw [Nat.card_congr splitRepairEquiv,Nat.card_prod]
  simp only [Nat.card_eq_fintype_card,ZMod.card]

/-- The fixed original vertex forces every full original allowed gauge label to be zero. -/
theorem old_label_zero (b : supportedC0 originalTower Set.univ ∅) : b = 0 := by
  apply Subtype.ext
  funext v
  exact supportedC0_vertex_zero originalTower Set.univ ∅ b v (Set.mem_univ v)

/-- Every original native arrow carries exactly the full identity vertex label. -/
theorem old_hom_label_zero {R Q : RepairGroupoid originalTower Set.univ ∅} (f : R ⟶ Q) :
    f.1 = (1 : Multiplicative (supportedC0 originalTower Set.univ ∅)) := by
  apply Multiplicative.toAdd.injective
  exact old_label_zero (Multiplicative.toAdd f.1)

/-- Original actual repairs are isomorphic precisely when the entire actual repairs are equal. -/
theorem old_hom_iff (R Q : RepairGroupoid originalTower Set.univ ∅) :
    Nonempty (R ⟶ Q) ↔ R = Q := by
  constructor
  · rintro ⟨f⟩
    have hf := f.2
    rw [old_hom_label_zero f] at hf
    change (1 : Multiplicative (supportedC0 originalTower Set.univ ∅)) • R.back = Q.back at hf
    rw [one_smul] at hf
    cases R
    cases Q
    cases hf
    rfl
  · intro h
    subst Q
    exact ⟨𝟙 R⟩

/-- Every original full native hom-set has at most one arrow; no stabilizer label is discarded. -/
theorem old_hom_unique {R Q : RepairGroupoid originalTower Set.univ ∅} (f g : R ⟶ Q) : f = g := by
  apply Subtype.ext
  rw [old_hom_label_zero f,old_hom_label_zero g]

/-- The same generic collapse preserves the entire new native automorphism, which is the identity. -/
theorem new_hom_unique
    {R Q : RepairGroupoid splitTower (Sum.inl '' (Set.univ : Set geometry.Vertex))
      (Subdivision.oldEdgeSet geometry chosen ∅)} (f g : R ⟶ Q) : f = g := by
  apply (Subdivision.collapseHomEquiv originalTower chosen factors Set.univ ∅ (by exact not_false) R Q).injective
  exact old_hom_unique _ _

end AAT.AG.RelativeRepairComposition.C17SubdivisionInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C17SubdivisionInput
