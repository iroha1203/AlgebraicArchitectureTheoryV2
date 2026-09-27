import ResearchLean.AG.OperationRepair.Classification

/-!
# Repair quotient classes and their order

The quotient of repair objects by equality of source kernels is the concrete
isomorphism-class presentation used by GOAL B. The relation is compared with
actual structure-preserving isomorphisms below.
-/

namespace AAT.AG.OperationRepair

universe u v w z z' z''

variable {S : Type u} {E : Type v} {O : Type w}
variable (T : OperationSystem S E) (observe : S → O) (R : S → S → Prop)

/-- An actual structure-preserving isomorphism of repair quotients. -/
structure RepairIso (q : RepairQuotient.{u, v, w, z} T observe R)
    (q' : RepairQuotient.{u, v, w, z'} T observe R) where
  hom : RepairHom T observe R q q'
  inv : RepairHom T observe R q' q
  left_inv : ∀ x, inv.toFun (hom.toFun x) = x
  right_inv : ∀ y, hom.toFun (inv.toFun y) = y

/-- Actual repair isomorphism is equivalent to equality of source kernels,
also when the quotient target universes differ. -/
theorem repairIso_iff_kernel_eq
    {q : RepairQuotient.{u, v, w, z} T observe R}
    {q' : RepairQuotient.{u, v, w, z'} T observe R} :
    Nonempty (RepairIso T observe R q q') ↔
      q.kernel.setoid = q'.kernel.setoid := by
  constructor
  · rintro ⟨iso⟩
    apply le_antisymm
    · exact (RepairHom.nonempty_iff_kernel_le.mp ⟨iso.hom⟩)
    · exact (RepairHom.nonempty_iff_kernel_le.mp ⟨iso.inv⟩)
  · intro h
    have hforward : q.kernel ≤ q'.kernel := by
      change q.kernel.setoid ≤ q'.kernel.setoid
      rw [h]
    have hbackward : q'.kernel ≤ q.kernel := by
      change q'.kernel.setoid ≤ q.kernel.setoid
      rw [h]
    obtain ⟨f⟩ := RepairHom.nonempty_iff_kernel_le.mpr hforward
    obtain ⟨g⟩ := RepairHom.nonempty_iff_kernel_le.mpr hbackward
    refine ⟨{
      hom := f
      inv := g
      left_inv := ?_
      right_inv := ?_ }⟩
    · intro x
      obtain ⟨s, rfl⟩ := q.surjective x
      rw [f.source_comm, g.source_comm]
    · intro y
      obtain ⟨s, rfl⟩ := q'.surjective y
      rw [g.source_comm, f.source_comm]

/-- Every repair quotient, in any target universe, is isomorphic over the
source to the standard quotient by its kernel. -/
theorem canonicalRepairIso
    (q : RepairQuotient.{u, v, w, z} T observe R) :
    Nonempty (RepairIso T observe R
      (quotientRepair T observe R q.kernel
        q.generated_le_kernel q.kernel_le_behavior) q) := by
  apply (repairIso_iff_kernel_eq T observe R).mpr
  exact quotientRepair_kernel T observe R q.kernel
    q.generated_le_kernel q.kernel_le_behavior

/-- The unique repair morphism attached to kernel inclusion. -/
noncomputable def repairHomOfLe
    {q : RepairQuotient.{u, v, w, z} T observe R}
    {q' : RepairQuotient.{u, v, w, z'} T observe R}
    (h : q.kernel ≤ q'.kernel) : RepairHom T observe R q q' :=
  Classical.choice (RepairHom.nonempty_iff_kernel_le.mpr h)

/-- The classification sends identity kernel inclusion to the identity map. -/
theorem repairHomOfLe_refl
    (q : RepairQuotient.{u, v, w, z} T observe R) :
    repairHomOfLe T observe R (q := q) (q' := q) (le_refl _) =
      RepairHom.id q :=
  RepairHom.subsingleton _ _

/-- The classification sends composite kernel inclusion to composition of
the unique repair morphisms. -/
theorem repairHomOfLe_comp
    {q : RepairQuotient.{u, v, w, z} T observe R}
    {q' : RepairQuotient.{u, v, w, z'} T observe R}
    {q'' : RepairQuotient.{u, v, w, z''} T observe R}
    (h₁ : q.kernel ≤ q'.kernel) (h₂ : q'.kernel ≤ q''.kernel) :
    repairHomOfLe T observe R (le_trans h₁ h₂) =
      RepairHom.comp (repairHomOfLe T observe R h₁)
        (repairHomOfLe T observe R h₂) :=
  RepairHom.subsingleton _ _

/-- Two same-universe repair quotients represent the same class when their
source kernels agree. -/
def repairClassSetoid : Setoid (RepairQuotient.{u, v, w, u} T observe R) where
  r q q' := q.kernel.setoid = q'.kernel.setoid
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Repair quotients modulo equality of their source kernels. -/
def RepairClass := Quotient (repairClassSetoid T observe R)

/-- Equality of repair classes is exactly existence of an actual
structure-preserving isomorphism over the original source. -/
theorem repairClass_eq_iff_iso
    (q q' : RepairQuotient.{u, v, w, u} T observe R) :
    (Quotient.mk (repairClassSetoid T observe R) q =
      Quotient.mk (repairClassSetoid T observe R) q') ↔
      Nonempty (RepairIso T observe R q q') := by
  rw [Quotient.eq]
  exact (repairIso_iff_kernel_eq T observe R).symm

/-- A repair class determines a congruence between the two endpoints. -/
def classKernel : RepairClass T observe R →
    {c : OperationCongruence T // generated T R ≤ c ∧ c ≤ behavior T observe} :=
  fun cl => Quotient.liftOn cl (fun q => q.intervalPoint) (by
    intro q q' h
    apply Subtype.ext
    exact OperationCongruence.ext h)

/-- Every interval congruence gives a repair class by the constructed quotient. -/
def classOfInterval
    (c : {c : OperationCongruence T // generated T R ≤ c ∧ c ≤ behavior T observe}) :
    RepairClass T observe R :=
  Quotient.mk (repairClassSetoid T observe R)
    (quotientRepair T observe R c.1 c.2.1 c.2.2)

/-- The kernel of the class constructed from an interval point is that point. -/
theorem classKernel_classOfInterval
    (c : {c : OperationCongruence T // generated T R ≤ c ∧ c ≤ behavior T observe}) :
    classKernel T observe R (classOfInterval T observe R c) = c := by
  apply Subtype.ext
  exact OperationCongruence.ext
    (quotientRepair_kernel T observe R c.1 c.2.1 c.2.2)

/-- The constructed quotient of a class's kernel represents the original
class. -/
theorem classOfInterval_classKernel (cl : RepairClass T observe R) :
    classOfInterval T observe R (classKernel T observe R cl) = cl := by
  refine Quotient.inductionOn cl ?_
  intro q
  apply Quotient.sound
  exact quotientRepair_kernel T observe R q.kernel
    q.generated_le_kernel q.kernel_le_behavior

/-- Classification of repair quotient classes by the congruence interval. -/
def repairClassEquiv : RepairClass T observe R ≃
    {c : OperationCongruence T // generated T R ≤ c ∧ c ≤ behavior T observe} where
  toFun := classKernel T observe R
  invFun := classOfInterval T observe R
  left_inv := classOfInterval_classKernel T observe R
  right_inv := classKernel_classOfInterval T observe R

/-- Inclusion order on repair classes, induced by their source kernels. -/
instance : LE (RepairClass T observe R) where
  le a b := classKernel T observe R a ≤ classKernel T observe R b

/-- The kernel-induced order is antisymmetric because the kernel classifies
each repair object up to its class. -/
instance : PartialOrder (RepairClass T observe R) where
  le_refl a := show classKernel T observe R a ≤ classKernel T observe R a from le_refl _
  le_trans a b c hab hbc := by
    change classKernel T observe R a ≤ classKernel T observe R b at hab
    change classKernel T observe R b ≤ classKernel T observe R c at hbc
    change classKernel T observe R a ≤ classKernel T observe R c
    exact le_trans hab hbc
  le_antisymm a b hab hba :=
    (repairClassEquiv T observe R).injective (le_antisymm hab hba)

/-- GOAL B order isomorphism: an arrow from `q` to `q'` exists precisely when
the source kernel of `q` is included in that of `q'`. -/
def repairOrderIso : RepairClass T observe R ≃o
    {c : OperationCongruence T // generated T R ≤ c ∧ c ≤ behavior T observe} where
  toEquiv := repairClassEquiv T observe R
  map_rel_iff' := Iff.rfl

#assert_standard_axioms_only AAT.AG.OperationRepair

end AAT.AG.OperationRepair
