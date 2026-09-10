import Mathlib.Algebra.Exact
import Mathlib.GroupTheory.Coset.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Restriction, reflection, and lift fibers for group homomorphisms

This file supplies the reusable group-theoretic core of G-120(C).  A
homomorphism carrying a subgroup `A` into a subgroup `B` restricts to a
homomorphism `A →* B`.  It reflects membership in `B` precisely when its
kernel is already contained in `A` and the image of `A` is the part of `B`
lying in the ambient range.  A nonempty fiber of the restricted homomorphism
is a right torsor for its kernel, and surjectivity produces the corresponding
short exact sequence.

Implementation notes: Lean's `MulAction` is a left-action interface, so the
required right multiplication is represented by a left action of the opposite
kernel group; using the kernel itself would reverse the action law.  The
four-term group sequence is recorded as injectivity, mathlib's
`Function.MulExact`, and surjectivity.  A categorical short complex would add
categorical packaging not used by the elementwise C and D applications.
-/

namespace AAT.AG.ComparisonInformationLoss

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Restrict a group homomorphism to subgroups once preservation is proved. -/
def restrictedSubgroupHom (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) : A →* B where
  toFun a := ⟨f a, hAB ⟨a, a.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f (a : G) (b : G))

/-- The value API for `restrictedSubgroupHom`; it normalizes a restricted
value to the original ambient homomorphism. -/
@[simp]
theorem restrictedSubgroupHom_coe (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) (a : A) :
    ((restrictedSubgroupHom f A B hAB a : B) : H) = f (a : G) :=
  rfl

/-- The exact reflection criterion used in G-120(C) and G-120(D). -/
theorem comap_eq_iff_ker_le_and_map_eq_inf_range
    (f : G →* H) (A : Subgroup G) (B : Subgroup H) :
    B.comap f = A ↔ f.ker ≤ A ∧ A.map f = B ⊓ f.range := by
  constructor
  · intro h
    constructor
    · intro g hg
      rw [← h]
      change f g ∈ B
      simpa only [MonoidHom.mem_ker.mp hg] using B.one_mem
    · apply le_antisymm
      · rintro h' ⟨g, hg, rfl⟩
        exact ⟨by rw [← h] at hg; exact hg, ⟨g, rfl⟩⟩
      · rintro h' ⟨hhB, g, rfl⟩
        exact ⟨g, by rw [← h]; exact hhB, rfl⟩
  · rintro ⟨hker, hmap⟩
    apply le_antisymm
    · intro g hg
      have hfg : f g ∈ A.map f := by
        rw [hmap]
        exact ⟨hg, ⟨g, rfl⟩⟩
      rcases hfg with ⟨a, ha, hfa⟩
      have hga : g * a⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfa, mul_inv_cancel]
      have : g = (g * a⁻¹) * a := by simp
      rw [this]
      exact A.mul_mem (hker hga) ha
    · intro g hg
      change f g ∈ B
      have : f g ∈ A.map f := ⟨g, hg, rfl⟩
      rw [hmap] at this
      exact this.1

/-- The fiber of a restricted homomorphism over a specified target element. -/
def RestrictedFiber (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) (t : B) :=
  {a : A // restrictedSubgroupHom f A B hAB a = t}

/-- A restricted lift exists exactly when the target lies in the ambient image
of the source subgroup. -/
theorem nonempty_restrictedFiber_iff_mem_map
    (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) (t : B) :
    Nonempty (RestrictedFiber f A B hAB t) ↔ (t : H) ∈ A.map f := by
  constructor
  · rintro ⟨⟨a, ha⟩⟩
    exact ⟨a, a.property, congrArg Subtype.val ha⟩
  · rintro ⟨g, hg, hgt⟩
    refine ⟨⟨⟨g, hg⟩, ?_⟩⟩
    apply Subtype.ext
    exact hgt

/-- Right multiplication by the restricted kernel, expressed as a left action
of the opposite group. -/
instance restrictedFiberSMul (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) (t : B) :
    SMul (restrictedSubgroupHom f A B hAB).kerᵐᵒᵖ
      (RestrictedFiber f A B hAB t) where
  smul k x := ⟨x.1 * ((MulOpposite.unop k :
      (restrictedSubgroupHom f A B hAB).ker) : A), by
    apply Subtype.ext
    rw [map_mul, x.property, MonoidHom.mem_ker.mp (MulOpposite.unop k).property,
      mul_one]⟩

/-- The computation API for the C.3 fiber action; it normalizes the action to
literal right multiplication on the source subgroup. -/
@[simp]
theorem restrictedFiber_smul_coe
    (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) (t : B)
    (k : (restrictedSubgroupHom f A B hAB).kerᵐᵒᵖ)
    (x : RestrictedFiber f A B hAB t) :
    (k • x : RestrictedFiber f A B hAB t).1 =
      x.1 * ((MulOpposite.unop k :
        (restrictedSubgroupHom f A B hAB).ker) : A) :=
  rfl

/-- The C.3 right-kernel action, presented through the opposite group so that
Lean's left `MulAction` laws express right multiplication in the correct order. -/
instance restrictedFiberMulAction
    (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) (t : B) :
    MulAction (restrictedSubgroupHom f A B hAB).kerᵐᵒᵖ
      (RestrictedFiber f A B hAB t) where
  one_smul x := by
    apply Subtype.ext
    change x.1 * (1 : A) = x.1
    simp
  mul_smul k l x := by
    apply Subtype.ext
    change x.1 * (((MulOpposite.unop l :
      (restrictedSubgroupHom f A B hAB).ker) : A) *
        ((MulOpposite.unop k :
          (restrictedSubgroupHom f A B hAB).ker) : A)) =
      (x.1 * ((MulOpposite.unop l :
        (restrictedSubgroupHom f A B hAB).ker) : A)) *
          ((MulOpposite.unop k :
            (restrictedSubgroupHom f A B hAB).ker) : A)
    simp [mul_assoc]

/-- The kernel action on every restricted fiber is free. -/
theorem restrictedFiber_action_free
    (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) (t : B)
    (x : RestrictedFiber f A B hAB t) :
    Function.Injective (fun k : (restrictedSubgroupHom f A B hAB).kerᵐᵒᵖ => k • x) := by
  intro k l hkl
  apply MulOpposite.unop_injective
  apply Subtype.ext
  have hval := congrArg (fun z : RestrictedFiber f A B hAB t => z.1) hkl
  exact mul_left_cancel hval

/-- The kernel action on a nonempty restricted fiber is transitive. -/
theorem restrictedFiber_action_transitive
    (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) (t : B)
    (x y : RestrictedFiber f A B hAB t) :
    ∃ k : (restrictedSubgroupHom f A B hAB).kerᵐᵒᵖ, k • x = y := by
  let kA : A := x.1⁻¹ * y.1
  have hk : kA ∈ (restrictedSubgroupHom f A B hAB).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, x.property, y.property, inv_mul_cancel]
  refine ⟨MulOpposite.op ⟨kA, hk⟩, ?_⟩
  apply Subtype.ext
  change x.1 * kA = y.1
  simp [kA]

/-- The unique right-kernel displacement between two lifts. -/
theorem restrictedFiber_existsUnique_smul_eq
    (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) (t : B)
    (x y : RestrictedFiber f A B hAB t) :
    ∃! k : (restrictedSubgroupHom f A B hAB).kerᵐᵒᵖ, k • x = y := by
  rcases restrictedFiber_action_transitive f A B hAB t x y with ⟨k, hk⟩
  refine ⟨k, hk, ?_⟩
  intro l hl
  exact restrictedFiber_action_free f A B hAB t x (hl.trans hk.symm)

/-- Inclusion of the kernel into the source of a restricted homomorphism. -/
def restrictedKernelInclusion
    (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) :
    (restrictedSubgroupHom f A B hAB).ker →* A :=
  (restrictedSubgroupHom f A B hAB).ker.subtype

/-- The group-level short-exact predicate used by G-120(C-D). -/
def IsGroupShortExact {K M N : Type*} [Group K] [Group M] [Group N]
    (i : K →* M) (p : M →* N) : Prop :=
  Function.Injective i ∧ Function.MulExact i p ∧ Function.Surjective p

/-- Exactness at the source subgroup follows from the literal kernel
inclusion. -/
theorem restrictedKernelInclusion_mulExact
    (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) :
    Function.MulExact (restrictedKernelInclusion f A B hAB)
      (restrictedSubgroupHom f A B hAB) := by
  rw [MonoidHom.mulExact_iff]
  exact ((restrictedSubgroupHom f A B hAB).ker.range_subtype).symm

/-- Surjectivity of the restriction is precisely equality of its ambient
subgroup image with the target subgroup. -/
theorem restrictedSubgroupHom_surjective_iff_map_eq
    (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) :
    Function.Surjective (restrictedSubgroupHom f A B hAB) ↔ A.map f = B := by
  constructor
  · intro hsurj
    apply le_antisymm hAB
    intro h hh
    rcases hsurj ⟨h, hh⟩ with ⟨a, ha⟩
    exact ⟨a, a.property, congrArg Subtype.val ha⟩
  · intro hmap t
    have ht : (t : H) ∈ A.map f := by rw [hmap]; exact t.property
    rcases (nonempty_restrictedFiber_iff_mem_map f A B hAB t).mpr ht with ⟨a⟩
    exact ⟨a.1, a.property⟩

/-- The restricted homomorphism yields the requested short exact sequence
exactly when the source subgroup maps onto the target subgroup. -/
theorem restrictedSubgroupHom_shortExact_iff_map_eq
    (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (hAB : A.map f ≤ B) :
    IsGroupShortExact (restrictedKernelInclusion f A B hAB)
        (restrictedSubgroupHom f A B hAB) ↔
      A.map f = B := by
  constructor
  · rintro ⟨_, _, hsurj⟩
    exact (restrictedSubgroupHom_surjective_iff_map_eq f A B hAB).mp hsurj
  · intro hmap
    exact ⟨Subtype.val_injective,
      restrictedKernelInclusion_mulExact f A B hAB,
      (restrictedSubgroupHom_surjective_iff_map_eq f A B hAB).mpr hmap⟩

/-- A nontrivial positive instance for the `IsGroupShortExact` predicate: the
kernel inclusion followed by the identity restriction on the full subgroup. -/
theorem isGroupShortExact_identity_top (G : Type u) [Group G] :
    IsGroupShortExact
      (restrictedKernelInclusion (MonoidHom.id G) ⊤ ⊤ (by simp))
      (restrictedSubgroupHom (MonoidHom.id G) ⊤ ⊤ (by simp)) := by
  apply (restrictedSubgroupHom_shortExact_iff_map_eq
    (MonoidHom.id G) ⊤ ⊤ (by simp)).mpr
  simp

/-- A negative instance for `IsGroupShortExact`: in every nontrivial group,
the identity homomorphism restricted from the bottom subgroup to the full
subgroup is not surjective. -/
theorem not_isGroupShortExact_identity_bot_top
    (G : Type u) [Group G] [Nontrivial G] :
    ¬ IsGroupShortExact
      (restrictedKernelInclusion (MonoidHom.id G) ⊥ ⊤ (by simp))
      (restrictedSubgroupHom (MonoidHom.id G) ⊥ ⊤ (by simp)) := by
  rw [restrictedSubgroupHom_shortExact_iff_map_eq]
  simp

#assert_standard_axioms_only AAT.AG.ComparisonInformationLoss

end AAT.AG.ComparisonInformationLoss
