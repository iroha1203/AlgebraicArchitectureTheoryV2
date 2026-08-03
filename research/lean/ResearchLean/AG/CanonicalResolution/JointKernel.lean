import ResearchLean.AG.CanonicalResolution.Reading

/-!
# The joint-kernel canonical reading

This module discharges F1 of `G-103-aat-canonical-resolution`.  The canonical
reading is the quotient by equality of every declared law evaluation.  Its
adequacy, factorization through every adequate reading, and factor-map
uniqueness are derived theorems rather than stored package fields.
-/

namespace AAT.AG.CanonicalResolution

universe u

namespace FiniteLawFamily

variable {Source : Type u}

/-- Simultaneous equality of all law evaluations as a source setoid. -/
def jointKernelSetoid (laws : FiniteLawFamily Source) : Setoid Source where
  r := laws.Equivalent
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h law => (h law).symm
    trans := fun hxy hyz law => (hxy law).trans (hyz law)
  }

/-- The quotient target of the joint-kernel reading. -/
abbrev JointKernelQuotient (laws : FiniteLawFamily Source) :=
  Quotient laws.jointKernelSetoid

/-- The canonical reading generated directly from the joint law kernel. -/
def jointKernelReading (laws : FiniteLawFamily Source) : Reading Source where
  Target := laws.JointKernelQuotient
  read := Quotient.mk laws.jointKernelSetoid
  surjective := Quotient.mk_surjective

/-- Equality in the canonical reading is exactly equality of all law evaluations. -/
theorem jointKernel_kernel_iff (laws : FiniteLawFamily Source) (x y : Source) :
    laws.jointKernelReading.Kernel x y ↔ laws.Equivalent x y := by
  change Quotient.mk laws.jointKernelSetoid x =
      Quotient.mk laws.jointKernelSetoid y ↔ laws.Equivalent x y
  exact Quotient.eq

/-- Each law evaluation descends canonically to the joint-kernel quotient. -/
def jointKernelLawFactor (laws : FiniteLawFamily Source) (law : laws.Law) :
    laws.JointKernelQuotient → laws.Value law :=
  Quotient.lift (laws.eval law) (fun _x _y hxy => hxy law)

/-- The canonical law factor agrees with the original evaluation on sources. -/
@[simp]
theorem jointKernelLawFactor_mk (laws : FiniteLawFamily Source)
    (law : laws.Law) (source : Source) :
    laws.jointKernelLawFactor law
        (Quotient.mk laws.jointKernelSetoid source) =
      laws.eval law source :=
  rfl

/-- The joint-kernel reading is adequate for every declared law. -/
theorem jointKernel_adequate (laws : FiniteLawFamily Source) :
    laws.Adequate laws.jointKernelReading := by
  intro law
  exact ⟨laws.jointKernelLawFactor law, fun source => rfl⟩

/-- The joint-kernel reading is coarser than every adequate reading. -/
theorem jointKernel_coarser_of_adequate (laws : FiniteLawFamily Source)
    (q : Reading Source) (hq : laws.Adequate q) :
    laws.jointKernelReading.CoarserThan q := by
  intro x y hxy
  apply (laws.jointKernel_kernel_iff x y).2
  exact (laws.adequate_iff_kernel q).1 hq hxy

/-- The canonical reading factors through every adequate reading. -/
theorem jointKernel_factorsThrough_of_adequate
    (laws : FiniteLawFamily Source) (q : Reading Source)
    (hq : laws.Adequate q) :
    laws.jointKernelReading.FactorsThrough q :=
  (laws.jointKernelReading.factorsThrough_iff_coarserThan q).2
    (laws.jointKernel_coarser_of_adequate q hq)

/-- The factor from an adequate reading to the canonical quotient. -/
noncomputable def jointKernelFactor (laws : FiniteLawFamily Source)
    (q : Reading Source) (hq : laws.Adequate q) :
    q.Target → laws.JointKernelQuotient :=
  Classical.choose (laws.jointKernel_factorsThrough_of_adequate q hq)

/-- The generated factor commutes with the two source readings. -/
theorem jointKernelFactor_commutes (laws : FiniteLawFamily Source)
    (q : Reading Source) (hq : laws.Adequate q) (source : Source) :
    laws.jointKernelFactor q hq (q.read source) =
      laws.jointKernelReading.read source :=
  Classical.choose_spec
    (laws.jointKernel_factorsThrough_of_adequate q hq) source

/-- A commuting factor into the fixed canonical quotient is unique. -/
theorem jointKernelFactor_unique (laws : FiniteLawFamily Source)
    (q : Reading Source) (hq : laws.Adequate q)
    (factor : q.Target → laws.JointKernelQuotient)
    (hfactor : ∀ source, factor (q.read source) =
      laws.jointKernelReading.read source) :
    factor = laws.jointKernelFactor q hq := by
  funext target
  obtain ⟨source, rfl⟩ := q.surjective target
  exact (hfactor source).trans
    (laws.jointKernelFactor_commutes q hq source).symm

/--
The canonical quotient has the universal property required by G-103(i).

For each adequate reading there is exactly one map from its quotient target to
the fixed joint-kernel quotient that commutes with the source maps.
-/
theorem jointKernel_universal (laws : FiniteLawFamily Source)
    (q : Reading Source) (hq : laws.Adequate q) :
    ∃! factor : q.Target → laws.JointKernelQuotient,
      ∀ source, factor (q.read source) =
        laws.jointKernelReading.read source := by
  refine ⟨laws.jointKernelFactor q hq,
    laws.jointKernelFactor_commutes q hq, ?_⟩
  intro factor hfactor
  exact laws.jointKernelFactor_unique q hq factor hfactor

end FiniteLawFamily

end AAT.AG.CanonicalResolution

#assert_standard_axioms_only AAT.AG.CanonicalResolution
