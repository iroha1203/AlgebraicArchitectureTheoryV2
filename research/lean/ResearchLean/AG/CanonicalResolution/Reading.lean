import Formal.Util.AssertStandardAxioms
import Mathlib.Data.Fintype.Basic

/-!
# Readings, adequacy, and the coarse-reading order

This module discharges F0 of `G-103-aat-canonical-resolution`.  A reading
contains only a surjective map from the fixed source.  Its kernel, map
factorization, the coarse-reading order, and law adequacy are all derived
outside the structure.

The orientation is chosen so that `coarse.CoarserThan fine` means exactly that
`coarse` factors through `fine`.  Thus an adequate reading refines the
canonical joint-kernel reading constructed in the next stage.
-/

namespace AAT.AG.CanonicalResolution

universe u

/-- A reading of a source, presented by a surjective map. -/
structure Reading (Source : Type u) where
  /-- The quotient values observed by the reading. -/
  Target : Type u
  /-- The source-to-quotient map. -/
  read : Source → Target
  /-- Every quotient value is represented by a source. -/
  surjective : Function.Surjective read

namespace Reading

variable {Source : Type u}

/-- The kernel relation induced by a reading. -/
def Kernel (q : Reading Source) (x y : Source) : Prop :=
  q.read x = q.read y

/-- The kernel of every reading is an equivalence relation. -/
def kernelSetoid (q : Reading Source) : Setoid Source where
  r := q.Kernel
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun hxy hyz => hxy.trans hyz
  }

/-- A map factors through a reading when it descends to the reading target. -/
def Factors (q : Reading Source) {Target : Type u}
    (f : Source → Target) : Prop :=
  ∃ descend : q.Target → Target, ∀ source, descend (q.read source) = f source

/-- One reading factors through another reading. -/
def FactorsThrough (coarse fine : Reading Source) : Prop :=
  fine.Factors coarse.read

/-- `coarse` is coarser than `fine` when the fine kernel lies in the coarse kernel. -/
def CoarserThan (coarse fine : Reading Source) : Prop :=
  ∀ ⦃x y⦄, fine.Kernel x y → coarse.Kernel x y

/-- Two readings have the same quotient relation on the source. -/
def KernelEquivalent (q r : Reading Source) : Prop :=
  ∀ x y, q.Kernel x y ↔ r.Kernel x y

/-- A map descends through a reading exactly when it is constant on its kernel. -/
theorem factors_iff_kernel (q : Reading Source) {Target : Type u}
    (f : Source → Target) :
    q.Factors f ↔ ∀ ⦃x y⦄, q.Kernel x y → f x = f y := by
  constructor
  · rintro ⟨descend, hdescend⟩ x y hxy
    calc
      f x = descend (q.read x) := (hdescend x).symm
      _ = descend (q.read y) := congrArg descend hxy
      _ = f y := hdescend y
  · intro hkernel
    classical
    let representative : q.Target → Source := fun target =>
      Classical.choose (q.surjective target)
    refine ⟨fun target => f (representative target), ?_⟩
    intro source
    apply hkernel
    exact Classical.choose_spec (q.surjective (q.read source))

/-- Reading factorization and kernel inclusion give the same coarse order. -/
theorem factorsThrough_iff_coarserThan (coarse fine : Reading Source) :
    coarse.FactorsThrough fine ↔ coarse.CoarserThan fine := by
  exact fine.factors_iff_kernel coarse.read

/-- The coarse-reading relation is reflexive. -/
theorem coarserThan_refl (q : Reading Source) : q.CoarserThan q :=
  by
    intro x y h
    exact h

/-- The coarse-reading relation is transitive. -/
theorem coarserThan_trans {q r s : Reading Source}
    (hqr : q.CoarserThan r) (hrs : r.CoarserThan s) :
    q.CoarserThan s := by
  intro x y h
  exact hqr (hrs h)

/-- Mutual coarse comparison is antisymmetry at the level of reading kernels. -/
theorem coarserThan_antisymm_kernel {q r : Reading Source}
    (hqr : q.CoarserThan r) (hrq : r.CoarserThan q) :
    q.KernelEquivalent r := by
  intro x y
  exact ⟨fun h => hrq h, fun h => hqr h⟩

/-- Kernel equivalence is reflexive. -/
theorem kernelEquivalent_refl (q : Reading Source) : q.KernelEquivalent q :=
  fun _ _ => Iff.rfl

/-- Kernel equivalence is symmetric. -/
theorem kernelEquivalent_symm {q r : Reading Source}
    (h : q.KernelEquivalent r) : r.KernelEquivalent q :=
  fun x y => (h x y).symm

/-- Kernel equivalence is transitive. -/
theorem kernelEquivalent_trans {q r s : Reading Source}
    (hqr : q.KernelEquivalent r) (hrs : r.KernelEquivalent s) :
    q.KernelEquivalent s :=
  fun x y => (hqr x y).trans (hrs x y)

end Reading

/-- A finite family of decidable law evaluations on one fixed source. -/
structure FiniteLawFamily (Source : Type u) where
  /-- Finite law index. -/
  Law : Type u
  /-- Enumeration of the law index. -/
  lawFintype : Fintype Law
  /-- The value type observed by each law. -/
  Value : Law → Type u
  /-- Equality of every law value is decidable. -/
  valueDecidableEq : ∀ law, DecidableEq (Value law)
  /-- Evaluation of a law on a source. -/
  eval : (law : Law) → Source → Value law

namespace FiniteLawFamily

variable {Source : Type u}

instance instLawFintype (laws : FiniteLawFamily Source) : Fintype laws.Law :=
  laws.lawFintype

instance instValueDecidableEq (laws : FiniteLawFamily Source)
    (law : laws.Law) : DecidableEq (laws.Value law) :=
  laws.valueDecidableEq law

/-- Sources are law-equivalent when all declared evaluations agree. -/
def Equivalent (laws : FiniteLawFamily Source) (x y : Source) : Prop :=
  ∀ law, laws.eval law x = laws.eval law y

/-- A reading is adequate when every declared law evaluation factors through it. -/
def Adequate (laws : FiniteLawFamily Source) (q : Reading Source) : Prop :=
  ∀ law, q.Factors (laws.eval law)

/-- Adequacy is exactly refinement of the joint law-equivalence relation. -/
theorem adequate_iff_kernel (laws : FiniteLawFamily Source)
    (q : Reading Source) :
    laws.Adequate q ↔
      ∀ ⦃x y⦄, q.Kernel x y → laws.Equivalent x y := by
  constructor
  · intro hadequate x y hxy law
    exact ((q.factors_iff_kernel (laws.eval law)).mp (hadequate law)) hxy
  · intro hkernel law
    apply (q.factors_iff_kernel (laws.eval law)).mpr
    intro x y hxy
    exact hkernel hxy law

end FiniteLawFamily

end AAT.AG.CanonicalResolution

#assert_standard_axioms_only AAT.AG.CanonicalResolution
