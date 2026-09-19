import Mathlib.CategoryTheory.SingleObj
import ResearchLean.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition
import Formal.Util.AssertStandardAxioms

/-!
# The full G-122 comparison group in independent twisted coordinates

The full raw comparison group of the fixed G-122 input is presented by two
independently supplied coordinates: a full restriction-kernel displacement
and a normalized comparison.  Multiplication is the explicit conjugation-
twisted formula forced by right displacement of the canonical section.

Unlike the ordinary product group on the underlying pair type, `TwistedCode`
has the correct semidirect multiplication.  Its identity and inverse are
given by local formulas.  Assembly preserves all three operations, separates
codes, and is a multiplicative equivalence onto the full raw comparison group.
Thus delooping gives a genuine one-object category equivalence, not merely a
type equivalence or a selected finite subgroup.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel
open AtomFoundation DoctrineFiberProduct GeometryTransport TransportCoherence
open FullGeometryNormalization

noncomputable section

namespace G122FullComparisonTwistedGroup

open G122FullComparisonKernelDecomposition

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance finiteAxisFoldAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Independent coordinates for a full raw comparison. -/
structure TwistedCode where
  /-- Right displacement in the full restriction kernel. -/
  kernel : FullKernelᵐᵒᵖ
  /-- The normalized comparison coordinate. -/
  normalized : NormalizedComparison

/-- Forget the bundled coordinate names used by the twisted presentation. -/
def TwistedCode.toFullComparisonCode (code : TwistedCode) :
    FullComparisonCode :=
  (code.kernel, code.normalized)

/-- Rebundle the established full comparison coordinates. -/
def TwistedCode.ofFullComparisonCode (code : FullComparisonCode) :
    TwistedCode :=
  ⟨code.1, code.2⟩

/-- Assemble independent twisted coordinates into a full raw comparison. -/
noncomputable def assemble (code : TwistedCode) : RawComparison :=
  G122FullComparisonKernelDecomposition.assemble code.toFullComparisonCode

/-- Read both independent coordinates from a full raw comparison. -/
noncomputable def read (raw : RawComparison) : TwistedCode :=
  TwistedCode.ofFullComparisonCode
    (G122FullComparisonKernelDecomposition.read raw)

/-- Reading after assembly recovers both supplied coordinates. -/
@[simp] theorem read_assemble (code : TwistedCode) :
    read (assemble code) = code := by
  cases code
  simp [read, assemble, TwistedCode.toFullComparisonCode,
    TwistedCode.ofFullComparisonCode,
    G122FullComparisonKernelDecomposition.read_assemble]

/-- Assembly after reading recovers every full raw comparison. -/
@[simp] theorem assemble_read (raw : RawComparison) :
    assemble (read raw) = raw := by
  exact G122FullComparisonKernelDecomposition.assemble_read raw

/-- Conjugate a full-kernel value by the canonical normalized section. -/
noncomputable def rightConjugate
    (normalized : NormalizedComparison) (kernelValue : FullKernel) :
    FullKernel :=
  ⟨(canonicalSectionHom normalized)⁻¹ * kernelValue.1 *
      canonicalSectionHom normalized, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      restriction_canonicalSection,
      MonoidHom.mem_ker.mp kernelValue.property]
    simp⟩

/-- Twisted coordinate multiplication.  The first displacement is conjugated
by the second normalized coordinate before the second displacement is
applied. -/
noncomputable def multiply (first second : TwistedCode) : TwistedCode :=
  ⟨MulOpposite.op
      (rightConjugate second.normalized (MulOpposite.unop first.kernel) *
        MulOpposite.unop second.kernel),
    first.normalized * second.normalized⟩

/-- The identity twisted coordinate. -/
def one : TwistedCode := ⟨1, 1⟩

/-- The inverse coordinate, including the conjugation required to move an
inverse right displacement past the inverse canonical section. -/
noncomputable def inverse (code : TwistedCode) : TwistedCode :=
  ⟨MulOpposite.op
      (rightConjugate code.normalized⁻¹
        (MulOpposite.unop code.kernel)⁻¹),
    code.normalized⁻¹⟩

/-- Assembly turns the explicit twisted product into actual multiplication. -/
theorem assemble_multiply (first second : TwistedCode) :
    assemble (multiply first second) = assemble first * assemble second := by
  change G122FullComparisonKernelDecomposition.assemble
      (multiply first second).toFullComparisonCode =
    G122FullComparisonKernelDecomposition.assemble
        first.toFullComparisonCode *
      G122FullComparisonKernelDecomposition.assemble
        second.toFullComparisonCode
  rw [G122FullComparisonKernelDecomposition.assemble_mul_formula]
  rfl

/-- The explicit identity assembles to the actual identity. -/
theorem assemble_one : assemble one = 1 := by
  simp [assemble, one, TwistedCode.toFullComparisonCode,
    G122FullComparisonKernelDecomposition.assemble]

/-- The explicit inverse assembles to the actual inverse. -/
theorem assemble_inverse (code : TwistedCode) :
    assemble (inverse code) = (assemble code)⁻¹ := by
  simp only [assemble, inverse, TwistedCode.toFullComparisonCode,
    G122FullComparisonKernelDecomposition.assemble, rightConjugate,
    map_inv]
  change
    (canonicalSectionHom code.normalized)⁻¹ *
        (canonicalSectionHom code.normalized *
          (MulOpposite.unop code.kernel).1⁻¹ *
          (canonicalSectionHom code.normalized)⁻¹) =
      (MulOpposite.unop code.kernel).1⁻¹ *
        (canonicalSectionHom code.normalized)⁻¹
  group

/-- Assembly separates independent twisted coordinates. -/
theorem assemble_injective : Function.Injective assemble := by
  intro first second equality
  rw [← read_assemble first, equality, read_assemble second]

/-- The explicit operations satisfy the group laws because assembly is
separating and preserves their displayed formulas. -/
noncomputable instance : Group TwistedCode where
  mul := multiply
  one := one
  inv := inverse
  mul_assoc := by
    intro first second third
    change multiply (multiply first second) third =
      multiply first (multiply second third)
    apply assemble_injective
    rw [assemble_multiply, assemble_multiply, assemble_multiply,
      assemble_multiply, mul_assoc]
  one_mul := by
    intro code
    change multiply one code = code
    apply assemble_injective
    rw [assemble_multiply, assemble_one, one_mul]
  mul_one := by
    intro code
    change multiply code one = code
    apply assemble_injective
    rw [assemble_multiply, assemble_one, mul_one]
  inv_mul_cancel := by
    intro code
    change multiply (inverse code) code = one
    apply assemble_injective
    rw [assemble_multiply, assemble_inverse, assemble_one, inv_mul_cancel]

/-- Independent twisted coordinates are multiplicatively equivalent to every
full raw comparison of the fixed G-122 input. -/
noncomputable def twistedCodeMulEquiv : TwistedCode ≃* RawComparison where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read
  map_mul' := assemble_multiply

/-- The kernel coordinate read from a raw comparison is its torsor displacement
from the canonical lift over the same normalized comparison. -/
theorem readKernel_smul_canonicalLift
    (normalized : NormalizedComparison) (raw : RawComparison)
    (normalization : restrictionHom raw = normalized) :
    (read raw).kernel • canonicalLift normalized =
      (⟨raw, normalization⟩ : AuthoredExactCanonicalComparisonLiftFiber
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible normalized) := by
  subst normalized
  apply Subtype.ext
  exact G122FullComparisonKernelDecomposition.assemble_read raw

/-- The actual full comparison group as a one-object category. -/
abbrev GlobalCategory := SingleObj RawComparison

/-- The independent twisted-coordinate group as a one-object local category. -/
abbrev LocalCategory := SingleObj TwistedCode

/-- Primitive reading from a full comparison into its normalized and kernel
coordinates. -/
noncomputable def reading : GlobalCategory ⥤ LocalCategory :=
  SingleObj.mapHom RawComparison TwistedCode
    twistedCodeMulEquiv.symm.toMonoidHom

/-- Direct assembly of every local Hom. -/
noncomputable def assembleHom {X Y : GlobalCategory}
    (localMorphism : reading.obj X ⟶ reading.obj Y) : X ⟶ Y :=
  twistedCodeMulEquiv localMorphism

/-- Hom reading after direct assembly is identity. -/
@[simp] theorem reading_assembleHom {X Y : GlobalCategory}
    (localMorphism : reading.obj X ⟶ reading.obj Y) :
    reading.map (assembleHom localMorphism) = localMorphism :=
  twistedCodeMulEquiv.symm_apply_apply localMorphism

/-- Direct assembly after Hom reading is identity. -/
@[simp] theorem assembleHom_reading {X Y : GlobalCategory}
    (global : X ⟶ Y) : assembleHom (reading.map global) = global :=
  twistedCodeMulEquiv.apply_symm_apply global

/-- The full G-122 comparison category is equivalent to the independent
twisted-coordinate category. -/
noncomputable def equivalence : GlobalCategory ≌ LocalCategory :=
  twistedCodeMulEquiv.symm.toSingleObjEquiv

/-- Every local Hom has exactly one actual full-comparison preimage. -/
theorem existsUnique_preimage {X Y : GlobalCategory}
    (localMorphism : reading.obj X ⟶ reading.obj Y) :
    ∃! global : X ⟶ Y, reading.map global = localMorphism := by
  refine ⟨assembleHom localMorphism,
    reading_assembleHom localMorphism, ?_⟩
  intro candidate equality
  rw [← assembleHom_reading candidate, equality]

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122FullComparisonTwistedGroup

end G122FullComparisonTwistedGroup

end

end AAT.AG.LocalSemanticReconstruction
