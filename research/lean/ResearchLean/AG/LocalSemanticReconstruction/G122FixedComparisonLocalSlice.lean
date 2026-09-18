import ResearchLean.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion
import Formal.Util.AssertStandardAxioms

/-!
# Finite local model for the fixed G-122 comparison slice

The three accepted comparison codes have only two semantic values: the
generated-cochain comparison is distinct from `barAlpha`, while the
constant-one comparison equals `barAlpha`.  This module takes the actual image
of those codes in the expanded direct-to-via-base Hom and constructs a finite
two-valued local model with mutually inverse reading and assembly maps.

The source of the equivalence contains actual morphisms, while the local value
contains only a two-case label.  This is the fixed comparison Hom slice only;
it does not separate arbitrary G-122 morphisms or construct a category-wide
local-model equivalence.
-/

namespace AAT.AG.LocalSemanticReconstruction

open AAT.AG.RealizationReconstruction

namespace G122FixedComparisonLocalSlice

open G122ClosedFamilyExpansion

noncomputable section

/-- The actual semantic image of the three fixed comparison codes in the
expanded direct-to-via-base Hom. -/
def SemanticImage :=
  {morphism : finiteAxisFoldDirectObject ⟶ finiteAxisFoldViaBaseObject //
    ∃ code : FiniteAxisFoldComparisonCode,
      FiniteAxisFoldComparisonCode.evaluate code = morphism}

/-- The two semantic classes visible in the fixed comparison image. -/
inductive LocalValue
  /-- The class shared by `barAlpha` and the constant-one `barBeta`. -/
  | alpha
  /-- The distinct generated-cochain `barBeta` class. -/
  | generated
  deriving DecidableEq, Fintype

/-- Assemble a local class into its actual expanded-category morphism. -/
noncomputable def assemble : LocalValue → SemanticImage
  | .alpha => ⟨finiteAxisFoldBarAlpha, ⟨.barAlpha, rfl⟩⟩
  | .generated =>
      ⟨finiteAxisFoldGeneratedBarBeta, ⟨.generatedBarBeta, rfl⟩⟩

/-- Read an actual morphism in the fixed semantic image as one of its two
semantic classes. -/
noncomputable def read (morphism : SemanticImage) : LocalValue :=
  by
    classical
    exact if morphism.1 = finiteAxisFoldBarAlpha then .alpha else .generated

/-- The two representatives used by the local value are distinct. -/
theorem generated_ne_alpha :
    finiteAxisFoldGeneratedBarBeta ≠ finiteAxisFoldBarAlpha :=
  finiteAxisFoldGeneratedBarBeta_ne_barAlpha

/-- `barAlpha` reads as the shared alpha class. -/
@[simp] theorem read_barAlpha :
    read ⟨finiteAxisFoldBarAlpha, ⟨.barAlpha, rfl⟩⟩ = .alpha := by
  simp [read]

/-- The generated-cochain comparison reads as its distinct class. -/
@[simp] theorem read_generatedBarBeta :
    read ⟨finiteAxisFoldGeneratedBarBeta, ⟨.generatedBarBeta, rfl⟩⟩ =
      .generated := by
  classical
  change (if finiteAxisFoldGeneratedBarBeta = finiteAxisFoldBarAlpha then
    LocalValue.alpha else LocalValue.generated) = LocalValue.generated
  rw [if_neg generated_ne_alpha]

/-- The constant-one comparison reads as the same class as `barAlpha`. -/
@[simp] theorem read_identityBarBeta :
    read ⟨finiteAxisFoldIdentityBarBeta, ⟨.identityBarBeta, rfl⟩⟩ =
      .alpha := by
  classical
  change (if finiteAxisFoldIdentityBarBeta = finiteAxisFoldBarAlpha then
    LocalValue.alpha else LocalValue.generated) = LocalValue.alpha
  rw [if_pos finiteAxisFoldIdentityBarBeta_eq_barAlpha]

/-- Reading after assembly is the identity on the finite local value. -/
@[simp] theorem read_assemble (value : LocalValue) :
    read (assemble value) = value := by
  cases value with
  | alpha => exact read_barAlpha
  | generated => exact read_generatedBarBeta

/-- Assembly after reading recovers every actual morphism in the fixed
semantic image. -/
@[simp] theorem assemble_read (morphism : SemanticImage) :
    assemble (read morphism) = morphism := by
  rcases morphism with ⟨morphism, ⟨code, equality⟩⟩
  subst morphism
  apply Subtype.ext
  cases code with
  | barAlpha =>
      rw [show read ⟨finiteAxisFoldBarAlpha, ⟨.barAlpha, rfl⟩⟩ =
        LocalValue.alpha from read_barAlpha]
      rfl
  | generatedBarBeta =>
      rw [show read
          ⟨finiteAxisFoldGeneratedBarBeta, ⟨.generatedBarBeta, rfl⟩⟩ =
        LocalValue.generated from read_generatedBarBeta]
      rfl
  | identityBarBeta =>
      rw [show read
          ⟨finiteAxisFoldIdentityBarBeta, ⟨.identityBarBeta, rfl⟩⟩ =
        LocalValue.alpha from read_identityBarBeta]
      exact finiteAxisFoldIdentityBarBeta_eq_barAlpha.symm

/-- The actual fixed semantic image and the finite local value are equivalent. -/
noncomputable def semanticEquivLocal : SemanticImage ≃ LocalValue where
  toFun := read
  invFun := assemble
  left_inv := assemble_read
  right_inv := read_assemble

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice

end

end G122FixedComparisonLocalSlice

end AAT.AG.LocalSemanticReconstruction
