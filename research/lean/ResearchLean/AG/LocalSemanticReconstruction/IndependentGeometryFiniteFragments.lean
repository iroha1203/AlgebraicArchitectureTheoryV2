import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryPrimitiveAssembly
import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteFragments
import Mathlib.Data.Finset.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Dependent finite fragments of the common geometry declaration

A fragment carries one correctly typed value at each of its finitely many
query addresses. Compatibility compares the same cell in nested fragments.
Singleton gluing and restriction are inverse without assuming finite carriers
or finite query universes. Applied to the fixed primitive object conditions,
this gives the exact full native object reconstruction from all finite pieces.

The finite support of each primitive law instance is a separate obligation;
compatibility alone is not used to infer any native law or graph totality.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive

noncomputable section

universe u v

variable {U : AtomCarrier.{u}}

/-- A finite piece uses the common query declaration before any realization is selected. -/
abbrev Fragment (D : Finset (Query.{u, v} U)) :=
  IndependentFiniteFragments.Fragment (fun q : Query.{u, v} U => Query.Value q) D

/-- A family supplies dependent primitive values on every finite query set. -/
abbrev FragmentFamily (U : AtomCarrier.{u}) :=
  IndependentFiniteFragments.FragmentFamily (fun q : Query.{u, v} U => Query.Value q)

/-- The address set of each diagram is finite even when the native carriers are infinite. -/
theorem fragment_finite (D : Finset (Query.{u, v} U)) : Finite D :=
  IndependentFiniteFragments.fragment_finite D

/-- Restrict the common point table to one finite fragment at a time. -/
def fragments (t : Table.{u, v} U) : FragmentFamily.{u, v} U :=
  IndependentFiniteFragments.fragments t

/-- Shared primitive addresses have identical dependent values under every inclusion. -/
def Compatible (m : FragmentFamily.{u, v} U) : Prop :=
  IndependentFiniteFragments.Compatible m

/-- Read singleton fragments to construct the primitive point table. -/
def glue (m : FragmentFamily.{u, v} U) : Table.{u, v} U :=
  IndependentFiniteFragments.glue m

/-- Primitive table restrictions agree on all shared queries. -/
theorem fragments_compatible (t : Table.{u, v} U) : Compatible (fragments t) :=
  IndependentFiniteFragments.fragments_compatible t

/-- Singleton gluing restores every original primitive cell. -/
theorem glue_fragments (t : Table.{u, v} U) : glue (fragments t) = t :=
  IndependentFiniteFragments.glue_fragments t

/-- Inclusion compatibility recovers each finite fragment from its singleton cells. -/
theorem fragments_glue (m : FragmentFamily.{u, v} U) (h : Compatible m) :
    fragments (glue m) = m := by
  exact IndependentFiniteFragments.fragments_glue m h

/-- Finite local objects satisfy the explicit primitive conditions in addition to compatibility. -/
abbrev LocalObject (U : AtomCarrier.{u}) :=
  {m : FragmentFamily.{u, v} U // Compatible m ∧ IsLawful (glue m)}

/-- Assemble the native complete object from singleton primitive readings and their local laws. -/
def assembleFragments (m : LocalObject.{u, v} U) : ReadingCore.{u, v} U :=
  assemble (glue m.val) m.property.2

/-- Every native object determines compatible finite pieces satisfying the primitive equations. -/
def readFragments (G : ReadingCore.{u, v} U) : LocalObject.{u, v} U :=
  ⟨fragments (read G), fragments_compatible _, read_isLawful G⟩

/-- Finite reading and primitive assembly recover all native fields, including raw. -/
theorem assembleFragments_readFragments (G : ReadingCore.{u, v} U) :
    assembleFragments (readFragments G) = G := assemble_read G

/-- Every compatible lawful finite family is recovered, without adding proof-witness choices. -/
theorem readFragments_assembleFragments (m : LocalObject.{u, v} U) :
    readFragments (assembleFragments m) = m := by
  apply Subtype.ext
  change fragments (read (assemble (glue m.val) m.property.2)) = m.val
  rw [read_assemble]
  exact fragments_glue m.val m.property.1

/-- The same common finite declaration reconstructs every complete native geometry object. -/
def finiteObjectEquiv : ReadingCore.{u, v} U ≃ LocalObject.{u, v} U where
  toFun := readFragments
  invFun := assembleFragments
  left_inv := assembleFragments_readFragments
  right_inv := readFragments_assembleFragments

/-- All finite pieces separate every native object field. -/
theorem readFragments_injective : Function.Injective (readFragments.{u, v} (U := U)) :=
  finiteObjectEquiv.injective

/-- Equal total primitive tables give equal complete finite local objects, independently of law proofs. -/
theorem localObject_ext {m n : LocalObject.{u, v} U} (h : glue m.val = glue n.val) : m = n := by
  apply Subtype.ext
  rw [← fragments_glue m.val m.property.1, ← fragments_glue n.val n.property.1, h]

/-- Replacing the reference-match flags by false retains compatible finite restrictions. -/
def eraseMatching (t : Table.{u, v} U) : Table.{u, v} U
  | .matching _ => ⟨false⟩
  | q => t q

/-- Compatibility of finite pieces does not imply primitive totality: all-false matches are rejected. -/
theorem eraseMatching_not_lawful (t : Table.{u, v} U) : ¬ IsLawful (eraseMatching t) := by
  intro h
  exact IndependentGeneratedObjectMatching.all_false_not_lawful
    (extraction (eraseMatching t)) h.foundation.extraction
    (composition (eraseMatching t)) (formation (eraseMatching t)) h.matching

/-- The failed totality example still obeys every finite restriction inclusion. -/
theorem eraseMatching_fragments_compatible (t : Table.{u, v} U) :
    Compatible (fragments (eraseMatching t)) := fragments_compatible _

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive
