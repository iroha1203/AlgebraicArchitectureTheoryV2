import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomLocalIdentity

/-!
# Unit laws for complete primitive local Hom composition

The directly constructed local identities act as left and right units for
both retained Hom meanings. The proof compares the fixed primitive operation
with native composition only after the local constructors are defined.

Implementation notes: the unit statements concern the direct local identity
and composition operations. Native category laws are used after both have been
compared with their completed Homs, rather than defining either operation.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.CategoryLaws

noncomputable section

universe u v

open CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction
open IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t : ObjectData.{u, v} U)

/-- The direct representative identity is a left unit for primitive local composition. -/
theorem representative_id_comp
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading
      (assemble t).core.reading.invariantReading .representative)
    (hp : FullRepresentative.PointLaws s t p) :
    Composition.representativeLocal s s t
      (IdentityLocal.representativeIdentity s)
      (IdentityLocal.representativeIdentity_points s) p hp = p := by
  rw [Composition.representativeLocal_eq_native,
    IdentityLocal.representativeIdentity_assemble]
  change NativeReader.localRepresentative
    ((𝟙 (assemble s)) ≫ FullRepresentative.assembleHom s t p hp) = p
  rw [Category.id_comp, NativeReader.localRepresentative_read_assemble]

/-- The direct representative identity is a right unit for primitive local composition. -/
theorem representative_comp_id
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading
      (assemble t).core.reading.invariantReading .representative)
    (hp : FullRepresentative.PointLaws s t p) :
    Composition.representativeLocal s t t p hp
      (IdentityLocal.representativeIdentity t)
      (IdentityLocal.representativeIdentity_points t) = p := by
  rw [Composition.representativeLocal_eq_native,
    IdentityLocal.representativeIdentity_assemble]
  change NativeReader.localRepresentative
    (FullRepresentative.assembleHom s t p hp ≫ 𝟙 (assemble t)) = p
  rw [Category.comp_id, NativeReader.localRepresentative_read_assemble]

/-- The direct explicit identity is a left unit for primitive local composition. -/
theorem explicit_id_comp
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading
      (assemble t).core.reading.invariantReading .explicit)
    (hp : FullExplicit.PointLaws s t p) :
    Composition.explicitLocal s s t
      (IdentityLocal.explicitIdentity s)
      (IdentityLocal.explicitIdentity_points s) p hp = p := by
  rw [Composition.explicitLocal_eq_native,
    IdentityLocal.explicitIdentity_assemble, ExplicitExactGeometryHom.id_comp,
    NativeReader.localExplicit_read_assemble]

/-- The direct explicit identity is a right unit for primitive local composition. -/
theorem explicit_comp_id
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading
      (assemble t).core.reading.invariantReading .explicit)
    (hp : FullExplicit.PointLaws s t p) :
    Composition.explicitLocal s t t p hp
      (IdentityLocal.explicitIdentity t)
      (IdentityLocal.explicitIdentity_points t) = p := by
  rw [Composition.explicitLocal_eq_native,
    IdentityLocal.explicitIdentity_assemble, ExplicitExactGeometryHom.comp_id,
    NativeReader.localExplicit_read_assemble]

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.CategoryLaws

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.CategoryLaws
