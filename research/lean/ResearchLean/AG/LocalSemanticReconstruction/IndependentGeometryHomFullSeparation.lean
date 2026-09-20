import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomLocalFullRecovery
import Formal.Util.AssertStandardAxioms

/-!
# Separation and unique native preimages for complete Hom readings

Both full reading equivalences retain every original query. Therefore two
different native Homs have a distinguishing primitive point, and every lawful
local quotient has exactly one native preimage. Finite fragment evaluation
agrees with the same point reading after auxiliary witness erasure.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}}

/-- Every value in a retained finite fragment is the same original query value exposed by the local quotient. -/
theorem local_fragment_point {mode : Mode} (I J : InvariantFamily U) (p : InvariantWitness.Local.{u, v} I J mode)
    (S : Finset (Query.{u, v} U mode)) (q : {q // q ∈ S}) :
    InvariantWitness.fragment I J p S q = InvariantWitness.point I J p q.val := by
  exact (congrArg (fun f => f.value S q)
    (TagChange.read_assemble (InvariantWitness.retained I J p).family)).symm

variable (s t : ObjectData.{u, v} U)

/-- Agreement on all common primitive queries is exactly equality of the original complete representative Homs. -/
theorem representative_eq_iff_queries (F T : GeometryTotalHom (assemble s) (assemble t)) :
    F = T ↔ ∀ q, readRepresentative F q = readRepresentative T q := by
  constructor
  · intro he
    cases he
    exact fun _ => rfl
  · intro he
    apply (representativeHomReadingEquiv s t).injective
    apply Subtype.ext
    apply InvariantWitness.point_ext
    intro q
    exact (point_localRepresentative F q).trans ((he q).trans (point_localRepresentative T q).symm)

/-- Agreement on all common queries is exactly equality of the original complete explicit Homs, including raw and realization data. -/
theorem explicit_eq_iff_queries (F T : ExplicitExactGeometryHom (assemble s) (assemble t)) :
    F = T ↔ ∀ q, readExplicit F q = readExplicit T q := by
  constructor
  · intro he
    cases he
    exact fun _ => rfl
  · intro he
    apply (explicitHomReadingEquiv s t).injective
    apply Subtype.ext
    apply InvariantWitness.point_ext
    intro q
    exact (point_localExplicit F q).trans ((he q).trans (point_localExplicit T q).symm)

/-- Every pair of different representative Homs is separated by an actual common primitive query. -/
theorem representative_distinct_query (F T : GeometryTotalHom (assemble s) (assemble t)) (hne : F ≠ T) :
    ∃ q, readRepresentative F q ≠ readRepresentative T q := by
  classical
  by_contra hn
  apply hne
  apply (representative_eq_iff_queries s t F T).2
  intro q
  by_contra hq
  exact hn ⟨q, hq⟩

/-- Every pair of different explicit Homs is separated even when their object actions agree. -/
theorem explicit_distinct_query (F T : ExplicitExactGeometryHom (assemble s) (assemble t)) (hne : F ≠ T) :
    ∃ q, readExplicit F q ≠ readExplicit T q := by
  classical
  by_contra hn
  apply hne
  apply (explicit_eq_iff_queries s t F T).2
  intro q
  by_contra hq
  exact hn ⟨q, hq⟩

/-- Every lawful representative local quotient has exactly one original complete native Hom as its preimage. -/
theorem representative_unique_preimage
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)
    (hp : FullRepresentative.PointLaws s t p) :
    ∃! F : GeometryTotalHom (assemble s) (assemble t), localRepresentative F = p := by
  refine ⟨FullRepresentative.assembleHom s t p hp, localRepresentative_read_assemble s t p hp, ?_⟩
  intro F hF
  apply (representativeHomReadingEquiv s t).injective
  exact Subtype.ext (hF.trans (localRepresentative_read_assemble s t p hp).symm)

/-- Every lawful explicit local quotient has exactly one original native Hom with all six components. -/
theorem explicit_unique_preimage
    (p : InvariantWitness.Local.{u, v}
      (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
    (hp : FullExplicit.PointLaws s t p) :
    ∃! F : ExplicitExactGeometryHom (assemble s) (assemble t), localExplicit F = p := by
  refine ⟨FullExplicit.assembleHom s t p hp, localExplicit_read_assemble s t p hp, ?_⟩
  intro F hF
  apply (explicitHomReadingEquiv s t).injective
  exact Subtype.ext (hF.trans (localExplicit_read_assemble s t p hp).symm)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
