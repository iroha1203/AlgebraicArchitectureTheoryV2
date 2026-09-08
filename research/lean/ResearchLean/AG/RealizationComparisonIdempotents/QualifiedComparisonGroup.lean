import ResearchLean.AG.RealizationComparisonIdempotents.ThreeStageProjection
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonStabilizer

/-!
# Qualified automorphisms of a comparison object

This file constructs G-119(B2).  An arbitrary complete-geometry comparison is
embedded in `M(E_geom)` with identity endpoint idempotents, and then regarded
as an object of its maximal subgroupoid.  We select exactly those
automorphisms whose two endpoint maps become identities after the composite
projection.  The resulting group is identified with the existing
`qualifiedComparisonSubgroup`.

## Implementation notes

The comparison itself is not required to become an identity at the base.  Its
endpoint qualifications are expressed as preimages of the existing
`compositeFiberAutSubgroup`; the Arrow square already supplies the
comparison-preservation equation and is not duplicated as a certificate.  The
two endpoint projections are constructed independently before the final group
equivalence, so their agreement with the existing projections is substantive.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.RealizationComparisonIdempotents

open AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

universe u v

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}

/-- Embed an arbitrary geometry comparison with identity endpoint idempotents
as an object of the maximal comparison subgroupoid. -/
noncomputable def identityIdempotentReversibleComparison
    (c : GeometryTotalHom G H) :
    ReversibleRepresentationChanges (GeomReadCategory.{u, v} U) :=
  ⟨Arrow.mk ((toKaroubi _).map c)⟩

/-- Normalization rule: the embedded comparison retains its source geometry. -/
@[simp]
theorem identityIdempotentReversibleComparison_left_X
    (c : GeometryTotalHom G H) :
    (identityIdempotentReversibleComparison c).of.left.X = G :=
  rfl

/-- Normalization rule: the embedded source idempotent is the raw identity. -/
@[simp]
theorem identityIdempotentReversibleComparison_left_p
    (c : GeometryTotalHom G H) :
    (identityIdempotentReversibleComparison c).of.left.p =
      (𝟙 G : GeometryTotalHom G G) :=
  rfl

/-- Normalization rule: the embedded comparison retains its target geometry. -/
@[simp]
theorem identityIdempotentReversibleComparison_right_X
    (c : GeometryTotalHom G H) :
    (identityIdempotentReversibleComparison c).of.right.X = H :=
  rfl

/-- Normalization rule: the embedded target idempotent is the raw identity. -/
@[simp]
theorem identityIdempotentReversibleComparison_right_p
    (c : GeometryTotalHom G H) :
    (identityIdempotentReversibleComparison c).of.right.p =
      (𝟙 H : GeometryTotalHom H H) :=
  rfl

/-- Normalization rule: the embedded comparison has underlying geometry map `c`. -/
@[simp]
theorem identityIdempotentReversibleComparison_hom_f
    (c : GeometryTotalHom G H) :
    (identityIdempotentReversibleComparison c).of.hom.f = c :=
  rfl

/-- The projected comparison is the actual twice-projected map; no identity
condition is imposed on it. -/
@[simp]
theorem identityIdempotentReversibleComparison_projected_hom
    (c : GeometryTotalHom G H) :
    ((crossStageComparisonProjection U).obj
        (identityIdempotentReversibleComparison c).of).hom.f = c.base.base :=
  rfl

/-- The source geometry automorphism underlying a reversible comparison change. -/
noncomputable def reversibleComparisonSourceAut
    {c : GeometryTotalHom G H}
    (a : Aut (identityIdempotentReversibleComparison c)) : Aut G where
  hom := a.hom.iso.hom.left.f
  inv := a.hom.iso.inv.left.f
  hom_inv_id := by
    have h := congrArg Karoubi.Hom.f (Comma.leftIso a.hom.iso).hom_inv_id
    simpa only [Karoubi.comp_f, Karoubi.id_f, Karoubi.coe_p] using h
  inv_hom_id := by
    have h := congrArg Karoubi.Hom.f (Comma.leftIso a.hom.iso).inv_hom_id
    simpa only [Karoubi.comp_f, Karoubi.id_f, Karoubi.coe_p] using h

/-- The target geometry automorphism underlying a reversible comparison change. -/
noncomputable def reversibleComparisonTargetAut
    {c : GeometryTotalHom G H}
    (a : Aut (identityIdempotentReversibleComparison c)) : Aut H where
  hom := a.hom.iso.hom.right.f
  inv := a.hom.iso.inv.right.f
  hom_inv_id := by
    have h := congrArg Karoubi.Hom.f (Comma.rightIso a.hom.iso).hom_inv_id
    simpa only [Karoubi.comp_f, Karoubi.id_f, Karoubi.coe_p] using h
  inv_hom_id := by
    have h := congrArg Karoubi.Hom.f (Comma.rightIso a.hom.iso).inv_hom_id
    simpa only [Karoubi.comp_f, Karoubi.id_f, Karoubi.coe_p] using h

/-- Source endpoint extraction as a group homomorphism. -/
noncomputable def reversibleComparisonSourceAutHom
    (c : GeometryTotalHom G H) :
    Aut (identityIdempotentReversibleComparison c) →* Aut G where
  toFun := reversibleComparisonSourceAut
  map_one' := by apply Iso.ext; rfl
  map_mul' _ _ := by apply Iso.ext; rfl

/-- Target endpoint extraction as a group homomorphism. -/
noncomputable def reversibleComparisonTargetAutHom
    (c : GeometryTotalHom G H) :
    Aut (identityIdempotentReversibleComparison c) →* Aut H where
  toFun := reversibleComparisonTargetAut
  map_one' := by apply Iso.ext; rfl
  map_mul' _ _ := by apply Iso.ext; rfl

/-- Automorphisms of the comparison whose two endpoint changes are invisible
after the composite projection. -/
noncomputable def baseQualifiedReversibleComparisonSubgroup
    (c : GeometryTotalHom G H) :
    Subgroup (Aut (identityIdempotentReversibleComparison c)) :=
  Subgroup.comap (reversibleComparisonSourceAutHom c)
      (compositeFiberAutSubgroup G) ⊓
    Subgroup.comap (reversibleComparisonTargetAutHom c)
      (compositeFiberAutSubgroup H)

/-- Membership is exactly the two endpoint base-identity conditions. -/
theorem mem_baseQualifiedReversibleComparisonSubgroup
    {c : GeometryTotalHom G H}
    {a : Aut (identityIdempotentReversibleComparison c)} :
    a ∈ baseQualifiedReversibleComparisonSubgroup c ↔
      (reversibleComparisonSourceAut a).hom.base.base =
          𝟙 (packagePoint G.core) ∧
        (reversibleComparisonTargetAut a).hom.base.base =
          𝟙 (packagePoint H.core) :=
  Iff.rfl

/-- The independently constructed source projection of the new qualified group. -/
noncomputable def baseQualifiedReversibleComparisonSourceProjection
    (c : GeometryTotalHom G H) :
    baseQualifiedReversibleComparisonSubgroup c →* CompositeFiberAut G where
  toFun a := ⟨reversibleComparisonSourceAut a.1, a.2.1⟩
  map_one' := by apply Subtype.ext; apply Iso.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Iso.ext; rfl

/-- The independently constructed target projection of the new qualified group. -/
noncomputable def baseQualifiedReversibleComparisonTargetProjection
    (c : GeometryTotalHom G H) :
    baseQualifiedReversibleComparisonSubgroup c →* CompositeFiberAut H where
  toFun a := ⟨reversibleComparisonTargetAut a.1, a.2.2⟩
  map_one' := by apply Subtype.ext; apply Iso.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Iso.ext; rfl

/-- The source endpoint of a qualified reversible change projects to the base identity. -/
theorem baseQualifiedReversibleComparison_source_projected_identity
    {c : GeometryTotalHom G H}
    (a : baseQualifiedReversibleComparisonSubgroup c) :
    ((crossStageComparisonProjection U).map a.1.hom.iso.hom).left.f =
      𝟙 (packagePoint G.core) := by
  simpa only [crossStageComparisonProjection_map_left_f] using a.2.1

/-- The target endpoint of a qualified reversible change projects to the base identity. -/
theorem baseQualifiedReversibleComparison_target_projected_identity
    {c : GeometryTotalHom G H}
    (a : baseQualifiedReversibleComparisonSubgroup c) :
    ((crossStageComparisonProjection U).map a.1.hom.iso.hom).right.f =
      𝟙 (packagePoint H.core) := by
  simpa only [crossStageComparisonProjection_map_right_f] using a.2.2

/-- Build the qualified reversible comparison change represented by an
existing qualified endpoint pair. -/
noncomputable def qualifiedComparisonToReversible
    (c : GeometryTotalHom G H)
    (q : qualifiedComparisonSubgroup c) :
    baseQualifiedReversibleComparisonSubgroup c :=
  ⟨Core.isoMk (Arrow.isoMk
      ((toKaroubi _).mapIso q.1.1.1)
      ((toKaroubi _).mapIso q.1.2.1)
      (by
        apply Karoubi.hom_ext
        exact q.2)),
    q.1.1.2, q.1.2.2⟩

/-- Recover the existing qualified endpoint pair from a qualified reversible change. -/
noncomputable def reversibleToQualifiedComparison
    (c : GeometryTotalHom G H)
    (a : baseQualifiedReversibleComparisonSubgroup c) :
    qualifiedComparisonSubgroup c :=
  ⟨(baseQualifiedReversibleComparisonSourceProjection c a,
      baseQualifiedReversibleComparisonTargetProjection c a), by
    exact congrArg Karoubi.Hom.f a.1.hom.iso.hom.w⟩

/-- G-119(B2): qualified comparison pairs are precisely the base-qualified
automorphisms of the embedded comparison in the maximal subgroupoid. -/
noncomputable def qualifiedComparisonReversibleMulEquiv
    (c : GeometryTotalHom G H) :
    qualifiedComparisonSubgroup c ≃*
      baseQualifiedReversibleComparisonSubgroup c where
  toFun := qualifiedComparisonToReversible c
  invFun := reversibleToQualifiedComparison c
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> apply Iso.ext <;> rfl
  right_inv a := by
    apply Subtype.ext
    apply Iso.ext
    apply Core.hom_ext
    apply Arrow.hom_ext
    · apply Karoubi.hom_ext
      rfl
    · apply Karoubi.hom_ext
      rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Iso.ext
    apply Core.hom_ext
    apply Arrow.hom_ext
    · apply Karoubi.hom_ext
      rfl
    · apply Karoubi.hom_ext
      rfl

/-- The group equivalence preserves the existing source projection. -/
@[simp]
theorem qualifiedComparisonReversibleMulEquiv_source_projection
    (c : GeometryTotalHom G H) (q : qualifiedComparisonSubgroup c) :
    baseQualifiedReversibleComparisonSourceProjection c
        (qualifiedComparisonReversibleMulEquiv c q) =
      qualifiedComparisonSourceProjection c q :=
  rfl

/-- The group equivalence preserves the existing target projection. -/
@[simp]
theorem qualifiedComparisonReversibleMulEquiv_target_projection
    (c : GeometryTotalHom G H) (q : qualifiedComparisonSubgroup c) :
    baseQualifiedReversibleComparisonTargetProjection c
        (qualifiedComparisonReversibleMulEquiv c q) =
      qualifiedComparisonTargetProjection c q :=
  rfl

/-- The inverse equivalence recovers the independent source projection. -/
@[simp]
theorem qualifiedComparisonReversibleMulEquiv_symm_source_projection
    (c : GeometryTotalHom G H)
    (a : baseQualifiedReversibleComparisonSubgroup c) :
    qualifiedComparisonSourceProjection c
        ((qualifiedComparisonReversibleMulEquiv c).symm a) =
      baseQualifiedReversibleComparisonSourceProjection c a :=
  rfl

/-- The inverse equivalence recovers the independent target projection. -/
@[simp]
theorem qualifiedComparisonReversibleMulEquiv_symm_target_projection
    (c : GeometryTotalHom G H)
    (a : baseQualifiedReversibleComparisonSubgroup c) :
    qualifiedComparisonTargetProjection c
        ((qualifiedComparisonReversibleMulEquiv c).symm a) =
      baseQualifiedReversibleComparisonTargetProjection c a :=
  rfl

/-- The new source projection retains the full underlying geometry map. -/
@[simp]
theorem baseQualifiedReversibleComparisonSourceProjection_hom
    (c : GeometryTotalHom G H)
    (a : baseQualifiedReversibleComparisonSubgroup c) :
    CompositeFiberAut.hom
        (baseQualifiedReversibleComparisonSourceProjection c a) =
      a.1.hom.iso.hom.left.f :=
  rfl

/-- The new target projection retains the full underlying geometry map. -/
@[simp]
theorem baseQualifiedReversibleComparisonTargetProjection_hom
    (c : GeometryTotalHom G H)
    (a : baseQualifiedReversibleComparisonSubgroup c) :
    CompositeFiberAut.hom
        (baseQualifiedReversibleComparisonTargetProjection c a) =
      a.1.hom.iso.hom.right.f :=
  rfl

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
