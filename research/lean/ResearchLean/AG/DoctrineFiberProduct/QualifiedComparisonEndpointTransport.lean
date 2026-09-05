import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonStabilizer

/-!
# Qualified comparison transport across the exact endpoint presentations

The two exact endpoint isomorphisms selected by G-118(C1) conjugate the full
qualified comparison group, its stabilizers, projection kernels, and lift
fibers.  The specialization below uses only the canonical-authored and
generated complete upper presentations; it does not quantify over arbitrary
finite presentation replacements.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

/-- The elementary endpoint-conjugation square used by the qualified
comparison transport. -/
private theorem qualifiedComparison_conjugatedIntertwining
    {C : Type u} [Category.{v} C] {X Y X' Y' : C}
    (sourceIso : X ≅ X') (targetIso : Y ≅ Y')
    (sourceAut : X ⟶ X) (hom : X ⟶ Y) (targetAut : Y ⟶ Y)
    (intertwining : sourceAut ≫ hom = hom ≫ targetAut) :
    ((sourceIso.inv ≫ sourceAut) ≫ sourceIso.hom) ≫
        ((sourceIso.inv ≫ hom) ≫ targetIso.hom) =
      ((sourceIso.inv ≫ hom) ≫ targetIso.hom) ≫
        ((targetIso.inv ≫ targetAut) ≫ targetIso.hom) := by
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun middle => sourceIso.inv ≫ middle ≫ targetIso.hom)
      intertwining

namespace CompositeFiberAut

/-- The inverse of the multiplicative conjugation has the same hom formula as
the inverse of its underlying equivalence. -/
@[simp] theorem conjugationMulEquiv_symm_hom
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) (automorphism : CompositeFiberAut H) :
    CompositeFiberAut.hom ((conjugationMulEquiv iso).symm automorphism) =
      (iso.hom.comp (CompositeFiberAut.hom automorphism)).comp iso.inv :=
  rfl

end CompositeFiberAut

/-- Simultaneous endpoint conjugation carries the full qualified comparison
group to the comparison written in the conjugated complete presentations. -/
noncomputable def qualifiedComparisonEndpointConjugationMulEquiv
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀) :
    qualifiedComparisonSubgroup comparison ≃*
      qualifiedComparisonSubgroup
        ((sourceIso.inv.comp comparison).comp targetIso.hom) where
  toFun pair :=
    ⟨(CompositeFiberAut.conjugationMulEquiv sourceIso pair.1.1,
      CompositeFiberAut.conjugationMulEquiv targetIso pair.1.2), by
      change
        (CompositeFiberAut.hom
          (CompositeFiberAut.conjugationMulEquiv sourceIso pair.1.1)).comp
            ((sourceIso.inv.comp comparison).comp targetIso.hom) =
          ((sourceIso.inv.comp comparison).comp targetIso.hom).comp
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv targetIso pair.1.2))
      rw [CompositeFiberAut.conjugationMulEquiv_hom,
        CompositeFiberAut.conjugationMulEquiv_hom]
      exact qualifiedComparison_conjugatedIntertwining
        sourceIso targetIso _ _ _ pair.2⟩
  invFun pair :=
    ⟨((CompositeFiberAut.conjugationMulEquiv sourceIso).symm pair.1.1,
      (CompositeFiberAut.conjugationMulEquiv targetIso).symm pair.1.2), by
      change
        (CompositeFiberAut.hom
          ((CompositeFiberAut.conjugationMulEquiv sourceIso).symm
            pair.1.1)).comp comparison =
          comparison.comp (CompositeFiberAut.hom
            ((CompositeFiberAut.conjugationMulEquiv targetIso).symm
              pair.1.2))
      rw [CompositeFiberAut.conjugationMulEquiv_symm_hom,
        CompositeFiberAut.conjugationMulEquiv_symm_hom]
      change
        (sourceIso.hom ≫ CompositeFiberAut.hom pair.1.1 ≫ sourceIso.inv) ≫
            comparison =
          comparison ≫
            (targetIso.hom ≫ CompositeFiberAut.hom pair.1.2 ≫ targetIso.inv)
      have relation :
          CompositeFiberAut.hom pair.1.1 ≫
              (sourceIso.inv ≫ comparison ≫ targetIso.hom) =
            (sourceIso.inv ≫ comparison ≫ targetIso.hom) ≫
              CompositeFiberAut.hom pair.1.2 := pair.2
      simpa only [Category.assoc, Iso.hom_inv_id_assoc,
        Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun middle => sourceIso.hom ≫ middle ≫ targetIso.inv)
          relation⟩
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · exact (CompositeFiberAut.conjugationMulEquiv sourceIso).symm_apply_apply
        pair.1.1
    · exact (CompositeFiberAut.conjugationMulEquiv targetIso).symm_apply_apply
        pair.1.2
  right_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · exact (CompositeFiberAut.conjugationMulEquiv sourceIso).apply_symm_apply
        pair.1.1
    · exact (CompositeFiberAut.conjugationMulEquiv targetIso).apply_symm_apply
        pair.1.2
  map_mul' left right := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul (CompositeFiberAut.conjugationMulEquiv sourceIso)
        left.1.1 right.1.1
    · exact map_mul (CompositeFiberAut.conjugationMulEquiv targetIso)
        left.1.2 right.1.2

/-- A raw pair lies in the conjugated comparison group exactly when its
inverse-conjugated pair lies in the source comparison group. -/
theorem inverseConjugatedPair_mem_qualifiedComparison_iff
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀)
    (pair : CompositeFiberAut G₁ × CompositeFiberAut H₁) :
    ((CompositeFiberAut.conjugationMulEquiv sourceIso).symm pair.1,
        (CompositeFiberAut.conjugationMulEquiv targetIso).symm pair.2) ∈
          qualifiedComparisonSubgroup comparison ↔
      pair ∈ qualifiedComparisonSubgroup
        ((sourceIso.inv.comp comparison).comp targetIso.hom) := by
  constructor
  · intro membership
    have targetMembership :
        ((CompositeFiberAut.conjugationMulEquiv sourceIso)
            ((CompositeFiberAut.conjugationMulEquiv sourceIso).symm pair.1),
          (CompositeFiberAut.conjugationMulEquiv targetIso)
            ((CompositeFiberAut.conjugationMulEquiv targetIso).symm pair.2)) ∈
          qualifiedComparisonSubgroup
            ((sourceIso.inv.comp comparison).comp targetIso.hom) :=
      (qualifiedComparisonEndpointConjugationMulEquiv
        sourceIso targetIso comparison ⟨_, membership⟩).2
    simpa only [MulEquiv.apply_symm_apply] using targetMembership
  · intro membership
    exact ((qualifiedComparisonEndpointConjugationMulEquiv
      sourceIso targetIso comparison).symm ⟨pair, membership⟩).2

/-- The source projection square for endpoint conjugation commutes. -/
@[simp] theorem qualifiedComparisonEndpointConjugation_sourceProjection
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀)
    (pair : qualifiedComparisonSubgroup comparison) :
    qualifiedComparisonSourceProjection
        ((sourceIso.inv.comp comparison).comp targetIso.hom)
        (qualifiedComparisonEndpointConjugationMulEquiv
          sourceIso targetIso comparison pair) =
      CompositeFiberAut.conjugationMulEquiv sourceIso
        (qualifiedComparisonSourceProjection comparison pair) :=
  rfl

/-- The target projection square for endpoint conjugation commutes. -/
@[simp] theorem qualifiedComparisonEndpointConjugation_targetProjection
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀)
    (pair : qualifiedComparisonSubgroup comparison) :
    qualifiedComparisonTargetProjection
        ((sourceIso.inv.comp comparison).comp targetIso.hom)
        (qualifiedComparisonEndpointConjugationMulEquiv
          sourceIso targetIso comparison pair) =
      CompositeFiberAut.conjugationMulEquiv targetIso
        (qualifiedComparisonTargetProjection comparison pair) :=
  rfl

/-- Endpoint conjugation restricts to the target comparison stabilizers. -/
noncomputable def qualifiedComparisonEndpointConjugationTargetStabilizerMulEquiv
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀) :
    qualifiedComparisonTargetStabilizer comparison ≃*
      qualifiedComparisonTargetStabilizer
        ((sourceIso.inv.comp comparison).comp targetIso.hom) where
  toFun stabilizer :=
    ⟨CompositeFiberAut.conjugationMulEquiv targetIso stabilizer.1, by
      change
        ((sourceIso.inv.comp comparison).comp targetIso.hom).comp
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv targetIso stabilizer.1)) =
          (sourceIso.inv.comp comparison).comp targetIso.hom
      rw [CompositeFiberAut.conjugationMulEquiv_hom]
      change
        (sourceIso.inv ≫ comparison ≫ targetIso.hom) ≫
            (targetIso.inv ≫ CompositeFiberAut.hom stabilizer.1 ≫
              targetIso.hom) =
          sourceIso.inv ≫ comparison ≫ targetIso.hom
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        congrArg (fun middle => sourceIso.inv ≫ middle ≫ targetIso.hom)
          stabilizer.2⟩
  invFun stabilizer :=
    ⟨(CompositeFiberAut.conjugationMulEquiv targetIso).symm stabilizer.1, by
      change comparison.comp
          (CompositeFiberAut.hom
            ((CompositeFiberAut.conjugationMulEquiv targetIso).symm
              stabilizer.1)) = comparison
      rw [CompositeFiberAut.conjugationMulEquiv_symm_hom]
      change
        comparison ≫
            (targetIso.hom ≫ CompositeFiberAut.hom stabilizer.1 ≫
              targetIso.inv) = comparison
      have relation :
          (sourceIso.inv ≫ comparison ≫ targetIso.hom) ≫
              CompositeFiberAut.hom stabilizer.1 =
            sourceIso.inv ≫ comparison ≫ targetIso.hom := stabilizer.2
      simpa only [Category.assoc, Iso.hom_inv_id_assoc,
        Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun middle => sourceIso.hom ≫ middle ≫ targetIso.inv)
          relation⟩
  left_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv targetIso).symm_apply_apply _
  right_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv targetIso).apply_symm_apply _
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (CompositeFiberAut.conjugationMulEquiv targetIso) _ _

/-- Endpoint conjugation restricts to the source comparison stabilizers. -/
noncomputable def qualifiedComparisonEndpointConjugationSourceStabilizerMulEquiv
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀) :
    qualifiedComparisonSourceStabilizer comparison ≃*
      qualifiedComparisonSourceStabilizer
        ((sourceIso.inv.comp comparison).comp targetIso.hom) where
  toFun stabilizer :=
    ⟨CompositeFiberAut.conjugationMulEquiv sourceIso stabilizer.1, by
      change
        (CompositeFiberAut.hom
          (CompositeFiberAut.conjugationMulEquiv sourceIso stabilizer.1)).comp
            ((sourceIso.inv.comp comparison).comp targetIso.hom) =
          (sourceIso.inv.comp comparison).comp targetIso.hom
      rw [CompositeFiberAut.conjugationMulEquiv_hom]
      change
        (sourceIso.inv ≫ CompositeFiberAut.hom stabilizer.1 ≫ sourceIso.hom) ≫
            (sourceIso.inv ≫ comparison ≫ targetIso.hom) =
          sourceIso.inv ≫ comparison ≫ targetIso.hom
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        congrArg (fun middle => sourceIso.inv ≫ middle ≫ targetIso.hom)
          stabilizer.2⟩
  invFun stabilizer :=
    ⟨(CompositeFiberAut.conjugationMulEquiv sourceIso).symm stabilizer.1, by
      change
        (CompositeFiberAut.hom
          ((CompositeFiberAut.conjugationMulEquiv sourceIso).symm
            stabilizer.1)).comp comparison = comparison
      rw [CompositeFiberAut.conjugationMulEquiv_symm_hom]
      change
        (sourceIso.hom ≫ CompositeFiberAut.hom stabilizer.1 ≫ sourceIso.inv) ≫
            comparison = comparison
      have relation :
          CompositeFiberAut.hom stabilizer.1 ≫
              (sourceIso.inv ≫ comparison ≫ targetIso.hom) =
            sourceIso.inv ≫ comparison ≫ targetIso.hom := stabilizer.2
      simpa only [Category.assoc, Iso.hom_inv_id_assoc,
        Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun middle => sourceIso.hom ≫ middle ≫ targetIso.inv)
          relation⟩
  left_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv sourceIso).symm_apply_apply _
  right_inv stabilizer := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv sourceIso).apply_symm_apply _
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (CompositeFiberAut.conjugationMulEquiv sourceIso) _ _

/-- The kernel of the source projection is transported by the full comparison
group equivalence. -/
noncomputable def qualifiedComparisonEndpointConjugationSourceKernelMulEquiv
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀) :
    (qualifiedComparisonSourceProjection comparison).ker ≃*
      (qualifiedComparisonSourceProjection
        ((sourceIso.inv.comp comparison).comp targetIso.hom)).ker where
  toFun pair :=
    ⟨qualifiedComparisonEndpointConjugationMulEquiv
        sourceIso targetIso comparison pair.1, by
      change qualifiedComparisonSourceProjection
          ((sourceIso.inv.comp comparison).comp targetIso.hom)
          (qualifiedComparisonEndpointConjugationMulEquiv
            sourceIso targetIso comparison pair.1) = 1
      rw [qualifiedComparisonEndpointConjugation_sourceProjection, pair.2,
        map_one]⟩
  invFun pair :=
    ⟨(qualifiedComparisonEndpointConjugationMulEquiv
        sourceIso targetIso comparison).symm pair.1, by
      apply (CompositeFiberAut.conjugationMulEquiv sourceIso).injective
      rw [map_one,
        ← qualifiedComparisonEndpointConjugation_sourceProjection,
        (qualifiedComparisonEndpointConjugationMulEquiv
          sourceIso targetIso comparison).apply_symm_apply]
      exact pair.2⟩
  left_inv pair := by
    apply Subtype.ext
    exact (qualifiedComparisonEndpointConjugationMulEquiv
      sourceIso targetIso comparison).symm_apply_apply pair.1
  right_inv pair := by
    apply Subtype.ext
    exact (qualifiedComparisonEndpointConjugationMulEquiv
      sourceIso targetIso comparison).apply_symm_apply pair.1
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (qualifiedComparisonEndpointConjugationMulEquiv
      sourceIso targetIso comparison) left.1 right.1

/-- The kernel of the target projection is transported by the full comparison
group equivalence. -/
noncomputable def qualifiedComparisonEndpointConjugationTargetKernelMulEquiv
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀) :
    (qualifiedComparisonTargetProjection comparison).ker ≃*
      (qualifiedComparisonTargetProjection
        ((sourceIso.inv.comp comparison).comp targetIso.hom)).ker where
  toFun pair :=
    ⟨qualifiedComparisonEndpointConjugationMulEquiv
        sourceIso targetIso comparison pair.1, by
      change qualifiedComparisonTargetProjection
          ((sourceIso.inv.comp comparison).comp targetIso.hom)
          (qualifiedComparisonEndpointConjugationMulEquiv
            sourceIso targetIso comparison pair.1) = 1
      rw [qualifiedComparisonEndpointConjugation_targetProjection, pair.2,
        map_one]⟩
  invFun pair :=
    ⟨(qualifiedComparisonEndpointConjugationMulEquiv
        sourceIso targetIso comparison).symm pair.1, by
      apply (CompositeFiberAut.conjugationMulEquiv targetIso).injective
      rw [map_one,
        ← qualifiedComparisonEndpointConjugation_targetProjection,
        (qualifiedComparisonEndpointConjugationMulEquiv
          sourceIso targetIso comparison).apply_symm_apply]
      exact pair.2⟩
  left_inv pair := by
    apply Subtype.ext
    exact (qualifiedComparisonEndpointConjugationMulEquiv
      sourceIso targetIso comparison).symm_apply_apply pair.1
  right_inv pair := by
    apply Subtype.ext
    exact (qualifiedComparisonEndpointConjugationMulEquiv
      sourceIso targetIso comparison).apply_symm_apply pair.1
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (qualifiedComparisonEndpointConjugationMulEquiv
      sourceIso targetIso comparison) left.1 right.1

/-- Target-partner fibers are equivalent under the two endpoint
conjugations. -/
noncomputable def qualifiedComparisonEndpointConjugationTargetLiftEquiv
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀) (base : CompositeFiberAut G₀) :
    QualifiedComparisonTargetLift comparison base ≃
      QualifiedComparisonTargetLift
        ((sourceIso.inv.comp comparison).comp targetIso.hom)
        (CompositeFiberAut.conjugationMulEquiv sourceIso base) where
  toFun lift :=
    ⟨CompositeFiberAut.conjugationMulEquiv targetIso lift.1, by
      let pair : qualifiedComparisonSubgroup comparison :=
        ⟨(base, lift.1), lift.2⟩
      exact (qualifiedComparisonEndpointConjugationMulEquiv
        sourceIso targetIso comparison pair).2⟩
  invFun lift :=
    ⟨(CompositeFiberAut.conjugationMulEquiv targetIso).symm lift.1, by
      change (CompositeFiberAut.hom base).comp comparison =
        comparison.comp (CompositeFiberAut.hom
          ((CompositeFiberAut.conjugationMulEquiv targetIso).symm lift.1))
      rw [CompositeFiberAut.conjugationMulEquiv_symm_hom]
      change CompositeFiberAut.hom base ≫ comparison =
        comparison ≫
          (targetIso.hom ≫ CompositeFiberAut.hom lift.1 ≫ targetIso.inv)
      have relation :
          (sourceIso.inv ≫ CompositeFiberAut.hom base ≫ sourceIso.hom) ≫
              (sourceIso.inv ≫ comparison ≫ targetIso.hom) =
            (sourceIso.inv ≫ comparison ≫ targetIso.hom) ≫
              CompositeFiberAut.hom lift.1 := lift.2
      simpa only [Category.assoc, Iso.hom_inv_id_assoc,
        Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun middle => sourceIso.hom ≫ middle ≫ targetIso.inv)
          relation⟩
  left_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv targetIso).symm_apply_apply _
  right_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv targetIso).apply_symm_apply _

/-- Source-partner fibers are equivalent under the two endpoint
conjugations. -/
noncomputable def qualifiedComparisonEndpointConjugationSourceLiftEquiv
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀) (pulled : CompositeFiberAut H₀) :
    QualifiedComparisonSourceLift comparison pulled ≃
      QualifiedComparisonSourceLift
        ((sourceIso.inv.comp comparison).comp targetIso.hom)
        (CompositeFiberAut.conjugationMulEquiv targetIso pulled) where
  toFun lift :=
    ⟨CompositeFiberAut.conjugationMulEquiv sourceIso lift.1, by
      let pair : qualifiedComparisonSubgroup comparison :=
        ⟨(lift.1, pulled), lift.2⟩
      exact (qualifiedComparisonEndpointConjugationMulEquiv
        sourceIso targetIso comparison pair).2⟩
  invFun lift :=
    ⟨(CompositeFiberAut.conjugationMulEquiv sourceIso).symm lift.1, by
      change (CompositeFiberAut.hom
          ((CompositeFiberAut.conjugationMulEquiv sourceIso).symm lift.1)).comp
            comparison = comparison.comp (CompositeFiberAut.hom pulled)
      rw [CompositeFiberAut.conjugationMulEquiv_symm_hom]
      change
        (sourceIso.hom ≫ CompositeFiberAut.hom lift.1 ≫ sourceIso.inv) ≫
            comparison = comparison ≫ CompositeFiberAut.hom pulled
      have relation :
          CompositeFiberAut.hom lift.1 ≫
              (sourceIso.inv ≫ comparison ≫ targetIso.hom) =
            (sourceIso.inv ≫ comparison ≫ targetIso.hom) ≫
              (targetIso.inv ≫ CompositeFiberAut.hom pulled ≫ targetIso.hom) :=
        lift.2
      simpa only [Category.assoc, Iso.hom_inv_id_assoc,
        Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun middle => sourceIso.hom ≫ middle ≫ targetIso.inv)
          relation⟩
  left_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv sourceIso).symm_apply_apply _
  right_inv lift := by
    apply Subtype.ext
    exact (CompositeFiberAut.conjugationMulEquiv sourceIso).apply_symm_apply _

/-- The target-stabilizer action on a nonempty target-partner fiber is
equivariant under endpoint conjugation. -/
theorem qualifiedComparisonEndpointConjugation_targetLift_smul
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀) (base : CompositeFiberAut G₀)
    (stabilizer : qualifiedComparisonTargetStabilizer comparison)
    (lift : QualifiedComparisonTargetLift comparison base) :
    qualifiedComparisonEndpointConjugationTargetLiftEquiv
        sourceIso targetIso comparison base (stabilizer • lift) =
      qualifiedComparisonEndpointConjugationTargetStabilizerMulEquiv
          sourceIso targetIso comparison stabilizer •
        qualifiedComparisonEndpointConjugationTargetLiftEquiv
          sourceIso targetIso comparison base lift := by
  apply Subtype.ext
  exact map_mul (CompositeFiberAut.conjugationMulEquiv targetIso)
    stabilizer.1 lift.1

/-- The source-stabilizer action on a nonempty source-partner fiber is
equivariant under endpoint conjugation. -/
theorem qualifiedComparisonEndpointConjugation_sourceLift_smul
    {U : AtomCarrier.{u}}
    {G₀ G₁ H₀ H₁ : GeometryPackage.{u, v} U}
    (sourceIso : G₀ ≅ G₁) (targetIso : H₀ ≅ H₁)
    (comparison : GeometryTotalHom G₀ H₀) (pulled : CompositeFiberAut H₀)
    (stabilizer : qualifiedComparisonSourceStabilizer comparison)
    (lift : QualifiedComparisonSourceLift comparison pulled) :
    qualifiedComparisonEndpointConjugationSourceLiftEquiv
        sourceIso targetIso comparison pulled (stabilizer • lift) =
      qualifiedComparisonEndpointConjugationSourceStabilizerMulEquiv
          sourceIso targetIso comparison stabilizer •
        qualifiedComparisonEndpointConjugationSourceLiftEquiv
          sourceIso targetIso comparison pulled lift := by
  apply Subtype.ext
  exact map_mul (CompositeFiberAut.conjugationMulEquiv sourceIso)
    stabilizer.1 lift.1

namespace UpperGeometryCompatibleProblemInputData

/-- The generated comparison is exactly the canonical companion comparison
written in the two selected generated complete presentations. -/
theorem generatedCompatibleUpperGeometryMateAt_eq_endpoint_conjugation
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.generatedCompatibleUpperGeometryMateAt i =
      (((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i).inv).comp
        (input.canonicalCompanionUpperRefinementBCSolution.component i)).comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i).hom := by
  have componentEquality := congrArg
    (fun solution : GeometryCompatibleUpperRefinementBCSolution input =>
      solution.component i)
    input.canonicalGeneratedUpperRefinementBCSolutionEquiv_companion
  change input.canonicalSolutionForwardAt
      input.canonicalCompanionUpperRefinementBCSolution i =
    input.generatedCompatibleUpperGeometryMateAt i at componentEquality
  exact componentEquality.symm.trans
    (input.canonicalSolutionForwardAt_exact_normalization
      input.canonicalCompanionUpperRefinementBCSolution i)

/-- The reverse selected presentation change is the independently exactified
backward solution component. -/
theorem canonicalCompanionUpperGeometryMateAt_eq_endpoint_conjugation
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.canonicalCompanionUpperRefinementBCSolution.component i =
      (((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i).hom).comp
        (input.generatedCompatibleUpperGeometryMateAt i)).comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i).inv := by
  change input.generatedSolutionBackwardAt
      input.generatedGeometryCompatibleUpperRefinementBCSolution i = _
  exact input.generatedSolutionBackwardAt_exact_normalization
    input.generatedGeometryCompatibleUpperRefinementBCSolution i

/-- G-118(C1): the actual canonical and generated comparison groups are
multiplicatively equivalent under the two selected complete endpoint changes. -/
noncomputable def canonicalGeneratedQualifiedComparisonMulEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    qualifiedComparisonSubgroup
        (input.canonicalCompanionUpperRefinementBCSolution.component i) ≃*
      qualifiedComparisonSubgroup
        (input.generatedCompatibleUpperGeometryMateAt i) := by
  rw [input.generatedCompatibleUpperGeometryMateAt_eq_endpoint_conjugation i]
  exact qualifiedComparisonEndpointConjugationMulEquiv
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalCompanionUpperRefinementBCSolution.component i)

/-- The actual target stabilizers are identified by the pulled endpoint
presentation change. -/
noncomputable def canonicalGeneratedTargetStabilizerMulEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    qualifiedComparisonTargetStabilizer
        (input.canonicalCompanionUpperRefinementBCSolution.component i) ≃*
      qualifiedComparisonTargetStabilizer
        (input.generatedCompatibleUpperGeometryMateAt i) := by
  rw [input.generatedCompatibleUpperGeometryMateAt_eq_endpoint_conjugation i]
  exact qualifiedComparisonEndpointConjugationTargetStabilizerMulEquiv
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalCompanionUpperRefinementBCSolution.component i)

/-- The actual source stabilizers are identified by the base endpoint
presentation change. -/
noncomputable def canonicalGeneratedSourceStabilizerMulEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    qualifiedComparisonSourceStabilizer
        (input.canonicalCompanionUpperRefinementBCSolution.component i) ≃*
      qualifiedComparisonSourceStabilizer
        (input.generatedCompatibleUpperGeometryMateAt i) := by
  rw [input.generatedCompatibleUpperGeometryMateAt_eq_endpoint_conjugation i]
  exact qualifiedComparisonEndpointConjugationSourceStabilizerMulEquiv
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalCompanionUpperRefinementBCSolution.component i)

/-- The actual source-projection kernels are identified by the full
comparison-group transport. -/
noncomputable def canonicalGeneratedSourceProjectionKernelMulEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (qualifiedComparisonSourceProjection
      (input.canonicalCompanionUpperRefinementBCSolution.component i)).ker ≃*
    (qualifiedComparisonSourceProjection
      (input.generatedCompatibleUpperGeometryMateAt i)).ker := by
  rw [input.generatedCompatibleUpperGeometryMateAt_eq_endpoint_conjugation i]
  exact qualifiedComparisonEndpointConjugationSourceKernelMulEquiv
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalCompanionUpperRefinementBCSolution.component i)

/-- The actual target-projection kernels are identified by the full
comparison-group transport. -/
noncomputable def canonicalGeneratedTargetProjectionKernelMulEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (qualifiedComparisonTargetProjection
      (input.canonicalCompanionUpperRefinementBCSolution.component i)).ker ≃*
    (qualifiedComparisonTargetProjection
      (input.generatedCompatibleUpperGeometryMateAt i)).ker := by
  rw [input.generatedCompatibleUpperGeometryMateAt_eq_endpoint_conjugation i]
  exact qualifiedComparisonEndpointConjugationTargetKernelMulEquiv
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalCompanionUpperRefinementBCSolution.component i)

/-- Every actual target-partner fiber is transported to the corresponding
generated target-partner fiber. -/
noncomputable def canonicalGeneratedQualifiedComparisonTargetLiftEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (base : CompositeFiberAut
      (input.canonicalAuthoredBaseRouteGeometryAt i)) :
    QualifiedComparisonTargetLift
        (input.canonicalCompanionUpperRefinementBCSolution.component i) base ≃
      QualifiedComparisonTargetLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
          base) := by
  rw [input.generatedCompatibleUpperGeometryMateAt_eq_endpoint_conjugation i]
  exact qualifiedComparisonEndpointConjugationTargetLiftEquiv
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalCompanionUpperRefinementBCSolution.component i) base

/-- Every actual source-partner fiber is transported to the corresponding
generated source-partner fiber. -/
noncomputable def canonicalGeneratedQualifiedComparisonSourceLiftEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (pulled : CompositeFiberAut
      (input.canonicalAuthoredPulledRouteGeometryAt i)) :
    QualifiedComparisonSourceLift
        (input.canonicalCompanionUpperRefinementBCSolution.component i) pulled ≃
      QualifiedComparisonSourceLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
          pulled) := by
  rw [input.generatedCompatibleUpperGeometryMateAt_eq_endpoint_conjugation i]
  exact qualifiedComparisonEndpointConjugationSourceLiftEquiv
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalCompanionUpperRefinementBCSolution.component i) pulled

/-- Nonemptiness of every actual target-partner fiber is preserved and
reflected by the selected presentation change. -/
theorem canonicalGeneratedQualifiedComparisonTargetLift_nonempty_iff
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (base : CompositeFiberAut
      (input.canonicalAuthoredBaseRouteGeometryAt i)) :
    Nonempty (QualifiedComparisonTargetLift
        (input.canonicalCompanionUpperRefinementBCSolution.component i) base) ↔
      Nonempty (QualifiedComparisonTargetLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
          base)) := by
  constructor
  · rintro ⟨lift⟩
    exact ⟨input.canonicalGeneratedQualifiedComparisonTargetLiftEquivAt
      i base lift⟩
  · rintro ⟨lift⟩
    exact ⟨(input.canonicalGeneratedQualifiedComparisonTargetLiftEquivAt
      i base).symm lift⟩

/-- Nonemptiness of every actual source-partner fiber is preserved and
reflected by the selected presentation change. -/
theorem canonicalGeneratedQualifiedComparisonSourceLift_nonempty_iff
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (pulled : CompositeFiberAut
      (input.canonicalAuthoredPulledRouteGeometryAt i)) :
    Nonempty (QualifiedComparisonSourceLift
        (input.canonicalCompanionUpperRefinementBCSolution.component i) pulled) ↔
      Nonempty (QualifiedComparisonSourceLift
        (input.generatedCompatibleUpperGeometryMateAt i)
        (CompositeFiberAut.conjugationMulEquiv
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
          pulled)) := by
  constructor
  · rintro ⟨lift⟩
    exact ⟨input.canonicalGeneratedQualifiedComparisonSourceLiftEquivAt
      i pulled lift⟩
  · rintro ⟨lift⟩
    exact ⟨(input.canonicalGeneratedQualifiedComparisonSourceLiftEquivAt
      i pulled).symm lift⟩

/-- Base-endpoint conjugation preserves the coefficient observation in the
forward selected presentation change. -/
theorem canonicalAuthoredBaseConjugation_coefficientHom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.canonicalAuthoredBaseRouteGeometryAt i)) :
    (CompositeFiberAut.hom
      (CompositeFiberAut.conjugationMulEquiv
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
        automorphism)).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom := by
  rw [CompositeFiberAut.conjugationMulEquiv_hom]
  unfold GeometryTotalHom.comp GeomReadHom.comp
  change
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
        i).geometry.coefficientHom.comp
      ((CompositeFiberAut.hom automorphism).geometry.coefficientHom.comp
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
          i).geometry.coefficientHom) = _
  rw [input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_coefficient_id,
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_coefficient_id]
  rfl

/-- Base-endpoint inverse conjugation preserves the coefficient observation. -/
theorem canonicalAuthoredBaseConjugation_symm_coefficientHom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.generatedBaseRouteGeometryAt i)) :
    (CompositeFiberAut.hom
      ((CompositeFiberAut.conjugationMulEquiv
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)).symm
        automorphism)).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom := by
  rw [CompositeFiberAut.conjugationMulEquiv_symm_hom]
  unfold GeometryTotalHom.comp GeomReadHom.comp
  change
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
        i).geometry.coefficientHom.comp
      ((CompositeFiberAut.hom automorphism).geometry.coefficientHom.comp
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
          i).geometry.coefficientHom) = _
  rw [input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_coefficient_id,
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_coefficient_id]
  rfl

/-- Pulled-endpoint conjugation preserves the coefficient observation in the
forward selected presentation change. -/
theorem canonicalAuthoredPulledConjugation_coefficientHom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.canonicalAuthoredPulledRouteGeometryAt i)) :
    (CompositeFiberAut.hom
      (CompositeFiberAut.conjugationMulEquiv
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
        automorphism)).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom := by
  rw [CompositeFiberAut.conjugationMulEquiv_hom]
  unfold GeometryTotalHom.comp GeomReadHom.comp
  change
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
        i).geometry.coefficientHom.comp
      ((CompositeFiberAut.hom automorphism).geometry.coefficientHom.comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
          i).geometry.coefficientHom) = _
  rw [input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_coefficient_id,
    input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_coefficient_id]
  rfl

/-- Pulled-endpoint inverse conjugation preserves the coefficient
observation. -/
theorem canonicalAuthoredPulledConjugation_symm_coefficientHom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.generatedPulledRouteGeometryAt i)) :
    (CompositeFiberAut.hom
      ((CompositeFiberAut.conjugationMulEquiv
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)).symm
        automorphism)).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom := by
  rw [CompositeFiberAut.conjugationMulEquiv_symm_hom]
  unfold GeometryTotalHom.comp GeomReadHom.comp
  change
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
        i).geometry.coefficientHom.comp
      ((CompositeFiberAut.hom automorphism).geometry.coefficientHom.comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
          i).geometry.coefficientHom) = _
  rw [input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_coefficient_id,
    input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_coefficient_id]
  rfl

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
