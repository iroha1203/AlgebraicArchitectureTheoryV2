import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredTransportLaws

/-!
# Qualified comparison stabilizers

This module constructs the group attached to an arbitrary complete-geometry
comparison.  Its elements are pairs of qualified endpoint automorphisms that
intertwine the comparison.  The two projection fibers are described by the
actual left and right comparison stabilizers, including their choice-free
simply-transitive actions.  When the comparison is an isomorphism, the group
is identified with the graph of the existing composite-fiber conjugation.

Implementation notes: multiplication in `Aut` exposes the underlying
categorical homs in reverse textual order, so every closure and action proof
states that order explicitly.  The lift fibers are subtypes of the actual
comparison subgroup, rather than new compatibility certificates.  Their
actions are defined before any origin is selected; only the coordinate
equivalences choose an origin.  In the isomorphism branch the existing
composite-fiber conjugation is reused instead of introducing a parallel
endpoint-transport construction.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

/-- Pairs of qualified endpoint changes that preserve a comparison. -/
def qualifiedComparisonSubgroup
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (comparison : GeometryTotalHom G H) :
    Subgroup (CompositeFiberAut G × CompositeFiberAut H) where
  carrier pair :=
    (CompositeFiberAut.hom pair.1).comp comparison =
      comparison.comp (CompositeFiberAut.hom pair.2)
  one_mem' := by rfl
  mul_mem' := by
    rintro ⟨base₁, pulled₁⟩ ⟨base₂, pulled₂⟩ first second
    have first' :
        (show G ⟶ G from CompositeFiberAut.hom base₁) ≫ comparison =
          (show G ⟶ H from comparison) ≫ CompositeFiberAut.hom pulled₁ := first
    have second' :
        (show G ⟶ G from CompositeFiberAut.hom base₂) ≫ comparison =
          (show G ⟶ H from comparison) ≫ CompositeFiberAut.hom pulled₂ := second
    change
      ((show G ⟶ G from CompositeFiberAut.hom base₂) ≫
          CompositeFiberAut.hom base₁) ≫ comparison =
        (show G ⟶ H from comparison) ≫
          ((show H ⟶ H from CompositeFiberAut.hom pulled₂) ≫
            CompositeFiberAut.hom pulled₁)
    rw [Category.assoc, first', ← Category.assoc, second', Category.assoc]
  inv_mem' := by
    rintro ⟨base, pulled⟩ relation
    have relation' :
        (show G ⟶ G from base.1.hom) ≫ comparison =
          (show G ⟶ H from comparison) ≫ pulled.1.hom := relation
    change
      (show G ⟶ G from CompositeFiberAut.inv base) ≫ comparison =
        (show G ⟶ H from comparison) ≫ CompositeFiberAut.inv pulled
    calc
      (show G ⟶ G from base.1.inv) ≫ comparison =
          base.1.inv ≫ ((comparison ≫ pulled.1.hom) ≫ pulled.1.inv) := by simp
      _ = base.1.inv ≫ ((base.1.hom ≫ comparison) ≫ pulled.1.inv) := by
        rw [relation']
      _ = (show G ⟶ H from comparison) ≫ pulled.1.inv := by simp

/-- The source-endpoint projection from the comparison-preserving group. -/
def qualifiedComparisonSourceProjection
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (comparison : GeometryTotalHom G H) :
    qualifiedComparisonSubgroup comparison →* CompositeFiberAut G :=
  (MonoidHom.fst (CompositeFiberAut G) (CompositeFiberAut H)).comp
    (qualifiedComparisonSubgroup comparison).subtype

/-- The target-endpoint projection from the comparison-preserving group. -/
def qualifiedComparisonTargetProjection
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (comparison : GeometryTotalHom G H) :
    qualifiedComparisonSubgroup comparison →* CompositeFiberAut H :=
  (MonoidHom.snd (CompositeFiberAut G) (CompositeFiberAut H)).comp
    (qualifiedComparisonSubgroup comparison).subtype

/-- Qualified target changes invisible after the comparison. -/
def qualifiedComparisonTargetStabilizer
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (comparison : GeometryTotalHom G H) : Subgroup (CompositeFiberAut H) where
  carrier automorphism :=
    comparison.comp (CompositeFiberAut.hom automorphism) = comparison
  one_mem' := by rfl
  mul_mem' := by
    intro left right hleft hright
    have hleft' :
        (show G ⟶ H from comparison) ≫ CompositeFiberAut.hom left = comparison :=
      hleft
    have hright' :
        (show G ⟶ H from comparison) ≫ CompositeFiberAut.hom right = comparison :=
      hright
    change (show G ⟶ H from comparison) ≫
      ((show H ⟶ H from CompositeFiberAut.hom right) ≫
        CompositeFiberAut.hom left) = comparison
    rw [← Category.assoc, hright', hleft']
  inv_mem' := by
    intro automorphism relation
    have relation' :
        (show G ⟶ H from comparison) ≫ automorphism.1.hom =
          comparison := relation
    change (show G ⟶ H from comparison) ≫
      CompositeFiberAut.inv automorphism = comparison
    calc
      (show G ⟶ H from comparison) ≫ automorphism.1.inv =
          (comparison ≫ automorphism.1.hom) ≫ automorphism.1.inv := by
            rw [relation']
      _ = comparison := by simp

/-- Qualified source changes invisible before the comparison. -/
def qualifiedComparisonSourceStabilizer
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (comparison : GeometryTotalHom G H) : Subgroup (CompositeFiberAut G) where
  carrier automorphism :=
    (CompositeFiberAut.hom automorphism).comp comparison = comparison
  one_mem' := by rfl
  mul_mem' := by
    intro left right hleft hright
    have hleft' :
        (show G ⟶ G from CompositeFiberAut.hom left) ≫ comparison = comparison :=
      hleft
    have hright' :
        (show G ⟶ G from CompositeFiberAut.hom right) ≫ comparison = comparison :=
      hright
    change
      ((show G ⟶ G from CompositeFiberAut.hom right) ≫
        CompositeFiberAut.hom left) ≫
        comparison = comparison
    rw [Category.assoc, hleft', hright']
  inv_mem' := by
    intro automorphism relation
    have relation' :
        (show G ⟶ G from automorphism.1.hom) ≫ comparison =
          comparison := relation
    change (show G ⟶ G from CompositeFiberAut.inv automorphism) ≫
      comparison = comparison
    calc
      (show G ⟶ G from automorphism.1.inv) ≫ comparison =
          automorphism.1.inv ≫ (automorphism.1.hom ≫ comparison) := by
            rw [relation']
      _ = comparison := by simp

/-- Membership in the comparison subgroup is the literal intertwining
equation. -/
@[simp] theorem mem_qualifiedComparisonSubgroup
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H}
    {pair : CompositeFiberAut G × CompositeFiberAut H} :
    pair ∈ qualifiedComparisonSubgroup comparison ↔
      (CompositeFiberAut.hom pair.1).comp comparison =
        comparison.comp (CompositeFiberAut.hom pair.2) :=
  Iff.rfl

/-- Membership in the target stabilizer is the literal postcomparison fixing
equation. -/
@[simp] theorem mem_qualifiedComparisonTargetStabilizer
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H}
    {automorphism : CompositeFiberAut H} :
    automorphism ∈ qualifiedComparisonTargetStabilizer comparison ↔
      comparison.comp (CompositeFiberAut.hom automorphism) = comparison :=
  Iff.rfl

/-- Membership in the source stabilizer is the literal precomparison fixing
equation. -/
@[simp] theorem mem_qualifiedComparisonSourceStabilizer
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H}
    {automorphism : CompositeFiberAut G} :
    automorphism ∈ qualifiedComparisonSourceStabilizer comparison ↔
      (CompositeFiberAut.hom automorphism).comp comparison = comparison :=
  Iff.rfl

/-- The target changes lifting one fixed source change. -/
abbrev QualifiedComparisonTargetLift
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (comparison : GeometryTotalHom G H) (base : CompositeFiberAut G) :=
  { pulled : CompositeFiberAut H //
    (base, pulled) ∈ qualifiedComparisonSubgroup comparison }

/-- The source changes lifting one fixed target change. -/
abbrev QualifiedComparisonSourceLift
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (comparison : GeometryTotalHom G H) (pulled : CompositeFiberAut H) :=
  { base : CompositeFiberAut G //
    (base, pulled) ∈ qualifiedComparisonSubgroup comparison }

/-- Left composition by a target stabilizer preserves a target lift fiber. -/
noncomputable def qualifiedComparisonTargetLiftAction
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {base : CompositeFiberAut G}
    (stabilizer : qualifiedComparisonTargetStabilizer comparison)
    (lift : QualifiedComparisonTargetLift comparison base) :
    QualifiedComparisonTargetLift comparison base :=
  ⟨stabilizer.1 * lift.1, by
    have liftRelation :
        (show G ⟶ G from base.1.hom) ≫ comparison =
          (show G ⟶ H from comparison) ≫ lift.1.1.hom := lift.2
    have stabilizerRelation :
        (show G ⟶ H from comparison) ≫ stabilizer.1.1.hom = comparison :=
      stabilizer.2
    change
      (show G ⟶ G from base.1.hom) ≫ comparison =
        (show G ⟶ H from comparison) ≫
          (lift.1.1.hom ≫ stabilizer.1.1.hom)
    symm
    calc
      (show G ⟶ H from comparison) ≫
          (lift.1.1.hom ≫ stabilizer.1.1.hom) =
          (comparison ≫ lift.1.1.hom) ≫ stabilizer.1.1.hom := by simp
      _ = (base.1.hom ≫ comparison) ≫ stabilizer.1.1.hom := by
        rw [liftRelation]
      _ = base.1.hom ≫ (comparison ≫ stabilizer.1.1.hom) :=
        Category.assoc _ _ _
      _ = base.1.hom ≫ comparison := by rw [stabilizerRelation]
  ⟩

/-- Scalar multiplication on a target lift fiber is the actual target
stabilizer action. -/
noncomputable instance qualifiedComparisonTargetLiftSMul
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {base : CompositeFiberAut G} :
    SMul (qualifiedComparisonTargetStabilizer comparison)
      (QualifiedComparisonTargetLift comparison base) where
  smul := qualifiedComparisonTargetLiftAction

/-- The target stabilizer laws make its fiber action a multiplicative action. -/
noncomputable instance qualifiedComparisonTargetLiftMulAction
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {base : CompositeFiberAut G} :
    MulAction (qualifiedComparisonTargetStabilizer comparison)
      (QualifiedComparisonTargetLift comparison base) where
  one_smul lift := by
    apply Subtype.ext
    exact one_mul lift.1
  mul_smul left right lift := by
    apply Subtype.ext
    exact mul_assoc left.1 right.1 lift.1

/-- The target-stabilizer action on a nonempty lift fiber is free. -/
theorem qualifiedComparisonTargetLiftAction_free
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {base : CompositeFiberAut G}
    (lift : QualifiedComparisonTargetLift comparison base)
    {left right : qualifiedComparisonTargetStabilizer comparison}
    (equality : left • lift = right • lift) : left = right := by
  have valueEquality : left.1 * lift.1 = right.1 * lift.1 :=
    congrArg Subtype.val equality
  apply Subtype.ext
  exact mul_right_cancel valueEquality

/-- Any two target lifts differ by a target stabilizer, without choosing a
global basepoint for the fiber. -/
theorem qualifiedComparisonTargetLiftAction_transitive
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {base : CompositeFiberAut G}
    (source target : QualifiedComparisonTargetLift comparison base) :
    ∃ stabilizer : qualifiedComparisonTargetStabilizer comparison,
      stabilizer • source = target := by
  let difference : CompositeFiberAut H := target.1 * source.1⁻¹
  have sourceInverse :=
    (qualifiedComparisonSubgroup comparison).inv_mem source.2
  have sourceInverseRelation :
      (show G ⟶ G from base.1.inv) ≫ comparison =
        (show G ⟶ H from comparison) ≫ source.1.1.inv := sourceInverse
  have targetRelation :
      (show G ⟶ G from base.1.hom) ≫ comparison =
        (show G ⟶ H from comparison) ≫ target.1.1.hom := target.2
  have differenceMem :
      difference ∈ qualifiedComparisonTargetStabilizer comparison := by
    change
      (show G ⟶ H from comparison) ≫
          (source.1.1.inv ≫ target.1.1.hom) = comparison
    calc
      (show G ⟶ H from comparison) ≫
          (source.1.1.inv ≫ target.1.1.hom) =
          (comparison ≫ source.1.1.inv) ≫ target.1.1.hom := by simp
      _ = (base.1.inv ≫ comparison) ≫ target.1.1.hom := by
        rw [sourceInverseRelation]
      _ = base.1.inv ≫ (comparison ≫ target.1.1.hom) := Category.assoc _ _ _
      _ = base.1.inv ≫ (base.1.hom ≫ comparison) := by
        rw [targetRelation]
      _ = comparison := by simp
  refine ⟨⟨difference, differenceMem⟩, ?_⟩
  apply Subtype.ext
  change (target.1 * source.1⁻¹) * source.1 = target.1
  simp

/-- A nonempty target lift fiber is a torsor under the actual target
comparison stabilizer. -/
theorem qualifiedComparisonTargetLift_existsUnique
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {base : CompositeFiberAut G}
    (source target : QualifiedComparisonTargetLift comparison base) :
    ∃! stabilizer : qualifiedComparisonTargetStabilizer comparison,
      stabilizer • source = target := by
  obtain ⟨stabilizer, action⟩ :=
    qualifiedComparisonTargetLiftAction_transitive source target
  refine ⟨stabilizer, action, ?_⟩
  intro other otherAction
  exact qualifiedComparisonTargetLiftAction_free source
    (otherAction.trans action.symm)

/-- Choosing one target lift gives coordinates on the fiber.  The action and
its simply-transitive theorem above do not depend on this choice. -/
noncomputable def qualifiedComparisonTargetLiftEquiv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {base : CompositeFiberAut G}
    (origin : QualifiedComparisonTargetLift comparison base) :
    qualifiedComparisonTargetStabilizer comparison ≃
      QualifiedComparisonTargetLift comparison base :=
  Equiv.ofBijective (fun stabilizer => stabilizer • origin) ⟨
    fun _ _ equality => qualifiedComparisonTargetLiftAction_free origin equality,
    fun target => qualifiedComparisonTargetLiftAction_transitive origin target⟩

/-- Left multiplication by a source stabilizer preserves a source lift fiber. -/
noncomputable def qualifiedComparisonSourceLiftAction
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {pulled : CompositeFiberAut H}
    (stabilizer : qualifiedComparisonSourceStabilizer comparison)
    (lift : QualifiedComparisonSourceLift comparison pulled) :
    QualifiedComparisonSourceLift comparison pulled :=
  ⟨stabilizer.1 * lift.1, by
    have liftRelation :
        (show G ⟶ G from lift.1.1.hom) ≫ comparison =
          (show G ⟶ H from comparison) ≫ pulled.1.hom := lift.2
    have stabilizerRelation :
        (show G ⟶ G from stabilizer.1.1.hom) ≫ comparison = comparison :=
      stabilizer.2
    change
      ((show G ⟶ G from lift.1.1.hom) ≫ stabilizer.1.1.hom) ≫ comparison =
        (show G ⟶ H from comparison) ≫ pulled.1.hom
    calc
      ((show G ⟶ G from lift.1.1.hom) ≫ stabilizer.1.1.hom) ≫ comparison =
          lift.1.1.hom ≫ (stabilizer.1.1.hom ≫ comparison) :=
        Category.assoc _ _ _
      _ = lift.1.1.hom ≫ comparison := by rw [stabilizerRelation]
      _ = comparison ≫ pulled.1.hom := liftRelation
  ⟩

/-- Scalar multiplication on a source lift fiber is the actual source
stabilizer action. -/
noncomputable instance qualifiedComparisonSourceLiftSMul
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {pulled : CompositeFiberAut H} :
    SMul (qualifiedComparisonSourceStabilizer comparison)
      (QualifiedComparisonSourceLift comparison pulled) where
  smul := qualifiedComparisonSourceLiftAction

/-- The source stabilizer laws make its fiber action a multiplicative action. -/
noncomputable instance qualifiedComparisonSourceLiftMulAction
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {pulled : CompositeFiberAut H} :
    MulAction (qualifiedComparisonSourceStabilizer comparison)
      (QualifiedComparisonSourceLift comparison pulled) where
  one_smul lift := by
    apply Subtype.ext
    exact one_mul lift.1
  mul_smul left right lift := by
    apply Subtype.ext
    exact mul_assoc left.1 right.1 lift.1

/-- The source-stabilizer action on a nonempty lift fiber is free. -/
theorem qualifiedComparisonSourceLiftAction_free
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {pulled : CompositeFiberAut H}
    (lift : QualifiedComparisonSourceLift comparison pulled)
    {left right : qualifiedComparisonSourceStabilizer comparison}
    (equality : left • lift = right • lift) : left = right := by
  have valueEquality : left.1 * lift.1 = right.1 * lift.1 :=
    congrArg Subtype.val equality
  apply Subtype.ext
  exact mul_right_cancel valueEquality

/-- Any two source lifts differ by a source stabilizer. -/
theorem qualifiedComparisonSourceLiftAction_transitive
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {pulled : CompositeFiberAut H}
    (source target : QualifiedComparisonSourceLift comparison pulled) :
    ∃ stabilizer : qualifiedComparisonSourceStabilizer comparison,
      stabilizer • source = target := by
  let difference : CompositeFiberAut G := target.1 * source.1⁻¹
  have sourceInverse :=
    (qualifiedComparisonSubgroup comparison).inv_mem source.2
  have sourceInverseRelation :
      (show G ⟶ G from source.1.1.inv) ≫ comparison =
        (show G ⟶ H from comparison) ≫ pulled.1.inv := sourceInverse
  have targetRelation :
      (show G ⟶ G from target.1.1.hom) ≫ comparison =
        (show G ⟶ H from comparison) ≫ pulled.1.hom := target.2
  have differenceMem :
      difference ∈ qualifiedComparisonSourceStabilizer comparison := by
    change
      ((show G ⟶ G from source.1.1.inv) ≫ target.1.1.hom) ≫
        comparison = comparison
    calc
      ((show G ⟶ G from source.1.1.inv) ≫ target.1.1.hom) ≫ comparison =
          source.1.1.inv ≫ (target.1.1.hom ≫ comparison) :=
        Category.assoc _ _ _
      _ = source.1.1.inv ≫ (comparison ≫ pulled.1.hom) := by
        rw [targetRelation]
      _ = (source.1.1.inv ≫ comparison) ≫ pulled.1.hom := by simp
      _ = (comparison ≫ pulled.1.inv) ≫ pulled.1.hom := by
        rw [sourceInverseRelation]
      _ = comparison := by simp
  refine ⟨⟨difference, differenceMem⟩, ?_⟩
  apply Subtype.ext
  change (target.1 * source.1⁻¹) * source.1 = target.1
  simp

/-- A nonempty source lift fiber is a torsor under the actual source
comparison stabilizer. -/
theorem qualifiedComparisonSourceLift_existsUnique
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {pulled : CompositeFiberAut H}
    (source target : QualifiedComparisonSourceLift comparison pulled) :
    ∃! stabilizer : qualifiedComparisonSourceStabilizer comparison,
      stabilizer • source = target := by
  obtain ⟨stabilizer, action⟩ :=
    qualifiedComparisonSourceLiftAction_transitive source target
  refine ⟨stabilizer, action, ?_⟩
  intro other otherAction
  exact qualifiedComparisonSourceLiftAction_free source
    (otherAction.trans action.symm)

/-- Choosing one source lift gives coordinates on the opposite fiber. -/
noncomputable def qualifiedComparisonSourceLiftEquiv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {pulled : CompositeFiberAut H}
    (origin : QualifiedComparisonSourceLift comparison pulled) :
    qualifiedComparisonSourceStabilizer comparison ≃
      QualifiedComparisonSourceLift comparison pulled :=
  Equiv.ofBijective (fun stabilizer => stabilizer • origin) ⟨
    fun _ _ equality => qualifiedComparisonSourceLiftAction_free origin equality,
    fun target => qualifiedComparisonSourceLiftAction_transitive origin target⟩

/-- The source projection image is exactly the set of source changes having a
target lift. -/
theorem mem_qualifiedComparisonSourceProjection_range_iff
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {base : CompositeFiberAut G} :
    base ∈ (qualifiedComparisonSourceProjection comparison).range ↔
      Nonempty (QualifiedComparisonTargetLift comparison base) := by
  constructor
  · rintro ⟨pair, equality⟩
    refine ⟨⟨pair.1.2, ?_⟩⟩
    simpa only [qualifiedComparisonSourceProjection] using
      equality ▸ pair.2
  · rintro ⟨lift⟩
    exact ⟨⟨(base, lift.1), lift.2⟩, rfl⟩

/-- The target projection image is exactly the set of target changes having a
source lift. -/
theorem mem_qualifiedComparisonTargetProjection_range_iff
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H} {pulled : CompositeFiberAut H} :
    pulled ∈ (qualifiedComparisonTargetProjection comparison).range ↔
      Nonempty (QualifiedComparisonSourceLift comparison pulled) := by
  constructor
  · rintro ⟨pair, equality⟩
    refine ⟨⟨pair.1.1, ?_⟩⟩
    simpa only [qualifiedComparisonTargetProjection] using
      equality ▸ pair.2
  · rintro ⟨lift⟩
    exact ⟨⟨(lift.1, pulled), lift.2⟩, rfl⟩

/-- The kernel of the source projection is the actual target comparison
stabilizer. -/
noncomputable def qualifiedComparisonSourceProjectionKernelMulEquiv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (comparison : GeometryTotalHom G H) :
    (qualifiedComparisonSourceProjection comparison).ker ≃*
      qualifiedComparisonTargetStabilizer comparison where
  toFun kernel :=
    ⟨kernel.1.1.2, by
      have sourceOne : kernel.1.1.1 = 1 := kernel.2
      have relation :
          (show G ⟶ G from kernel.1.1.1.1.hom) ≫ comparison =
            (show G ⟶ H from comparison) ≫ kernel.1.1.2.1.hom := kernel.1.2
      rw [sourceOne] at relation
      simpa using relation.symm⟩
  invFun stabilizer :=
    ⟨⟨(1, stabilizer.1), by
      have relation :
          (show G ⟶ H from comparison) ≫ stabilizer.1.1.hom = comparison :=
        stabilizer.2
      change (𝟙 G : G ⟶ G) ≫ comparison =
        (show G ⟶ H from comparison) ≫ stabilizer.1.1.hom
      simpa using relation.symm⟩, rfl⟩
  left_inv kernel := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact kernel.2.symm
    · rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The kernel of the target projection is the actual source comparison
stabilizer. -/
noncomputable def qualifiedComparisonTargetProjectionKernelMulEquiv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (comparison : GeometryTotalHom G H) :
    (qualifiedComparisonTargetProjection comparison).ker ≃*
      qualifiedComparisonSourceStabilizer comparison where
  toFun kernel :=
    ⟨kernel.1.1.1, by
      have targetOne : kernel.1.1.2 = 1 := kernel.2
      have relation :
          (show G ⟶ G from kernel.1.1.1.1.hom) ≫ comparison =
            (show G ⟶ H from comparison) ≫ kernel.1.1.2.1.hom := kernel.1.2
      rw [targetOne] at relation
      simpa using relation⟩
  invFun stabilizer :=
    ⟨⟨(stabilizer.1, 1), by
      have relation :
          (show G ⟶ G from stabilizer.1.1.hom) ≫ comparison = comparison :=
        stabilizer.2
      change (show G ⟶ G from stabilizer.1.1.hom) ≫ comparison =
        (show G ⟶ H from comparison) ≫ (𝟙 H : H ⟶ H)
      simpa using relation⟩, rfl⟩
  left_inv kernel := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact kernel.2.symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- For an isomorphism, conjugation supplies every comparison-preserving pair. -/
noncomputable def qualifiedComparisonIsoGraphMulEquiv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) :
    CompositeFiberAut G ≃* qualifiedComparisonSubgroup iso.hom where
  toFun base :=
    ⟨(base, CompositeFiberAut.conjugationMulEquiv iso base), by
      change
        (show G ⟶ G from base.1.hom) ≫ iso.hom =
          (show G ⟶ H from iso.hom) ≫
            ((iso.inv ≫ base.1.hom) ≫ iso.hom)
      simp⟩
  invFun pair := pair.1.1
  left_inv _ := rfl
  right_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Iso.ext
      have relation :
          (show G ⟶ G from pair.1.1.1.hom) ≫ iso.hom =
            (show G ⟶ H from iso.hom) ≫ pair.1.2.1.hom := pair.2
      have conjugationRelation :
          (show G ⟶ H from iso.hom) ≫
              (CompositeFiberAut.conjugationMulEquiv iso pair.1.1).1.hom =
            pair.1.1.1.hom ≫ iso.hom := by
        change iso.hom ≫ CompositeFiberAut.hom
            (CompositeFiberAut.conjugationMulEquiv iso pair.1.1) =
          pair.1.1.1.hom ≫ iso.hom
        rw [CompositeFiberAut.conjugationMulEquiv_hom]
        change iso.hom ≫ ((iso.inv ≫ pair.1.1.1.hom) ≫ iso.hom) =
          pair.1.1.1.hom ≫ iso.hom
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact (cancel_epi iso.hom).1
        (conjugationRelation.trans relation)
  map_mul' left right := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact map_mul (CompositeFiberAut.conjugationMulEquiv iso) left right

/-- For an isomorphism, the source projection is an equivalence onto the full
qualified source group. -/
noncomputable def qualifiedComparisonIsoSourceProjectionMulEquiv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) :
    qualifiedComparisonSubgroup iso.hom ≃* CompositeFiberAut G :=
  (qualifiedComparisonIsoGraphMulEquiv iso).symm

/-- For an isomorphism, the target projection is an equivalence onto the full
qualified target group. -/
noncomputable def qualifiedComparisonIsoTargetProjectionMulEquiv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) :
    qualifiedComparisonSubgroup iso.hom ≃* CompositeFiberAut H :=
  (qualifiedComparisonIsoGraphMulEquiv iso).symm.trans
    (CompositeFiberAut.conjugationMulEquiv iso)

/-- The source equivalence of an isomorphic comparison is its actual source
projection. -/
@[simp] theorem qualifiedComparisonIsoSourceProjectionMulEquiv_apply
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) (pair : qualifiedComparisonSubgroup iso.hom) :
    qualifiedComparisonIsoSourceProjectionMulEquiv iso pair =
      qualifiedComparisonSourceProjection iso.hom pair :=
  rfl

/-- The target equivalence of an isomorphic comparison is its actual target
projection. -/
@[simp] theorem qualifiedComparisonIsoTargetProjectionMulEquiv_apply
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) (pair : qualifiedComparisonSubgroup iso.hom) :
    qualifiedComparisonIsoTargetProjectionMulEquiv iso pair =
      qualifiedComparisonTargetProjection iso.hom pair := by
  change CompositeFiberAut.conjugationMulEquiv iso pair.1.1 = pair.1.2
  have recovered := (qualifiedComparisonIsoGraphMulEquiv iso).apply_symm_apply pair
  exact congrArg (fun element => element.1.2) recovered

/-- The source projection of an isomorphic comparison is surjective. -/
theorem qualifiedComparisonIsoSourceProjection_surjective
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) :
    Function.Surjective (qualifiedComparisonSourceProjection iso.hom) := by
  simpa only [← qualifiedComparisonIsoSourceProjectionMulEquiv_apply iso] using
    (qualifiedComparisonIsoSourceProjectionMulEquiv iso).surjective

/-- The target projection of an isomorphic comparison is surjective. -/
theorem qualifiedComparisonIsoTargetProjection_surjective
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) :
    Function.Surjective (qualifiedComparisonTargetProjection iso.hom) := by
  intro target
  let pair := (qualifiedComparisonIsoTargetProjectionMulEquiv iso).symm target
  refine ⟨pair, ?_⟩
  rw [← qualifiedComparisonIsoTargetProjectionMulEquiv_apply]
  exact (qualifiedComparisonIsoTargetProjectionMulEquiv iso).apply_symm_apply target

/-- An isomorphic comparison has trivial target stabilizer. -/
theorem qualifiedComparisonTargetStabilizer_eq_bot_of_iso
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) :
    qualifiedComparisonTargetStabilizer iso.hom = ⊥ := by
  ext automorphism
  constructor
  · intro relation
    change iso.hom.comp automorphism.1.hom = iso.hom at relation
    have relation' :
        (show G ⟶ H from iso.hom) ≫ automorphism.1.hom = iso.hom := relation
    change automorphism = 1
    apply Subtype.ext
    apply Iso.ext
    have homIdentity : automorphism.1.hom = 𝟙 H :=
      (cancel_epi iso.hom).1 (by simpa using relation')
    simpa using homIdentity
  · intro identity
    change automorphism = 1 at identity
    subst automorphism
    rfl

/-- An isomorphic comparison has trivial source stabilizer. -/
theorem qualifiedComparisonSourceStabilizer_eq_bot_of_iso
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) :
    qualifiedComparisonSourceStabilizer iso.hom = ⊥ := by
  ext automorphism
  constructor
  · intro relation
    change automorphism.1.hom.comp iso.hom = iso.hom at relation
    have relation' :
        (show G ⟶ G from automorphism.1.hom) ≫ iso.hom = iso.hom := relation
    change automorphism = 1
    apply Subtype.ext
    apply Iso.ext
    have homIdentity : automorphism.1.hom = 𝟙 G :=
      (cancel_mono iso.hom).1 (by simpa using relation')
    simpa using homIdentity
  · intro identity
    change automorphism = 1 at identity
    subst automorphism
    rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
