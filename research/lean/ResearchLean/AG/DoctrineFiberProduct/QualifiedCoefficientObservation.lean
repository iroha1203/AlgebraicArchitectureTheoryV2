import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonStabilizer

/-!
# Coefficient observation of composite-fiber automorphisms

This is the coefficient projection fixed by G-118(D).  It is introduced here
as a shared predecessor for the coefficient-kernel action required by C2.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

namespace CompositeFiberAut

/-- The coefficient-ring equivalence underlying a qualified complete-
geometry automorphism. -/
noncomputable def coefficientRingEquiv
    {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    (automorphism : CompositeFiberAut G) :
    G.Coefficient ≃+* G.Coefficient where
  toFun := (CompositeFiberAut.hom automorphism).geometry.coefficientHom
  invFun := (CompositeFiberAut.inv automorphism).geometry.coefficientHom
  left_inv value := by
    exact congrArg
      (fun hom : GeometryTotalHom G G => hom.geometry.coefficientHom value)
      automorphism.1.hom_inv_id
  right_inv value := by
    exact congrArg
      (fun hom : GeometryTotalHom G G => hom.geometry.coefficientHom value)
      automorphism.1.inv_hom_id
  map_mul' := (CompositeFiberAut.hom automorphism).geometry.coefficientHom.map_mul
  map_add' := (CompositeFiberAut.hom automorphism).geometry.coefficientHom.map_add

/-- The coefficient-ring automorphism underlying a qualified complete-
geometry automorphism. -/
noncomputable def coefficientAut
    {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    (automorphism : CompositeFiberAut G) :
    Aut (CommRingCat.of G.Coefficient) :=
  (coefficientRingEquiv automorphism).toCommRingCatIso

/-- Coefficient observation is a group homomorphism.  Its product order is
the categorical `Aut` product order already used by `CompositeFiberAut`. -/
noncomputable def coefficientObservation
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    CompositeFiberAut G →* Aut (CommRingCat.of G.Coefficient) where
  toFun := coefficientAut
  map_one' := by
    apply CategoryTheory.Iso.ext
    ext value
    rfl
  map_mul' left right := by
    apply CategoryTheory.Iso.ext
    ext value
    rfl

/-- The coefficient observation exposes the actual forward coefficient map. -/
@[simp] theorem coefficientObservation_hom
    {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    (automorphism : CompositeFiberAut G) :
    (coefficientObservation G automorphism).hom.hom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom :=
  rfl

/-- Membership in the coefficient kernel is the literal coefficient-identity
condition used by coefficient-trivial reselections. -/
@[simp] theorem mem_coefficientObservation_ker_iff
    {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    {automorphism : CompositeFiberAut G} :
    automorphism ∈ (coefficientObservation G).ker ↔
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom =
        RingHom.id G.Coefficient := by
  change coefficientAut automorphism = 1 ↔ _
  constructor
  · intro equality
    exact congrArg
      (fun coefficientAutomorphism => coefficientAutomorphism.hom.hom)
      equality
  · intro equality
    apply CategoryTheory.Iso.ext
    ext value
    exact DFunLike.congr_fun equality value

end CompositeFiberAut

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
