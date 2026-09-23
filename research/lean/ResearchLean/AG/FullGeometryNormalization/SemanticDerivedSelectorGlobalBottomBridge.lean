import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorGlobalComparison
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorBottomReflection

/-!
# Bottom-fixed part of the unrestricted semantic comparison

The bottom condition on the full complete-geometry endpoint group is the
kernel of its actual projection to pointed-doctrine automorphisms.  This
formulation keeps the bottom subgroup distinct from the full group, where
endpoint automorphisms may move the pointed doctrine.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss
open RealizationComparisonIdempotents

section

variable {U : AtomCarrier.{u}}
variable (input : BCSemanticInput U)
variable (interpretation : BCDiagnosticInterpretation U input)
variable (z : input.diagnostic.TwoCell)
variable (omega : DefectCochain interpretation.data)
variable (k : Type v) [CommRing k]
variable (g : FixedCoefficientGeometryAt
  (semanticExactBarSourceCoreAt input interpretation z) k)
variable (endpoint_eq : packagePoint
  (semanticExactBarSourceCoreAt input interpretation z) =
    input.square.southwest)
variable (square_isPullback : IsPullback input.square.left input.square.top
  input.square.bottom input.square.right)

/-- Observe both unrestricted endpoint automorphisms at their actual package
bottoms. -/
noncomputable def semanticExactGlobalBottomEndpointHom :
    SemanticExactGlobalH input interpretation z omega k g endpoint_eq
        square_isPullback →*
      (Aut ((crossStageProjection.{u, v} U).obj
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq).1) ×
       Aut ((crossStageProjection.{u, v} U).obj
        (semanticDerivedViaBaseGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq).1)) :=
  (MonoidHom.prodMap
      (functorAutomorphismHom (crossStageProjection.{u, v} U) _)
      (functorAutomorphismHom (crossStageProjection.{u, v} U) _)).comp
    (Subgroup.subtype _)

/-- The literal bottom subgroup of the full centralizer. -/
noncomputable abbrev SemanticExactGlobalBottomH :=
  (semanticExactGlobalBottomEndpointHom input interpretation z omega k g
    endpoint_eq square_isPullback).ker

/-- Membership in the global bottom group means that both complete-geometry
endpoint morphisms fix their pointed-doctrine bases. -/
theorem mem_SemanticExactGlobalBottomH
    (pair : SemanticExactGlobalH input interpretation z omega k g endpoint_eq
      square_isPullback) :
    pair ∈ SemanticExactGlobalBottomH input interpretation z omega k g
        endpoint_eq square_isPullback ↔
      pair.1.1.hom.base.base =
          𝟙 (packagePoint (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1.core) ∧
        pair.1.2.hom.base.base =
          𝟙 (packagePoint (semanticDerivedViaBaseGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1.core) := by
  change semanticExactGlobalBottomEndpointHom input interpretation z omega k g
      endpoint_eq square_isPullback pair = 1 ↔ _
  constructor
  · intro h
    have h₁ := congrArg (fun p => p.1.hom) h
    have h₂ := congrArg (fun p => p.2.hom) h
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    apply Prod.ext
    · apply Iso.ext
      exact h₁
    · apply Iso.ext
      exact h₂

/-- An unrestricted complete-geometry automorphism with identity bottom map
is an automorphism in the corresponding fixed fiber. -/
noncomputable def geometryFiberAutOfBottomIdentity
    {X : ExtractionInstance U} (G : GeomFiber.{u, v} X)
    (a : Aut G.1)
    (hbottom : a.hom.base.base = 𝟙 (packagePoint G.1.core)) : Aut G := by
  have hmap : functorAutomorphismHom (crossStageProjection.{u, v} U)
      G.1 a = 1 := by
    apply Iso.ext
    exact hbottom
  have hinv : a.inv.base.base = 𝟙 (packagePoint G.1.core) := by
    have h := congrArg
      (fun q : Aut ((crossStageProjection.{u, v} U).obj G.1) => q.inv) hmap
    exact h
  refine
    { hom := ⟨a.hom, ?_⟩
      inv := ⟨a.inv, ?_⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply CategoryTheory.IsHomLift.of_commsq
      (crossStageProjection.{u, v} U) (𝟙 X) a.hom _ _
    change a.hom.base.base ≫ eqToHom G.2 = eqToHom G.2 ≫ 𝟙 X
    rw [hbottom]
    simp
  · apply CategoryTheory.IsHomLift.of_commsq
      (crossStageProjection.{u, v} U) (𝟙 X) a.inv _ _
    change a.inv.base.base ≫ eqToHom G.2 = eqToHom G.2 ≫ 𝟙 X
    rw [hinv]
    simp
  · apply CategoryTheory.Functor.Fiber.hom_ext
    exact a.hom_inv_id
  · apply CategoryTheory.Functor.Fiber.hom_ext
    exact a.inv_hom_id

/-- Include endpoint automorphisms of the fixed geometry fiber into the
unrestricted complete-geometry endpoint product. -/
noncomputable def semanticExactFiberEndpointInclusionHom :
    (Aut (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq) ×
      Aut (semanticDerivedViaBaseGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)) →*
      (Aut (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1 ×
       Aut (semanticDerivedViaBaseGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1) :=
  MonoidHom.prodMap
    (functorAutomorphismHom (semanticExactGlobalInclusion input) _)
    (functorAutomorphismHom (semanticExactGlobalInclusion input) _)

/-- Every centralizing fiber pair is a bottom-fixed pair in the unrestricted
centralizer. -/
noncomputable def semanticExactFiberHInclusionHom :
    SemanticExactCentralizingEndpointSubgroup input interpretation z omega k g
        endpoint_eq square_isPullback →*
      SemanticExactGlobalBottomH input interpretation z omega k g endpoint_eq
        square_isPullback where
  toFun pair := by
    let mapped := semanticExactFiberEndpointInclusionHom input interpretation z
      k g endpoint_eq pair.1
    have hcentral : mapped ∈
        SemanticExactGlobalH input interpretation z omega k g endpoint_eq
          square_isPullback := by
      constructor
      · have h := congrArg (semanticExactGlobalInclusion input).map pair.2.1
        simpa only [Functor.map_comp] using h
      · have h := congrArg (semanticExactGlobalInclusion input).map pair.2.2
        simpa only [Functor.map_comp] using h
    refine ⟨⟨mapped, hcentral⟩, ?_⟩
    apply (mem_SemanticExactGlobalBottomH input interpretation z omega k g
      endpoint_eq square_isPullback _).2
    constructor
    · exact semanticGeometryFiberMorphism_packageBase_identity pair.1.1.hom
    · exact semanticGeometryFiberMorphism_packageBase_identity pair.1.2.hom
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one (semanticExactFiberEndpointInclusionHom input interpretation z
      k g endpoint_eq)
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (semanticExactFiberEndpointInclusionHom input interpretation z
      k g endpoint_eq) a.1 b.1

/-- Recover the fixed-fiber centralizer from a full centralizing pair that
lies in the kernel of bottom projection. -/
noncomputable def semanticExactGlobalBottomToFiberHHom :
    SemanticExactGlobalBottomH input interpretation z omega k g endpoint_eq
        square_isPullback →*
      SemanticExactCentralizingEndpointSubgroup input interpretation z omega k g
        endpoint_eq square_isPullback where
  toFun pair := by
    have hbottom := (mem_SemanticExactGlobalBottomH input interpretation z
      omega k g endpoint_eq square_isPullback pair.1).1 pair.2
    let source := geometryFiberAutOfBottomIdentity
      (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
      pair.1.1.1 hbottom.1
    let target := geometryFiberAutOfBottomIdentity
      (semanticDerivedViaBaseGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
      pair.1.1.2 hbottom.2
    refine ⟨(source, target), ?_⟩
    constructor
    · apply CategoryTheory.Functor.Fiber.hom_ext
      exact pair.1.2.1
    · apply CategoryTheory.Functor.Fiber.hom_ext
      exact pair.1.2.2
  map_one' := by
    apply Subtype.ext
    apply Prod.ext <;> apply Iso.ext <;>
      apply CategoryTheory.Functor.Fiber.hom_ext <;> rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Prod.ext <;> apply Iso.ext <;>
      apply CategoryTheory.Functor.Fiber.hom_ext <;> rfl

/-- The fiber centralizer is precisely the kernel of the full endpoint base
projection. -/
noncomputable def semanticExactFiberHGlobalBottomIso :
    SemanticExactCentralizingEndpointSubgroup input interpretation z omega k g
        endpoint_eq square_isPullback ≃*
      SemanticExactGlobalBottomH input interpretation z omega k g endpoint_eq
        square_isPullback :=
  MulEquiv.ofBijective
    (semanticExactFiberHInclusionHom input interpretation z omega k g
      endpoint_eq square_isPullback) (by
    constructor
    · intro a b h
      apply Subtype.ext
      apply Prod.ext <;> apply Iso.ext <;>
        apply CategoryTheory.Functor.Fiber.hom_ext
      · exact congrArg (fun q : SemanticExactGlobalBottomH input
          interpretation z omega k g endpoint_eq square_isPullback =>
          q.1.1.1.hom) h
      · exact congrArg (fun q : SemanticExactGlobalBottomH input
          interpretation z omega k g endpoint_eq square_isPullback =>
          q.1.1.2.hom) h
    · intro b
      refine ⟨semanticExactGlobalBottomToFiberHHom input interpretation z
        omega k g endpoint_eq square_isPullback b, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext <;> apply Iso.ext <;> rfl)

end

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
