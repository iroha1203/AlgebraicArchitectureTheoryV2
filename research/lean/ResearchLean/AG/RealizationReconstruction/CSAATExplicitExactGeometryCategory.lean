import ResearchLean.AG.RealizationReconstruction.CSAATExplicitExactGeometryHom
import ResearchLean.AG.RealizationReconstruction.CSAATExactGeometryCategory
import Formal.Util.AssertStandardAxioms

/-!
# Category laws for exact geometry with explicit context action

This file proves extensionality and the three category laws for the parallel
exact geometry hom whose realization component retains every actual
`ContextMorphism`.  Its object type is all geometry packages, not a decoder
image or a post-selected class of representable objects.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation
open GeometryTransport

universe u v

namespace ExplicitRealizationTransportSupply

/-- Two explicit supplies agree when their actual context action and all three
carrier equivalences agree pointwise.  Remaining fields are propositions. -/
@[ext (iff := false)] theorem ext
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {f : PackageTotalHom P Q}
    {first second : ExplicitRealizationTransportSupply P Q f}
    (hcontext : ∀ {W V : Site.ContextCategoryObject P.algebra.contextPreorder}
      (g : Site.ContextMorphism W.ctx V.ctx),
      first.contextMorphism g = second.contextMorphism g)
    (hsupport : ∀ W, first.supportEquiv W = second.supportEquiv W)
    (haxis : ∀ W, first.axisEquiv W = second.axisEquiv W)
    (hobservable : ∀ W, first.observableEquiv W = second.observableEquiv W) :
    first = second := by
  have hc : @first.contextMorphism = @second.contextMorphism := by
    funext W V g
    exact hcontext g
  have hs : first.supportEquiv = second.supportEquiv := by
    funext W
    exact hsupport W
  have ha : first.axisEquiv = second.axisEquiv := by
    funext W
    exact haxis W
  have ho : first.observableEquiv = second.observableEquiv := by
    funext W
    exact hobservable W
  cases first
  cases second
  cases hc
  cases hs
  cases ha
  cases ho
  rfl

end ExplicitRealizationTransportSupply

namespace ExplicitExactGeometryHom

/-- Extensionality compares every computational component.  Once the common
base is fixed, coverage is proof-valued and overlap uses its accepted
thin-context subsingleton theorem. -/
@[ext (iff := false)] theorem ext
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : ExplicitExactGeometryHom G H}
    (hbase : first.base = second.base)
    (hcoefficient : first.coefficientHom = second.coefficientHom)
    (hraw : HEq first.raw second.raw)
    (hrealization : HEq first.realization second.realization) : first = second := by
  rcases first with
    ⟨base1, coverage1, overlap1, coefficient1, raw1, realization1⟩
  rcases second with
    ⟨base2, coverage2, overlap2, coefficient2, raw2, realization2⟩
  dsimp at hbase hcoefficient hraw hrealization
  cases hbase
  have hcoverage : coverage1 = coverage2 := Subsingleton.elim _ _
  have hoverlap : overlap1 = overlap2 := Subsingleton.elim _ _
  cases hcoverage
  cases hoverlap
  cases hcoefficient
  cases hraw
  cases hrealization
  rfl

/-- The constructed identity is a left unit, including on every actual
context morphism and on all three realization carriers. -/
theorem id_comp
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : ExplicitExactGeometryHom G H) : comp (id G) hom = hom := by
  have hbase : (comp (id G) hom).base = hom.base := by
    apply PackageTotalHom.ext
    · apply ExtInstHom.ext
      apply ExactDoctrineHom.ext
      · rfl
      · apply Equiv.ext
        intro atom
        rfl
    · exact PackageTotalHom.upper_id_comp hom.base.upper
  apply ext hbase
  · rfl
  · apply RawAmbientRestrictionSystemExactMapAgainst.hext
    · rfl
    · rfl
    · rfl
    · apply heq_of_eq
      funext W
      apply StructuralRelationFamilyExactEquiv.ext
      apply Equiv.ext
      intro relation
      rfl
  · cases hbase
    apply heq_of_eq
    apply ExplicitRealizationTransportSupply.ext
    · intro W V g
      rfl
    · intro W
      apply Equiv.ext
      intro support
      rfl
    · intro W
      apply Equiv.ext
      intro axis
      rfl
    · intro W
      apply Equiv.ext
      intro observable
      rfl

/-- The constructed identity is a right unit on the full exact hom. -/
theorem comp_id
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : ExplicitExactGeometryHom G H) : comp hom (id H) = hom := by
  have hbase : (comp hom (id H)).base = hom.base := by
    apply PackageTotalHom.ext
    · apply ExtInstHom.ext
      apply ExactDoctrineHom.ext
      · rfl
      · apply Equiv.ext
        intro atom
        rfl
    · exact PackageTotalHom.upper_comp_id hom.base.upper
  apply ext hbase
  · apply RingHom.ext
    intro coefficient
    rfl
  · apply RawAmbientRestrictionSystemExactMapAgainst.hext
    · rfl
    · apply RingHom.ext
      intro coefficient
      rfl
    · apply heq_of_eq
      funext W
      apply CoordinateFamilyExactEquiv.ext
      · apply Equiv.ext
        intro coordinate
        rfl
      · apply heq_of_eq
        funext coordinate
        apply Equiv.ext
        intro datum
        rfl
    · apply heq_of_eq
      funext W
      apply StructuralRelationFamilyExactEquiv.ext
      apply Equiv.ext
      intro relation
      rfl
  · cases hbase
    apply heq_of_eq
    apply ExplicitRealizationTransportSupply.ext
    · intro W V g
      rfl
    · intro W
      apply Equiv.ext
      intro support
      rfl
    · intro W
      apply Equiv.ext
      intro axis
      rfl
    · intro W
      apply Equiv.ext
      intro observable
      rfl

/-- Composition is associative on base, coefficient, all typed raw actions,
and the explicit action on every actual context morphism. -/
theorem comp_assoc
    {U : AtomCarrier.{u}} {G H K L : GeometryPackage.{u, v} U}
    (first : ExplicitExactGeometryHom G H)
    (second : ExplicitExactGeometryHom H K)
    (third : ExplicitExactGeometryHom K L) :
    comp (comp first second) third = comp first (comp second third) := by
  have hbase : (comp (comp first second) third).base =
      (comp first (comp second third)).base := by
    apply PackageTotalHom.ext
    · apply ExtInstHom.ext
      apply ExactDoctrineHom.ext
      · rfl
      · apply Equiv.ext
        intro atom
        rfl
    · exact PackageTotalHom.upper_comp_assoc
        first.base.upper second.base.upper third.base.upper
  apply ext hbase
  · apply RingHom.ext
    intro coefficient
    rfl
  · apply RawAmbientRestrictionSystemExactMapAgainst.hext
    · rfl
    · apply RingHom.ext
      intro coefficient
      rfl
    · apply heq_of_eq
      funext W
      apply CoordinateFamilyExactEquiv.ext
      · apply Equiv.ext
        intro coordinate
        rfl
      · apply heq_of_eq
        funext coordinate
        apply Equiv.ext
        intro datum
        rfl
    · apply heq_of_eq
      funext W
      apply StructuralRelationFamilyExactEquiv.ext
      apply Equiv.ext
      intro relation
      rfl
  · cases hbase
    apply heq_of_eq
    apply ExplicitRealizationTransportSupply.ext
    · intro W V g
      rfl
    · intro W
      apply Equiv.ext
      intro support
      rfl
    · intro W
      apply Equiv.ext
      intro axis
      rfl
    · intro W
      apply Equiv.ext
      intro observable
      rfl

end ExplicitExactGeometryHom

/-- Wrapper for all geometry packages with exact morphisms retaining the
actual context action.  The wrapper avoids conflicting with the older exact
category while imposing no decoder-image condition on objects. -/
structure ExplicitExactGeomCategory (U : AtomCarrier.{u}) where
  toGeometryPackage : GeometryPackage.{u, v} U

namespace ExplicitExactGeomCategory

/-- Regard any geometry package as an object of the explicit exact category. -/
def ofGeometryPackage {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) : ExplicitExactGeomCategory.{u, v} U :=
  ⟨G⟩

end ExplicitExactGeomCategory

/-- Category structure supplied by the explicit exact hom laws. -/
noncomputable instance explicitExactGeometryCategory
    (U : AtomCarrier.{u}) : Category (ExplicitExactGeomCategory.{u, v} U) where
  Hom G H := ExplicitExactGeometryHom G.toGeometryPackage H.toGeometryPackage
  id G := ExplicitExactGeometryHom.id G.toGeometryPackage
  comp first second := ExplicitExactGeometryHom.comp first second
  id_comp := ExplicitExactGeometryHom.id_comp
  comp_id := ExplicitExactGeometryHom.comp_id
  assoc := ExplicitExactGeometryHom.comp_assoc

/-- A genuine lens isomorphism gives a morphism in the explicit exact
geometry category without changing its six-component construction. -/
noncomputable def lensIsoExplicitExactGeometryCategoryHom
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    ExplicitExactGeomCategory.ofGeometryPackage (lensAATReadingCore input X) ⟶
      ExplicitExactGeomCategory.ofGeometryPackage (lensAATReadingCore input Y) :=
  lensIsoExplicitExactGeometryHom e

/-- A genuine protocol isomorphism gives a morphism in the same explicit
exact geometry category. -/
noncomputable def protocolIsoExplicitExactGeometryCategoryHom
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    ExplicitExactGeomCategory.ofGeometryPackage
        (protocolAATReadingCore input X) ⟶
      ExplicitExactGeomCategory.ofGeometryPackage
        (protocolAATReadingCore input Y) :=
  protocolIsoExplicitExactGeometryHom e

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
