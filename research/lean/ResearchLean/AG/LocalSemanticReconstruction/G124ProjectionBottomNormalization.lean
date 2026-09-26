import ResearchLean.AG.LocalSemanticReconstruction.G124ProjectionBottom
import ResearchLean.AG.LocalSemanticReconstruction.G124ProjectionGlobal
import ResearchLean.AG.FullGeometryNormalization.GeometryBottomQualifiedComparisonGroup
import Formal.Util.AssertStandardAxioms

/-! Compare the primitive bottom projection with the established raw
admissible bottom and transport the bottom-fixed automorphism condition. -/

namespace AAT.AG.LocalSemanticReconstruction.G124ProjectionBottomNormalization

open CategoryTheory AtomFoundation GeometryTransport
open FullGeometryNormalization RealizationComparisonIdempotents
open IndependentAATPrimitiveReconstruction

universe u v

/-- The raw admissible bottom is the restriction of the native geometry
projection to pointed extraction instances. -/
theorem raw_eq_restricted_native (U : AtomCarrier.{u}) :
    (canonicalGeometryNormalizationAdmissibleProperty.{u, v} U).ι ⋙
      G124ProjectionBottom.nativeRepresentative U =
      rawGeometryBottomProjection U := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target morphism
  rfl

/-- Reading conjugates the original bottom action by the canonical
primitive-reading component.  This is the comparison relevant to the
bottom-fixed condition, not equality of core packages. -/
theorem representativeBottom_conjugation
    (U : AtomCarrier.{u})
    (geometry : GeomReadCategory.{u, v} U)
    (morphism : geometry ⟶ geometry) :
    (G124ProjectionBottom.localRepresentative U).map
        ((IndependentGeometryCategoryReconstruction.representativeReadingFunctor U).map
          morphism) =
      ((G124ProjectionBottom.representativeReadingIso U).app geometry).hom ≫
        (G124ProjectionBottom.nativeRepresentative U).map morphism ≫
        ((G124ProjectionBottom.representativeReadingIso U).app geometry).inv := by
  let η := (G124ProjectionBottom.representativeReadingIso U).app geometry
  have h := (G124ProjectionBottom.representativeReadingIso U).hom.naturality morphism
  change (G124ProjectionBottom.localRepresentative U).map
      ((IndependentGeometryCategoryReconstruction.representativeReadingFunctor U).map
        morphism) ≫ η.hom =
    η.hom ≫ (G124ProjectionBottom.nativeRepresentative U).map morphism at h
  calc
    (G124ProjectionBottom.localRepresentative U).map
        ((IndependentGeometryCategoryReconstruction.representativeReadingFunctor U).map
          morphism) =
      ((G124ProjectionBottom.localRepresentative U).map
        ((IndependentGeometryCategoryReconstruction.representativeReadingFunctor U).map
          morphism) ≫ η.hom) ≫ η.inv := by simp
    _ = (η.hom ≫ (G124ProjectionBottom.nativeRepresentative U).map morphism) ≫
        η.inv := by rw [h]
    _ = η.hom ≫ (G124ProjectionBottom.nativeRepresentative U).map morphism ≫
        η.inv := by rw [Category.assoc]

/-- The canonical bottom comparison preserves and reflects the exact
bottom-fixed condition on every representative endomorphism. -/
theorem representativeBottom_fixed_iff
    (U : AtomCarrier.{u})
    (geometry : GeomReadCategory.{u, v} U)
    (morphism : geometry ⟶ geometry) :
    (G124ProjectionBottom.localRepresentative U).map
        ((IndependentGeometryCategoryReconstruction.representativeReadingFunctor U).map
          morphism) = 𝟙 _ ↔
      (G124ProjectionBottom.nativeRepresentative U).map morphism = 𝟙 _ := by
  let η := (G124ProjectionBottom.representativeReadingIso U).app geometry
  have hconj := representativeBottom_conjugation U geometry morphism
  change (G124ProjectionBottom.localRepresentative U).map
      ((IndependentGeometryCategoryReconstruction.representativeReadingFunctor U).map
        morphism) = η.hom ≫
      (G124ProjectionBottom.nativeRepresentative U).map morphism ≫ η.inv at hconj
  constructor
  · intro hfixed
    calc
      (G124ProjectionBottom.nativeRepresentative U).map morphism =
          η.inv ≫ (η.hom ≫
            (G124ProjectionBottom.nativeRepresentative U).map morphism ≫ η.inv) ≫
            η.hom := by simp [Category.assoc]
      _ = η.inv ≫ 𝟙 _ ≫ η.hom := by rw [← hconj, hfixed]; rfl
      _ = 𝟙 _ := by simp
  · intro hfixed
    rw [hfixed] at hconj
    simpa using hconj

/-- At every common parameter, the canonical bottom-reading isomorphism
conjugates the complete bottom action of an endomorphism. -/
theorem bottom_conjugation
    (parameter : Parameter.{u, v})
    (source : NativeCategory parameter)
    (morphism : source ⟶ source) :
    (G124ProjectionGlobal.localBottom parameter).map
        ((reading parameter).map morphism) =
      ((G124ProjectionGlobal.bottomReadingIso parameter).app source).hom ≫
        (G124ProjectionGlobal.nativeBottom parameter).map morphism ≫
        ((G124ProjectionGlobal.bottomReadingIso parameter).app source).inv := by
  let η := (G124ProjectionGlobal.bottomReadingIso parameter).app source
  have h := (G124ProjectionGlobal.bottomReadingIso parameter).hom.naturality morphism
  change (G124ProjectionGlobal.localBottom parameter).map
      ((reading parameter).map morphism) ≫ η.hom =
    η.hom ≫ (G124ProjectionGlobal.nativeBottom parameter).map morphism at h
  calc
    (G124ProjectionGlobal.localBottom parameter).map
        ((reading parameter).map morphism) =
      ((G124ProjectionGlobal.localBottom parameter).map
        ((reading parameter).map morphism) ≫ η.hom) ≫ η.inv := by simp
    _ = (η.hom ≫ (G124ProjectionGlobal.nativeBottom parameter).map morphism) ≫
        η.inv := by rw [h]
    _ = η.hom ≫ (G124ProjectionGlobal.nativeBottom parameter).map morphism ≫
        η.inv := by rw [Category.assoc]

/-- Bottom-fixed endomorphisms are preserved and reflected by the same
canonical conjugation, in every geometry and CS branch. -/
theorem bottom_fixed_iff
    (parameter : Parameter.{u, v})
    (source : NativeCategory parameter)
    (morphism : source ⟶ source) :
    (G124ProjectionGlobal.localBottom parameter).map
        ((reading parameter).map morphism) = 𝟙 _ ↔
      (G124ProjectionGlobal.nativeBottom parameter).map morphism = 𝟙 _ := by
  let η := (G124ProjectionGlobal.bottomReadingIso parameter).app source
  have hconj := bottom_conjugation parameter source morphism
  change (G124ProjectionGlobal.localBottom parameter).map
      ((reading parameter).map morphism) = η.hom ≫
      (G124ProjectionGlobal.nativeBottom parameter).map morphism ≫ η.inv at hconj
  constructor
  · intro hfixed
    calc
      (G124ProjectionGlobal.nativeBottom parameter).map morphism =
          η.inv ≫ (η.hom ≫
            (G124ProjectionGlobal.nativeBottom parameter).map morphism ≫ η.inv) ≫
            η.hom := by simp [Category.assoc]
      _ = η.inv ≫ 𝟙 _ ≫ η.hom := by rw [← hconj, hfixed]; rfl
      _ = 𝟙 _ := by simp
  · intro hfixed
    rw [hfixed] at hconj
    simpa using hconj

#assert_standard_axioms_only
  AAT.AG.LocalSemanticReconstruction.G124ProjectionBottomNormalization

end AAT.AG.LocalSemanticReconstruction.G124ProjectionBottomNormalization
