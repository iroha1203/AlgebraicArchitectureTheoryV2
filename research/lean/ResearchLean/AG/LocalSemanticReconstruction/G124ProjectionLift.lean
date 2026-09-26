import ResearchLean.AG.LocalSemanticReconstruction.G124ProjectionBottom
import ResearchLean.AG.LocalSemanticReconstruction.G124ProjectionCoefficient
import Formal.Util.AssertStandardAxioms

/-! Lift direct primitive projection comparisons through the common
`ULiftHom` presentation used by the fixed G-124 parameter. -/

namespace AAT.AG.LocalSemanticReconstruction.G124ProjectionLift

open CategoryTheory
open IndependentAATPrimitiveReconstruction
open AtomFoundation IndependentGeometryHomPrimitive

universe u v w x y z

/-- A natural projection comparison survives the common Hom-universe lift.
The local functor still selects primitive components directly. -/
noncomputable def liftReadingIso
    {C : Type u} {D : Type v} {E : Type w}
    [Category.{x} C] [Category.{y} D] [Category.{z} E]
    (reader : C ⥤ D) (localProjection : D ⥤ E) (native : C ⥤ E)
    (comparison : reader ⋙ localProjection ≅ native) :
    ((ULiftHom.down (C := C)) ⋙ reader ⋙ (ULiftHom.up (C := D))) ⋙
      ((ULiftHom.down (C := D)) ⋙ localProjection) ≅
      (ULiftHom.down (C := C)) ⋙ native :=
  NatIso.ofComponents
    (fun object => comparison.app object.objDown)
    (by
      intro source target morphism
      change localProjection.map (reader.map morphism.down) ≫
          (comparison.app target.objDown).hom =
        (comparison.app source.objDown).hom ≫ native.map morphism.down
      exact comparison.hom.naturality morphism.down)

/-- The main G-124 reader preserves the directly selected representative
pointed-extraction projection. -/
noncomputable def representativeBottomIso (U : AtomCarrier.{u}) :
    reading (Parameter.geometry U Mode.representative : Parameter.{u, v}) ⋙
      ((ULiftHom.down (C :=
        IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v} U)) ⋙
        G124ProjectionBottom.localRepresentative U) ≅
    (ULiftHom.down (C := GeometryTransport.GeomReadCategory.{u, v} U)) ⋙
      G124ProjectionBottom.nativeRepresentative U :=
  liftReadingIso
    (IndependentGeometryCategoryReconstruction.representativeReadingFunctor U)
    (G124ProjectionBottom.localRepresentative U)
    (G124ProjectionBottom.nativeRepresentative U)
    (G124ProjectionBottom.representativeReadingIso U)

noncomputable def explicitBottomIso (U : AtomCarrier.{u}) :
    reading (Parameter.geometry U Mode.explicit : Parameter.{u, v}) ⋙
      ((ULiftHom.down (C :=
        IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v} U)) ⋙
        G124ProjectionBottom.localExplicit U) ≅
    (ULiftHom.down (C :=
      RealizationReconstruction.ExplicitExactGeomCategory.{u, v} U)) ⋙
      G124ProjectionBottom.nativeExplicit U :=
  liftReadingIso
    (IndependentGeometryCategoryReconstruction.explicitReadingFunctor U)
    (G124ProjectionBottom.localExplicit U)
    (G124ProjectionBottom.nativeExplicit U)
    (G124ProjectionBottom.explicitReadingIso U)

/-- The intermediate core stage is also read directly from primitive package
rows in representative geometry. -/
noncomputable def representativeCoreIso (U : AtomCarrier.{u}) :
    reading (Parameter.geometry U Mode.representative : Parameter.{u, v}) ⋙
      ((ULiftHom.down (C :=
        IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v} U)) ⋙
        G124ProjectionBottom.localRepresentativeCore U) ≅
    (ULiftHom.down (C := GeometryTransport.GeomReadCategory.{u, v} U)) ⋙
      GeometryTransport.geometryProjection U :=
  liftReadingIso
    (IndependentGeometryCategoryReconstruction.representativeReadingFunctor U)
    (G124ProjectionBottom.localRepresentativeCore U)
    (GeometryTransport.geometryProjection U)
    (G124ProjectionBottom.representativeCoreReadingIso U)

noncomputable def explicitCoreIso (U : AtomCarrier.{u}) :
    reading (Parameter.geometry U Mode.explicit : Parameter.{u, v}) ⋙
      ((ULiftHom.down (C :=
        IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v} U)) ⋙
        G124ProjectionBottom.localExplicitCore U) ≅
    (ULiftHom.down (C :=
      RealizationReconstruction.ExplicitExactGeomCategory.{u, v} U)) ⋙
      G124ProjectionBottom.nativeExplicitCore U :=
  liftReadingIso
    (IndependentGeometryCategoryReconstruction.explicitReadingFunctor U)
    (G124ProjectionBottom.localExplicitCore U)
    (G124ProjectionBottom.nativeExplicitCore U)
    (G124ProjectionBottom.explicitCoreReadingIso U)

noncomputable def representativeCoefficientIso (U : AtomCarrier.{u}) :
    reading (Parameter.geometry U Mode.representative : Parameter.{u, v}) ⋙
      ((ULiftHom.down (C :=
        IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v} U)) ⋙
        G124ProjectionCoefficient.localRepresentative U) ≅
    (ULiftHom.down (C := GeometryTransport.GeomReadCategory.{u, v} U)) ⋙
      G124ProjectionCoefficient.nativeRepresentative U :=
  liftReadingIso
    (IndependentGeometryCategoryReconstruction.representativeReadingFunctor U)
    (G124ProjectionCoefficient.localRepresentative U)
    (G124ProjectionCoefficient.nativeRepresentative U)
    (G124ProjectionCoefficient.representativeReadingIso U)

noncomputable def explicitCoefficientIso (U : AtomCarrier.{u}) :
    reading (Parameter.geometry U Mode.explicit : Parameter.{u, v}) ⋙
      ((ULiftHom.down (C :=
        IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v} U)) ⋙
        G124ProjectionCoefficient.localExplicit U) ≅
    (ULiftHom.down (C :=
      RealizationReconstruction.ExplicitExactGeomCategory.{u, v} U)) ⋙
      G124ProjectionCoefficient.nativeExplicit U :=
  liftReadingIso
    (IndependentGeometryCategoryReconstruction.explicitReadingFunctor U)
    (G124ProjectionCoefficient.localExplicit U)
    (G124ProjectionCoefficient.nativeExplicit U)
    (G124ProjectionCoefficient.explicitReadingIso U)

/-- Every point used by a representative component assembler is exactly a
point of the fixed main local Hom table. -/
theorem representativeComponentPoint
    (U : AtomCarrier.{u})
    {source target : IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v} U}
    (morphism : source ⟶ target)
    (query : IndependentGeometryHomPrimitive.Query.{u, v} U Mode.representative) :
    localHomTable (Parameter.geometry U Mode.representative : Parameter.{u, v})
      ((ULiftHom.up (C :=
        IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v} U)).map
          morphism) query =
    (IndependentGeometryHomPrimitive.PackageAssembly.retained
      (IndependentGeometryCategoryReconstruction.objectData source.localObject).1
      (IndependentGeometryCategoryReconstruction.objectData target.localObject).1
      morphism.val).table query := rfl

theorem representativeComponentObjectTable
    (U : AtomCarrier.{u})
    (source : IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v} U) :
    localObjectTable (Parameter.geometry U Mode.representative : Parameter.{u, v})
        (ULiftHom.objUp source) =
      IndependentGeometryPrimitive.glue source.localObject.val := rfl

theorem explicitComponentObjectTable
    (U : AtomCarrier.{u})
    (source : IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v} U) :
    localObjectTable (Parameter.geometry U Mode.explicit : Parameter.{u, v})
        (ULiftHom.objUp source) =
      IndependentGeometryPrimitive.glue source.localObject.val := rfl

/-- The explicit action uses the same fixed local Hom table with its own
mode-specific query type. -/
theorem explicitComponentPoint
    (U : AtomCarrier.{u})
    {source target : IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v} U}
    (morphism : source ⟶ target)
    (query : IndependentGeometryHomPrimitive.Query.{u, v} U Mode.explicit) :
    localHomTable (Parameter.geometry U Mode.explicit : Parameter.{u, v})
      ((ULiftHom.up (C :=
        IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v} U)).map
          morphism) query =
    (IndependentGeometryHomPrimitive.PackageAssembly.retained
      (IndependentGeometryCategoryReconstruction.objectData source.localObject).1
      (IndependentGeometryCategoryReconstruction.objectData target.localObject).1
      morphism.val).table query := rfl

/-- Erasing an auxiliary presentation choice leaves every original
representative component query unchanged. -/
theorem representativePoint_auxiliary_choice_independent
    (U : AtomCarrier.{u})
    (I J : InvariantFamily U)
    (first second : IndependentGeometryHomPrimitive.InvariantWitness.Presentation.{u, v}
      I J Mode.representative)
    (h : first.retained = second.retained)
    (query : IndependentGeometryHomPrimitive.Query.{u, v} U Mode.representative) :
    IndependentGeometryHomPrimitive.InvariantWitness.point I J
        (Quotient.mk _ first) query =
      IndependentGeometryHomPrimitive.InvariantWitness.point I J
        (Quotient.mk _ second) query := by
  rw [IndependentGeometryHomPrimitive.InvariantWitness.auxiliary_choice_independent
    I J first second h]

/-- The explicit point table has the same choice independence. -/
theorem explicitPoint_auxiliary_choice_independent
    (U : AtomCarrier.{u})
    (I J : InvariantFamily U)
    (first second : IndependentGeometryHomPrimitive.InvariantWitness.Presentation.{u, v}
      I J Mode.explicit)
    (h : first.retained = second.retained)
    (query : IndependentGeometryHomPrimitive.Query.{u, v} U Mode.explicit) :
    IndependentGeometryHomPrimitive.InvariantWitness.point I J
        (Quotient.mk _ first) query =
      IndependentGeometryHomPrimitive.InvariantWitness.point I J
        (Quotient.mk _ second) query := by
  rw [IndependentGeometryHomPrimitive.InvariantWitness.auxiliary_choice_independent
    I J first second h]

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124ProjectionLift

end AAT.AG.LocalSemanticReconstruction.G124ProjectionLift
