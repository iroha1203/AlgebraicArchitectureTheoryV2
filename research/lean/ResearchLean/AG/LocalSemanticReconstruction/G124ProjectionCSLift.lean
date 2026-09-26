import ResearchLean.AG.LocalSemanticReconstruction.G124ProjectionLift
import ResearchLean.AG.LocalSemanticReconstruction.G124ProjectionCS
import Formal.Util.AssertStandardAxioms

/-! The CS component comparisons at the exact universe lift of the fixed
four-family G-124 parameter. -/

namespace AAT.AG.LocalSemanticReconstruction.G124ProjectionCSLift

open CategoryTheory RealizationReconstruction
open IndependentAATPrimitiveReconstruction

universe u v w

noncomputable def lensBottomIso
    (input : LensFamilyInput.{max u v}) :
    reading (Parameter.lens input : Parameter.{u, v}) ⋙
      ((ULiftHom.down (C := IndependentLensPrimitiveReconstruction.Object input)) ⋙
        G124ProjectionCS.lensBottomLocal input) ≅
    (ULiftHom.down (C := LensRealization input.View input.reference)) ⋙
      G124ProjectionCS.lensBottomNative input :=
  G124ProjectionLift.liftReadingIso
    (IndependentLensPrimitiveReconstruction.readingFunctor input)
    (G124ProjectionCS.lensBottomLocal input)
    (G124ProjectionCS.lensBottomNative input)
    (G124ProjectionCS.lensBottomReadingIso input)

noncomputable def protocolBottomIso
    (input : ProtocolFamilyInput.{max u v}) :
    reading (Parameter.protocol input : Parameter.{u, v}) ⋙
      ((ULiftHom.down (C := IndependentProtocolPrimitiveReconstruction.Object input)) ⋙
        G124ProjectionCS.protocolBottomLocal input) ≅
    (ULiftHom.down (C := ProtocolRealization input.schema input.observation)) ⋙
      G124ProjectionCS.protocolBottomNative input :=
  G124ProjectionLift.liftReadingIso
    (IndependentProtocolPrimitiveReconstruction.readingFunctor input)
    (G124ProjectionCS.protocolBottomLocal input)
    (G124ProjectionCS.protocolBottomNative input)
    (G124ProjectionCS.protocolBottomReadingIso input)

noncomputable def lensObservationIso
    (input : LensFamilyInput.{max u v}) :
    reading (Parameter.lens input : Parameter.{u, v}) ⋙
      ((ULiftHom.down (C := IndependentLensPrimitiveReconstruction.Object input)) ⋙
        G124ProjectionCS.lensObservationLocal input) ≅
    (ULiftHom.down (C := LensRealization input.View input.reference)) ⋙
      G124ProjectionCS.lensObservationNative input :=
  G124ProjectionLift.liftReadingIso
    (IndependentLensPrimitiveReconstruction.readingFunctor input)
    (G124ProjectionCS.lensObservationLocal input)
    (G124ProjectionCS.lensObservationNative input)
    (G124ProjectionCS.lensObservationReadingIso input)

noncomputable def protocolObservationIso
    (input : ProtocolFamilyInput.{max u v}) :
    reading (Parameter.protocol input : Parameter.{u, v}) ⋙
      ((ULiftHom.down (C := IndependentProtocolPrimitiveReconstruction.Object input)) ⋙
        G124ProjectionCS.protocolObservationLocal input) ≅
    (ULiftHom.down (C := ProtocolRealization input.schema input.observation)) ⋙
      G124ProjectionCS.protocolObservationNative input :=
  G124ProjectionLift.liftReadingIso
    (IndependentProtocolPrimitiveReconstruction.readingFunctor input)
    (G124ProjectionCS.protocolObservationLocal input)
    (G124ProjectionCS.protocolObservationNative input)
    (G124ProjectionCS.protocolObservationReadingIso input)

/-- The CS AAT coefficient is the fixed integer ring at the exact main
parameter universe, on native and local sides alike. -/
noncomputable def lensCoefficientNative
    (input : LensFamilyInput.{max u v}) :
    NativeCategory (Parameter.lens input : Parameter.{u, v}) ⥤ CommRingCat :=
  G124ProjectionCS.constantIntegerCoefficient _

noncomputable def lensCoefficientLocal
    (input : LensFamilyInput.{max u v}) :
    LocalCategory (Parameter.lens input : Parameter.{u, v}) ⥤ CommRingCat :=
  G124ProjectionCS.constantIntegerCoefficient _

noncomputable def protocolCoefficientNative
    (input : ProtocolFamilyInput.{max u v}) :
    NativeCategory (Parameter.protocol input : Parameter.{u, v}) ⥤ CommRingCat :=
  G124ProjectionCS.constantIntegerCoefficient _

noncomputable def protocolCoefficientLocal
    (input : ProtocolFamilyInput.{max u v}) :
    LocalCategory (Parameter.protocol input : Parameter.{u, v}) ⥤ CommRingCat :=
  G124ProjectionCS.constantIntegerCoefficient _

noncomputable def lensCoefficientIso
    (input : LensFamilyInput.{max u v}) :
    reading (Parameter.lens input : Parameter.{u, v}) ⋙
      lensCoefficientLocal input ≅ lensCoefficientNative input :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

noncomputable def protocolCoefficientIso
    (input : ProtocolFamilyInput.{max u v}) :
    reading (Parameter.protocol input : Parameter.{u, v}) ⋙
      protocolCoefficientLocal input ≅ protocolCoefficientNative input :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The lens component maps consume exactly the fixed main local Hom graph. -/
theorem lensComponentPoint
    (input : LensFamilyInput.{max u v})
    {source target : IndependentLensPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target)
    (query : HomQuery (Parameter.lens input : Parameter.{u, v})) :
    localHomTable (Parameter.lens input : Parameter.{u, v})
      ((ULiftHom.up (C := IndependentLensPrimitiveReconstruction.Object input)).map
        morphism) query =
      IndependentLensPrimitiveReconstruction.Hom.table morphism query := rfl

theorem lensComponentObjectTable
    (input : LensFamilyInput.{max u v})
    (source : IndependentLensPrimitiveReconstruction.Object input) :
    localObjectTable (Parameter.lens input : Parameter.{u, v})
        (ULiftHom.objUp source) =
      IndependentLensPrimitiveReconstruction.Object.table source := rfl

/-- Protocol state, edge, and observation queries likewise come from one
common local Hom table at the exact parameter universe. -/
theorem protocolComponentPoint
    (input : ProtocolFamilyInput.{max u v})
    {source target : IndependentProtocolPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target)
    (query : HomQuery (Parameter.protocol input : Parameter.{u, v})) :
    localHomTable (Parameter.protocol input : Parameter.{u, v})
      ((ULiftHom.up (C := IndependentProtocolPrimitiveReconstruction.Object input)).map
        morphism) query =
      IndependentProtocolPrimitiveReconstruction.Hom.table morphism query := rfl

theorem protocolComponentObjectTable
    (input : ProtocolFamilyInput.{max u v})
    (source : IndependentProtocolPrimitiveReconstruction.Object input) :
    localObjectTable (Parameter.protocol input : Parameter.{u, v})
        (ULiftHom.objUp source) =
      IndependentProtocolPrimitiveReconstruction.Object.table source := rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124ProjectionCSLift

end AAT.AG.LocalSemanticReconstruction.G124ProjectionCSLift
