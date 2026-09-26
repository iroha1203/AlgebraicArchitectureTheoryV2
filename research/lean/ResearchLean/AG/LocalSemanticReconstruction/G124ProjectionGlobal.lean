import ResearchLean.AG.LocalSemanticReconstruction.G124ProjectionCSLift
import ResearchLean.AG.LocalSemanticReconstruction.G124ProjectionObservationComponents
import Formal.Util.AssertStandardAxioms

/-! The direct component projections at every parameter of the fixed common
G-124 primitive reconstruction. -/

namespace AAT.AG.LocalSemanticReconstruction.G124ProjectionGlobal

open CategoryTheory AtomFoundation IndependentGeometryHomPrimitive
open IndependentAATPrimitiveReconstruction RealizationReconstruction

universe u v

attribute [local instance] uliftCategory

/-- A component target is categorically equivalent to its original category:
`ULift` changes only the object universe and `ULiftHom` only the arrow universe.
The inverse functor recovers every original object and arrow. -/
noncomputable def componentEquivalence.{a, b, h, w}
    (C : Type a) [Category.{b} C] :
    C ≌ ULiftHom.{h} (ULift.{w} C) :=
  ULiftHomULiftCategory.equiv.{h, w, b, a} C

/-- Transport the exact component functor through that equivalence. -/
noncomputable def liftComponent.{a, b, h, w} {C : Type a} [Category.{b} C] :
    C ⥤ ULiftHom.{h} (ULift.{w} C) :=
  (componentEquivalence.{a, b, h, w} C).functor

/-- The original pointed-extraction target selected by each AAT branch. -/
def BottomTarget : Parameter.{u, v} → Type (max u v + 2)
  | .geometry carrier _ => ULiftHom.{max u v + 1} (ULift.{max u v + 2} (ExtractionInstance.{u} carrier))
  | .lens input => ULiftHom.{max u v + 1} (ULift.{max u v + 2}
      (ExtractionInstance.{(max u v) + 1} (lensAATCarrier input)))
  | .protocol input => ULiftHom.{max u v + 1} (ULift.{max u v + 2}
      (ExtractionInstance.{(max u v) + 1} (protocolAATCarrier input)))

noncomputable instance bottomCategory (parameter : Parameter.{u, v}) :
    Category (BottomTarget parameter) := by
  cases parameter with
  | geometry carrier mode => simp only [BottomTarget]; infer_instance
  | lens input => simp only [BottomTarget]; infer_instance
  | protocol input => simp only [BottomTarget]; infer_instance

/-- Native bottom projection for the exact common parameter, retaining its
actual full Hom action. -/
noncomputable def nativeBottom (parameter : Parameter.{u, v}) :
    NativeCategory parameter ⥤ BottomTarget parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact (ULiftHom.down (C := GeometryTransport.GeomReadCategory.{u, v} carrier)) ⋙
            G124ProjectionBottom.nativeRepresentative carrier ⋙
            (liftComponent (C := ExtractionInstance.{u} carrier))
      | explicit =>
          exact (ULiftHom.down (C := ExplicitExactGeomCategory.{u, v} carrier)) ⋙
            G124ProjectionBottom.nativeExplicit carrier ⋙
            (liftComponent (C := ExtractionInstance.{u} carrier))
  | lens input =>
      exact (ULiftHom.down (C := LensRealization input.View input.reference)) ⋙
        G124ProjectionCS.lensBottomNative input ⋙
        (liftComponent (C := ExtractionInstance (lensAATCarrier input)))
  | protocol input =>
      exact (ULiftHom.down (C :=
          ProtocolRealization input.schema input.observation)) ⋙
        G124ProjectionCS.protocolBottomNative input ⋙
        (liftComponent (C := ExtractionInstance (protocolAATCarrier input)))

/-- Local bottom projection selects the pointed doctrine and source map from
primitive object and Hom rows in each branch. -/
noncomputable def localBottom (parameter : Parameter.{u, v}) :
    LocalCategory parameter ⥤ BottomTarget parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact (ULiftHom.down (C :=
            IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v} carrier)) ⋙
              G124ProjectionBottom.localRepresentative carrier ⋙
              (liftComponent (C := ExtractionInstance.{u} carrier))
      | explicit =>
          exact (ULiftHom.down (C :=
            IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v} carrier)) ⋙
              G124ProjectionBottom.localExplicit carrier ⋙
              (liftComponent (C := ExtractionInstance.{u} carrier))
  | lens input =>
      exact (ULiftHom.down (C :=
        IndependentLensPrimitiveReconstruction.Object input)) ⋙
          G124ProjectionCS.lensBottomLocal input ⋙
          (liftComponent (C := ExtractionInstance (lensAATCarrier input)))
  | protocol input =>
      exact (ULiftHom.down (C :=
        IndependentProtocolPrimitiveReconstruction.Object input)) ⋙
          G124ProjectionCS.protocolBottomLocal input ⋙
          (liftComponent (C := ExtractionInstance (protocolAATCarrier input)))

/-- The first required III-1 natural isomorphism at every fixed parameter. -/
noncomputable def bottomReadingIso (parameter : Parameter.{u, v}) :
    reading parameter ⋙ localBottom parameter ≅ nativeBottom parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact Functor.isoWhiskerRight
            (G124ProjectionLift.representativeBottomIso.{u, v} carrier)
            (liftComponent (C := ExtractionInstance.{u} carrier))
      | explicit =>
          exact Functor.isoWhiskerRight
            (G124ProjectionLift.explicitBottomIso.{u, v} carrier)
            (liftComponent (C := ExtractionInstance.{u} carrier))
  | lens input =>
      exact Functor.isoWhiskerRight
        (G124ProjectionCSLift.lensBottomIso.{u, v} input)
        (liftComponent (C := ExtractionInstance (lensAATCarrier input)))
  | protocol input =>
      exact Functor.isoWhiskerRight
        (G124ProjectionCSLift.protocolBottomIso.{u, v} input)
        (liftComponent (C := ExtractionInstance (protocolAATCarrier input)))

/-- Geometry coefficients retain their original carrier and directed ring
map; CS coefficients are the fixed integer ring. -/
def CoefficientTarget : Parameter.{u, v} → Type (max u v + 1)
  | .geometry _ _ => ULiftHom.{max u v + 1} (ULift.{max u v + 1} CommRingCat.{v})
  | .lens _ => ULiftHom.{max u v + 1} (ULift.{max u v + 1} CommRingCat.{0})
  | .protocol _ => ULiftHom.{max u v + 1} (ULift.{max u v + 1} CommRingCat.{0})

noncomputable instance coefficientCategory (parameter : Parameter.{u, v}) :
    Category (CoefficientTarget parameter) := by
  cases parameter with
  | geometry carrier mode => simp only [CoefficientTarget]; infer_instance
  | lens input => simp only [CoefficientTarget]; infer_instance
  | protocol input => simp only [CoefficientTarget]; infer_instance

noncomputable def nativeCoefficient (parameter : Parameter.{u, v}) :
    NativeCategory parameter ⥤ CoefficientTarget parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact (ULiftHom.down (C := GeometryTransport.GeomReadCategory.{u, v} carrier)) ⋙
            G124ProjectionCoefficient.nativeRepresentative carrier ⋙
            (liftComponent (C := CommRingCat.{v}))
      | explicit =>
          exact (ULiftHom.down (C := ExplicitExactGeomCategory.{u, v} carrier)) ⋙
            G124ProjectionCoefficient.nativeExplicit carrier ⋙
            (liftComponent (C := CommRingCat.{v}))
  | lens input =>
      exact G124ProjectionCSLift.lensCoefficientNative.{u, v} input ⋙
        (liftComponent (C := CommRingCat.{0}))
  | protocol input =>
      exact G124ProjectionCSLift.protocolCoefficientNative.{u, v} input ⋙
        (liftComponent (C := CommRingCat.{0}))

noncomputable def localCoefficient (parameter : Parameter.{u, v}) :
    LocalCategory parameter ⥤ CoefficientTarget parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact (ULiftHom.down (C :=
            IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v} carrier)) ⋙
              G124ProjectionCoefficient.localRepresentative carrier ⋙
              (liftComponent (C := CommRingCat.{v}))
      | explicit =>
          exact (ULiftHom.down (C :=
            IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v} carrier)) ⋙
              G124ProjectionCoefficient.localExplicit carrier ⋙
              (liftComponent (C := CommRingCat.{v}))
  | lens input =>
      exact G124ProjectionCSLift.lensCoefficientLocal.{u, v} input ⋙
        (liftComponent (C := CommRingCat.{0}))
  | protocol input =>
      exact G124ProjectionCSLift.protocolCoefficientLocal.{u, v} input ⋙
        (liftComponent (C := CommRingCat.{0}))

/-- The third required III-1 natural isomorphism, including the directed
geometry coefficient map and the CS integer identity. -/
noncomputable def coefficientReadingIso (parameter : Parameter.{u, v}) :
    reading parameter ⋙ localCoefficient parameter ≅ nativeCoefficient parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact Functor.isoWhiskerRight
            (G124ProjectionLift.representativeCoefficientIso.{u, v} carrier)
            (liftComponent (C := CommRingCat.{v}))
      | explicit =>
          exact Functor.isoWhiskerRight
            (G124ProjectionLift.explicitCoefficientIso.{u, v} carrier)
            (liftComponent (C := CommRingCat.{v}))
  | lens input =>
      exact Functor.isoWhiskerRight
        (G124ProjectionCSLift.lensCoefficientIso.{u, v} input)
        (liftComponent (C := CommRingCat.{0}))
  | protocol input =>
      exact Functor.isoWhiskerRight
        (G124ProjectionCSLift.protocolCoefficientIso.{u, v} input)
        (liftComponent (C := CommRingCat.{0}))

/-- Each observation target is the full component category, presented at one
common universe.  Geometry retains context and observable actions; lens and
protocol retain their unrestricted get and observation slices. -/
def ObservationTarget : Parameter.{u, v} → Type (max u v + 1)
  | .geometry carrier .representative =>
      ULiftHom.{max u v + 1} (ULift.{max u v + 1}
        (G124ProjectionObservationComponents.RepresentativeObject carrier))
  | .geometry carrier .explicit =>
      ULiftHom.{max u v + 1} (ULift.{max u v + 1}
        (G124ProjectionObservationComponents.ExplicitObject carrier))
  | .lens input =>
      ULiftHom.{max u v + 1} (ULift.{max u v + 1}
        (G124ProjectionCS.LensGetSlice input.View))
  | .protocol input =>
      ULiftHom.{max u v + 1} (ULift.{max u v + 1}
        (G124ProjectionCS.ProtocolObservationSlice input))

noncomputable instance observationCategory (parameter : Parameter.{u, v}) :
    Category (ObservationTarget parameter) := by
  cases parameter with
  | geometry carrier mode => cases mode <;> simp only [ObservationTarget] <;> infer_instance
  | lens input => simp only [ObservationTarget]; infer_instance
  | protocol input => simp only [ObservationTarget]; infer_instance

/-- Native observation action in the exact component category. -/
noncomputable def nativeObservation (parameter : Parameter.{u, v}) :
    NativeCategory parameter ⥤ ObservationTarget parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact (ULiftHom.down (C := GeometryTransport.GeomReadCategory.{u, v} carrier)) ⋙
            G124ProjectionObservationComponents.nativeRepresentative carrier ⋙
            liftComponent (C := G124ProjectionObservationComponents.RepresentativeObject carrier)
      | explicit =>
          exact (ULiftHom.down (C := ExplicitExactGeomCategory.{u, v} carrier)) ⋙
            G124ProjectionObservationComponents.nativeExplicit carrier ⋙
            liftComponent (C := G124ProjectionObservationComponents.ExplicitObject carrier)
  | lens input =>
      exact (ULiftHom.down (C := LensRealization input.View input.reference)) ⋙
        G124ProjectionCS.lensObservationNative input ⋙
        liftComponent (C := G124ProjectionCS.LensGetSlice input.View)
  | protocol input =>
      exact (ULiftHom.down (C := ProtocolRealization input.schema input.observation)) ⋙
        G124ProjectionCS.protocolObservationNative input ⋙
        liftComponent (C := G124ProjectionCS.ProtocolObservationSlice input)

/-- Local observation action reads the primitive object and Hom components. -/
noncomputable def localObservation (parameter : Parameter.{u, v}) :
    LocalCategory parameter ⥤ ObservationTarget parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact (ULiftHom.down (C :=
            IndependentGeometryCategoryReconstruction.RepresentativeLocalObject.{u, v} carrier)) ⋙
              G124ProjectionObservationComponents.localRepresentative carrier ⋙
              liftComponent (C := G124ProjectionObservationComponents.RepresentativeObject carrier)
      | explicit =>
          exact (ULiftHom.down (C :=
            IndependentGeometryCategoryReconstruction.ExplicitLocalObject.{u, v} carrier)) ⋙
              G124ProjectionObservationComponents.localExplicit carrier ⋙
              liftComponent (C := G124ProjectionObservationComponents.ExplicitObject carrier)
  | lens input =>
      exact (ULiftHom.down (C := IndependentLensPrimitiveReconstruction.Object input)) ⋙
        G124ProjectionCS.lensObservationLocal input ⋙
        liftComponent (C := G124ProjectionCS.LensGetSlice input.View)
  | protocol input =>
      exact (ULiftHom.down (C := IndependentProtocolPrimitiveReconstruction.Object input)) ⋙
        G124ProjectionCS.protocolObservationLocal input ⋙
        liftComponent (C := G124ProjectionCS.ProtocolObservationSlice input)

/-- The second III-1 comparison holds across all four exact observation modes. -/
noncomputable def observationReadingIso (parameter : Parameter.{u, v}) :
    reading parameter ⋙ localObservation parameter ≅ nativeObservation parameter := by
  cases parameter with
  | geometry carrier mode =>
      cases mode with
      | representative =>
          exact Functor.isoWhiskerRight
            (G124ProjectionLift.liftReadingIso.{_, _, _, _, _, u + 1, _, max (u + 1) v}
              (IndependentGeometryCategoryReconstruction.representativeReadingFunctor carrier)
              (G124ProjectionObservationComponents.localRepresentative carrier)
              (G124ProjectionObservationComponents.nativeRepresentative carrier)
              (G124ProjectionObservationComponents.representativeReadingIso carrier))
            (liftComponent (C := G124ProjectionObservationComponents.RepresentativeObject carrier))
      | explicit =>
          exact Functor.isoWhiskerRight
            (G124ProjectionLift.liftReadingIso.{_, _, _, _, _, u + 1, _, max (u + 1) v}
              (IndependentGeometryCategoryReconstruction.explicitReadingFunctor carrier)
              (G124ProjectionObservationComponents.localExplicit carrier)
              (G124ProjectionObservationComponents.nativeExplicit carrier)
              (G124ProjectionObservationComponents.explicitReadingIso carrier))
            (liftComponent (C := G124ProjectionObservationComponents.ExplicitObject carrier))
  | lens input =>
      exact Functor.isoWhiskerRight
        (G124ProjectionCSLift.lensObservationIso.{u, v} input)
        (liftComponent (C := G124ProjectionCS.LensGetSlice input.View))
  | protocol input =>
      exact Functor.isoWhiskerRight
        (G124ProjectionCSLift.protocolObservationIso.{u, v} input)
        (liftComponent (C := G124ProjectionCS.ProtocolObservationSlice input))

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124ProjectionGlobal

end AAT.AG.LocalSemanticReconstruction.G124ProjectionGlobal
