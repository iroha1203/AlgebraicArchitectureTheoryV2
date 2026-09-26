import ResearchLean.AG.LocalSemanticReconstruction.G124ComparisonTransport
import ResearchLean.AG.RealizationComparisonIdempotents.FunctorNaturality
import Formal.Util.AssertStandardAxioms

/-! Karoubi and Arrow actions of the common reader and its three direct
component projections. -/

namespace AAT.AG.LocalSemanticReconstruction.G124KaroubiProjection

open CategoryTheory CategoryTheory.Idempotents
open IndependentAATPrimitiveReconstruction RealizationComparisonIdempotents
open G124ProjectionGlobal

universe u v

/-- The one accepted reader, extended to arbitrary idempotents. -/
noncomputable def karoubiReading (parameter : Parameter.{u, v}) :
    Karoubi (NativeCategory parameter) ⥤ Karoubi (LocalCategory parameter) :=
  (functorExtension₂ _ _).obj (reading parameter)

/-- The one accepted reader on arbitrary comparisons. -/
noncomputable def arrowReading (parameter : Parameter.{u, v}) :
    Arrow (NativeCategory parameter) ⥤ Arrow (LocalCategory parameter) :=
  Functor.mapArrow (reading parameter)

/-- The reader on an arbitrary idempotent comparison square. -/
noncomputable def karoubiArrowReading (parameter : Parameter.{u, v}) :
    Karoubi (Arrow (NativeCategory parameter)) ⥤
      Karoubi (Arrow (LocalCategory parameter)) :=
  karoubiArrowMap (reading parameter)

@[simp] theorem karoubiReading_obj_X (parameter : Parameter.{u, v})
    (P : Karoubi (NativeCategory parameter)) :
    ((karoubiReading parameter).obj P).X = (reading parameter).obj P.X := rfl

@[simp] theorem karoubiReading_obj_p (parameter : Parameter.{u, v})
    (P : Karoubi (NativeCategory parameter)) :
    ((karoubiReading parameter).obj P).p = (reading parameter).map P.p := rfl

@[simp] theorem karoubiReading_map_f (parameter : Parameter.{u, v})
    {P Q : Karoubi (NativeCategory parameter)} (f : P ⟶ Q) :
    ((karoubiReading parameter).map f).f = (reading parameter).map f.f := rfl

@[simp] theorem arrowReading_obj_hom (parameter : Parameter.{u, v})
    (c : Arrow (NativeCategory parameter)) :
    ((arrowReading parameter).obj c).hom = (reading parameter).map c.hom := rfl

@[simp] theorem karoubiArrowReading_obj_left_p (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (NativeCategory parameter))) :
    ((karoubiArrowReading parameter).obj P).p.left =
      (reading parameter).map P.p.left := rfl

@[simp] theorem karoubiArrowReading_obj_right_p (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (NativeCategory parameter))) :
    ((karoubiArrowReading parameter).obj P).p.right =
      (reading parameter).map P.p.right := rfl

/-- The G-119 comparison of `Kar(Arr(-))` and `Arr(Kar(-))` at the actual
G-124 reader, for every parameter and every idempotent comparison. -/
noncomputable def karoubiArrowReaderNaturality (parameter : Parameter.{u, v}) :
    karoubiArrowNaturalityLeft (reading parameter) ≅
      karoubiArrowNaturalityRight (reading parameter) :=
  karoubiArrowNaturalityIso (reading parameter)

/-- The three local component projections extended to all idempotents. -/
noncomputable def bottomKaroubiProjection (parameter : Parameter.{u, v}) :
    Karoubi (LocalCategory parameter) ⥤ Karoubi (BottomTarget parameter) :=
  (functorExtension₂ _ _).obj (localBottom parameter)

noncomputable def observationKaroubiProjection (parameter : Parameter.{u, v}) :
    Karoubi (LocalCategory parameter) ⥤ Karoubi (ObservationTarget parameter) :=
  (functorExtension₂ _ _).obj (localObservation parameter)

noncomputable def coefficientKaroubiProjection (parameter : Parameter.{u, v}) :
    Karoubi (LocalCategory parameter) ⥤ Karoubi (CoefficientTarget parameter) :=
  (functorExtension₂ _ _).obj (localCoefficient parameter)

@[simp] theorem bottomKaroubiProjection_obj_p (parameter : Parameter.{u, v})
    (P : Karoubi (LocalCategory parameter)) :
    ((bottomKaroubiProjection parameter).obj P).p =
      (localBottom parameter).map P.p := rfl

@[simp] theorem observationKaroubiProjection_obj_p (parameter : Parameter.{u, v})
    (P : Karoubi (LocalCategory parameter)) :
    ((observationKaroubiProjection parameter).obj P).p =
      (localObservation parameter).map P.p := rfl

@[simp] theorem coefficientKaroubiProjection_obj_p (parameter : Parameter.{u, v})
    (P : Karoubi (LocalCategory parameter)) :
    ((coefficientKaroubiProjection parameter).obj P).p =
      (localCoefficient parameter).map P.p := rfl

/-- The three projections on idempotent comparison arrows. -/
noncomputable def bottomKaroubiArrowProjection (parameter : Parameter.{u, v}) :
    Karoubi (Arrow (LocalCategory parameter)) ⥤
      Karoubi (Arrow (BottomTarget parameter)) :=
  karoubiArrowMap (localBottom parameter)

noncomputable def observationKaroubiArrowProjection (parameter : Parameter.{u, v}) :
    Karoubi (Arrow (LocalCategory parameter)) ⥤
      Karoubi (Arrow (ObservationTarget parameter)) :=
  karoubiArrowMap (localObservation parameter)

noncomputable def coefficientKaroubiArrowProjection (parameter : Parameter.{u, v}) :
    Karoubi (Arrow (LocalCategory parameter)) ⥤
      Karoubi (Arrow (CoefficientTarget parameter)) :=
  karoubiArrowMap (localCoefficient parameter)

/-- The III-1 bottom comparison commutes with extension to arbitrary
idempotents; its component contains the complete pointed-extraction map. -/
noncomputable def bottomKaroubiReadingIso (parameter : Parameter.{u, v}) :
    karoubiReading parameter ⋙ bottomKaroubiProjection parameter ≅
      (functorExtension₂ _ _).obj (nativeBottom parameter) := by
  change (functorExtension₂ _ _).obj (reading parameter ⋙ localBottom parameter) ≅
    (functorExtension₂ _ _).obj (nativeBottom parameter)
  exact (functorExtension₂ _ _).mapIso (bottomReadingIso parameter)

noncomputable def observationKaroubiReadingIso (parameter : Parameter.{u, v}) :
    karoubiReading parameter ⋙ observationKaroubiProjection parameter ≅
      (functorExtension₂ _ _).obj (nativeObservation parameter) := by
  change (functorExtension₂ _ _).obj (reading parameter ⋙ localObservation parameter) ≅
    (functorExtension₂ _ _).obj (nativeObservation parameter)
  exact (functorExtension₂ _ _).mapIso (observationReadingIso parameter)

noncomputable def coefficientKaroubiReadingIso (parameter : Parameter.{u, v}) :
    karoubiReading parameter ⋙ coefficientKaroubiProjection parameter ≅
      (functorExtension₂ _ _).obj (nativeCoefficient parameter) := by
  change (functorExtension₂ _ _).obj (reading parameter ⋙ localCoefficient parameter) ≅
    (functorExtension₂ _ _).obj (nativeCoefficient parameter)
  exact (functorExtension₂ _ _).mapIso (coefficientReadingIso parameter)

noncomputable def bottomArrowReadingIso (parameter : Parameter.{u, v}) :
    arrowReading parameter ⋙ Functor.mapArrow (localBottom parameter) ≅
      Functor.mapArrow (nativeBottom parameter) := by
  change (Functor.mapArrowFunctor _ _).obj (reading parameter ⋙ localBottom parameter) ≅
    (Functor.mapArrowFunctor _ _).obj (nativeBottom parameter)
  exact (Functor.mapArrowFunctor _ _).mapIso (bottomReadingIso parameter)

noncomputable def observationArrowReadingIso (parameter : Parameter.{u, v}) :
    arrowReading parameter ⋙ Functor.mapArrow (localObservation parameter) ≅
      Functor.mapArrow (nativeObservation parameter) := by
  change (Functor.mapArrowFunctor _ _).obj
      (reading parameter ⋙ localObservation parameter) ≅
    (Functor.mapArrowFunctor _ _).obj (nativeObservation parameter)
  exact (Functor.mapArrowFunctor _ _).mapIso (observationReadingIso parameter)

noncomputable def coefficientArrowReadingIso (parameter : Parameter.{u, v}) :
    arrowReading parameter ⋙ Functor.mapArrow (localCoefficient parameter) ≅
      Functor.mapArrow (nativeCoefficient parameter) := by
  change (Functor.mapArrowFunctor _ _).obj
      (reading parameter ⋙ localCoefficient parameter) ≅
    (Functor.mapArrowFunctor _ _).obj (nativeCoefficient parameter)
  exact (Functor.mapArrowFunctor _ _).mapIso (coefficientReadingIso parameter)

noncomputable def bottomKaroubiArrowReadingIso (parameter : Parameter.{u, v}) :
    karoubiArrowReading parameter ⋙ bottomKaroubiArrowProjection parameter ≅
      karoubiArrowMap (nativeBottom parameter) := by
  change (functorExtension₂ _ _).obj
      ((Functor.mapArrowFunctor _ _).obj (reading parameter ⋙ localBottom parameter)) ≅
    (functorExtension₂ _ _).obj
      ((Functor.mapArrowFunctor _ _).obj (nativeBottom parameter))
  exact (functorExtension₂ _ _).mapIso
    ((Functor.mapArrowFunctor _ _).mapIso (bottomReadingIso parameter))

noncomputable def observationKaroubiArrowReadingIso (parameter : Parameter.{u, v}) :
    karoubiArrowReading parameter ⋙ observationKaroubiArrowProjection parameter ≅
      karoubiArrowMap (nativeObservation parameter) := by
  change (functorExtension₂ _ _).obj
      ((Functor.mapArrowFunctor _ _).obj
        (reading parameter ⋙ localObservation parameter)) ≅
    (functorExtension₂ _ _).obj
      ((Functor.mapArrowFunctor _ _).obj (nativeObservation parameter))
  exact (functorExtension₂ _ _).mapIso
    ((Functor.mapArrowFunctor _ _).mapIso (observationReadingIso parameter))

noncomputable def coefficientKaroubiArrowReadingIso (parameter : Parameter.{u, v}) :
    karoubiArrowReading parameter ⋙ coefficientKaroubiArrowProjection parameter ≅
      karoubiArrowMap (nativeCoefficient parameter) := by
  change (functorExtension₂ _ _).obj
      ((Functor.mapArrowFunctor _ _).obj
        (reading parameter ⋙ localCoefficient parameter)) ≅
    (functorExtension₂ _ _).obj
      ((Functor.mapArrowFunctor _ _).obj (nativeCoefficient parameter))
  exact (functorExtension₂ _ _).mapIso
    ((Functor.mapArrowFunctor _ _).mapIso (coefficientReadingIso parameter))

/-- Both idempotent endpoints and the comparison map are evaluated through
the actual direct component functor, for each of the three projections. -/
@[simp] theorem bottomKaroubiArrow_obj_hom (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (LocalCategory parameter))) :
    ((bottomKaroubiArrowProjection parameter).obj P).X.hom =
      (localBottom parameter).map P.X.hom := rfl

@[simp] theorem bottomKaroubiArrow_obj_left_p (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (LocalCategory parameter))) :
    ((bottomKaroubiArrowProjection parameter).obj P).p.left =
      (localBottom parameter).map P.p.left := rfl

@[simp] theorem bottomKaroubiArrow_obj_right_p (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (LocalCategory parameter))) :
    ((bottomKaroubiArrowProjection parameter).obj P).p.right =
      (localBottom parameter).map P.p.right := rfl

@[simp] theorem observationKaroubiArrow_obj_hom (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (LocalCategory parameter))) :
    ((observationKaroubiArrowProjection parameter).obj P).X.hom =
      (localObservation parameter).map P.X.hom := rfl

@[simp] theorem observationKaroubiArrow_obj_left_p (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (LocalCategory parameter))) :
    ((observationKaroubiArrowProjection parameter).obj P).p.left =
      (localObservation parameter).map P.p.left := rfl

@[simp] theorem observationKaroubiArrow_obj_right_p (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (LocalCategory parameter))) :
    ((observationKaroubiArrowProjection parameter).obj P).p.right =
      (localObservation parameter).map P.p.right := rfl

@[simp] theorem coefficientKaroubiArrow_obj_hom (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (LocalCategory parameter))) :
    ((coefficientKaroubiArrowProjection parameter).obj P).X.hom =
      (localCoefficient parameter).map P.X.hom := rfl

@[simp] theorem coefficientKaroubiArrow_obj_left_p (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (LocalCategory parameter))) :
    ((coefficientKaroubiArrowProjection parameter).obj P).p.left =
      (localCoefficient parameter).map P.p.left := rfl

@[simp] theorem coefficientKaroubiArrow_obj_right_p (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (LocalCategory parameter))) :
    ((coefficientKaroubiArrowProjection parameter).obj P).p.right =
      (localCoefficient parameter).map P.p.right := rfl

@[simp] theorem karoubiArrowReaderNaturality_left_f
    (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (NativeCategory parameter))) :
    (((karoubiArrowReaderNaturality parameter).hom.app P).left).f =
      (reading parameter).map P.p.left :=
  karoubiArrowNaturalityIso_hom_app_left_f (reading parameter) P

@[simp] theorem karoubiArrowReaderNaturality_right_f
    (parameter : Parameter.{u, v})
    (P : Karoubi (Arrow (NativeCategory parameter))) :
    (((karoubiArrowReaderNaturality parameter).hom.app P).right).f =
      (reading parameter).map P.p.right :=
  karoubiArrowNaturalityIso_hom_app_right_f (reading parameter) P

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124KaroubiProjection

end AAT.AG.LocalSemanticReconstruction.G124KaroubiProjection
