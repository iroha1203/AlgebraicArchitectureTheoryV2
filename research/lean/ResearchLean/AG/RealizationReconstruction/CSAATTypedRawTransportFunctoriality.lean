import ResearchLean.AG.RealizationReconstruction.CSAATTypedRawTransport
import Formal.Util.AssertStandardAxioms

/-!
# Identity and composition for exact typed raw transport

This module proves that the primitive typed data introduced in Cycle 151 form
a coherent transport calculus.  Identity and composition are constructed for
coordinate families, structural-relation generators, and complete raw systems
along context functors.  In particular, restriction coherence for a composite
is derived from the two constituent restriction squares; it is not accepted
as a new composite certificate.

The coefficient ring is fixed in this layer.  This is exactly the situation
for the two G-123 CS families, whose independently constructed ReadingCores use
`Int`.  Coefficient-changing typed geometry transport and the non-raw geometry
fields remain later obligations.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u v

namespace CoordinateFamilyExactEquiv

/-- Identity exact transport of a typed coordinate family. -/
def refl
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A}
    (family : LawAlgebra.CoordinateFamily W) :
    CoordinateFamilyExactEquiv family family where
  coordinateEquiv := Equiv.refl _
  label_eq := fun _ => rfl
  localDataEquiv := fun _ => Equiv.refl _

/-- Composite exact transport of typed coordinate families. -/
def trans
    {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {Q : Site.ArchitectureContext C}
    {firstFamily : LawAlgebra.CoordinateFamily W}
    {middleFamily : LawAlgebra.CoordinateFamily V}
    {lastFamily : LawAlgebra.CoordinateFamily Q}
    (first : CoordinateFamilyExactEquiv firstFamily middleFamily)
    (second : CoordinateFamilyExactEquiv middleFamily lastFamily) :
    CoordinateFamilyExactEquiv firstFamily lastFamily where
  coordinateEquiv := first.coordinateEquiv.trans second.coordinateEquiv
  label_eq coordinate :=
    (second.label_eq (first.coordinateEquiv coordinate)).trans
      (first.label_eq coordinate)
  localDataEquiv coordinate :=
    (first.localDataEquiv coordinate).trans
      (second.localDataEquiv (first.coordinateEquiv coordinate))

/-- Polynomial transport for a composite is composition of the two complete
polynomial equivalences. -/
theorem polynomialEquiv_trans
    {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {Q : Site.ArchitectureContext C}
    {firstFamily : LawAlgebra.CoordinateFamily W}
    {middleFamily : LawAlgebra.CoordinateFamily V}
    {lastFamily : LawAlgebra.CoordinateFamily Q}
    (first : CoordinateFamilyExactEquiv firstFamily middleFamily)
    (second : CoordinateFamilyExactEquiv middleFamily lastFamily)
    (k : Type v) [CommRing k] :
    (first.trans second).polynomialEquiv k =
      (first.polynomialEquiv k).trans (second.polynomialEquiv k) := by
  simp [trans, polynomialEquiv]

end CoordinateFamilyExactEquiv

namespace StructuralRelationFamilyExactEquiv

/-- Identity exact transport of structural relation generators. -/
def refl
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {k : Type v} [CommRing k]
    {family : LawAlgebra.CoordinateFamily W}
    (relations : LawAlgebra.StructuralRelationFamily family k) :
    StructuralRelationFamilyExactEquiv
      (CoordinateFamilyExactEquiv.refl family) relations relations where
  relationEquiv := Equiv.refl _
  polynomial_eq := fun _ => by
    simp [CoordinateFamilyExactEquiv.polynomialEquiv,
      CoordinateFamilyExactEquiv.refl]

/-- Composite exact transport of structural relation generators. -/
def trans
    {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {Q : Site.ArchitectureContext C} {k : Type v} [CommRing k]
    {firstFamily : LawAlgebra.CoordinateFamily W}
    {middleFamily : LawAlgebra.CoordinateFamily V}
    {lastFamily : LawAlgebra.CoordinateFamily Q}
    {firstRelations : LawAlgebra.StructuralRelationFamily firstFamily k}
    {middleRelations : LawAlgebra.StructuralRelationFamily middleFamily k}
    {lastRelations : LawAlgebra.StructuralRelationFamily lastFamily k}
    {firstCoordinate : CoordinateFamilyExactEquiv firstFamily middleFamily}
    {secondCoordinate : CoordinateFamilyExactEquiv middleFamily lastFamily}
    (first : StructuralRelationFamilyExactEquiv firstCoordinate
      firstRelations middleRelations)
    (second : StructuralRelationFamilyExactEquiv secondCoordinate
      middleRelations lastRelations) :
    StructuralRelationFamilyExactEquiv (firstCoordinate.trans secondCoordinate)
      firstRelations lastRelations where
  relationEquiv := first.relationEquiv.trans second.relationEquiv
  polynomial_eq relation := by
    rw [CoordinateFamilyExactEquiv.polynomialEquiv_trans]
    change secondCoordinate.polynomialEquiv k
        (firstCoordinate.polynomialEquiv k
          (firstRelations.polynomial relation)) = _
    rw [first.polynomial_eq, second.polynomial_eq]
    rfl

end StructuralRelationFamilyExactEquiv

namespace RawAmbientRestrictionSystemExactTransportAlong

/-- Identity exact transport of a complete raw restriction system. -/
noncomputable def refl
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k) :
    RawAmbientRestrictionSystemExactTransportAlong S S (𝟭 S.category) k raw raw where
  coordinate W := CoordinateFamilyExactEquiv.refl (raw.coordFamily W)
  relation W := StructuralRelationFamilyExactEquiv.refl (raw.relationFamily W)
  restriction_polynomial map polynomial := by
    simp [CoordinateFamilyExactEquiv.polynomialEquiv,
      CoordinateFamilyExactEquiv.refl]

/-- Composite exact transport along composite context functors.  Its
restriction square is derived by applying the second coordinate equivalence to
the first square and then using the second square. -/
noncomputable def trans
    {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}
    {S : Site.AATSite A} {T : Site.AATSite B} {Q : Site.AATSite C}
    {F : S.category ⥤ T.category} {G : T.category ⥤ Q.category}
    {k : Type v} [CommRing k]
    {source : LawAlgebra.RawAmbientRestrictionSystem S k}
    {middle : LawAlgebra.RawAmbientRestrictionSystem T k}
    {target : LawAlgebra.RawAmbientRestrictionSystem Q k}
    (first : RawAmbientRestrictionSystemExactTransportAlong
      S T F k source middle)
    (second : RawAmbientRestrictionSystemExactTransportAlong
      T Q G k middle target) :
    RawAmbientRestrictionSystemExactTransportAlong
      S Q (F ⋙ G) k source target where
  coordinate W := (first.coordinate W).trans
    (second.coordinate (F.obj W))
  relation W := (first.relation W).trans
    (second.relation (F.obj W))
  restriction_polynomial map polynomial := by
    rw [CoordinateFamilyExactEquiv.polynomialEquiv_trans]
    change (second.coordinate (F.obj _)).polynomialEquiv k
        ((first.coordinate _).polynomialEquiv k
          ((source.restrictionStable map).restriction.polynomialMap polynomial)) = _
    rw [first.restriction_polynomial]
    simpa [CoordinateFamilyExactEquiv.polynomialEquiv_trans] using
      (second.restriction_polynomial (F.map map)
        ((first.coordinate _).polynomialEquiv k polynomial))

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end RawAmbientRestrictionSystemExactTransportAlong

end AAT.AG.RealizationReconstruction
