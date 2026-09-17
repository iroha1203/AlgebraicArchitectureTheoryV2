import ResearchLean.AG.RealizationReconstruction.CSAATExactGeometryMorphisms
import Formal.Util.AssertStandardAxioms

/-!
# Extensionality infrastructure for exact typed geometry morphisms
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation
open GeometryTransport

universe u v

namespace CoordinateFamilyExactEquiv

@[ext (iff := false)] theorem ext
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {source : LawAlgebra.CoordinateFamily W}
    {target : LawAlgebra.CoordinateFamily V}
    {first second : CoordinateFamilyExactEquiv source target}
    (hcoordinate : first.coordinateEquiv = second.coordinateEquiv)
    (hlocal : HEq first.localDataEquiv second.localDataEquiv) :
    first = second := by
  cases first
  cases second
  cases hcoordinate
  cases hlocal
  rfl

theorem refl_trans
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {source : LawAlgebra.CoordinateFamily W}
    {target : LawAlgebra.CoordinateFamily V}
    (transport : CoordinateFamilyExactEquiv source target) :
    (CoordinateFamilyExactEquiv.refl source).trans transport = transport := by
  apply ext
  · apply Equiv.ext
    intro coordinate
    rfl
  · apply heq_of_eq
    funext coordinate
    apply Equiv.ext
    intro datum
    simp [CoordinateFamilyExactEquiv.trans,
      CoordinateFamilyExactEquiv.refl]

theorem trans_refl
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {source : LawAlgebra.CoordinateFamily W}
    {target : LawAlgebra.CoordinateFamily V}
    (transport : CoordinateFamilyExactEquiv source target) :
    transport.trans (CoordinateFamilyExactEquiv.refl target) = transport := by
  apply ext
  · apply Equiv.ext
    intro coordinate
    rfl
  · apply heq_of_eq
    funext coordinate
    apply Equiv.ext
    intro datum
    simp [CoordinateFamilyExactEquiv.trans,
      CoordinateFamilyExactEquiv.refl]

theorem trans_assoc
    {U : AtomCarrier.{u}} {A B C D : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {Q : Site.ArchitectureContext C} {R : Site.ArchitectureContext D}
    {firstFamily : LawAlgebra.CoordinateFamily W}
    {secondFamily : LawAlgebra.CoordinateFamily V}
    {thirdFamily : LawAlgebra.CoordinateFamily Q}
    {fourthFamily : LawAlgebra.CoordinateFamily R}
    (first : CoordinateFamilyExactEquiv firstFamily secondFamily)
    (second : CoordinateFamilyExactEquiv secondFamily thirdFamily)
    (third : CoordinateFamilyExactEquiv thirdFamily fourthFamily) :
    (first.trans second).trans third = first.trans (second.trans third) := by
  apply ext
  · apply Equiv.ext
    intro coordinate
    rfl
  · apply heq_of_eq
    funext coordinate
    apply Equiv.ext
    intro datum
    rfl

end CoordinateFamilyExactEquiv

namespace StructuralRelationFamilyExactEquiv

@[ext (iff := false)] theorem ext
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {k : Type v} [CommRing k]
    {sourceFamily : LawAlgebra.CoordinateFamily W}
    {targetFamily : LawAlgebra.CoordinateFamily V}
    {coordinate : CoordinateFamilyExactEquiv sourceFamily targetFamily}
    {source : LawAlgebra.StructuralRelationFamily sourceFamily k}
    {target : LawAlgebra.StructuralRelationFamily targetFamily k}
    {first second : StructuralRelationFamilyExactEquiv coordinate source target}
    (hrelation : first.relationEquiv = second.relationEquiv) : first = second := by
  cases first
  cases second
  cases hrelation
  rfl

end StructuralRelationFamilyExactEquiv

namespace RawAmbientRestrictionSystemExactMapAgainst

@[ext (iff := false)] theorem ext
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {S : Site.AATSite A} {T : Site.AATSite B}
    {inverse : T.category ⥤ S.category}
    {k l : Type v} [CommRing k] [CommRing l]
    {coefficient : k →+* l}
    {source : LawAlgebra.RawAmbientRestrictionSystem S k}
    {target : LawAlgebra.RawAmbientRestrictionSystem T l}
    {first second : RawAmbientRestrictionSystemExactMapAgainst
      S T inverse coefficient source target}
    (hcoordinate : first.coordinate = second.coordinate)
    (hrelation : HEq first.relation second.relation) : first = second := by
  cases first
  cases second
  cases hcoordinate
  cases hrelation
  rfl

end RawAmbientRestrictionSystemExactMapAgainst

namespace RealizationTransportSupply

@[ext (iff := false)] theorem exactExt
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {f : PackageTotalHom P Q}
    {first second : RealizationTransportSupply P Q f}
    (hsupport : first.supportComp = second.supportComp)
    (haxis : first.axisComp = second.axisComp)
    (hobservable : first.observableComp = second.observableComp) :
    first = second := by
  cases first
  cases second
  cases hsupport
  cases haxis
  cases hobservable
  rfl

end RealizationTransportSupply

namespace ExactGeomReadHom

@[ext (iff := false)] theorem ext
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    {first second : ExactGeomReadHom G H baseHom}
    (hcoefficient : first.coefficientHom = second.coefficientHom)
    (hraw : HEq first.raw second.raw)
    (hrealization : first.realization = second.realization) : first = second := by
  have hcoverage : first.coverage = second.coverage := Subsingleton.elim _ _
  have hoverlap : first.overlap = second.overlap := Subsingleton.elim _ _
  cases first
  cases second
  cases hcoverage
  cases hoverlap
  cases hcoefficient
  cases hraw
  cases hrealization
  rfl

end ExactGeomReadHom

namespace ExactGeometryTotalHom

@[ext (iff := false)] theorem ext
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : ExactGeometryTotalHom G H}
    (hbase : first.base = second.base)
    (hgeometry : HEq first.geometry second.geometry) : first = second := by
  cases first
  cases second
  cases hbase
  cases hgeometry
  rfl

end ExactGeometryTotalHom

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
