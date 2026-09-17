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

/-- Heterogeneous extensionality across propositionally equal inverse-context
functors and coefficient maps.  The computational coordinate and relation
actions remain explicit hypotheses. -/
theorem hext
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {S : Site.AATSite A} {T : Site.AATSite B}
    {firstInverse secondInverse : T.category ⥤ S.category}
    {k l : Type v} [CommRing k] [CommRing l]
    {firstCoefficient secondCoefficient : k →+* l}
    {source : LawAlgebra.RawAmbientRestrictionSystem S k}
    {target : LawAlgebra.RawAmbientRestrictionSystem T l}
    {first : RawAmbientRestrictionSystemExactMapAgainst
      S T firstInverse firstCoefficient source target}
    {second : RawAmbientRestrictionSystemExactMapAgainst
      S T secondInverse secondCoefficient source target}
    (hinverse : firstInverse = secondInverse)
    (hcoefficient : firstCoefficient = secondCoefficient)
    (hcoordinate : HEq first.coordinate second.coordinate)
    (hrelation : HEq first.relation second.relation) : HEq first second := by
  cases hinverse
  cases hcoefficient
  exact heq_of_eq (ext (eq_of_heq hcoordinate) hrelation)

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

/-- Heterogeneous extensionality over propositionally equal core-base maps. -/
theorem hext
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {firstBase secondBase : PackageTotalHom G.core H.core}
    {first : ExactGeomReadHom G H firstBase}
    {second : ExactGeomReadHom G H secondBase}
    (hbase : firstBase = secondBase)
    (hcoefficient : first.coefficientHom = second.coefficientHom)
    (hraw : HEq first.raw second.raw)
    (hrealization : HEq first.realization second.realization) : HEq first second := by
  cases hbase
  exact heq_of_eq (ext hcoefficient hraw (eq_of_heq hrealization))

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

/-- Exact geometry composition has the constructed identity as a left unit.
The raw proof compares every coordinate and structural-relation generator; it
does not use subsingleton elimination on computational raw data. -/
theorem id_comp
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : ExactGeometryTotalHom G H) : comp (id G) hom = hom := by
  let composed := comp (id G) hom
  have hbase : composed.base = hom.base := by
    apply PackageTotalHom.ext
    · apply ExtInstHom.ext
      apply ExactDoctrineHom.ext
      · rfl
      · apply Equiv.ext
        intro atom
        rfl
    · exact PackageTotalHom.upper_id_comp hom.base.upper
  apply ext hbase
  apply ExactGeomReadHom.hext hbase
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
  · rfl

/-- Exact geometry composition has the constructed identity as a right unit.
Every coordinate, local-data, and relation action is compared directly. -/
theorem comp_id
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : ExactGeometryTotalHom G H) : comp hom (id H) = hom := by
  let composed := comp hom (id H)
  have hbase : composed.base = hom.base := by
    apply PackageTotalHom.ext
    · apply ExtInstHom.ext
      apply ExactDoctrineHom.ext
      · rfl
      · apply Equiv.ext
        intro atom
        rfl
    · exact PackageTotalHom.upper_comp_id hom.base.upper
  apply ext hbase
  apply ExactGeomReadHom.hext hbase
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
  · rfl

/-- Exact geometry composition is associative.  The proof keeps the full
coefficient, coordinate, local-data, relation, and realization actions. -/
theorem comp_assoc
    {U : AtomCarrier.{u}}
    {G H K L : GeometryPackage.{u, v} U}
    (first : ExactGeometryTotalHom G H)
    (second : ExactGeometryTotalHom H K)
    (third : ExactGeometryTotalHom K L) :
    comp (comp first second) third = comp first (comp second third) := by
  let left := comp (comp first second) third
  let right := comp first (comp second third)
  have hbase : left.base = right.base := by
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
  apply ExactGeomReadHom.hext hbase
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
  · rfl

end ExactGeometryTotalHom

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
