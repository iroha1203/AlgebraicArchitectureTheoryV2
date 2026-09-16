import ResearchLean.AG.RealizationReconstruction.CSAATTypedRawTransportFunctoriality
import Formal.Util.AssertStandardAxioms

/-!
# Coefficient-aware exact maps of typed raw systems

The exact transports of Cycles 151--152 use one coefficient ring.  Geometry
morphisms also carry a possibly noninvertible coefficient homomorphism and
reindex source data along the inverse context functor.  Consequently their raw
component cannot in general be an isomorphism.

This module introduces the directed primitive needed by that geometry layer.
For every target context it retains an equivalence of the complete coordinate
and relation-generator types, while polynomial transport is the forward
coefficient map followed by the actual coordinate rename.  The restriction
square is required for every target arrow and every source polynomial.  The
identity map is constructed from the raw-system laws; no completed raw map or
restriction certificate is supplied.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation
open GeometryTransport

universe u v

namespace CoordinateFamilyExactEquiv

/-- The directed polynomial map induced by coefficient change and complete
coordinate renaming. -/
noncomputable def polynomialHom
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {source : LawAlgebra.CoordinateFamily W}
    {target : LawAlgebra.CoordinateFamily V}
    (transport : CoordinateFamilyExactEquiv source target)
    {k l : Type v} [CommRing k] [CommRing l]
    (coefficient : k →+* l) :
    LawAlgebra.FreeTypedCommAlg source k →+*
      LawAlgebra.FreeTypedCommAlg target l :=
  (transport.polynomialEquiv l).toRingHom.comp (MvPolynomial.map coefficient)

/-- Coefficients are sent by the supplied coefficient homomorphism. -/
@[simp] theorem polynomialHom_C
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {source : LawAlgebra.CoordinateFamily W}
    {target : LawAlgebra.CoordinateFamily V}
    (transport : CoordinateFamilyExactEquiv source target)
    {k l : Type v} [CommRing k] [CommRing l]
    (coefficient : k →+* l) (value : k) :
    transport.polynomialHom coefficient (MvPolynomial.C value) =
      MvPolynomial.C (coefficient value) := by
  simp [polynomialHom, polynomialEquiv]

/-- Every variable is sent by the stored complete coordinate equivalence. -/
@[simp] theorem polynomialHom_X
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {source : LawAlgebra.CoordinateFamily W}
    {target : LawAlgebra.CoordinateFamily V}
    (transport : CoordinateFamilyExactEquiv source target)
    {k l : Type v} [CommRing k] [CommRing l]
    (coefficient : k →+* l) (coordinate : source.Coord) :
    transport.polynomialHom coefficient (MvPolynomial.X coordinate) =
      MvPolynomial.X (transport.coordinateEquiv coordinate) := by
  simp [polynomialHom, polynomialEquiv]

/-- Directed polynomial maps compose by composing both the coefficient maps
and the complete coordinate equivalences. -/
theorem polynomialHom_trans
    {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {Q : Site.ArchitectureContext C}
    {firstFamily : LawAlgebra.CoordinateFamily W}
    {middleFamily : LawAlgebra.CoordinateFamily V}
    {lastFamily : LawAlgebra.CoordinateFamily Q}
    (first : CoordinateFamilyExactEquiv firstFamily middleFamily)
    (second : CoordinateFamilyExactEquiv middleFamily lastFamily)
    {k l m : Type v} [CommRing k] [CommRing l] [CommRing m]
    (firstCoefficient : k →+* l) (secondCoefficient : l →+* m) :
    (first.trans second).polynomialHom
        (secondCoefficient.comp firstCoefficient) =
      (second.polynomialHom secondCoefficient).comp
        (first.polynomialHom firstCoefficient) := by
  apply MvPolynomial.ringHom_ext <;> intro value
  · simp
  · simp [CoordinateFamilyExactEquiv.trans]

end CoordinateFamilyExactEquiv

namespace StructuralRelationFamilyExactEquiv

/-- Coefficient base change along a composite ring map is the successive base
change of the complete structural relation family. -/
theorem relationBaseChange_comp
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A}
    {k l m : Type v} [CommRing k] [CommRing l] [CommRing m]
    {family : LawAlgebra.CoordinateFamily W}
    (relations : LawAlgebra.StructuralRelationFamily family k)
    (firstCoefficient : k →+* l) (secondCoefficient : l →+* m) :
    relations.baseChange (secondCoefficient.comp firstCoefficient) =
      (relations.baseChange firstCoefficient).baseChange secondCoefficient := by
  cases relations
  simp [LawAlgebra.StructuralRelationFamily.baseChange, MvPolynomial.map_map]

/-- Exact relation transport survives coefficient base change without changing
its generator equivalence. -/
noncomputable def baseChange
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {k l : Type v} [CommRing k] [CommRing l]
    {sourceFamily : LawAlgebra.CoordinateFamily W}
    {targetFamily : LawAlgebra.CoordinateFamily V}
    {coordinate : CoordinateFamilyExactEquiv sourceFamily targetFamily}
    {source : LawAlgebra.StructuralRelationFamily sourceFamily k}
    {target : LawAlgebra.StructuralRelationFamily targetFamily k}
    (transport : StructuralRelationFamilyExactEquiv coordinate source target)
    (coefficient : k →+* l) :
    StructuralRelationFamilyExactEquiv coordinate
      (source.baseChange coefficient) (target.baseChange coefficient) where
  relationEquiv := transport.relationEquiv
  polynomial_eq relation := by
    have hcomm :
        (coordinate.polynomialEquiv l).toRingHom.comp
            (MvPolynomial.map coefficient) =
          (MvPolynomial.map coefficient).comp
            (coordinate.polynomialEquiv k).toRingHom := by
      apply MvPolynomial.ringHom_ext <;> intro value <;>
        simp [CoordinateFamilyExactEquiv.polynomialEquiv]
    calc
      coordinate.polynomialEquiv l
          ((source.baseChange coefficient).polynomial relation) =
        MvPolynomial.map coefficient
          (coordinate.polynomialEquiv k (source.polynomial relation)) :=
            RingHom.congr_fun hcomm (source.polynomial relation)
      _ = (target.baseChange coefficient).polynomial
          (transport.relationEquiv relation) := by
            rw [transport.polynomial_eq]
            rfl

end StructuralRelationFamilyExactEquiv

/-- A coefficient-aware exact typed raw map, indexed by target contexts.

The source context at `W` is `inverse.obj W`, matching the orientation of
geometry raw reindexing.  Structural relations are first changed along the
coefficient homomorphism and are then compared generator-by-generator with
the independently constructed target relations. -/
structure RawAmbientRestrictionSystemExactMapAgainst
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    (S : Site.AATSite A) (T : Site.AATSite B)
    (inverse : T.category ⥤ S.category)
    {k l : Type v} [CommRing k] [CommRing l]
    (coefficient : k →+* l)
    (source : LawAlgebra.RawAmbientRestrictionSystem S k)
    (target : LawAlgebra.RawAmbientRestrictionSystem T l) where
  coordinate : ∀ W,
    CoordinateFamilyExactEquiv
      (source.coordFamily (inverse.obj W)) (target.coordFamily W)
  relation : ∀ W,
    StructuralRelationFamilyExactEquiv (coordinate W)
      ((source.relationFamily (inverse.obj W)).baseChange coefficient)
      (target.relationFamily W)
  restriction_polynomial : ∀ {W V : T.category} (map : W ⟶ V)
      (polynomial : LawAlgebra.FreeTypedCommAlg
        (source.coordFamily (inverse.obj V)) k),
    (coordinate W).polynomialHom coefficient
        ((source.restrictionStable (inverse.map map)).restriction.polynomialMap
          polynomial) =
      (target.restrictionStable map).restriction.polynomialMap
        ((coordinate V).polynomialHom coefficient polynomial)

namespace RawAmbientRestrictionSystemExactMapAgainst

/-- Identity coefficient-aware exact raw map. -/
noncomputable def refl
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k) :
    RawAmbientRestrictionSystemExactMapAgainst S S (𝟭 S.category)
      (RingHom.id k) raw raw where
  coordinate W := CoordinateFamilyExactEquiv.refl (raw.coordFamily W)
  relation W := {
    relationEquiv := Equiv.refl _
    polynomial_eq := fun relation => by
      simpa [CoordinateFamilyExactEquiv.polynomialEquiv,
        CoordinateFamilyExactEquiv.refl,
        LawAlgebra.StructuralRelationFamily.baseChange] using
        (MvPolynomial.map_id (R := k)
          ((raw.relationFamily W).polynomial relation))
  }
  restriction_polynomial map polynomial := by
    simp [CoordinateFamilyExactEquiv.polynomialHom,
      CoordinateFamilyExactEquiv.polynomialEquiv,
      CoordinateFamilyExactEquiv.refl, MvPolynomial.map_id]

/-- Composition of coefficient-aware exact raw maps.  The composite relation
and restriction laws are derived from the two constituent maps. -/
noncomputable def trans
    {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}
    {S : Site.AATSite A} {T : Site.AATSite B} {Q : Site.AATSite C}
    {firstInverse : T.category ⥤ S.category}
    {secondInverse : Q.category ⥤ T.category}
    {k l m : Type v} [CommRing k] [CommRing l] [CommRing m]
    {firstCoefficient : k →+* l} {secondCoefficient : l →+* m}
    {source : LawAlgebra.RawAmbientRestrictionSystem S k}
    {middle : LawAlgebra.RawAmbientRestrictionSystem T l}
    {target : LawAlgebra.RawAmbientRestrictionSystem Q m}
    (first : RawAmbientRestrictionSystemExactMapAgainst
      S T firstInverse firstCoefficient source middle)
    (second : RawAmbientRestrictionSystemExactMapAgainst
      T Q secondInverse secondCoefficient middle target) :
    RawAmbientRestrictionSystemExactMapAgainst S Q
      (secondInverse ⋙ firstInverse)
      (secondCoefficient.comp firstCoefficient) source target where
  coordinate W := (first.coordinate (secondInverse.obj W)).trans
    (second.coordinate W)
  relation W := by
    rw [StructuralRelationFamilyExactEquiv.relationBaseChange_comp]
    exact ((first.relation (secondInverse.obj W)).baseChange
      secondCoefficient).trans (second.relation W)
  restriction_polynomial map polynomial := by
    rw [CoordinateFamilyExactEquiv.polynomialHom_trans]
    change (second.coordinate _).polynomialHom secondCoefficient
        ((first.coordinate _).polynomialHom firstCoefficient
          ((source.restrictionStable
            (firstInverse.map (secondInverse.map map))).restriction.polynomialMap
              polynomial)) = _
    rw [first.restriction_polynomial, second.restriction_polynomial]
    rw [CoordinateFamilyExactEquiv.polynomialHom_trans]
    rfl

/-- The literal raw equality carried by an existing strict geometry morphism
produces the coefficient-aware exact raw map.  This is the raw component of
the later strict embedding; the equality is consumed here to construct every
typed coordinate, relation, and restriction field. -/
noncomputable def ofGeometryRawEquality
    {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (baseHom : PackageTotalHom G.core H.core)
    (coefficient : G.Coefficient →+* H.Coefficient)
    (raw_eq : H.raw = rawTransport baseHom coefficient) :
    RawAmbientRestrictionSystemExactMapAgainst G.site H.site
      (coreContextInverse baseHom) coefficient G.raw H.raw := by
  rw [raw_eq]
  refine {
    coordinate := fun W => {
      coordinateEquiv := Equiv.refl _
      label_eq := fun _ => rfl
      localDataEquiv := fun _ => Equiv.refl _
    }
    relation := fun W => {
      relationEquiv := Equiv.refl _
      polynomial_eq := fun _ => by
        simp [CoordinateFamilyExactEquiv.polynomialEquiv, rawTransport,
          rawReindex, rawReindexCore, copyRelationFamily,
          copyCoordinateFamily]
    }
    restriction_polynomial := ?_
  }
  intro W V map polynomial
  simpa [CoordinateFamilyExactEquiv.polynomialHom,
    CoordinateFamilyExactEquiv.polynomialEquiv,
    rawTransport, rawReindex, rawReindexCore,
    LawAlgebra.RawAmbientRestrictionSystem.baseChange,
    LawAlgebra.RestrictionStableStructuralRelations.baseChange,
    LawAlgebra.TypedCoordinateRestriction.polynomialMap] using
      (MvPolynomial.map_bind₁ coefficient
        (G.raw.restrictionStable
          ((coreContextInverse baseHom).map map)).restriction.variableImage
        polynomial)

/-- The raw field of every existing strict geometry hom embeds into the new
coefficient-aware exact interface. -/
noncomputable def ofGeomReadHom
    {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    (hom : GeomReadHom G H baseHom) :
    RawAmbientRestrictionSystemExactMapAgainst G.site H.site
      (coreContextInverse baseHom) hom.coefficientHom G.raw H.raw :=
  ofGeometryRawEquality baseHom hom.coefficientHom hom.raw_eq

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end RawAmbientRestrictionSystemExactMapAgainst

end AAT.AG.RealizationReconstruction
