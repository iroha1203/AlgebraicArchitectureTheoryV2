import ResearchLean.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRawLocalValidation
import ResearchLean.AG.RealizationReconstruction.CSAATExactGeometryCategory
import Mathlib.Logic.Equiv.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Primitive readings of coefficient-aware explicit raw maps

Implementation notes: coordinate names, local-data values, and relation names
use independent forward and backward Bool graphs. Labels and polynomials are
compared at individual coordinates or relation generators. Restriction
naturality is imposed on variable images and extended to all polynomials by
the universal property of the free polynomial algebra. Coefficient maps retain
their native directed, potentially noninvertible meaning.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentExplicitRaw

noncomputable section

universe u v

open CategoryTheory LawAlgebra RealizationReconstruction AlgebraicGraphCoherence

variable {U : AtomCarrier.{u}}

namespace Coordinate

variable {A B : ArchitectureObject U}
variable {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}

/-- Primitive coordinate and dependent local-data graph families. -/
abbrev Data (S : CoordinateFamily W) (T : CoordinateFamily V) :=
  (e : EquivGraphCode S.Coord T.Coord) ×
    ∀ c, EquivGraphCode (S.LocalData c) (T.LocalData (e.assemble c))

/-- Source-only native coordinate and local-data equivalence families. -/
abbrev NativeData (S : CoordinateFamily W) (T : CoordinateFamily V) :=
  (e : S.Coord ≃ T.Coord) × ∀ c, S.LocalData c ≃ T.LocalData (e c)

variable {S : CoordinateFamily W} {T : CoordinateFamily V}

/-- Convert both native equivalence families into their primitive inverse graphs. -/
def dataEquiv : NativeData S T ≃ Data S T :=
  (Equiv.sigmaCongrLeft' EquivGraphCode.equivEquiv.symm).trans
    (Equiv.sigmaCongrRight fun _ => Equiv.piCongrRight fun _ => EquivGraphCode.equivEquiv.symm)

/-- Coordinate reconstruction is the original native equivalence. -/
theorem coordinate_dataEquiv (d : NativeData S T) : (dataEquiv d).1.assemble = d.1 :=
  EquivGraphCode.assemble_read d.1

/-- The label at each decoded coordinate is its source label. -/
def IsLawful (d : Data S T) : Prop := ∀ c, T.label (d.1.assemble c) = S.label c

/-- Primitive inverse graph data with pointwise label preservation. -/
abbrev Code (S : CoordinateFamily W) (T : CoordinateFamily V) :=
  {d : Data S T // IsLawful d}

/-- Source-only dependent view of a native complete coordinate equivalence. -/
def nativeEquiv : CoordinateFamilyExactEquiv S T ≃
    {d : NativeData S T // ∀ c, T.label (d.1 c) = S.label c} where
  toFun R := ⟨⟨R.coordinateEquiv, R.localDataEquiv⟩, R.label_eq⟩
  invFun d := ⟨d.val.1, d.property, d.val.2⟩
  left_inv R := by cases R; rfl
  right_inv d := by rcases d with ⟨⟨e, l⟩, h⟩; rfl

/-- Complete typed coordinate equivalences correspond to primitive graph data and label equations. -/
def readingEquiv : CoordinateFamilyExactEquiv S T ≃ Code S T :=
  nativeEquiv.trans (Equiv.subtypeEquiv dataEquiv (fun d => by
    change (∀ c, T.label (d.1 c) = S.label c) ↔
      (∀ c, T.label ((dataEquiv d).1.assemble c) = S.label c)
    rw [coordinate_dataEquiv]))

/-- Assemble native coordinate and local-data equivalences from primitive graph cells. -/
def assemble (c : Code S T) : CoordinateFamilyExactEquiv S T := readingEquiv.symm c

/-- Read every native coordinate and dependent local-data action into primitive graphs. -/
def read (R : CoordinateFamilyExactEquiv S T) : Code S T := readingEquiv R

/-- Assembly recovers every native coordinate-transport component. -/
theorem assemble_read (R : CoordinateFamilyExactEquiv S T) : assemble (read R) = R :=
  readingEquiv.left_inv R

/-- Reading recovers every primitive coordinate and local-data graph. -/
theorem read_assemble (c : Code S T) : read (assemble c) = c := readingEquiv.right_inv c

/-- The actual coordinate map is decoded directly from its primitive graph. -/
theorem coordinate_assemble (c : Code S T) : (assemble c).coordinateEquiv = c.val.1.assemble := rfl

/-- Each actual local-data equivalence is decoded from its own primitive graph. -/
theorem localData_assemble (c : Code S T) (i : S.Coord) :
    (assemble c).localDataEquiv i = (c.val.2 i).assemble := rfl

end Coordinate

variable {A B : ArchitectureObject U} {S : Site.AATSite A} {T : Site.AATSite B}
variable {k l : Type v} [CommRing k] [CommRing l]

/-- Computational raw-map data contains only coordinate/local-data graphs and relation graphs. -/
structure Data (inverse : T.category ⥤ S.category)
    (source : RawAmbientRestrictionSystem S k) (target : RawAmbientRestrictionSystem T l) where
  /-- Primitive coordinate and local-data graph family at every target context. -/
  coordinate : ∀ W, Coordinate.Code (source.coordFamily (inverse.obj W)) (target.coordFamily W)
  /-- Primitive forward and backward relation-generator graphs. -/
  relation : ∀ W, EquivGraphCode (source.relationFamily (inverse.obj W)).Relation
    (target.relationFamily W).Relation

variable {inverse : T.category ⥤ S.category}
variable {source : RawAmbientRestrictionSystem S k} {target : RawAmbientRestrictionSystem T l}

/-- The actual coordinate action is decoded from its primitive inverse graphs. -/
def coordinateMap (d : Data inverse source target) (W : T.category) :=
  (Coordinate.assemble (d.coordinate W)).coordinateEquiv

/-- Point polynomial preservation and variable-image naturality are the independent raw laws. -/
structure IsLawful (coefficient : k →+* l) (d : Data inverse source target) : Prop where
  /-- Preserve each structural relation generator after forward coefficient change and coordinate rename. -/
  polynomial : ∀ W r,
    MvPolynomial.rename (coordinateMap d W)
      (MvPolynomial.map coefficient ((source.relationFamily (inverse.obj W)).polynomial r)) =
        (target.relationFamily W).polynomial ((d.relation W).assemble r)
  /-- Restriction commutes on each variable; all polynomial instances are derived later. -/
  image : ∀ {W V : T.category} (g : W ⟶ V) (c : (source.coordFamily (inverse.obj V)).Coord),
    MvPolynomial.rename (coordinateMap d W)
      (MvPolynomial.map coefficient
        ((source.restrictionStable (inverse.map g)).restriction.variableImage c)) =
      (target.restrictionStable g).restriction.variableImage (coordinateMap d V c)

/-- Construct the entire native raw map, extending the variable square to all polynomials. -/
def assemble (coefficient : k →+* l) (d : Data inverse source target) (hl : IsLawful coefficient d) :
    RawAmbientRestrictionSystemExactMapAgainst S T inverse coefficient source target where
  coordinate W := Coordinate.assemble (d.coordinate W)
  relation W :=
    { relationEquiv := (d.relation W).assemble
      polynomial_eq r := by
        simpa [CoordinateFamilyExactEquiv.polynomialEquiv, StructuralRelationFamily.baseChange,
          coordinateMap] using hl.polynomial W r }
  restriction_polynomial {W V} g p := by
    have hh :
        ((Coordinate.assemble (d.coordinate W)).polynomialHom coefficient).comp
            (source.restrictionStable (inverse.map g)).restriction.polynomialMap =
          (target.restrictionStable g).restriction.polynomialMap.comp
            ((Coordinate.assemble (d.coordinate V)).polynomialHom coefficient) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [TypedCoordinateRestriction.polynomialMap]
      · intro c
        simpa [TypedCoordinateRestriction.polynomialMap, CoordinateFamilyExactEquiv.polynomialHom,
          CoordinateFamilyExactEquiv.polynomialEquiv, coordinateMap] using hl.image g c
    exact RingHom.congr_fun hh p

/-- Read all coordinate, local-data, and relation actions from a native explicit raw map. -/
def read {coefficient : k →+* l}
    (R : RawAmbientRestrictionSystemExactMapAgainst S T inverse coefficient source target) :
    Data inverse source target where
  coordinate W := Coordinate.read (R.coordinate W)
  relation W := EquivGraphCode.read (R.relation W).relationEquiv

/-- The decoded coordinate point family is the native coordinate equivalence. -/
theorem coordinateMap_read {coefficient : k →+* l}
    (R : RawAmbientRestrictionSystemExactMapAgainst S T inverse coefficient source target)
    (W : T.category) : coordinateMap (read R) W = (R.coordinate W).coordinateEquiv := by
  unfold coordinateMap read
  rw [Coordinate.assemble_read]

/-- Native polynomial naturality supplies both independent relation and variable equations. -/
theorem read_isLawful {coefficient : k →+* l}
    (R : RawAmbientRestrictionSystemExactMapAgainst S T inverse coefficient source target) :
    IsLawful coefficient (read R) where
  polynomial W r := by
    rw [coordinateMap_read]
    change MvPolynomial.rename (R.coordinate W).coordinateEquiv
      (MvPolynomial.map coefficient ((source.relationFamily (inverse.obj W)).polynomial r)) =
        (target.relationFamily W).polynomial ((EquivGraphCode.read (R.relation W).relationEquiv).assemble r)
    rw [EquivGraphCode.assemble_read]
    simpa [CoordinateFamilyExactEquiv.polynomialEquiv, StructuralRelationFamily.baseChange]
      using (R.relation W).polynomial_eq r
  image g c := by
    rw [coordinateMap_read, coordinateMap_read]
    simpa [CoordinateFamilyExactEquiv.polynomialHom, CoordinateFamilyExactEquiv.polynomialEquiv,
      TypedCoordinateRestriction.polynomialMap] using R.restriction_polynomial g (MvPolynomial.X c)

/-- Dependent relation transports agree when their coordinate transport and relation equivalence agree. -/
theorem relation_heq {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {F : CoordinateFamily W} {G : CoordinateFamily V}
    {c d : CoordinateFamilyExactEquiv F G}
    {R : StructuralRelationFamily F k} {R' : StructuralRelationFamily G k}
    {r : StructuralRelationFamilyExactEquiv c R R'}
    {s : StructuralRelationFamilyExactEquiv d R R'}
    (h : c = d) (hr : r.relationEquiv = s.relationEquiv) : HEq r s := by
  cases h
  exact heq_of_eq (StructuralRelationFamilyExactEquiv.ext hr)

/-- The native raw map is recovered in all of its computational fields. -/
theorem assemble_read {coefficient : k →+* l}
    (R : RawAmbientRestrictionSystemExactMapAgainst S T inverse coefficient source target) :
    assemble coefficient (read R) (read_isLawful R) = R := by
  apply RawAmbientRestrictionSystemExactMapAgainst.ext
  · funext W
    exact Coordinate.assemble_read (R.coordinate W)
  · apply Function.hfunext rfl
    intro W V h
    cases h
    exact relation_heq (Coordinate.assemble_read (R.coordinate W))
      (EquivGraphCode.assemble_read (R.relation W).relationEquiv)

/-- Data equality is determined by the independent coordinate and relation graph families. -/
theorem Data.ext {d e : Data inverse source target}
    (hc : d.coordinate = e.coordinate) (hr : d.relation = e.relation) : d = e := by
  cases d
  cases e
  cases hc
  cases hr
  rfl

/-- Every primitive coordinate, local-data, and relation graph survives assembly. -/
theorem read_assemble (coefficient : k →+* l) (d : Data inverse source target)
    (hl : IsLawful coefficient d) : read (assemble coefficient d hl) = d := by
  apply Data.ext
  · funext W
    exact Coordinate.read_assemble (d.coordinate W)
  · funext W
    exact EquivGraphCode.read_assemble (d.relation W)

/-- Native explicit raw maps correspond to exactly the graph data satisfying the point equations. -/
def readingEquiv (coefficient : k →+* l) :
    RawAmbientRestrictionSystemExactMapAgainst S T inverse coefficient source target ≃
      {d : Data inverse source target // IsLawful coefficient d} where
  toFun R := ⟨read R, read_isLawful R⟩
  invFun d := assemble coefficient d.val d.property
  left_inv := assemble_read
  right_inv d := Subtype.ext (read_assemble coefficient d.val d.property)

/-- Primitive coordinate and relation graphs separate the entire explicit raw map. -/
theorem read_injective {coefficient : k →+* l} :
    Function.Injective (read (inverse := inverse) (source := source) (target := target)
      (coefficient := coefficient)) := by
  intro R R' h
  exact (readingEquiv coefficient).injective (Subtype.ext h)

/-- One failed relation-generator equation rejects the complete raw-map candidate. -/
theorem not_lawful_of_polynomial_mismatch (coefficient : k →+* l)
    (d : Data inverse source target) (W : T.category)
    (r : (source.relationFamily (inverse.obj W)).Relation)
    (h : MvPolynomial.rename (coordinateMap d W)
        (MvPolynomial.map coefficient ((source.relationFamily (inverse.obj W)).polynomial r)) ≠
      (target.relationFamily W).polynomial ((d.relation W).assemble r)) :
    ¬ IsLawful coefficient d := fun hd => h (hd.polynomial W r)

/-- One failed variable-image square rejects the complete raw-map candidate. -/
theorem not_lawful_of_image_mismatch (coefficient : k →+* l)
    (d : Data inverse source target) {W V : T.category} (g : W ⟶ V)
    (c : (source.coordFamily (inverse.obj V)).Coord)
    (h : MvPolynomial.rename (coordinateMap d W)
        (MvPolynomial.map coefficient
          ((source.restrictionStable (inverse.map g)).restriction.variableImage c)) ≠
      (target.restrictionStable g).restriction.variableImage (coordinateMap d V c)) :
    ¬ IsLawful coefficient d := fun hd => h (hd.image g c)

/-- A lawful one-coordinate raw system whose sole structural relation is the constant one. -/
def oneRelationRaw (S : Site.AATSite A) : RawAmbientRestrictionSystem S ℤ where
  coordFamily _ := ⟨PUnit.{u + 1}, fun _ => .state, fun _ => PUnit.{u + 1}⟩
  relationFamily _ := ⟨PUnit.{u + 1}, fun _ => 1⟩
  restrictionStable _ := {
    restriction := ⟨MvPolynomial.X⟩
    maps_JStruct := by
      intro p hp
      simpa [TypedCoordinateRestriction.polynomialMap] using hp }
  identity_polynomialMap _ := by
    ext <;> simp [TypedCoordinateRestriction.polynomialMap]
  composition_polynomialMap _ _ := by
    ext <;> simp [TypedCoordinateRestriction.polynomialMap]

/-- Identity coordinate and relation graphs between systems differing only in their relation polynomial. -/
def changedPolynomialData (S : Site.AATSite A) :
    Data (𝟭 S.category) (IndependentRawLocal.unitRaw S ℤ) (oneRelationRaw S) where
  coordinate W := Coordinate.read
    (CoordinateFamilyExactEquiv.refl ((IndependentRawLocal.unitRaw S ℤ).coordFamily W))
  relation _ := EquivGraphCode.read (Equiv.refl _)

/-- Changing the single relation X to 1 is rejected at that generator, although both raw objects are lawful. -/
theorem changedPolynomialData_not_lawful (S : Site.AATSite A) (W : S.category) :
    ¬ IsLawful (RingHom.id ℤ) (changedPolynomialData S) := by
  intro h
  have hp := h.polynomial W PUnit.unit
  have hc := congrArg MvPolynomial.constantCoeff hp
  simp [coordinateMap, changedPolynomialData, Coordinate.assemble_read,
    CoordinateFamilyExactEquiv.refl, IndependentRawLocal.unitRaw, oneRelationRaw] at hc

/-- The identity on the original one-coordinate system is a positive control on the same site. -/
theorem unitRaw_identity_lawful (S : Site.AATSite A) :
    IsLawful (RingHom.id ℤ)
      (read (RawAmbientRestrictionSystemExactMapAgainst.refl S ℤ
        (IndependentRawLocal.unitRaw S ℤ))) := read_isLawful _

end

end AAT.AG.LocalSemanticReconstruction.IndependentExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentExplicitRaw
