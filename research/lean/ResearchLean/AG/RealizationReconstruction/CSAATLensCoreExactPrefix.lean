import ResearchLean.AG.RealizationReconstruction.CSAATReadingCoreRawAgainst
import Formal.Util.AssertStandardAxioms

/-!
# Genuine lens all-object core exactness

This module constructs extraction and composition compatibility, conjugation
of an arbitrary raw lens structure, and the all-`ArchitectureObject` map needed
by a genuine lens `SignedExactCoreReadingHom`.  A Cantor-separated marker keeps
the unrecognized reader branch unrecognized.  The resulting reader reflection
proves exact residual equality for every context, object, Law index, and Atom.

The lawful endpoint conditions are ambient fields of `LensRealization`; these
proofs do not use them.  No lawfulness premise is imposed on the arbitrary raw
`LensLawStructure` transported by the object map.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation

universe u

/-- The generated lens atom family is independent of the realization carrier,
so a genuine change preserves it along the identity Atom equivalence. -/
theorem lensCore_extraction_eq
    {input : LensFamilyInput.{u}}
    (X Y : LensRealization input.View input.reference) :
    (lensAATCorePackage input Y).family =
      (lensAATCorePackage input X).family.transport (Equiv.refl _) := by
  apply AtomFamily.ext
  intro atom
  dsimp only [lensAATCorePackage, AATCorePackage.generate,
    AATCorePackage.family, lensAATCoreReading,
    ExtractionDoctrine.atomize, AtomFamily.transport]
  simp [ExtractionDoctrine.extracts, lensAATExtractionDoctrine,
    lensAATExtracts]

/-- Point-generated composition commutes with identity transport of the full
atom family, for every caller-supplied list-finite family. -/
theorem lensCore_composition_eq
    {input : LensFamilyInput.{u}}
    (X Y : LensRealization input.View input.reference)
    (F : AtomFamily (lensAATCarrier input)) (hF : F.ListFinite) :
    (lensAATCorePackage input Y).reading.composition.compose
        (F.transport (Equiv.refl _)) (hF.transport (Equiv.refl _)) =
      ((lensAATCorePackage input X).reading.composition.compose F hF).transport
        (Equiv.refl _) := by
  change supportedPointConfiguration (F.transport (Equiv.refl _)) .point =
    (supportedPointConfiguration F .point).transport (Equiv.refl _)
  apply AtomConfiguration.ext
  · apply AtomFamily.ext
    intro atom
    simp [AtomFamily.transport]
  · intro source target
    simp [supportedPointConfiguration, AtomConfiguration.transport,
      AtomFamily.transport]
  · intro source target
    simp [supportedPointConfiguration, AtomConfiguration.transport]

/-- Conjugate any raw source lens structure through a genuine semantic
isomorphism.  No lens laws are required of the supplied raw structure. -/
def lensIsoTransportLawStructure
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (data : LensLawStructure input.View X.Carrier) :
    LensLawStructure input.View Y.Carrier where
  get state := data.get (e.inv.toFun state)
  put state view := e.hom.toFun (data.put (e.inv.toFun state) view)

/-- Raw lens structures are determined by their complete get and put maps. -/
theorem lensLawStructure_ext {View Carrier : Type u}
    {a b : LensLawStructure View Carrier}
    (hget : a.get = b.get) (hput : a.put = b.put) : a = b := by
  cases a
  cases b
  cases hget
  cases hput
  rfl

/-- Conjugation sends the actual source get/put structure to the actual target
structure, using both morphism naturality and inverse cancellation. -/
theorem lensIsoTransportLawStructure_actual
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    lensIsoTransportLawStructure e X.toLensData.toLawStructure =
      Y.toLensData.toLawStructure := by
  apply lensLawStructure_ext
  · funext state
    exact e.inv.get_naturality state
  · funext state view
    change e.hom.toFun (X.put (e.inv.toFun state) view) = Y.put state view
    rw [e.hom.put_naturality]
    have h := congrArg (fun f => f.toFun state) e.inv_hom_id
    exact congrArg (fun mapped => Y.put mapped view) h

/-- Cantor separation supplies a structure-map type that cannot be mistaken
for the target lens-structure type. -/
theorem type_not_equiv_set (T : Type (u + 1)) : T ≠ Set T := by
  intro h
  have equiv : T ≃ Set T := Equiv.cast h
  exact Function.cantor_surjective equiv equiv.surjective

theorem set_not_equiv_type (T : Type (u + 1)) : Set T ≠ T := by
  intro h
  exact type_not_equiv_set T h.symm

/-- Map every architecture object.  Recognized source lens structures are
conjugated; unrecognized objects receive a Cantor-separated marker while their
configuration and selected quantities are retained exactly. -/
noncomputable def lensIsoObjectMap
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (object : ArchitectureObject (lensAATCarrier input)) :
    ArchitectureObject (lensAATCarrier input) := by
  classical
  by_cases h : object.StructureMaps =
      ULift.{u + 1, u} (LensLawStructure input.View X.Carrier)
  · exact {
      configuration := object.configuration
      StructureMaps := ULift.{u + 1, u} (LensLawStructure input.View Y.Carrier)
      SelectedQuantities := object.SelectedQuantities
      structureMaps := ULift.up
        (lensIsoTransportLawStructure e (h ▸ object.structureMaps).down)
      selectedQuantities := object.selectedQuantities }
  · exact {
      configuration := object.configuration
      StructureMaps := Set
        (ULift.{u + 1, u} (LensLawStructure input.View Y.Carrier))
      SelectedQuantities := object.SelectedQuantities
      structureMaps := ∅
      selectedQuantities := object.selectedQuantities }

theorem lensIsoObjectMap_configuration_eq
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (object : ArchitectureObject (lensAATCarrier input)) :
    (lensIsoObjectMap e object).configuration = object.configuration := by
  classical
  simp only [lensIsoObjectMap]
  split <;> rfl

theorem lensIsoObjectMap_selectedQuantities_eq
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (object : ArchitectureObject (lensAATCarrier input)) :
    (lensIsoObjectMap e object).SelectedQuantities =
      object.SelectedQuantities := by
  classical
  simp only [lensIsoObjectMap]
  split <;> rfl

/-- The arbitrary-object map sends every object formed by the source reading
to the corresponding object formed by the target reading. -/
theorem lensIsoObjectMap_object_formation_eq
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (configuration : AtomConfiguration (lensAATCarrier input)) :
    lensIsoObjectMap e ((lensCoreObjectReading input X).object configuration) =
      (lensCoreObjectReading input Y).object configuration := by
  classical
  simp only [lensIsoObjectMap]
  split
  · rename_i h
    simp only [lensCoreObjectReading] at h ⊢
    rw [lensIsoTransportLawStructure_actual]
  · rename_i h
    exact (h rfl).elim

/-- Reading the mapped object is exactly mapping the source reader result.
This includes both recognized and unrecognized arbitrary objects. -/
theorem lensIsoObjectMap_reader_eq
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (object : ArchitectureObject (lensAATCarrier input)) :
    lensLawStructure? input Y.Carrier (lensIsoObjectMap e object) =
      (lensLawStructure? input X.Carrier object).map
        (lensIsoTransportLawStructure e) := by
  classical
  by_cases h : object.StructureMaps =
      ULift.{u + 1, u} (LensLawStructure input.View X.Carrier)
  · simp only [lensIsoObjectMap, dif_pos h]
    unfold lensLawStructure?
    split
    · rfl
    · rename_i bad
      exact (bad rfl).elim
  · simp only [lensIsoObjectMap, dif_neg h]
    unfold lensLawStructure?
    split
    · rename_i impossible
      exact (set_not_equiv_type
        (ULift.{u + 1, u} (LensLawStructure input.View Y.Carrier))
        impossible).elim
    · simp

theorem lensIsoObjectMap_reader_some_iff
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (object : ArchitectureObject (lensAATCarrier input))
    (data : LensLawStructure input.View X.Carrier) :
    lensLawStructure? input X.Carrier object = some data ↔
      lensLawStructure? input Y.Carrier (lensIsoObjectMap e object) =
        some (lensIsoTransportLawStructure e data) := by
  rw [lensIsoObjectMap_reader_eq]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    cases hs : lensLawStructure? input X.Carrier object with
    | none => simp [hs] at h
    | some found =>
        simp only [hs, Option.map_some] at h
        have hinjective : Function.Injective (lensIsoTransportLawStructure e) := by
          intro left right equal
          apply lensLawStructure_ext
          · funext state
            have point := congrArg
              (fun data => data.get (e.hom.toFun state)) equal
            change left.get (e.inv.toFun (e.hom.toFun state)) =
              right.get (e.inv.toFun (e.hom.toFun state)) at point
            have hstate : e.inv.toFun (e.hom.toFun state) = state := by
              exact (lensIsoStateEquiv e).left_inv state
            rw [hstate] at point
            exact point
          · funext state view
            have point := congrArg
              (fun data => data.put (e.hom.toFun state) view) equal
            change e.hom.toFun
                (left.put (e.inv.toFun (e.hom.toFun state)) view) =
              e.hom.toFun
                (right.put (e.inv.toFun (e.hom.toFun state)) view) at point
            have hstate : e.inv.toFun (e.hom.toFun state) = state := by
              exact (lensIsoStateEquiv e).left_inv state
            rw [hstate] at point
            have recovered := congrArg e.inv.toFun point
            have hleft : e.inv.toFun (e.hom.toFun (left.put state view)) =
                left.put state view := by
              exact (lensIsoStateEquiv e).left_inv (left.put state view)
            have hright : e.inv.toFun (e.hom.toFun (right.put state view)) =
                right.put state view := by
              exact (lensIsoStateEquiv e).left_inv (right.put state view)
            rw [hleft, hright] at recovered
            exact recovered
        exact congrArg some (hinjective (Option.some.inj h))

theorem lensIsoObjectMap_reader_none_iff
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (object : ArchitectureObject (lensAATCarrier input)) :
    lensLawStructure? input X.Carrier object = none ↔
      lensLawStructure? input Y.Carrier (lensIsoObjectMap e object) = none := by
  rw [lensIsoObjectMap_reader_eq]
  exact Option.map_eq_none_iff.symm

/-- Forward raw hom from an arbitrary source structure to its conjugate. -/
def lensIsoTransportLawHom
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (data : LensLawStructure input.View X.Carrier) :
    LensLawHom data (lensIsoTransportLawStructure e data) where
  toFun := e.hom.toFun
  get_naturality state := by
    change data.get (e.inv.toFun (e.hom.toFun state)) = data.get state
    exact congrArg data.get ((lensIsoStateEquiv e).left_inv state)
  put_naturality state view := by
    change e.hom.toFun (data.put state view) =
      e.hom.toFun (data.put (e.inv.toFun (e.hom.toFun state)) view)
    exact congrArg (fun mapped => e.hom.toFun (data.put mapped view))
      ((lensIsoStateEquiv e).left_inv state).symm

/-- Inverse raw hom back from the conjugated arbitrary structure. -/
def lensIsoTransportLawHomInv
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (data : LensLawStructure input.View X.Carrier) :
    LensLawHom (lensIsoTransportLawStructure e data) data where
  toFun := e.inv.toFun
  get_naturality _ := rfl
  put_naturality state view := by
    change e.inv.toFun
      (e.hom.toFun (data.put (e.inv.toFun state) view)) =
        data.put (e.inv.toFun state) view
    exact (lensIsoStateEquiv e).left_inv
      (data.put (e.inv.toFun state) view)

/-- Conjugation preserves and reflects every Law instance of every arbitrary
raw source lens structure. -/
theorem lensIsoTransportLawStructure_holds_iff
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (data : LensLawStructure input.View X.Carrier)
    (index : LensLawIndex input.View X.Carrier) :
    index.Holds data ↔
      (lensIsoLawIndexEquiv e index).Holds
        (lensIsoTransportLawStructure e data) := by
  change index.Holds data ↔
    (lensLawIndexMap (lensIsoTransportLawHom e data) index).Holds
      (lensIsoTransportLawStructure e data)
  exact lensLawIndex_holds_iff_of_inverse
    (lensIsoTransportLawHom e data) (lensIsoTransportLawHomInv e data)
    (lensIsoStateEquiv e).left_inv (lensIsoStateEquiv e).right_inv index

/-- The source and mapped object readers agree on every Law truth value. -/
theorem lensIsoObjectMap_readHolds_iff
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (object : ArchitectureObject (lensAATCarrier input))
    (index : LensLawIndex input.View X.Carrier) :
    (lensLawStructure? input X.Carrier object).elim False index.Holds ↔
      (lensLawStructure? input Y.Carrier (lensIsoObjectMap e object)).elim False
        (lensIsoLawIndexEquiv e index).Holds := by
  rw [lensIsoObjectMap_reader_eq]
  cases hreader : lensLawStructure? input X.Carrier object with
  | none => simp
  | some data =>
      simpa using lensIsoTransportLawStructure_holds_iff e data index

/-- Exact residual equality for every pair of contexts, architecture object,
Law index, and Atom.  This is stronger than endpoint residual-zero
preservation and is the all-object equation field required by the core bridge. -/
theorem lensIsoObjectMap_equationResidual_eq
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (sourceContext : Site.ArchitectureContext
      (lensLawObject input X.Carrier X.toLensData.toLawStructure))
    (targetContext : Site.ArchitectureContext
      (lensLawObject input Y.Carrier Y.toLensData.toLawStructure))
    (object : ArchitectureObject (lensAATCarrier input))
    (index : LensLawIndex input.View X.Carrier)
    (atom : LensAATAtom input) :
    lensIsoLawCoordinateEquiv e
        ((lensLawEquationSystem input X.Carrier
          X.toLensData.toLawStructure).equationResidual
            ⟨sourceContext⟩ object (ULift.up index) atom) =
      (lensLawEquationSystem input Y.Carrier
        Y.toLensData.toLawStructure).equationResidual
          ⟨targetContext⟩ (lensIsoObjectMap e object)
            (ULift.up (lensIsoLawIndexEquiv e index)) atom := by
  classical
  change lensIsoLawCoordinateEquiv e
      (MvPolynomial.C (if
        (lensLawStructure? input X.Carrier object).elim False index.Holds
        then 0 else 1)) =
    MvPolynomial.C (if
      (lensLawStructure? input Y.Carrier (lensIsoObjectMap e object)).elim False
        (lensIsoLawIndexEquiv e index).Holds then 0 else 1)
  rw [show
    ((lensLawStructure? input X.Carrier object).elim False index.Holds) =
      ((lensLawStructure? input Y.Carrier
        (lensIsoObjectMap e object)).elim False
          (lensIsoLawIndexEquiv e index).Holds) from
      propext (lensIsoObjectMap_readHolds_iff e object index)]
  simp

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
