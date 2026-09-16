import ResearchLean.AG.RealizationReconstruction.CSAATReadingCoreProvenance
import ResearchLean.AG.RealizationReconstruction.CSAATForwardMorphisms
import Formal.Util.AssertStandardAxioms

/-!
# Exact equation and coordinate data from genuine CS isomorphisms

This module begins the exact bridge from the source-generated CS
`ReadingCore`s to `GeometryTotalHom`.  A genuine isomorphism in either
independent CS category constructs equivalences on the complete state,
Law-index, and Law-coordinate families.  The forward maps of those
equivalences are proved to be exactly the maps previously generated from the
named-operation interfaces.

No completed core hom, geometry hom, inverse certificate, selected subset, or
finite presentation is accepted as input.  Construction of the full
`SignedExactCoreReadingHom` and `GeometryTotalHom` remains the next obligation.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Lens isomorphisms -/

/-- A genuine lens isomorphism acts bijectively on every state, with inverse
read directly from the categorical inverse. -/
def lensIsoStateEquiv {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    X.Carrier ≃ Y.Carrier where
  toFun := e.hom.toFun
  invFun := e.inv.toFun
  left_inv state := by
    have h := congrArg (fun f : X ⟶ X => f.toFun state) e.hom_inv_id
    exact h
  right_inv state := by
    have h := congrArg (fun f : Y ⟶ Y => f.toFun state) e.inv_hom_id
    exact h

/-- The complete fully quantified lens-law index family is transported by a
genuine lens isomorphism. -/
def lensIsoLawIndexEquiv {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    LensLawIndex input.View X.Carrier ≃ LensLawIndex input.View Y.Carrier where
  toFun := lensLawIndexMap e.hom.toLawHom
  invFun := lensLawIndexMap e.inv.toLawHom
  left_inv index := by
    cases index with
    | putGet state =>
        exact congrArg LensLawIndex.putGet ((lensIsoStateEquiv e).left_inv state)
    | getPut state view =>
        exact congrArg (fun mapped => LensLawIndex.getPut mapped view)
          ((lensIsoStateEquiv e).left_inv state)
    | putPut state first second =>
        exact congrArg (fun mapped => LensLawIndex.putPut mapped first second)
          ((lensIsoStateEquiv e).left_inv state)
  right_inv index := by
    cases index with
    | putGet state =>
        exact congrArg LensLawIndex.putGet ((lensIsoStateEquiv e).right_inv state)
    | getPut state view =>
        exact congrArg (fun mapped => LensLawIndex.getPut mapped view)
          ((lensIsoStateEquiv e).right_inv state)
    | putPut state first second =>
        exact congrArg (fun mapped => LensLawIndex.putPut mapped first second)
          ((lensIsoStateEquiv e).right_inv state)

/-- The forward half of the exact index equivalence is the arbitrary-morphism
index map already generated from the named get/put squares. -/
@[simp] theorem lensIsoLawIndexEquiv_apply
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (index : LensLawIndex input.View X.Carrier) :
    lensIsoLawIndexEquiv e index =
      (LensAATForwardMorphism.ofSemanticHom e.hom).lawIndexMap index :=
  rfl

/-- Exact lens index transport preserves and reflects the raw Law meaning,
before using endpoint lawfulness. -/
theorem lensIsoLawIndex_holds_iff {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (index : LensLawIndex input.View X.Carrier) :
    index.Holds X.toLensData.toLawStructure ↔
      (lensIsoLawIndexEquiv e index).Holds Y.toLensData.toLawStructure := by
  constructor
  · exact lensLawIndexMap_holds e.hom.toLawHom index
  · intro htarget
    have hsource := lensLawIndexMap_holds e.inv.toLawHom
      (lensIsoLawIndexEquiv e index) htarget
    change (lensLawIndexMap e.inv.toLawHom
      (lensLawIndexMap e.hom.toLawHom index)).Holds
        X.toLensData.toLawStructure at hsource
    have hcancel : lensLawIndexMap e.inv.toLawHom
        (lensLawIndexMap e.hom.toLawHom index) = index :=
      (lensIsoLawIndexEquiv e).left_inv index
    rw [hcancel] at hsource
    exact hsource

/-- Lift the exact Law-index equivalence and retain every AAT Atom coordinate. -/
def lensIsoLawCoordinateIndexEquiv {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    (ULift.{u + 1, u} (LensLawIndex input.View X.Carrier) × LensAATAtom input) ≃
      (ULift.{u + 1, u} (LensLawIndex input.View Y.Carrier) × LensAATAtom input) :=
  Equiv.prodCongr
    (Equiv.ulift.trans ((lensIsoLawIndexEquiv e).trans Equiv.ulift.symm))
    (Equiv.refl _)

/-- A genuine lens isomorphism induces an algebra equivalence of the complete
Law polynomial rings, not merely a one-way ring hom. -/
noncomputable def lensIsoLawCoordinateEquiv {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    LensLawCoordinateRing input X.Carrier ≃ₐ[Int]
      LensLawCoordinateRing input Y.Carrier :=
  MvPolynomial.renameEquiv Int (lensIsoLawCoordinateIndexEquiv e)

/-- Every lens Law/Atom variable is sent to the exact state-index image and
the same Atom. -/
@[simp] theorem lensIsoLawCoordinateEquiv_X {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (index : LensLawIndex input.View X.Carrier) (atom : LensAATAtom input) :
    lensIsoLawCoordinateEquiv e (MvPolynomial.X (ULift.up index, atom)) =
      MvPolynomial.X (ULift.up (lensIsoLawIndexEquiv e index), atom) := by
  simp [lensIsoLawCoordinateEquiv, lensIsoLawCoordinateIndexEquiv]

/-- Forgetting invertibility from the exact coordinate equivalence gives the
same forward polynomial map generated from the named get/put squares. -/
theorem lensIsoLawCoordinateEquiv_toRingHom
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    (lensIsoLawCoordinateEquiv e).toRingEquiv.toRingHom =
      (LensAATForwardMorphism.ofSemanticHom e.hom).lawCoordinateMap := by
  apply MvPolynomial.ringHom_ext <;> intro value
  · simp [lensIsoLawCoordinateEquiv]
  · rcases value with ⟨index, atom⟩
    cases index with
    | up index =>
        change lensIsoLawCoordinateEquiv e
          (MvPolynomial.X (ULift.up index, atom)) = _
        rw [lensIsoLawCoordinateEquiv_X]
        exact (lensLawCoordinateMap_violation input e.hom.toLawHom index atom).symm

/-! ## Protocol isomorphisms -/

/-- A genuine protocol isomorphism acts bijectively on the complete state
carrier at every schema vertex. -/
def protocolIsoStateEquiv {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (vertex : input.schema.Vertex) : X.State vertex ≃ Y.State vertex where
  toFun := protocolStateMap e.hom vertex
  invFun := protocolStateMap e.inv vertex
  left_inv state := by
    have h := congrArg
      (fun f : X ⟶ X => protocolStateMap f vertex state) e.hom_inv_id
    exact h
  right_inv state := by
    have h := congrArg
      (fun f : Y ⟶ Y => protocolStateMap f vertex state) e.inv_hom_id
    exact h

/-- The complete relation/observation index family is transported by a
genuine protocol isomorphism. -/
def protocolIsoLawIndexEquiv {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    ProtocolLawIndex X.State ≃ ProtocolLawIndex Y.State where
  toFun := protocolLawIndexMap e.hom.toLawHom
  invFun := protocolLawIndexMap e.inv.toLawHom
  left_inv index := by
    cases index with
    | relation relation state =>
        exact congrArg (fun mapped => ProtocolLawIndex.relation relation mapped)
          ((protocolIsoStateEquiv e _).left_inv state)
    | observation edge state =>
        exact congrArg (fun mapped => ProtocolLawIndex.observation edge mapped)
          ((protocolIsoStateEquiv e _).left_inv state)
  right_inv index := by
    cases index with
    | relation relation state =>
        exact congrArg (fun mapped => ProtocolLawIndex.relation relation mapped)
          ((protocolIsoStateEquiv e _).right_inv state)
    | observation edge state =>
        exact congrArg (fun mapped => ProtocolLawIndex.observation edge mapped)
          ((protocolIsoStateEquiv e _).right_inv state)

/-- The forward half is exactly the prior arbitrary-morphism index map. -/
@[simp] theorem protocolIsoLawIndexEquiv_apply
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (index : ProtocolLawIndex X.State) :
    protocolIsoLawIndexEquiv e index =
      (ProtocolAATForwardMorphism.ofSemanticHom e.hom).lawIndexMap index :=
  rfl

/-- Exact protocol index transport preserves and reflects every path-relation
and named-edge observation Law instance. -/
theorem protocolIsoLawIndex_holds_iff {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (index : ProtocolLawIndex X.State) :
    index.Holds X.toLawStructure ↔
      (protocolIsoLawIndexEquiv e index).Holds Y.toLawStructure := by
  constructor
  · exact protocolLawIndexMap_holds e.hom.toLawHom index
  · intro htarget
    have hsource := protocolLawIndexMap_holds e.inv.toLawHom
      (protocolIsoLawIndexEquiv e index) htarget
    change (protocolLawIndexMap e.inv.toLawHom
      (protocolLawIndexMap e.hom.toLawHom index)).Holds X.toLawStructure at hsource
    have hcancel : protocolLawIndexMap e.inv.toLawHom
        (protocolLawIndexMap e.hom.toLawHom index) = index :=
      (protocolIsoLawIndexEquiv e).left_inv index
    rw [hcancel] at hsource
    exact hsource

/-- Lift the exact protocol Law-index equivalence and retain every AAT Atom. -/
def protocolIsoLawCoordinateIndexEquiv {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    (ULift.{u + 1, u} (ProtocolLawIndex X.State) × ProtocolAATAtom input) ≃
      (ULift.{u + 1, u} (ProtocolLawIndex Y.State) × ProtocolAATAtom input) :=
  Equiv.prodCongr
    (Equiv.ulift.trans ((protocolIsoLawIndexEquiv e).trans Equiv.ulift.symm))
    (Equiv.refl _)

/-- A genuine protocol isomorphism induces an algebra equivalence of the
complete Law polynomial rings. -/
noncomputable def protocolIsoLawCoordinateEquiv
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    ProtocolLawCoordinateRing input X.State ≃ₐ[Int]
      ProtocolLawCoordinateRing input Y.State :=
  MvPolynomial.renameEquiv Int (protocolIsoLawCoordinateIndexEquiv e)

/-- Every protocol Law/Atom variable is sent to the exact mapped state index
and unchanged Atom. -/
@[simp] theorem protocolIsoLawCoordinateEquiv_X
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (index : ProtocolLawIndex X.State) (atom : ProtocolAATAtom input) :
    protocolIsoLawCoordinateEquiv e (MvPolynomial.X (ULift.up index, atom)) =
      MvPolynomial.X (ULift.up (protocolIsoLawIndexEquiv e index), atom) := by
  simp [protocolIsoLawCoordinateEquiv, protocolIsoLawCoordinateIndexEquiv]

/-- Forgetting invertibility gives the same forward polynomial map generated
from all named edge and observation squares. -/
theorem protocolIsoLawCoordinateEquiv_toRingHom
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    (protocolIsoLawCoordinateEquiv e).toRingEquiv.toRingHom =
      (ProtocolAATForwardMorphism.ofSemanticHom e.hom).lawCoordinateMap := by
  apply MvPolynomial.ringHom_ext <;> intro value
  · simp [protocolIsoLawCoordinateEquiv]
  · rcases value with ⟨index, atom⟩
    cases index with
    | up index =>
        change protocolIsoLawCoordinateEquiv e
          (MvPolynomial.X (ULift.up index, atom)) = _
        rw [protocolIsoLawCoordinateEquiv_X]
        exact (protocolLawCoordinateMap_violation input e.hom.toLawHom index atom).symm

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
