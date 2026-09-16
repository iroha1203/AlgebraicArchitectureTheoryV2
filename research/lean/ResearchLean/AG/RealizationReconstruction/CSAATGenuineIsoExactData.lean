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

/-! ## Raw exact Law transport -/

/-- Mutually inverse raw lens homomorphisms transport the complete Law-index
family, without assuming either endpoint satisfies any lens law. -/
def lensLawIndexEquivOfInverse {View Source Target : Type u}
    {source : LensLawStructure View Source} {target : LensLawStructure View Target}
    (f : LensLawHom source target) (g : LensLawHom target source)
    (left_inv : Function.LeftInverse g.toFun f.toFun)
    (right_inv : Function.RightInverse g.toFun f.toFun) :
    LensLawIndex View Source ≃ LensLawIndex View Target where
  toFun := lensLawIndexMap f
  invFun := lensLawIndexMap g
  left_inv index := by
    cases index with
    | putGet state =>
        exact congrArg LensLawIndex.putGet (left_inv state)
    | getPut state view =>
        exact congrArg (fun mapped => LensLawIndex.getPut mapped view)
          (left_inv state)
    | putPut state first second =>
        exact congrArg (fun mapped => LensLawIndex.putPut mapped first second)
          (left_inv state)
  right_inv index := by
    cases index with
    | putGet state =>
        exact congrArg LensLawIndex.putGet (right_inv state)
    | getPut state view =>
        exact congrArg (fun mapped => LensLawIndex.getPut mapped view)
          (right_inv state)
    | putPut state first second =>
        exact congrArg (fun mapped => LensLawIndex.putPut mapped first second)
          (right_inv state)

/-- Raw lens meaning is preserved and reflected by mutually inverse raw
homomorphisms.  No endpoint lawfulness premise is available here. -/
theorem lensLawIndex_holds_iff_of_inverse {View Source Target : Type u}
    {source : LensLawStructure View Source} {target : LensLawStructure View Target}
    (f : LensLawHom source target) (g : LensLawHom target source)
    (left_inv : Function.LeftInverse g.toFun f.toFun)
    (right_inv : Function.RightInverse g.toFun f.toFun)
    (index : LensLawIndex View Source) :
    index.Holds source ↔
      (lensLawIndexEquivOfInverse f g left_inv right_inv index).Holds target := by
  constructor
  · exact lensLawIndexMap_holds f index
  · intro htarget
    have hsource := lensLawIndexMap_holds g
      (lensLawIndexEquivOfInverse f g left_inv right_inv index) htarget
    change (lensLawIndexMap g (lensLawIndexMap f index)).Holds source at hsource
    have hcancel : lensLawIndexMap g (lensLawIndexMap f index) = index :=
      (lensLawIndexEquivOfInverse f g left_inv right_inv).left_inv index
    rw [hcancel] at hsource
    exact hsource

/-- Mutually inverse raw protocol homomorphisms transport every relation and
observation index, without assuming either endpoint is lawful. -/
def protocolLawIndexEquivOfInverse {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target}
    (f : ProtocolLawHom source target) (g : ProtocolLawHom target source)
    (left_inv : ∀ vertex, Function.LeftInverse (g.stateMap vertex) (f.stateMap vertex))
    (right_inv : ∀ vertex, Function.RightInverse (g.stateMap vertex) (f.stateMap vertex)) :
    ProtocolLawIndex Source ≃ ProtocolLawIndex Target where
  toFun := protocolLawIndexMap f
  invFun := protocolLawIndexMap g
  left_inv index := by
    cases index with
    | relation relation state =>
        exact congrArg (fun mapped => ProtocolLawIndex.relation relation mapped)
          (left_inv _ state)
    | observation edge state =>
        exact congrArg (fun mapped => ProtocolLawIndex.observation edge mapped)
          (left_inv _ state)
  right_inv index := by
    cases index with
    | relation relation state =>
        exact congrArg (fun mapped => ProtocolLawIndex.relation relation mapped)
          (right_inv _ state)
    | observation edge state =>
        exact congrArg (fun mapped => ProtocolLawIndex.observation edge mapped)
          (right_inv _ state)

/-- Raw protocol meaning is preserved and reflected by mutually inverse raw
homomorphisms.  The statement quantifies over arbitrary raw endpoints. -/
theorem protocolLawIndex_holds_iff_of_inverse {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target}
    (f : ProtocolLawHom source target) (g : ProtocolLawHom target source)
    (left_inv : ∀ vertex, Function.LeftInverse (g.stateMap vertex) (f.stateMap vertex))
    (right_inv : ∀ vertex, Function.RightInverse (g.stateMap vertex) (f.stateMap vertex))
    (index : ProtocolLawIndex Source) :
    index.Holds source ↔
      (protocolLawIndexEquivOfInverse f g left_inv right_inv index).Holds target := by
  constructor
  · exact protocolLawIndexMap_holds f index
  · intro htarget
    have hsource := protocolLawIndexMap_holds g
      (protocolLawIndexEquivOfInverse f g left_inv right_inv index) htarget
    change (protocolLawIndexMap g (protocolLawIndexMap f index)).Holds source at hsource
    have hcancel : protocolLawIndexMap g (protocolLawIndexMap f index) = index :=
      (protocolLawIndexEquivOfInverse f g left_inv right_inv).left_inv index
    rw [hcancel] at hsource
    exact hsource

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
    LensLawIndex input.View X.Carrier ≃ LensLawIndex input.View Y.Carrier :=
  lensLawIndexEquivOfInverse e.hom.toLawHom e.inv.toLawHom
    (lensIsoStateEquiv e).left_inv (lensIsoStateEquiv e).right_inv

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
  exact lensLawIndex_holds_iff_of_inverse e.hom.toLawHom e.inv.toLawHom
    (lensIsoStateEquiv e).left_inv (lensIsoStateEquiv e).right_inv index

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
    ProtocolLawIndex X.State ≃ ProtocolLawIndex Y.State :=
  protocolLawIndexEquivOfInverse e.hom.toLawHom e.inv.toLawHom
    (fun vertex => (protocolIsoStateEquiv e vertex).left_inv)
    (fun vertex => (protocolIsoStateEquiv e vertex).right_inv)

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
  exact protocolLawIndex_holds_iff_of_inverse e.hom.toLawHom e.inv.toLawHom
    (fun vertex => (protocolIsoStateEquiv e vertex).left_inv)
    (fun vertex => (protocolIsoStateEquiv e vertex).right_inv) index

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
