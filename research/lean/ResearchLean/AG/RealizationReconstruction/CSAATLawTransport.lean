import ResearchLean.AG.RealizationReconstruction.CSAATLawSystems
import Formal.Util.AssertStandardAxioms

/-!
# CS morphisms transport the constructed AAT law instances

This module transports the Cycle 126 equation instances along every arbitrary,
possibly noninjective, morphism of the two independent CS categories. The
transport is constructed from the original state maps and their operation or
observation squares. It does not accept an AAT law-preservation certificate.

## Implementation notes

The index map sends each fully quantified equation instance to the instance at
the transported state while retaining every view, relation, named edge, and
Atom. Polynomial coordinates are renamed by that same map. Equation truth is
preserved by the original get/put squares or protocol naturality; no reflection
of arbitrary raw equations is claimed for a noninjective state map.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Lens transport -/

/-- Transport a lens-law instance along an arbitrary semantic lens morphism. -/
def lensLawIndexMap {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    LensLawIndex input.View X.Carrier → LensLawIndex input.View Y.Carrier
  | .putGet state => .putGet (f.toFun state)
  | .getPut state view => .getPut (f.toFun state) view
  | .putPut state first second => .putPut (f.toFun state) first second

/-- Lens law-index transport preserves identity. -/
@[simp] theorem lensLawIndexMap_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference)
    (index : LensLawIndex input.View X.Carrier) :
    lensLawIndexMap (𝟙 X) index = index := by
  cases index <;> rfl

/-- Lens law-index transport preserves composition. -/
@[simp] theorem lensLawIndexMap_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (index : LensLawIndex input.View X.Carrier) :
    lensLawIndexMap (f ≫ g) index =
      lensLawIndexMap g (lensLawIndexMap f index) := by
  cases index <;> rfl

/-- The original get/put preservation equations transport every raw lens-law
instance. -/
theorem lensLawIndexMap_holds {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (index : LensLawIndex input.View X.Carrier)
    (h : index.Holds X.toLensData.toLawStructure) :
    (lensLawIndexMap f index).Holds Y.toLensData.toLawStructure := by
  cases index with
  | putGet state =>
      change Y.put (f.toFun state) (Y.get (f.toFun state)) = f.toFun state
      rw [f.get_naturality, ← f.put_naturality]
      exact congrArg f.toFun h
  | getPut state view =>
      change Y.get (Y.put (f.toFun state) view) = view
      rw [← f.put_naturality, f.get_naturality]
      exact h
  | putPut state first second =>
      change Y.put (Y.put (f.toFun state) first) second =
        Y.put (f.toFun state) second
      rw [← f.put_naturality, ← f.put_naturality, ← f.put_naturality]
      exact congrArg f.toFun h

/-- Rename each lens equation/Atom coordinate by the transported instance. -/
noncomputable def lensLawCoordinateMap {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    LensLawCoordinateRing input X.Carrier →+*
      LensLawCoordinateRing input Y.Carrier :=
  (MvPolynomial.rename fun coordinate :
      ULift.{u + 1, u} (LensLawIndex input.View X.Carrier) × LensAATAtom input =>
    (ULift.up (lensLawIndexMap f coordinate.1.down), coordinate.2)).toRingHom

/-- Lens coordinate renaming preserves the exact equation/Atom variable. -/
@[simp] theorem lensLawCoordinateMap_violation {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (index : LensLawIndex input.View X.Carrier) (atom : LensAATAtom input) :
    lensLawCoordinateMap f (MvPolynomial.X (ULift.up index, atom)) =
      MvPolynomial.X (ULift.up (lensLawIndexMap f index), atom) := by
  simp [lensLawCoordinateMap]

/-- Lens coordinate transport preserves identity. -/
@[simp] theorem lensLawCoordinateMap_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    lensLawCoordinateMap (𝟙 X) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro value
    simp [lensLawCoordinateMap]
  · intro coordinate
    rcases coordinate with ⟨index, atom⟩
    simp [lensLawCoordinateMap]

/-- Lens coordinate transport preserves composition. -/
@[simp] theorem lensLawCoordinateMap_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    lensLawCoordinateMap (f ≫ g) =
      (lensLawCoordinateMap g).comp (lensLawCoordinateMap f) := by
  apply MvPolynomial.ringHom_ext
  · intro value
    simp [lensLawCoordinateMap]
  · intro coordinate
    rcases coordinate with ⟨index, atom⟩
    simp [lensLawCoordinateMap]

/-- The Cycle 126 AAT equation holds after transport along every arbitrary
semantic lens morphism. -/
theorem lensLawEquationHolds_map {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y)
    (index : LensLawIndex input.View X.Carrier)
    (h : (lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure).EquationHolds
      (ULift.up index) (lensLawObject input X.Carrier X.toLensData.toLawStructure)) :
    (lensLawEquationSystem input Y.Carrier Y.toLensData.toLawStructure).EquationHolds
      (ULift.up (lensLawIndexMap f index))
      (lensLawObject input Y.Carrier Y.toLensData.toLawStructure) := by
  apply (lensLawEquationHolds_iff input Y.Carrier _ _ _).mpr
  apply lensLawIndexMap_holds f index
  exact (lensLawEquationHolds_iff input X.Carrier _ _ index).mp h

/-! ## Protocol transport -/

/-- Transport a protocol law instance by an arbitrary semantic morphism. -/
def protocolLawIndexMap {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y) :
    ProtocolLawIndex X.State → ProtocolLawIndex Y.State
  | .relation r state => .relation r (protocolStateMap a _ state)
  | .observation edge state => .observation edge (protocolStateMap a _ state)

/-- Protocol law-index transport preserves identity. -/
@[simp] theorem protocolLawIndexMap_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (index : ProtocolLawIndex X.State) :
    protocolLawIndexMap (𝟙 X) index = index := by
  cases index <;> rfl

/-- Protocol law-index transport preserves composition. -/
@[simp] theorem protocolLawIndexMap_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (a : X ⟶ Y) (b : Y ⟶ Z) (index : ProtocolLawIndex X.State) :
    protocolLawIndexMap (a ≫ b) index =
      protocolLawIndexMap b (protocolLawIndexMap a index) := by
  cases index <;> rfl

/-- Every finite path commutes with the state components of a protocol morphism. -/
theorem protocolEvaluatePath_naturality {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    {source target : input.schema.Vertex} (path : Quiver.Path source target)
    (state : X.State source) :
    protocolStateMap a target
        (input.schema.evaluatePath X.edgeAction path state) =
      input.schema.evaluatePath Y.edgeAction path
        (protocolStateMap a source state) := by
  rw [protocolEvaluatePath_eq_pathAction, protocolEvaluatePath_eq_pathAction]
  exact DFunLike.congr_fun (ProtocolRealization.path_naturality a path) state

/-- Path and observation naturality transport every raw protocol-law instance. -/
theorem protocolLawIndexMap_holds {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    (index : ProtocolLawIndex X.State) (h : index.Holds X.toLawStructure) :
    (protocolLawIndexMap a index).Holds Y.toLawStructure := by
  cases index with
  | relation r state =>
      change input.schema.evaluatePath Y.edgeAction
          (input.schema.relationLeft r) (protocolStateMap a _ state) =
        input.schema.evaluatePath Y.edgeAction
          (input.schema.relationRight r) (protocolStateMap a _ state)
      rw [← protocolEvaluatePath_naturality a _ state,
        ← protocolEvaluatePath_naturality a _ state]
      change input.schema.evaluatePath X.edgeAction
          (input.schema.relationLeft r) state =
        input.schema.evaluatePath X.edgeAction
          (input.schema.relationRight r) state at h
      exact congrArg (protocolStateMap a (input.schema.relationTarget r)) h
  | observation edge state =>
      change input.observation.map (input.schema.edgeMorphism edge)
          (Y.observe _ (protocolStateMap a _ state)) =
        Y.observe _ (Y.edgeAction edge (protocolStateMap a _ state))
      have hObservationSource :
          Y.observe _ (protocolStateMap a _ state) = X.observe _ state := by
        simpa [protocolStateMap, Function.comp_apply] using
          DFunLike.congr_fun (ProtocolRealization.observation_app a _) state
      have hEdge :
          Y.edgeAction edge (protocolStateMap a _ state) =
            protocolStateMap a _ (X.edgeAction edge state) := by
        simpa [protocolStateMap, Function.comp_apply] using
          (DFunLike.congr_fun (ProtocolRealization.edge_naturality a edge) state).symm
      have hObservationTarget :
          Y.observe _ (protocolStateMap a _ (X.edgeAction edge state)) =
            X.observe _ (X.edgeAction edge state) := by
        simpa [protocolStateMap, Function.comp_apply] using
          DFunLike.congr_fun (ProtocolRealization.observation_app a _) (X.edgeAction edge state)
      rw [hObservationSource, hEdge, hObservationTarget]
      exact h

/-- Rename each protocol equation/Atom coordinate by the transported instance. -/
noncomputable def protocolLawCoordinateMap {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y) :
    ProtocolLawCoordinateRing input X.State →+*
      ProtocolLawCoordinateRing input Y.State :=
  (MvPolynomial.rename fun coordinate :
      ULift.{u + 1, u} (ProtocolLawIndex X.State) × ProtocolAATAtom input =>
    (ULift.up (protocolLawIndexMap a coordinate.1.down), coordinate.2)).toRingHom

/-- Protocol coordinate renaming preserves the exact equation/Atom variable. -/
@[simp] theorem protocolLawCoordinateMap_violation {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    (index : ProtocolLawIndex X.State) (atom : ProtocolAATAtom input) :
    protocolLawCoordinateMap a (MvPolynomial.X (ULift.up index, atom)) =
      MvPolynomial.X (ULift.up (protocolLawIndexMap a index), atom) := by
  simp [protocolLawCoordinateMap]

/-- Protocol coordinate transport preserves identity. -/
@[simp] theorem protocolLawCoordinateMap_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    protocolLawCoordinateMap (𝟙 X) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro value
    simp [protocolLawCoordinateMap]
  · intro coordinate
    rcases coordinate with ⟨index, atom⟩
    simp [protocolLawCoordinateMap]

/-- Protocol coordinate transport preserves composition. -/
@[simp] theorem protocolLawCoordinateMap_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    protocolLawCoordinateMap (a ≫ b) =
      (protocolLawCoordinateMap b).comp (protocolLawCoordinateMap a) := by
  apply MvPolynomial.ringHom_ext
  · intro value
    simp [protocolLawCoordinateMap]
  · intro coordinate
    rcases coordinate with ⟨index, atom⟩
    simp [protocolLawCoordinateMap]

/-- The Cycle 126 AAT protocol equation holds after transport along every
arbitrary, possibly noninvertible, semantic protocol morphism. -/
theorem protocolLawEquationHolds_map {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y)
    (index : ProtocolLawIndex X.State)
    (h : (protocolLawEquationSystem input X.State X.toLawStructure).EquationHolds
      (ULift.up index) (protocolLawObject input X.State X.toLawStructure)) :
    (protocolLawEquationSystem input Y.State Y.toLawStructure).EquationHolds
      (ULift.up (protocolLawIndexMap a index))
      (protocolLawObject input Y.State Y.toLawStructure) := by
  apply (protocolLawEquationHolds_iff input Y.State _ _ _).mpr
  apply protocolLawIndexMap_holds a index
  exact (protocolLawEquationHolds_iff input X.State _ _ index).mp h

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
