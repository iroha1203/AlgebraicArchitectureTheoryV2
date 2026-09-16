import ResearchLean.AG.RealizationReconstruction.CSAATGeometryRawForward
import ResearchLean.AG.RealizationReconstruction.CSAATCanonicalRawCoordinates
import Formal.Util.AssertStandardAxioms

/-!
# Exact typed raw transport for genuine CS isomorphisms

Cycle 150 showed that equality of endpoint coordinate types is insufficient:
a genuine CS automorphism can act nontrivially on Law coordinates even when a
constant raw presentation acts by the identity.  This module keeps the actual
action.  It defines an exact transport of typed raw systems along a context
functor, recording the coordinate equivalence, labels, local-data types,
structural relations, and the restriction square before quotienting.

For the concrete lens and protocol systems, every coordinate is the actual
Law-index/Atom coordinate of the independently constructed endpoint.  The
transport is built from a genuine semantic isomorphism.  Empty additional
structural relations and identity context restrictions make their coherence
proofs consequences of the constructed coordinate action; no raw transport,
completed geometry morphism, or endpoint type equality is an input.

This is the typed raw layer.  A later cycle must connect it to a geometry
morphism API whose raw component accepts exact transport rather than literal
equality of raw-system structures.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u v

/-! ## Generic exact typed transport -/

/-- Exact preservation of a typed coordinate family, including the namespace
label and the local-data type attached to every coordinate. -/
structure CoordinateFamilyExactEquiv
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    (source : LawAlgebra.CoordinateFamily W)
    (target : LawAlgebra.CoordinateFamily V) where
  coordinateEquiv : source.Coord ≃ target.Coord
  label_eq : ∀ coordinate,
    target.label (coordinateEquiv coordinate) = source.label coordinate
  localDataEquiv : ∀ coordinate,
    source.LocalData coordinate ≃ target.LocalData (coordinateEquiv coordinate)

namespace CoordinateFamilyExactEquiv

/-- The induced equivalence of complete typed polynomial algebras. -/
noncomputable def polynomialEquiv
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {source : LawAlgebra.CoordinateFamily W}
    {target : LawAlgebra.CoordinateFamily V}
    (transport : CoordinateFamilyExactEquiv source target)
    (k : Type v) [CommRing k] :
    LawAlgebra.FreeTypedCommAlg source k ≃ₐ[k]
      LawAlgebra.FreeTypedCommAlg target k :=
  MvPolynomial.renameEquiv k transport.coordinateEquiv

/-- Exact coordinate transport sends every variable to the variable named by
the stored coordinate equivalence. -/
@[simp] theorem polynomialEquiv_X
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {source : LawAlgebra.CoordinateFamily W}
    {target : LawAlgebra.CoordinateFamily V}
    (transport : CoordinateFamilyExactEquiv source target)
    (k : Type v) [CommRing k] (coordinate : source.Coord) :
    transport.polynomialEquiv k (MvPolynomial.X coordinate) =
      MvPolynomial.X (transport.coordinateEquiv coordinate) := by
  simp [polynomialEquiv]

end CoordinateFamilyExactEquiv

/-- Exact preservation of structural relation generators.  The quotient-level
map is deliberately derived later from these typed polynomial equations. -/
structure StructuralRelationFamilyExactEquiv
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {k : Type v} [CommRing k]
    {sourceFamily : LawAlgebra.CoordinateFamily W}
    {targetFamily : LawAlgebra.CoordinateFamily V}
    (coordinate : CoordinateFamilyExactEquiv sourceFamily targetFamily)
    (source : LawAlgebra.StructuralRelationFamily sourceFamily k)
    (target : LawAlgebra.StructuralRelationFamily targetFamily k) where
  relationEquiv : source.Relation ≃ target.Relation
  polynomial_eq : ∀ relation,
    coordinate.polynomialEquiv k (source.polynomial relation) =
      target.polynomial (relationEquiv relation)

/-- Exact typed transport of raw systems along a selected context functor.
The restriction square says that coordinate renaming commutes with every
contravariant typed polynomial restriction. -/
structure RawAmbientRestrictionSystemExactTransportAlong
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    (S : Site.AATSite A) (T : Site.AATSite B)
    (F : CategoryTheory.Functor S.category T.category)
    (k : Type v) [CommRing k]
    (source : LawAlgebra.RawAmbientRestrictionSystem S k)
    (target : LawAlgebra.RawAmbientRestrictionSystem T k) where
  coordinate : ∀ W,
    CoordinateFamilyExactEquiv
      (source.coordFamily W) (target.coordFamily (F.obj W))
  relation : ∀ W,
    StructuralRelationFamilyExactEquiv (coordinate W)
      (source.relationFamily W) (target.relationFamily (F.obj W))
  restriction_polynomial : ∀ {W V : S.category} (map : W ⟶ V)
      (polynomial : LawAlgebra.FreeTypedCommAlg (source.coordFamily V) k),
    (coordinate W).polynomialEquiv k
        ((source.restrictionStable map).restriction.polynomialMap polynomial) =
      (target.restrictionStable (F.map map)).restriction.polynomialMap
        ((coordinate V).polynomialEquiv k polynomial)

/-! ## Empty-relation equation-coordinate transport -/

/-- The complete equation-coordinate raw systems on two sites are transported
exactly along any context functor and any equivalence of their full equation
coordinate types. -/
noncomputable def equationCoordinateRawExactTransportAlong
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    (S : Site.AATSite A) (T : Site.AATSite B)
    (F : CategoryTheory.Functor S.category T.category)
    (coordinateEquiv : S.equationSystem.Coordinate ≃
      T.equationSystem.Coordinate) :
    RawAmbientRestrictionSystemExactTransportAlong S T F Int
      (equationCoordinateRawSystemOn S)
      (equationCoordinateRawSystemOn T) where
  coordinate _ :=
    { coordinateEquiv := coordinateEquiv
      label_eq := fun _ => rfl
      localDataEquiv := fun _ => Equiv.refl PUnit }
  relation _ :=
    { relationEquiv := Equiv.refl PEmpty
      polynomial_eq := fun relation => PEmpty.elim relation }
  restriction_polynomial map polynomial := by
    change (MvPolynomial.renameEquiv Int coordinateEquiv)
        ((equationCoordinateRawRestriction S map).polynomialMap polynomial) =
      (equationCoordinateRawRestriction T (F.map map)).polynomialMap
        ((MvPolynomial.renameEquiv Int coordinateEquiv) polynomial)
    rw [equationCoordinateRawRestriction_polynomialMap S map,
      equationCoordinateRawRestriction_polynomialMap T (F.map map)]
    rfl

/-! ## Genuine lens isomorphisms -/

/-- The actual lens raw systems are related by the complete coordinate action
of a genuine semantic isomorphism. -/
noncomputable def lensIsoRawExactTransport
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    RawAmbientRestrictionSystemExactTransportAlong
      (lensAATGeometryReadingSite input X)
      (lensAATGeometryReadingSite input Y)
      (LensAATForwardMorphism.ofSemanticHom e.hom).lawContextFunctor Int
      (lensAATGeometryReadingRawSystem input X)
      (lensAATGeometryReadingRawSystem input Y) :=
  equationCoordinateRawExactTransportAlong _ _ _
    (lensIsoLawCoordinateIndexEquiv e)

/-- The typed raw action is exactly the genuine lens Law-index action on every
Law-index/Atom variable, including nontrivial hidden-state automorphisms. -/
@[simp] theorem lensIsoRawExactTransport_coordinate_apply
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (W : (lensAATGeometryReadingSite input X).category)
    (index : LensLawIndex input.View X.Carrier) (atom : LensAATAtom input) :
    ((lensIsoRawExactTransport e).coordinate W).coordinateEquiv
        (ULift.up index, atom) =
      (ULift.up (lensIsoLawIndexEquiv e index), atom) :=
  rfl

/-- The complete lens polynomial presheaves are isomorphic by the same actual
coordinate action stored in `lensIsoRawExactTransport`. -/
noncomputable def lensIsoEquationPolynomialIso
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    equationCoordinatePolynomialPresheaf
        (lensAATGeometryReadingSite input X) ≅
      ((LensAATForwardMorphism.ofSemanticHom e.hom).lawContextFunctor).op ⋙
        equationCoordinatePolynomialPresheaf
          (lensAATGeometryReadingSite input Y) where
  hom := lensAATEquationPolynomialForwardHom input
    (LensAATForwardMorphism.ofSemanticHom e.hom)
  inv := {
    app := fun _ => CategoryTheory.Under.homMk
      (CommRingCat.ofHom
        (lensIsoLawCoordinateEquiv e).symm.toRingEquiv.toRingHom) (by
          ext value
          change (lensIsoLawCoordinateEquiv e).symm
              (MvPolynomial.C value.down) = MvPolynomial.C value.down
          simp [lensIsoLawCoordinateEquiv])
    naturality := by
      intro W V contextMap
      apply CategoryTheory.Under.UnderMorphism.ext
      apply CommRingCat.hom_ext
      ext polynomial
      rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext W
    apply CategoryTheory.Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext polynomial
    exact (lensIsoLawCoordinateEquiv e).symm_apply_apply polynomial
  inv_hom_id := by
    apply NatTrans.ext
    funext W
    apply CategoryTheory.Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext polynomial
    exact (lensIsoLawCoordinateEquiv e).apply_symm_apply polynomial

/-- The actual lens raw quotients are isomorphic, and the forward half is the
already constructed all-coordinate raw map. -/
noncomputable def lensIsoActualRawPresheafIso
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    (lensAATGeometryReadingRawSystem input X).toPresheaf ≅
      ((LensAATForwardMorphism.ofSemanticHom e.hom).lawContextFunctor).op ⋙
        (lensAATGeometryReadingRawSystem input Y).toPresheaf :=
  (lensAATGeometryReadingRawPresheafIso input X).trans
    ((lensIsoEquationPolynomialIso e).trans
      (Functor.isoWhiskerLeft
        ((LensAATForwardMorphism.ofSemanticHom e.hom).lawContextFunctor).op
        (lensAATGeometryReadingRawPresheafIso input Y).symm))

/-- The derived raw-presheaf isomorphism uses exactly the existing actual
forward raw map, not the rejected constant-coordinate identity action. -/
theorem lensIsoActualRawPresheafIso_hom
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    (lensIsoActualRawPresheafIso e).hom =
      lensAATGeometryReadingRawForwardHom input
        (LensAATForwardMorphism.ofSemanticHom e.hom) := by
  rfl

/-- On the fixed Cycle 150 Boolean automorphism, the repaired typed raw
transport moves the same complete Law variable that the rejected constant
route fixed. -/
theorem lensIsoRawExactTransport_boolSwap_coordinate_ne
    (W : (lensAATGeometryReadingSite constantRawRouteBoolInput
      constantRawRouteBoolLens).category) :
    CoordinateFamilyExactEquiv.coordinateEquiv
        ((lensIsoRawExactTransport constantRawRouteBoolSwap).coordinate W)
        (ULift.up (LensLawIndex.putGet (PUnit.unit, false)),
          (.point : LensAATAtom constantRawRouteBoolInput)) ≠
      (ULift.up (LensLawIndex.putGet (PUnit.unit, false)),
        (.point : LensAATAtom constantRawRouteBoolInput)) := by
  intro h
  exact constantRawRouteBoolSwap_lawIndex_ne
    (ULift.up.inj (Prod.mk.inj h).1)

/-! ## Genuine protocol isomorphisms -/

/-- The actual protocol raw systems are related by the complete coordinate
action of a genuine semantic isomorphism. -/
noncomputable def protocolIsoRawExactTransport
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    RawAmbientRestrictionSystemExactTransportAlong
      (protocolAATGeometryReadingSite input X)
      (protocolAATGeometryReadingSite input Y)
      (ProtocolAATForwardMorphism.ofSemanticHom e.hom).lawContextFunctor Int
      (protocolAATGeometryReadingRawSystem input X)
      (protocolAATGeometryReadingRawSystem input Y) :=
  equationCoordinateRawExactTransportAlong _ _ _
    (protocolIsoLawCoordinateIndexEquiv e)

/-- The typed raw action is exactly the genuine protocol Law-index action on
every relation/observation-index and Atom variable. -/
@[simp] theorem protocolIsoRawExactTransport_coordinate_apply
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (W : (protocolAATGeometryReadingSite input X).category)
    (index : ProtocolLawIndex X.State) (atom : ProtocolAATAtom input) :
    ((protocolIsoRawExactTransport e).coordinate W).coordinateEquiv
        (ULift.up index, atom) =
      (ULift.up (protocolIsoLawIndexEquiv e index), atom) :=
  rfl

/-- The complete protocol polynomial presheaves are isomorphic by the same
actual relation/observation-coordinate action stored above. -/
noncomputable def protocolIsoEquationPolynomialIso
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    equationCoordinatePolynomialPresheaf
        (protocolAATGeometryReadingSite input X) ≅
      ((ProtocolAATForwardMorphism.ofSemanticHom e.hom).lawContextFunctor).op ⋙
        equationCoordinatePolynomialPresheaf
          (protocolAATGeometryReadingSite input Y) where
  hom := protocolAATEquationPolynomialForwardHom input
    (ProtocolAATForwardMorphism.ofSemanticHom e.hom)
  inv := {
    app := fun _ => CategoryTheory.Under.homMk
      (CommRingCat.ofHom
        (protocolIsoLawCoordinateEquiv e).symm.toRingEquiv.toRingHom) (by
          ext value
          change (protocolIsoLawCoordinateEquiv e).symm
              (MvPolynomial.C value.down) = MvPolynomial.C value.down
          simp [protocolIsoLawCoordinateEquiv])
    naturality := by
      intro W V contextMap
      apply CategoryTheory.Under.UnderMorphism.ext
      apply CommRingCat.hom_ext
      ext polynomial
      rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext W
    apply CategoryTheory.Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext polynomial
    exact (protocolIsoLawCoordinateEquiv e).symm_apply_apply polynomial
  inv_hom_id := by
    apply NatTrans.ext
    funext W
    apply CategoryTheory.Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext polynomial
    exact (protocolIsoLawCoordinateEquiv e).apply_symm_apply polynomial

/-- The actual protocol raw quotients are isomorphic, with forward half equal
to the existing all-coordinate raw map. -/
noncomputable def protocolIsoActualRawPresheafIso
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    (protocolAATGeometryReadingRawSystem input X).toPresheaf ≅
      ((ProtocolAATForwardMorphism.ofSemanticHom e.hom).lawContextFunctor).op ⋙
        (protocolAATGeometryReadingRawSystem input Y).toPresheaf :=
  (protocolAATGeometryReadingRawPresheafIso input X).trans
    ((protocolIsoEquationPolynomialIso e).trans
      (Functor.isoWhiskerLeft
        ((ProtocolAATForwardMorphism.ofSemanticHom e.hom).lawContextFunctor).op
        (protocolAATGeometryReadingRawPresheafIso input Y).symm))

/-- The derived protocol raw-presheaf isomorphism uses exactly the existing
actual forward raw map. -/
theorem protocolIsoActualRawPresheafIso_hom
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    (protocolIsoActualRawPresheafIso e).hom =
      protocolAATGeometryReadingRawForwardHom input
        (ProtocolAATForwardMorphism.ofSemanticHom e.hom) := by
  rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
