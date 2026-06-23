import Formal.AG.Research.QualitySurface.SemanticRepairAdequacyDischarge

/-!
Cycle 3 evidence for `G-aat-quality-surface-04`.

Cycle 1 built the finite/small semantic repair obstruction tower.  Cycle 2
discharged its visible `LayeredRepairAdequacy` premise from a finite/local
certificate prism.  This file adds the corresponding finite functoriality
surface: an explicit tower morphism transports Cech boundaries, finite shadow
zero readings, and finite layer vanishings.  Reflection is deliberately
separated into a boundary-lift certificate, rather than hidden in the morphism.

The result remains a target-support checkpoint.  It does not claim arbitrary
site morphism functoriality, true sheaf `H1`, cover-refinement completeness,
runtime extraction completeness, ArchMap correctness, or whole-codebase
quality.
-/

universe u v w x y

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairTowerFunctoriality

open SemanticRepairObstructionTower
open SemanticRepairAdequacyDischarge

/-! ## Finite tower morphisms -/

/--
A finite obstruction-tower morphism.

The fields are only cochain-level transport, differential commutation,
selected residual preservation, finite-shadow zero preservation, and forward
finite-token preservation.  The morphism does not contain `H1Vanishes`,
`ObstructionTowerVanishes`, `GlobalSemanticRepairCoherent`, target equivalence,
or finite-shadow reflection as fields.
-/
structure FiniteObstructionTowerMorphism
    {Atom : Type u}
    (T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) where
  mapC0 : T.C0 -> U.C0
  mapC1 : T.C1 -> U.C1
  mapC2 : T.C2 -> U.C2
  map_delta0 :
    forall primitive, mapC1 (T.delta0 primitive) = U.delta0 (mapC0 primitive)
  map_delta1 :
    forall cochain, mapC2 (T.delta1 cochain) = U.delta1 (mapC1 cochain)
  map_c2Zero : mapC2 T.c2Zero = U.c2Zero
  map_residual : mapC1 T.residual = U.residual
  finiteShadow_preserves_false :
    forall cochain, T.finiteShadow cochain = false ->
      U.finiteShadow (mapC1 cochain) = false
  torsor_preserves_false :
    T.torsorObstruction = false -> U.torsorObstruction = false
  higher_preserves_false :
    T.higherObstruction = false -> U.higherObstruction = false
  stack_preserves_false :
    T.stackObstruction = false -> U.stackObstruction = false

/-! ## Forward transport -/

/-- A tower morphism sends finite 1-cocycles to finite 1-cocycles. -/
theorem cechZ1_of_towerMorphism
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (morphism : FiniteObstructionTowerMorphism T U)
    {cochain : T.C1}
    (hcocycle : CechZ1 T cochain) :
    CechZ1 U (morphism.mapC1 cochain) := by
  calc
    U.delta1 (morphism.mapC1 cochain) =
        morphism.mapC2 (T.delta1 cochain) := by
      exact (morphism.map_delta1 cochain).symm
    _ = morphism.mapC2 T.c2Zero := by
      rw [hcocycle]
    _ = U.c2Zero := morphism.map_c2Zero

/-- A tower morphism sends finite first-layer boundaries to boundaries. -/
theorem cechB1_of_towerMorphism
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (morphism : FiniteObstructionTowerMorphism T U)
    {cochain : T.C1}
    (hboundary : CechB1 T cochain) :
    CechB1 U (morphism.mapC1 cochain) := by
  rcases hboundary with ⟨primitive, hprimitive⟩
  refine ⟨morphism.mapC0 primitive, ?_⟩
  calc
    U.delta0 (morphism.mapC0 primitive) =
        morphism.mapC1 (T.delta0 primitive) := by
      exact (morphism.map_delta0 primitive).symm
    _ = morphism.mapC1 cochain := by
      rw [hprimitive]

/-- A tower morphism preserves first-layer obstruction vanishing. -/
theorem h1Vanishes_of_towerMorphism
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (morphism : FiniteObstructionTowerMorphism T U) :
    H1Vanishes T -> H1Vanishes U := by
  intro hvanishes
  rcases hvanishes with ⟨primitive, hboundary⟩
  refine ⟨morphism.mapC0 primitive, ?_⟩
  calc
    U.delta0 (morphism.mapC0 primitive) =
        morphism.mapC1 (T.delta0 primitive) := by
      exact (morphism.map_delta0 primitive).symm
    _ = morphism.mapC1 T.residual := by
      rw [hboundary]
    _ = U.residual := morphism.map_residual

/-- A tower morphism preserves finite-shadow zero readings. -/
theorem finiteShadowTrivial_of_towerMorphism
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (morphism : FiniteObstructionTowerMorphism T U) :
    FiniteShadowTrivial T -> FiniteShadowTrivial U := by
  intro hshadow
  have htarget :
      U.finiteShadow (morphism.mapC1 T.residual) = false :=
    morphism.finiteShadow_preserves_false T.residual hshadow
  simpa [morphism.map_residual] using htarget

/-- A tower morphism preserves full finite tower vanishing layerwise. -/
theorem obstructionTowerVanishes_transport_of_morphism
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (morphism : FiniteObstructionTowerMorphism T U) :
    ObstructionTowerVanishes T -> ObstructionTowerVanishes U := by
  intro hvanishes
  exact
    ⟨h1Vanishes_of_towerMorphism morphism hvanishes.1,
      morphism.torsor_preserves_false hvanishes.2.1,
      morphism.higher_preserves_false hvanishes.2.2.1,
      morphism.stack_preserves_false hvanishes.2.2.2⟩

/-! ## Boundary reflection as a separate certificate -/

/--
A boundary-lift certificate for a tower morphism.

This is a separate certificate because boundary reflection is stronger than
the forward cochain map.  It does not store `H1Vanishes`; it stores primitive
lifts for target boundary witnesses.
-/
structure BoundaryLiftCertificate
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (morphism : FiniteObstructionTowerMorphism T U) where
  lift_boundary :
    forall targetPrimitive,
      U.delta0 targetPrimitive = U.residual ->
        exists sourcePrimitive,
          morphism.mapC0 sourcePrimitive = targetPrimitive /\
            T.delta0 sourcePrimitive = T.residual

/-- Boundary-lift certificates reflect first-layer vanishing. -/
theorem h1Vanishes_reflects_of_boundaryLift
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {morphism : FiniteObstructionTowerMorphism T U}
    (certificate : BoundaryLiftCertificate morphism) :
    H1Vanishes U -> H1Vanishes T := by
  intro hvanishes
  rcases hvanishes with ⟨targetPrimitive, hboundary⟩
  rcases certificate.lift_boundary targetPrimitive hboundary with
    ⟨sourcePrimitive, _hmap, hsourceBoundary⟩
  exact ⟨sourcePrimitive, hsourceBoundary⟩

/-- Boundary-lift certificates transport nonzero first-layer obstructions forward. -/
theorem h1Nonzero_transport_of_boundaryLift
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {morphism : FiniteObstructionTowerMorphism T U}
    (certificate : BoundaryLiftCertificate morphism) :
    H1Nonzero T -> H1Nonzero U := by
  intro hnonzero
  exact
    ⟨semanticRepairObstructionClass_wellDefined U,
      fun htarget =>
        hnonzero.2 (h1Vanishes_reflects_of_boundaryLift certificate htarget)⟩

/-- Boundary-lift certificates preserve no-global consequences of nonzero `H1`. -/
theorem no_globalRepairCoherent_transport_of_boundaryLift
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {morphism : FiniteObstructionTowerMorphism T U}
    (certificate : BoundaryLiftCertificate morphism)
    (adequacy : LayeredRepairAdequacy U) :
    H1Nonzero T -> Not (GlobalSemanticRepairCoherent U) := by
  intro hnonzero
  exact no_globalRepairCoherent_of_nonzero_h1 U adequacy
    (h1Nonzero_transport_of_boundaryLift certificate hnonzero)

/-! ## Transporting discharge prisms -/

/--
Transport data for a finite discharge prism.

The target bridge from coverage and faithfulness to semantic closure is local
target data.  Global coherence, tower vanishing, `H1` vanishing, target
equivalence, and finite-shadow reflection are not fields.
-/
structure DischargePrismTransport
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (morphism : FiniteObstructionTowerMorphism T U)
    (sourcePrism : LayeredRepairDischargePrism T) where
  targetCoverage : U.C0 -> Prop
  targetFaithfulness : U.C0 -> Prop
  target_c0_complete : forall targetPrimitive, targetPrimitive ∈ U.c0Order
  boundary_source_lift :
    forall targetPrimitive,
      U.delta0 targetPrimitive = U.residual ->
        exists sourcePrimitive,
          morphism.mapC0 sourcePrimitive = targetPrimitive /\
            T.delta0 sourcePrimitive = T.residual
  coverage_transport :
    forall sourcePrimitive targetPrimitive,
      morphism.mapC0 sourcePrimitive = targetPrimitive ->
        sourcePrism.boundary.coverage sourcePrimitive ->
          targetCoverage targetPrimitive
  faithfulness_transport :
    forall sourcePrimitive targetPrimitive,
      morphism.mapC0 sourcePrimitive = targetPrimitive ->
        sourcePrism.boundary.faithfulness sourcePrimitive ->
          targetFaithfulness targetPrimitive
  semantic_closed_of_target_coverage_and_faithfulness :
    forall targetPrimitive,
      targetCoverage targetPrimitive ->
        targetFaithfulness targetPrimitive ->
          U.primitiveSemanticallyClosed targetPrimitive

/-- A prism-transport record gives the underlying boundary-lift certificate. -/
def boundaryLiftCertificate_of_dischargePrismTransport
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {morphism : FiniteObstructionTowerMorphism T U}
    {sourcePrism : LayeredRepairDischargePrism T}
    (transport : DischargePrismTransport morphism sourcePrism) :
    BoundaryLiftCertificate morphism where
  lift_boundary := transport.boundary_source_lift

/-- Transport a finite discharge prism along a tower morphism. -/
def dischargePrism_transport
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {morphism : FiniteObstructionTowerMorphism T U}
    {sourcePrism : LayeredRepairDischargePrism T}
    (transport : DischargePrismTransport morphism sourcePrism) :
    LayeredRepairDischargePrism U where
  boundary := {
    coverage := transport.targetCoverage
    faithfulness := transport.targetFaithfulness
    c0_complete := transport.target_c0_complete
    coverage_of_listed_boundary := by
      intro targetPrimitive _hlisted hboundary
      rcases transport.boundary_source_lift targetPrimitive hboundary with
        ⟨sourcePrimitive, hmap, hsourceBoundary⟩
      exact
        transport.coverage_transport sourcePrimitive targetPrimitive hmap
          (sourcePrism.boundary.coverage_of_listed_boundary sourcePrimitive
            (sourcePrism.boundary.c0_complete sourcePrimitive)
            hsourceBoundary)
    faithfulness_of_listed_boundary := by
      intro targetPrimitive _hlisted hboundary
      rcases transport.boundary_source_lift targetPrimitive hboundary with
        ⟨sourcePrimitive, hmap, hsourceBoundary⟩
      exact
        transport.faithfulness_transport sourcePrimitive targetPrimitive hmap
          (sourcePrism.boundary.faithfulness_of_listed_boundary sourcePrimitive
            (sourcePrism.boundary.c0_complete sourcePrimitive)
            hsourceBoundary)
    semantic_closed_of_coverage_and_faithfulness :=
      transport.semantic_closed_of_target_coverage_and_faithfulness
  }

/-- Transported discharge prisms give transported `LayeredRepairAdequacy`. -/
def layeredAdequacy_transport_of_dischargePrism
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {morphism : FiniteObstructionTowerMorphism T U}
    {sourcePrism : LayeredRepairDischargePrism T}
    (transport : DischargePrismTransport morphism sourcePrism) :
    LayeredRepairAdequacy U :=
  layeredRepairAdequacy_of_dischargePrism
    (dischargePrism_transport transport)

/-- Transport global repair coherence through tower vanishing and a transported prism. -/
theorem globalRepairCoherent_transport_of_dischargePrism
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {morphism : FiniteObstructionTowerMorphism T U}
    {sourcePrism : LayeredRepairDischargePrism T}
    (transport : DischargePrismTransport morphism sourcePrism) :
    GlobalSemanticRepairCoherent T -> GlobalSemanticRepairCoherent U := by
  intro hglobal
  have hsourceVanishes : ObstructionTowerVanishes T :=
    globalRepairCoherent_forces_obstructionTowerVanishes T
      (layeredRepairAdequacy_of_dischargePrism sourcePrism)
      hglobal
  have htargetVanishes : ObstructionTowerVanishes U :=
    obstructionTowerVanishes_transport_of_morphism morphism hsourceVanishes
  exact
    globalRepairCoherent_of_obstructionTowerVanishes U
      (layeredAdequacy_transport_of_dischargePrism transport)
      htargetVanishes

/-- The prism-transport package exposes forward and reflected first-layer functoriality. -/
theorem layeredRepairTowerFunctoriality_package
    {Atom : Type u}
    {T U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {morphism : FiniteObstructionTowerMorphism T U}
    {sourcePrism : LayeredRepairDischargePrism T}
    (transport : DischargePrismTransport morphism sourcePrism) :
    (H1Vanishes T -> H1Vanishes U) /\
      (H1Vanishes U -> H1Vanishes T) /\
      (H1Nonzero T -> H1Nonzero U) /\
      (ObstructionTowerVanishes T -> ObstructionTowerVanishes U) /\
      (GlobalSemanticRepairCoherent T -> GlobalSemanticRepairCoherent U) /\
      Nonempty (LayeredRepairDischargePrism U) := by
  exact
    ⟨h1Vanishes_of_towerMorphism morphism,
      h1Vanishes_reflects_of_boundaryLift
        (boundaryLiftCertificate_of_dischargePrismTransport transport),
      h1Nonzero_transport_of_boundaryLift
        (boundaryLiftCertificate_of_dischargePrismTransport transport),
      obstructionTowerVanishes_transport_of_morphism morphism,
      globalRepairCoherent_transport_of_dischargePrism transport,
      ⟨dischargePrism_transport transport⟩⟩

end SemanticRepairTowerFunctoriality
end QualitySurface
end Formal.AG.Research
