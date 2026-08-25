import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticVanishingPreservation

/-!
# Diagnostic covariance under composed fiber functors

The endpoint group action and canonical reselection map are functorial under a
two-stage transport.  These are the common `(d2)` and `(d4)` cores of
horizontal and vertical Beck--Chevalley pasting.  Both equalities are generated
from the functorial action on endpoint automorphisms.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- The common G-110(E) `(d2)` API predecessor for horizontal and vertical
pasting.  The endpoint group homomorphism of a composite core-fiber functor is
the composite of the two generated endpoint group homomorphisms. -/
theorem coreFiberFunctorPackageAutHom_comp
    {U : AtomCarrier.{u}} {X Y Z : ExtractionInstance U}
    (F : CategoryTheory.Functor (CoreFiber X) (CoreFiber Y))
    (H : CategoryTheory.Functor (CoreFiber Y) (CoreFiber Z))
    (P : CoreFiber X) :
    coreFiberFunctorPackageAutHom (F ⋙ H) P =
      (coreFiberFunctorPackageAutHom H (F.obj P)).comp
        (coreFiberFunctorPackageAutHom F P) := by
  apply MonoidHom.ext
  intro automorphism
  apply (packageFiberAutCoreFiberEquiv ((F ⋙ H).obj P)).injective
  apply Iso.ext
  calc
    _ = (F ⋙ H).map
        (packageFiberAutCoreFiberEquiv P automorphism).hom :=
      coreFiberFunctorPackageAutHom_hom (F ⋙ H) P automorphism
    _ = H.map (F.map
        (packageFiberAutCoreFiberEquiv P automorphism).hom) := rfl
    _ = H.map
        (packageFiberAutCoreFiberEquiv (F.obj P)
          (coreFiberFunctorPackageAutHom F P automorphism)).hom := by
      rw [coreFiberFunctorPackageAutHom_hom]
    _ = _ :=
      (coreFiberFunctorPackageAutHom_hom H (F.obj P)
        (coreFiberFunctorPackageAutHom F P automorphism)).symm

/-- The common G-110(E) `(d4)` API predecessor for horizontal and vertical
pasting.  From a source fiberwise diagnostic datum, two composable core-fiber
functors, and a source reselection, it derives the composite canonical map from
the `(d2)` endpoint group-homomorphism composition law. -/
theorem mapEdgeReselection_comp
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CategoryTheory.Functor (CoreFiber X) (CoreFiber Y))
    (H : CategoryTheory.Functor (CoreFiber Y) (CoreFiber Z))
    (reselection : EdgeReselection data.toLiftData) :
    mapEdgeReselection data (F ⋙ H) reselection =
      mapEdgeReselection (data.map F) H
        (mapEdgeReselection data F reselection) := by
  funext i j edge
  change coreFiberFunctorPackageAutHom (F ⋙ H) (data.package j)
      (reselection i j edge) =
    coreFiberFunctorPackageAutHom H (F.obj (data.package j))
      (coreFiberFunctorPackageAutHom F (data.package j)
        (reselection i j edge))
  rw [coreFiberFunctorPackageAutHom_comp]
  rfl

/-- Extensionality for fiberwise diagnostic data after identifying its
dependent package, edge-isomorphism, and comparator fields. -/
theorem fiberwiseAdmissibleTransportData_ext
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (left right : FiberwiseAdmissibleTransportData G U X)
    (package_eq : left.package = right.package)
    (edgeIso_eq : HEq
      (@FiberwiseAdmissibleTransportData.edgeIso G U X left)
      (@FiberwiseAdmissibleTransportData.edgeIso G U X right))
    (comparator_eq : HEq
      (@FiberwiseAdmissibleTransportData.comparator G U X left)
      (@FiberwiseAdmissibleTransportData.comparator G U X right)) :
    left = right := by
  cases left with
  | mk leftPackage leftEdge leftComparator =>
      cases right with
      | mk rightPackage rightEdge rightComparator =>
          cases package_eq
          cases edgeIso_eq
          cases comparator_eq
          rfl

/-- The G-110(E) `(d3)` composition law: transporting the complete generated
fiberwise datum along a composite functor equals successive transport.  The
comparator field is identified through the `(d2)` endpoint-action theorem. -/
theorem fiberwiseAdmissibleTransportData_map_comp
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CoreFiber X ⥤ CoreFiber Y)
    (H : CoreFiber Y ⥤ CoreFiber Z) :
    data.map (F ⋙ H) = (data.map F).map H := by
  apply fiberwiseAdmissibleTransportData_ext
  · rfl
  · rfl
  · apply heq_of_eq
    funext cell
    simpa [FiberwiseAdmissibleTransportData.map] using congrArg
      (fun hom => hom (data.comparator cell))
      (coreFiberFunctorPackageAutHom_comp F H
        (data.package (G.twoTarget cell)))

/-- The reviewed admissible transport-data constructor itself commutes with
two-stage functorial transport. -/
theorem fiberwiseAdmissibleTransportData_transported_comp
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CoreFiber X ⥤ CoreFiber Y)
    (H : CoreFiber Y ⥤ CoreFiber Z) :
    data.transported (F ⋙ H) = (data.map F).transported H := by
  unfold FiberwiseAdmissibleTransportData.transported
  rw [fiberwiseAdmissibleTransportData_map_comp]

/-- The G-110(E) `(d5)` composition law.  A source coherence proof generates
the first target coherence and then the second; neither target certificate is
accepted as input. -/
theorem coherentAt_map_comp
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CoreFiber X ⥤ CoreFiber Y)
    (H : CoreFiber Y ⥤ CoreFiber Z)
    (reselection : EdgeReselection data.toLiftData)
    (coherent : CoherentAt data.toTransportData reselection) :
    CoherentAt ((data.map F).transported H)
      (mapEdgeReselection (data.map F) H
        (mapEdgeReselection data F reselection)) :=
  coherentAt_map (data.map F) H
    (mapEdgeReselection data F reselection)
    (coherentAt_map data F reselection coherent)

/-- The G-110(E) `(d6)` composition law.  Vanishing is transported through
both generated coherence witnesses in sequence. -/
theorem transportObstructionVanishes_map_comp
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CoreFiber X ⥤ CoreFiber Y)
    (H : CoreFiber Y ⥤ CoreFiber Z)
    (vanishes : TransportObstructionVanishes data.toTransportData) :
    TransportObstructionVanishes ((data.map F).transported H) :=
  transportObstructionVanishes_map (data.map F) H
    (transportObstructionVanishes_map data F vanishes)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
