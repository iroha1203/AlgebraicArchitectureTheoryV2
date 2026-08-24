import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticVanishingPreservation

/-!
# Diagnostic covariance under composed fiber functors

The canonical reselection map is functorial under a two-stage transport.  This
is the common `(d4)` core of horizontal and vertical Beck--Chevalley pasting:
mapping a source reselection along a composite core-fiber functor agrees with
mapping it through the two component functors.  The theorem compares the
actual generated endpoint automorphisms, rather than accepting a compatibility
field from the caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- Mapping an edge reselection through a composite functor agrees pointwise
with the two successive canonical maps. -/
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
  apply (packageFiberAutCoreFiberEquiv ((F ⋙ H).obj (data.package j))).injective
  apply Iso.ext
  change
    (packageFiberAutCoreFiberEquiv ((F ⋙ H).obj (data.package j))
      (coreFiberFunctorPackageAutHom (F ⋙ H) (data.package j)
        (reselection i j edge))).hom =
    (packageFiberAutCoreFiberEquiv (H.obj (F.obj (data.package j)))
      (coreFiberFunctorPackageAutHom H (F.obj (data.package j))
        (coreFiberFunctorPackageAutHom F (data.package j)
          (reselection i j edge)))).hom
  calc
    _ = (F ⋙ H).map
        (packageFiberAutCoreFiberEquiv (data.package j)
          (reselection i j edge)).hom :=
      coreFiberFunctorPackageAutHom_hom (F ⋙ H) (data.package j)
        (reselection i j edge)
    _ = H.map (F.map
        (packageFiberAutCoreFiberEquiv (data.package j)
          (reselection i j edge)).hom) := rfl
    _ = H.map
        (packageFiberAutCoreFiberEquiv (F.obj (data.package j))
          (coreFiberFunctorPackageAutHom F (data.package j)
            (reselection i j edge))).hom := by
      rw [coreFiberFunctorPackageAutHom_hom]
    _ = _ :=
      (coreFiberFunctorPackageAutHom_hom H (F.obj (data.package j))
        (coreFiberFunctorPackageAutHom F (data.package j)
          (reselection i j edge))).symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
