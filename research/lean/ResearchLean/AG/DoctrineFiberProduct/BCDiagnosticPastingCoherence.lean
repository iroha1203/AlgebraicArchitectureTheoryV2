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

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
