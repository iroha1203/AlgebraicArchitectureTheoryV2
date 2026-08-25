import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticVanishingPreservation

/-!
# Diagnostic compatibility under a natural isomorphism

This module supplies the natural-isomorphism layer required to compare a
successive component-square diagnostic route with an aligned outer route.
For an arbitrary natural isomorphism of generated core-fiber functors it
derives, rather than accepts, the pointwise package comparison, edge
naturality, comparator conjugacy, mapped-reselection conjugacy, reselected
edge and path naturality, and the paired coherence and vanishing conclusions.

The construction is independent of a particular pasting direction.  The
horizontal and vertical component-to-outer mate equations can therefore use
the same compatibility package after their route alignments have been fixed.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- Complete generated diagnostic compatibility for two naturally isomorphic
core-fiber functors acting on one fixed fiberwise interpretation.  This is an
output proposition: its comparison data and preservation conclusions are all
generated from `comparison` and the source datum. -/
structure FiberwiseDiagnosticNaturalIsoCompatibility
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F H : CoreFiber X ⥤ CoreFiber Y) (comparison : F ≅ H) where
  /-- The comparison at each diagnostic vertex is the given natural
  isomorphism evaluated on the source package. -/
  packageComparison : ∀ vertex,
    (data.map F).package vertex ≅ (data.map H).package vertex
  packageComparison_eq : ∀ vertex,
    packageComparison vertex = comparison.app (data.package vertex)
  /-- Mapped edge isomorphisms commute with the pointwise comparison. -/
  edgeIso_naturality : ∀ {i j} (edge : G.Edge i j),
    (data.map F).edgeIso edge ≪≫ packageComparison j =
      packageComparison i ≪≫ (data.map H).edgeIso edge
  /-- Generated target comparators are conjugate through the pointwise
  endpoint comparison. -/
  comparator_naturality : ∀ cell,
    packageFiberAutMulEquivOfCoreFiberIso
        (packageComparison (G.twoTarget cell))
        ((data.map F).comparator cell) =
      (data.map H).comparator cell
  /-- Every generated mapped reselection is conjugate through the same
  pointwise endpoint comparison. -/
  mappedReselection_naturality : ∀ reselection {i j}
      (edge : G.Edge i j),
    packageFiberAutMulEquivOfCoreFiberIso (packageComparison j)
        (mapEdgeReselection data F reselection i j edge) =
      mapEdgeReselection data H reselection i j edge
  /-- The complete mapped reselected edge commutes with the comparison. -/
  reselectedEdge_naturality : ∀ reselection {i j}
      (edge : G.Edge i j),
    fiberReselectedEdge (data.map F)
          (mapEdgeReselection data F reselection) edge ≫
        (packageComparison j).hom =
      (packageComparison i).hom ≫
        fiberReselectedEdge (data.map H)
          (mapEdgeReselection data H reselection) edge
  /-- The complete mapped reselected path commutes with the comparison. -/
  reselectedPath_naturality : ∀ reselection {i j}
      (path : G.Path i j),
    fiberReselectedPath (data.map F)
          (mapEdgeReselection data F reselection) path ≫
        (packageComparison j).hom =
      (packageComparison i).hom ≫
        fiberReselectedPath (data.map H)
          (mapEdgeReselection data H reselection) path
  /-- One source coherence proof generates both target coherence proofs.
  This is paired forward covariance; it does not by itself assert that the
  two preservation proofs commute through `packageComparison`. -/
  coherentAt_forward_pair : ∀ reselection,
    CoherentAt data.toTransportData reselection →
      CoherentAt (data.transported F)
          (mapEdgeReselection data F reselection) ∧
        CoherentAt (data.transported H)
          (mapEdgeReselection data H reselection)
  /-- Source obstruction vanishing generates vanishing on both target routes.
  This is paired forward covariance, not a cross-route equality. -/
  vanishing_forward_pair : TransportObstructionVanishes data.toTransportData →
    TransportObstructionVanishes (data.transported F) ∧
      TransportObstructionVanishes (data.transported H)

/-- Construct the naturality package and its paired forward conclusions from
naturality and the existing generated covariance theorems.  This does not assert
a cross-route commutation law. -/
noncomputable def fiberwiseDiagnosticNaturalIsoCompatibility
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F H : CoreFiber X ⥤ CoreFiber Y) (comparison : F ≅ H) :
    FiberwiseDiagnosticNaturalIsoCompatibility data F H comparison where
  packageComparison vertex := comparison.app (data.package vertex)
  packageComparison_eq vertex := rfl
  edgeIso_naturality edge := by
    apply Iso.ext
    exact comparison.hom.naturality (data.edgeIso edge).hom
  comparator_naturality cell := by
    exact coreFiberFunctorPackageAutHom_iso_naturality comparison
      (data.package (G.twoTarget cell)) (data.comparator cell)
  mappedReselection_naturality := by
    intro reselection i j edge
    exact coreFiberFunctorPackageAutHom_iso_naturality comparison
      (data.package j) (reselection i j edge)
  reselectedEdge_naturality := by
    intro reselection i j edge
    rw [fiberReselectedEdge_map, fiberReselectedEdge_map]
    exact comparison.hom.naturality
      (fiberReselectedEdge data reselection edge)
  reselectedPath_naturality := by
    intro reselection i j path
    rw [fiberReselectedPath_map, fiberReselectedPath_map]
    exact comparison.hom.naturality
      (fiberReselectedPath data reselection path)
  coherentAt_forward_pair reselection coherent :=
    ⟨coherentAt_map data F reselection coherent,
      coherentAt_map data H reselection coherent⟩
  vanishing_forward_pair vanishes :=
    ⟨transportObstructionVanishes_map data F vanishes,
      transportObstructionVanishes_map data H vanishes⟩

/-! ## Exact Beck--Chevalley specialization -/

/-- The canonical exact Beck--Chevalley mate generates the diagnostic naturality
package for the actual direct and via-base routes. -/
noncomputable def bcDiagnosticNaturalIsoCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      presentation.1.cospan.firstSource.toSemantic) :
    FiberwiseDiagnosticNaturalIsoCompatibility data
      (bcDiagnosticDirectFunctor presentation)
      (bcDiagnosticViaBaseFunctor presentation)
      (by
        letI : IsIso (coreBeckChevalleyMate presentation) :=
          coreBeckChevalleyMate_isIso presentation
        exact asIso (coreBeckChevalleyMate presentation)) := by
  letI : IsIso (coreBeckChevalleyMate presentation) :=
    coreBeckChevalleyMate_isIso presentation
  exact fiberwiseDiagnosticNaturalIsoCompatibility data _ _
    (asIso (coreBeckChevalleyMate presentation))

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
