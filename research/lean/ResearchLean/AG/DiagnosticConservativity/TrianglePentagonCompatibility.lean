import ResearchLean.AG.DiagnosticConservativity.TransportCoherence

/-!
# G-113 revision 2 triangle and pentagon compatibility

The generated G-113 adjunction carries the actual G-111 unitor and
compositor cells to the G-112 semantic-global cells.  This module composes
those mates into the two unit routes and the two three-arrow routes.  It then
identifies each composite with the corresponding native G-112 route before
using the native triangle and pentagon equations.

The route definitions are deliberately separate.  In particular, the unit
laws are not packaged as a conjunction and the pentagon is not obtained by
merely pairing the two predecessor coherence theorems.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## Unit routes -/

/-- The source-unit route formed from the conjugate mates of the actual
G-111 unitor and compositor. -/
noncomputable def semanticGlobalTransportEquivalence_leftUnitMateRoute
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) (targetPackage : CoreFiber target) :
    (exact_bottom_semantic_global_reindex_functor hom).obj targetPackage ⟶
      (exact_bottom_semantic_global_reindex_functor
        (𝟙 source ≫ hom)).obj targetPackage :=
  ((conjugateIsoEquiv
      (Adjunction.id (C := CoreFiber source))
      (semanticGlobalTransportReindexAdjunction (𝟙 source))
      (coreFiberUnitor source)).hom.app
        ((exact_bottom_semantic_global_reindex_functor hom).obj
          targetPackage)) ≫
    ((conjugateIsoEquiv
      ((semanticGlobalTransportReindexAdjunction (𝟙 source)).comp
        (semanticGlobalTransportReindexAdjunction hom))
      (semanticGlobalTransportReindexAdjunction (𝟙 source ≫ hom))
      (coreFiberCompositor (𝟙 source) hom)).hom.app targetPackage)

/-- The target-unit route formed from the conjugate mates of the actual
G-111 unitor and compositor. -/
noncomputable def semanticGlobalTransportEquivalence_rightUnitMateRoute
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) (targetPackage : CoreFiber target) :
    (exact_bottom_semantic_global_reindex_functor hom).obj targetPackage ⟶
      (exact_bottom_semantic_global_reindex_functor
        (hom ≫ 𝟙 target)).obj targetPackage :=
  (exact_bottom_semantic_global_reindex_functor hom).map
      ((conjugateIsoEquiv
        (Adjunction.id (C := CoreFiber target))
        (semanticGlobalTransportReindexAdjunction (𝟙 target))
        (coreFiberUnitor target)).hom.app targetPackage) ≫
    ((conjugateIsoEquiv
      ((semanticGlobalTransportReindexAdjunction hom).comp
        (semanticGlobalTransportReindexAdjunction (𝟙 target)))
      (semanticGlobalTransportReindexAdjunction (hom ≫ 𝟙 target))
      (coreFiberCompositor hom (𝟙 target))).hom.app targetPackage)

/-- The source-unit mate route is the actual G-112 source-unit route. -/
theorem semanticGlobalTransportEquivalence_leftUnitMateRoute_eq_g112
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) (targetPackage : CoreFiber target) :
    semanticGlobalTransportEquivalence_leftUnitMateRoute hom targetPackage =
      exact_bottom_semantic_global_left_unit_route hom targetPackage := by
  unfold semanticGlobalTransportEquivalence_leftUnitMateRoute
  rw [semanticGlobalTransportEquivalence_unitor_conjugate,
    semanticGlobalTransportEquivalence_compositor_conjugate]
  rfl

/-- The target-unit mate route is the actual G-112 target-unit route. -/
theorem semanticGlobalTransportEquivalence_rightUnitMateRoute_eq_g112
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) (targetPackage : CoreFiber target) :
    semanticGlobalTransportEquivalence_rightUnitMateRoute hom targetPackage =
      exact_bottom_semantic_global_right_unit_route hom targetPackage := by
  unfold semanticGlobalTransportEquivalence_rightUnitMateRoute
  rw [semanticGlobalTransportEquivalence_unitor_conjugate,
    semanticGlobalTransportEquivalence_compositor_conjugate]
  rfl

/-- Cross-system source-unit triangle for the actual composite mate route. -/
theorem semanticGlobalTransportEquivalence_leftUnitTriangle
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) (targetPackage : CoreFiber target) :
    semanticGlobalTransportEquivalence_leftUnitMateRoute hom targetPackage =
      exact_bottom_semantic_global_left_unit_cast hom targetPackage := by
  rw [semanticGlobalTransportEquivalence_leftUnitMateRoute_eq_g112]
  exact exact_bottom_semantic_global_left_unit_triangle hom targetPackage

/-- Cross-system target-unit triangle for the actual composite mate route. -/
theorem semanticGlobalTransportEquivalence_rightUnitTriangle
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) (targetPackage : CoreFiber target) :
    semanticGlobalTransportEquivalence_rightUnitMateRoute hom targetPackage =
      exact_bottom_semantic_global_right_unit_cast hom targetPackage := by
  rw [semanticGlobalTransportEquivalence_rightUnitMateRoute_eq_g112]
  exact exact_bottom_semantic_global_right_unit_triangle hom targetPackage

/-! ## Three-arrow routes -/

/-- The left-associated three-arrow route formed from the conjugate mates of
the two actual G-111 compositor cells. -/
noncomputable def semanticGlobalTransportEquivalence_pentagonLeftMateRoute
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject)
    (targetPackage : CoreFiber fourthObject) :
    (exact_bottom_semantic_global_reindex_functor first).obj
      ((exact_bottom_semantic_global_reindex_functor second).obj
        ((exact_bottom_semantic_global_reindex_functor third).obj
          targetPackage)) ⟶
      (exact_bottom_semantic_global_reindex_functor
        ((first ≫ second) ≫ third)).obj targetPackage :=
  ((conjugateIsoEquiv
      ((semanticGlobalTransportReindexAdjunction first).comp
        (semanticGlobalTransportReindexAdjunction second))
      (semanticGlobalTransportReindexAdjunction (first ≫ second))
      (coreFiberCompositor first second)).hom.app
        ((exact_bottom_semantic_global_reindex_functor third).obj
          targetPackage)) ≫
    ((conjugateIsoEquiv
      ((semanticGlobalTransportReindexAdjunction (first ≫ second)).comp
        (semanticGlobalTransportReindexAdjunction third))
      (semanticGlobalTransportReindexAdjunction
        ((first ≫ second) ≫ third))
      (coreFiberCompositor (first ≫ second) third)).hom.app targetPackage)

/-- The right-associated three-arrow route formed from the conjugate mates of
the two actual G-111 compositor cells and the G-112 associativity cast. -/
noncomputable def semanticGlobalTransportEquivalence_pentagonRightMateRoute
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject)
    (targetPackage : CoreFiber fourthObject) :
    (exact_bottom_semantic_global_reindex_functor first).obj
      ((exact_bottom_semantic_global_reindex_functor second).obj
        ((exact_bottom_semantic_global_reindex_functor third).obj
          targetPackage)) ⟶
      (exact_bottom_semantic_global_reindex_functor
        ((first ≫ second) ≫ third)).obj targetPackage :=
  (exact_bottom_semantic_global_reindex_functor first).map
      ((conjugateIsoEquiv
        ((semanticGlobalTransportReindexAdjunction second).comp
          (semanticGlobalTransportReindexAdjunction third))
        (semanticGlobalTransportReindexAdjunction (second ≫ third))
        (coreFiberCompositor second third)).hom.app targetPackage) ≫
    ((conjugateIsoEquiv
      ((semanticGlobalTransportReindexAdjunction first).comp
        (semanticGlobalTransportReindexAdjunction (second ≫ third)))
      (semanticGlobalTransportReindexAdjunction
        (first ≫ (second ≫ third)))
      (coreFiberCompositor first (second ≫ third))).hom.app targetPackage) ≫
    exact_bottom_semantic_global_reindex_eq_cast
      (Category.assoc first second third).symm targetPackage

/-- The left three-arrow mate route is the actual G-112 left pentagon route. -/
theorem semanticGlobalTransportEquivalence_pentagonLeftMateRoute_eq_g112
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject)
    (targetPackage : CoreFiber fourthObject) :
    semanticGlobalTransportEquivalence_pentagonLeftMateRoute
        first second third targetPackage =
      exact_bottom_semantic_global_pentagon_left_route
        first second third targetPackage := by
  unfold semanticGlobalTransportEquivalence_pentagonLeftMateRoute
  rw [semanticGlobalTransportEquivalence_compositor_conjugate,
    semanticGlobalTransportEquivalence_compositor_conjugate]
  rfl

/-- The right three-arrow mate route is the actual G-112 right pentagon route. -/
theorem semanticGlobalTransportEquivalence_pentagonRightMateRoute_eq_g112
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject)
    (targetPackage : CoreFiber fourthObject) :
    semanticGlobalTransportEquivalence_pentagonRightMateRoute
        first second third targetPackage =
      exact_bottom_semantic_global_pentagon_right_route
        first second third targetPackage := by
  unfold semanticGlobalTransportEquivalence_pentagonRightMateRoute
  rw [semanticGlobalTransportEquivalence_compositor_conjugate,
    semanticGlobalTransportEquivalence_compositor_conjugate]
  rfl

/-- Cross-system pentagon for the two actual three-arrow mate routes. -/
theorem semanticGlobalTransportEquivalence_pentagon
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject)
    (targetPackage : CoreFiber fourthObject) :
    semanticGlobalTransportEquivalence_pentagonLeftMateRoute
        first second third targetPackage =
      semanticGlobalTransportEquivalence_pentagonRightMateRoute
        first second third targetPackage := by
  rw [semanticGlobalTransportEquivalence_pentagonLeftMateRoute_eq_g112,
    semanticGlobalTransportEquivalence_pentagonRightMateRoute_eq_g112]
  exact exact_bottom_semantic_global_pentagon
    first second third targetPackage

/-! ## Indexed specializations -/

/-- The source-unit triangle at every vertex of an indexed hom. -/
theorem indexedDiagnosticTransportEquivalence_leftUnitTriangle
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) (targetPackage : CoreFiber (E.vertex vertex)) :
    semanticGlobalTransportEquivalence_leftUnitMateRoute
        (hom.app vertex) targetPackage =
      exact_bottom_semantic_global_left_unit_cast
        (hom.app vertex) targetPackage :=
  semanticGlobalTransportEquivalence_leftUnitTriangle
    (hom.app vertex) targetPackage

/-- The target-unit triangle at every vertex of an indexed hom. -/
theorem indexedDiagnosticTransportEquivalence_rightUnitTriangle
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) (targetPackage : CoreFiber (E.vertex vertex)) :
    semanticGlobalTransportEquivalence_rightUnitMateRoute
        (hom.app vertex) targetPackage =
      exact_bottom_semantic_global_right_unit_cast
        (hom.app vertex) targetPackage :=
  semanticGlobalTransportEquivalence_rightUnitTriangle
    (hom.app vertex) targetPackage

/-- The three-arrow pentagon at every vertex of three composable indexed homs. -/
theorem indexedDiagnosticTransportEquivalence_pentagon
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (vertex : G.Vertex) (targetPackage : CoreFiber (H.vertex vertex)) :
    semanticGlobalTransportEquivalence_pentagonLeftMateRoute
        (first.app vertex) (second.app vertex) (third.app vertex)
        targetPackage =
      semanticGlobalTransportEquivalence_pentagonRightMateRoute
        (first.app vertex) (second.app vertex) (third.app vertex)
        targetPackage :=
  semanticGlobalTransportEquivalence_pentagon
    (first.app vertex) (second.app vertex) (third.app vertex) targetPackage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
