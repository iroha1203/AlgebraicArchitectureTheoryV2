import ResearchLean.AG.RelativeRepairComposition.SubdivisionHomotopy
import ResearchLean.AG.RelativeRepairComposition.RelativeCohomologyValues

/-!
# Entire original H1 and H2 representatives under actual subdivision

The quotient isomorphisms are induced by the same native collapse chain map.
Their values on every original cycle are proved through the native class API.

## Implementation notes

Cycle membership comes from the actual d1 and d2 comparisons, not from repair
existence or from a supplied cycle certificate. Native short-complex naturality
connects each quotient representative to the same actual degree map.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory Limits TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable (P : ClosedRegion K) (candidates allowed : Set (EdgeName (K := K)))
variable (hp : chosen ∉ P.edges) (hc : chosen ∉ candidates)

/-- The same actual degree-one collapse retains every full supported cocycle. -/
noncomputable def collapseZ1 (z : RelativeComplex.Z1 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) :
    RelativeComplex.Z1 T.toTower.localCoefficients P candidates allowed :=
  ⟨(relative1Equiv T chosen F P candidates allowed hp hc z.1).1,by
    change RelativeComplex.d1Supported T.toTower.localCoefficients P candidates allowed
      (relative1Equiv T chosen F P candidates allowed hp hc z.1).1 = 0
    rw [← relative_d1 T chosen F P candidates allowed hp hc,z.2]⟩

/-- The same actual degree-two map retains the complete original face cocycle. -/
noncomputable def collapseZ2 (z : RelativeComplex.Z2 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp)) : RelativeComplex.Z2 T.toTower.localCoefficients P :=
  ⟨z.1,by
    change RelativeComplex.d2Relative T.toTower.localCoefficients P z.1 = 0
    rw [← relative_d2 T chosen F P hp,z.2]⟩

/-- Every full edge cocycle is mapped by the literal native degree-one collapse. -/
theorem collapseZ1_value (z : RelativeComplex.Z1 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) :
    (collapseZ1 T chosen F P candidates allowed hp hc z).1 =
      (relativeCollapse T chosen F P candidates allowed hp hc).f 1 z.1 := rfl

omit hc candidates allowed in
/-- Every original face value is retained in the mapped full cocycle. -/
theorem collapseZ2_value (z : RelativeComplex.Z2 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp)) :
    (collapseZ2 T chosen F P hp z).1.1 = z.1.1 := rfl

/-- Entire original H1 quotients are isomorphic through the same actual native collapse. -/
noncomputable def relativeH1Iso : AddCommGrpCat.of (RelativeComplex.H1 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) ≅
    AddCommGrpCat.of (RelativeComplex.H1 T.toTower.localCoefficients P candidates allowed) :=
  (RelativeCohomologyValues.firstHomologyIso (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)).symm ≪≫
    relativeHomologyIso T chosen F P candidates allowed hp hc 1 ≪≫
    RelativeCohomologyValues.firstHomologyIso T.toTower.localCoefficients P candidates allowed

/-- Entire original H2 quotients are isomorphic through the same actual native collapse. -/
noncomputable def relativeH2Iso : AddCommGrpCat.of (RelativeComplex.H2 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) ≅
    AddCommGrpCat.of (RelativeComplex.H2 T.toTower.localCoefficients P candidates allowed) :=
  (RelativeCohomologyValues.secondHomologyIso (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)).symm ≪≫
    relativeHomologyIso T chosen F P candidates allowed hp hc 2 ≪≫
    RelativeCohomologyValues.secondHomologyIso T.toTower.localCoefficients P candidates allowed

/-- Every original H1 representative goes to the class of the same full actual collapsed correction. -/
theorem relativeH1Iso_class (z : RelativeComplex.Z1 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) :
    (relativeH1Iso T chosen F P candidates allowed hp hc).hom (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (collapseZ1 T chosen F P candidates allowed hp hc z) := by
  change (RelativeCohomologyValues.firstHomologyIso T.toTower.localCoefficients P candidates allowed).hom
    (HomologicalComplex.homologyMap (relativeCollapse T chosen F P candidates allowed hp hc) 1
      ((RelativeCohomologyValues.firstHomologyIso (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)).inv (QuotientAddGroup.mk z))) = _
  rw [RelativeCohomologyValues.native_h1_inverse_class]
  change (RelativeCohomologyValues.firstHomologyIso T.toTower.localCoefficients P candidates allowed).hom
    (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 1).map
      (relativeCollapse T chosen F P candidates allowed hp hc)) (CohomologyClass.classHom _ _)) = _
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 1).map
        (relativeCollapse T chosen F P candidates allowed hp hc))
      (RelativeCohomologyValues.nativeCycle1 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed) z) =
      RelativeCohomologyValues.nativeCycle1 T.toTower.localCoefficients P candidates allowed
        (collapseZ1 T chosen F P candidates allowed hp hc z) := Subtype.ext rfl
  rw [hz]
  exact RelativeCohomologyValues.native_h1_class T.toTower.localCoefficients P candidates allowed _

/-- Every original H2 representative goes to the class of precisely its full original face cocycle. -/
theorem relativeH2Iso_class (z : RelativeComplex.Z2 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp)) :
    (relativeH2Iso T chosen F P candidates allowed hp hc).hom (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (collapseZ2 T chosen F P hp z) := by
  change (RelativeCohomologyValues.secondHomologyIso T.toTower.localCoefficients P candidates allowed).hom
    (HomologicalComplex.homologyMap (relativeCollapse T chosen F P candidates allowed hp hc) 2
      ((RelativeCohomologyValues.secondHomologyIso (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)).inv (QuotientAddGroup.mk z))) = _
  rw [RelativeCohomologyValues.native_h2_inverse_class]
  change (RelativeCohomologyValues.secondHomologyIso T.toTower.localCoefficients P candidates allowed).hom
    (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 2).map
      (relativeCollapse T chosen F P candidates allowed hp hc)) (CohomologyClass.classHom _ _)) = _
  rw [CohomologyClass.class_naturality]
  have hz : CohomologyClass.cycleMap
      ((HomologicalComplex.shortComplexFunctor Ab (ComplexShape.up ℕ) 2).map
        (relativeCollapse T chosen F P candidates allowed hp hc))
      (RelativeCohomologyValues.nativeCycle2 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed) z) =
      RelativeCohomologyValues.nativeCycle2 T.toTower.localCoefficients P candidates allowed
        (collapseZ2 T chosen F P hp z) := Subtype.ext rfl
  rw [hz]
  exact RelativeCohomologyValues.native_h2_class T.toTower.localCoefficients P candidates allowed _

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
