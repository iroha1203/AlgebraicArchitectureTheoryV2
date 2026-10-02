import ResearchLean.AG.RelativeRepairComposition.SubdivisionComplexIso
import ResearchLean.AG.RelativeRepairComposition.NativeProductContraction

/-!
# Same actual subdivision collapse preserves every native homology degree

The map is the already constructed supported relative split followed by the
original coordinate projection. Its inverse is zero first correction, with the
fresh vertex label forced by actual first-factor transport.

## Implementation notes

The homotopy equivalence uses the generated full identity contraction, including
all higher degrees. Raw-value APIs fix the map and inverse before interpreting
native cohomology or obstruction representatives.
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

/-- The same actual supported cochain maps give a native homotopy equivalence in every degree. -/
noncomputable def relativeHomotopyEquiv :
    HomotopyEquiv (RelativeComplex.cochainComplex (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed))
      (RelativeComplex.cochainComplex T.toTower.localCoefficients P candidates allowed) :=
  (HomotopyEquiv.ofIso (relativeProductIso T chosen F P candidates allowed hp hc)).trans
    (NativeProductComplex.contractionEquiv _ _ (freshContraction T chosen F))

/-- The native forward chain map is the same actual vertex/correction collapse. -/
noncomputable def relativeCollapse := (relativeHomotopyEquiv T chosen F P candidates allowed hp hc).hom

/-- The native inverse is the same zero-first-correction section of actual subdivision. -/
noncomputable def relativeSection := (relativeHomotopyEquiv T chosen F P candidates allowed hp hc).inv

/-- The forward degree-zero map retains every old vertex label exactly. -/
theorem relativeCollapse_zero (b : RelativeComplex.C0Group (originalTower T chosen F).toTower.localCoefficients
    (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) :
    ((relativeCollapse T chosen F P candidates allowed hp hc).f 0 b).1 =
      collapseVertex T chosen F b.1 := rfl

/-- The forward degree-one map is precisely the full actual two-factor correction collapse. -/
theorem relativeCollapse_one (h : RelativeComplex.C1Group (originalTower T chosen F).toTower.localCoefficients
    (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)) :
    ((relativeCollapse T chosen F P candidates allowed hp hc).f 1 h).1 =
      collapseCorrection T chosen F h.1 := rfl

/-- The forward degree-two map preserves every original face value. -/
theorem relativeCollapse_two (c : RelativeComplex.relativeC2 (originalTower T chosen F).toTower.localCoefficients
    (oldRegion K chosen P hp)) : (relativeCollapse T chosen F P candidates allowed hp hc).f 2 c = c := rfl

/-- The forward degree-three map preserves every original full three-cell value. -/
theorem relativeCollapse_three (c : RelativeComplex.relativeC3 (originalTower T chosen F).toTower.localCoefficients
    (oldRegion K chosen P hp)) : (relativeCollapse T chosen F P candidates allowed hp hc).f 3 c = c := rfl

/-- The inverse restores every old vertex label and the forced fresh transported value. -/
theorem relativeSection_zero (b : RelativeComplex.C0Group T.toTower.localCoefficients P candidates allowed) :
    ((relativeSection T chosen F P candidates allowed hp hc).f 0 b).1 =
      expandVertex T chosen F b.1 (rho1AddEquiv T chosen F (b.1 chosen.1)) := by
  change expandVertex T chosen F b.1 (0 + rho1AddEquiv T chosen F (b.1 chosen.1)) = _
  rw [zero_add]

/-- The inverse restores every old correction with zero complete first-factor correction. -/
theorem relativeSection_one (h : RelativeComplex.C1Group T.toTower.localCoefficients P candidates allowed) :
    ((relativeSection T chosen F P candidates allowed hp hc).f 1 h).1 =
      expandCorrection T chosen F h.1 0 := rfl

/-- The same actual collapse induces an isomorphism of native homology for every natural degree. -/
noncomputable def relativeHomologyIso (n : ℕ) :
    (RelativeComplex.cochainComplex (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)).homology n ≅
    (RelativeComplex.cochainComplex T.toTower.localCoefficients P candidates allowed).homology n :=
  (relativeHomotopyEquiv T chosen F P candidates allowed hp hc).toHomologyIso n

/-- Every degree of the native homology comparison uses precisely the same actual collapse chain map. -/
theorem relativeHomologyIso_hom (n : ℕ) :
    (relativeHomologyIso T chosen F P candidates allowed hp hc n).hom =
      HomologicalComplex.homologyMap (relativeCollapse T chosen F P candidates allowed hp hc) n := rfl

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
