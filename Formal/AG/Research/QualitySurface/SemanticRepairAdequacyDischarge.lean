import Formal.AG.Research.QualitySurface.SemanticRepairObstructionTower

/-!
Cycle 2 evidence for `G-aat-quality-surface-04`.

Cycle 1 exposed `LayeredRepairAdequacy` as a visible material premise for the
finite semantic repair obstruction tower.  This file discharges that premise
from a lower-level finite certificate prism.  The prism records finite
enumeration, boundary-local coverage, boundary-local faithfulness, and a local
bridge from coverage plus faithfulness to semantic closure.  It deliberately
does not contain global coherence, tower vanishing, `H1` vanishing, target
equivalence, torsor triviality, stack effectiveness, or finite-shadow
completeness.

The result remains a target-support checkpoint.  It improves the material
premise audit for the finite/small tower, but it does not claim the full
universal obstruction tower theorem, true sheaf `H1`, functoriality, richer
nonabelian/higher stacky witnesses, or concrete ArchSig shadow adequacy.
-/

universe u v w x y

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairAdequacyDischarge

open SemanticRepairObstructionTower
open SemanticResidualComponentFaithfulness

/-! ## Finite/local discharge certificates -/

/--
A finite certificate for the semantic boundary-closure part of
`LayeredRepairAdequacy`.

The certificate is intentionally lower-level than the adequacy field
`forall primitive, boundary -> primitiveSemanticallyClosed primitive`.  It asks
for finite enumeration, boundary-local coverage, boundary-local faithfulness,
and a local bridge from coverage plus faithfulness to semantic closure.
-/
structure FiniteBoundarySemanticClosureCertificate
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) where
  coverage : T.C0 -> Prop
  faithfulness : T.C0 -> Prop
  c0_complete : forall primitive, primitive ∈ T.c0Order
  coverage_of_listed_boundary :
    forall primitive,
      primitive ∈ T.c0Order ->
        T.delta0 primitive = T.residual ->
          coverage primitive
  faithfulness_of_listed_boundary :
    forall primitive,
      primitive ∈ T.c0Order ->
        T.delta0 primitive = T.residual ->
          faithfulness primitive
  semantic_closed_of_coverage_and_faithfulness :
    forall primitive,
      coverage primitive ->
        faithfulness primitive ->
          T.primitiveSemanticallyClosed primitive

/--
Boundary semantic closure derived from finite coverage and faithfulness
certificates.
-/
theorem boundarySemanticClosed_of_finiteBoundaryCertificate
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (certificate : FiniteBoundarySemanticClosureCertificate T)
    {primitive : T.C0}
    (hboundary : T.delta0 primitive = T.residual) :
    T.primitiveSemanticallyClosed primitive := by
  exact
    certificate.semantic_closed_of_coverage_and_faithfulness primitive
      (certificate.coverage_of_listed_boundary primitive
        (certificate.c0_complete primitive) hboundary)
      (certificate.faithfulness_of_listed_boundary primitive
        (certificate.c0_complete primitive) hboundary)

/--
The discharge prism for the finite obstruction tower.

The only datum is a finite boundary semantic certificate.  The Boolean
nonabelian / higher / stack layers in the current tower are discharged by their
own definitional identity theorems below, rather than by hidden global fields.
-/
structure LayeredRepairDischargePrism
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) where
  boundary : FiniteBoundarySemanticClosureCertificate T

/-! ## Discharging `LayeredRepairAdequacy` -/

/-- Current finite nonabelian token effectivity is local identity, not a hidden premise. -/
theorem nonabelianTokenEffectivity_of_trivial
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    SemanticRepairObstructionTower.NonabelianTorsorTrivial T ->
      SemanticRepairObstructionTower.NonabelianTorsorTrivial T := by
  intro h
  exact h

/-- Current finite higher token effectivity is local identity, not a hidden premise. -/
theorem higherTokenEffectivity_of_vanishes
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    SemanticRepairObstructionTower.HigherCoherenceVanishes T ->
      SemanticRepairObstructionTower.HigherCoherenceVanishes T := by
  intro h
  exact h

/-- Current finite stack token effectivity is local identity, not a hidden premise. -/
theorem stackTokenEffectivity_of_vanishes
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    SemanticRepairObstructionTower.StackEffectivelyVanishes T ->
      SemanticRepairObstructionTower.StackEffectivelyVanishes T := by
  intro h
  exact h

/-- Build `LayeredRepairAdequacy` from the finite discharge prism. -/
def layeredRepairAdequacy_of_dischargePrism
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (prism : LayeredRepairDischargePrism T) :
    SemanticRepairObstructionTower.LayeredRepairAdequacy T where
  semanticFaithful_of_boundary := by
    intro primitive hboundary
    exact
      boundarySemanticClosed_of_finiteBoundaryCertificate
        prism.boundary hboundary
  torsorEffective_of_trivial := by
    exact nonabelianTokenEffectivity_of_trivial T
  torsorTrivial_of_effective := by
    exact nonabelianTokenEffectivity_of_trivial T
  higherEffective_of_vanishes := by
    exact higherTokenEffectivity_of_vanishes T
  higherVanishes_of_effective := by
    exact higherTokenEffectivity_of_vanishes T
  stackEffective_of_vanishes := by
    exact stackTokenEffectivity_of_vanishes T
  stackVanishes_of_effective := by
    exact stackTokenEffectivity_of_vanishes T

/-- Semantic faithfulness discharge derived from the finite prism. -/
theorem semanticRepair_semanticFaithfulness_of_dischargePrism
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (prism : LayeredRepairDischargePrism T)
    {primitive : T.C0}
    (hboundary : T.delta0 primitive = T.residual) :
    T.primitiveSemanticallyClosed primitive := by
  exact
    SemanticRepairObstructionTower.semanticRepair_semanticFaithfulness_discharge
      (layeredRepairAdequacy_of_dischargePrism prism) hboundary

/-- Transport / coverage discharge derived from the finite prism. -/
theorem semanticRepair_transportCoverage_of_dischargePrism
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (prism : LayeredRepairDischargePrism T)
    {primitive : T.C0}
    (hboundary : T.delta0 primitive = T.residual) :
    T.primitiveSemanticallyClosed primitive := by
  exact
    SemanticRepairObstructionTower.semanticRepair_transportCoverage_discharge
      (layeredRepairAdequacy_of_dischargePrism prism) hboundary

/-- Effective descent from tower vanishing, with adequacy discharged by the prism. -/
theorem globalRepairCoherent_of_obstructionTowerVanishes_of_dischargePrism
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (prism : LayeredRepairDischargePrism T) :
    SemanticRepairObstructionTower.ObstructionTowerVanishes T ->
      SemanticRepairObstructionTower.GlobalSemanticRepairCoherent T := by
  exact
    SemanticRepairObstructionTower.globalRepairCoherent_of_obstructionTowerVanishes
      T (layeredRepairAdequacy_of_dischargePrism prism)

/-- Finite target-boundary equivalence, with adequacy discharged by the prism. -/
theorem universalSemanticRepairObstructionTower_iff_of_dischargePrism
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (prism : LayeredRepairDischargePrism T) :
    SemanticRepairObstructionTower.GlobalSemanticRepairCoherent T <->
      SemanticRepairObstructionTower.ObstructionTowerVanishes T := by
  exact
    SemanticRepairObstructionTower.universalSemanticRepairObstructionTower_iff
      T (layeredRepairAdequacy_of_dischargePrism prism)

/-- The Cycle 1 package theorem, with adequacy discharged by the finite prism. -/
theorem universalSemanticRepairObstructionTower_package_of_dischargePrism
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (prism : LayeredRepairDischargePrism T) :
    (forall primitive,
      SemanticRepairObstructionTower.CechZ1 T (T.delta0 primitive)) /\
      SemanticRepairObstructionTower.CechZ1 T T.residual /\
      (SemanticRepairObstructionTower.GlobalSemanticRepairCoherent T ->
        SemanticRepairObstructionTower.ObstructionTowerVanishes T) /\
      (Not (SemanticRepairObstructionTower.ObstructionTowerVanishes T) ->
        Not (SemanticRepairObstructionTower.GlobalSemanticRepairCoherent T)) /\
      (SemanticRepairObstructionTower.ObstructionTowerVanishes T ->
        SemanticRepairObstructionTower.GlobalSemanticRepairCoherent T) /\
      (SemanticRepairObstructionTower.GlobalSemanticRepairCoherent T <->
        SemanticRepairObstructionTower.ObstructionTowerVanishes T) /\
      (SemanticRepairObstructionTower.H1Vanishes T ->
        SemanticRepairObstructionTower.FiniteShadowTrivial T) := by
  exact
    SemanticRepairObstructionTower.universalSemanticRepairObstructionTower_package
      T (layeredRepairAdequacy_of_dischargePrism prism)

/-! ## G-02 weak finite shadow as a discharged prism instance -/

/--
The G-02 semantic faithfulness hypotheses provide the finite boundary
certificate for the weak shadow tower.
-/
def finiteGluingComplex_boundarySemanticClosureCertificate
    {Atom : Type u}
    (K : SemanticRepairGluingComplex.FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (hfaithful : SemanticRepairGluingComplex.SemanticFaithfulnessHypotheses K) :
    FiniteBoundarySemanticClosureCertificate
      (SemanticRepairObstructionTower.ofFiniteSemanticRepairGluingComplex K) where
  coverage := fun primitive =>
    ResidualComponentCoveredSupport
      K.projection K.cover (K.supportOf primitive)
  faithfulness := fun primitive =>
    ResidualComponentFaithfulSupport
      K.projection K.cover (K.supportOf primitive)
  c0_complete := by
    intro primitive
    exact K.c0_complete primitive
  coverage_of_listed_boundary := by
    intro primitive _hlisted hboundary
    exact hfaithful.component_covered_of_boundary primitive hboundary
  faithfulness_of_listed_boundary := by
    intro primitive _hlisted hboundary
    exact hfaithful.component_faithful_of_boundary primitive hboundary
  semantic_closed_of_coverage_and_faithfulness := by
    intro primitive hcoverage hfaithfulness
    exact
      (semanticRepairClosed_iff_residualComponentCovered_and_faithful).mpr
        ⟨hcoverage, hfaithfulness⟩

/-- The G-02 weak finite shadow has a discharge prism under its faithfulness hypotheses. -/
def finiteGluingComplex_dischargePrism
    {Atom : Type u}
    (K : SemanticRepairGluingComplex.FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (hfaithful : SemanticRepairGluingComplex.SemanticFaithfulnessHypotheses K) :
    LayeredRepairDischargePrism
      (SemanticRepairObstructionTower.ofFiniteSemanticRepairGluingComplex K) where
  boundary :=
    finiteGluingComplex_boundarySemanticClosureCertificate K hfaithful

/-- G-02's weak finite shadow adequacy is obtained through the discharge prism. -/
def finiteGluingComplex_layeredAdequacy_from_dischargePrism
    {Atom : Type u}
    (K : SemanticRepairGluingComplex.FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (hfaithful : SemanticRepairGluingComplex.SemanticFaithfulnessHypotheses K) :
    SemanticRepairObstructionTower.LayeredRepairAdequacy
      (SemanticRepairObstructionTower.ofFiniteSemanticRepairGluingComplex K) :=
  layeredRepairAdequacy_of_dischargePrism
    (finiteGluingComplex_dischargePrism K hfaithful)

/--
The G-02 finite descent theorem is recovered through the discharged prism
rather than through an opaque adequacy argument.
-/
theorem finiteGluingComplex_as_obstructionTower_shadow_of_dischargePrism
    {Atom : Type u}
    (K : SemanticRepairGluingComplex.FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (hfaithful : SemanticRepairGluingComplex.SemanticFaithfulnessHypotheses K) :
    SemanticRepairObstructionTower.GlobalSemanticRepairCoherent
        (SemanticRepairObstructionTower.ofFiniteSemanticRepairGluingComplex K) <->
      SemanticRepairGluingComplex.ObstructionClassVanishes K := by
  calc
    SemanticRepairObstructionTower.GlobalSemanticRepairCoherent
        (SemanticRepairObstructionTower.ofFiniteSemanticRepairGluingComplex K)
        <->
          SemanticRepairObstructionTower.ObstructionTowerVanishes
            (SemanticRepairObstructionTower.ofFiniteSemanticRepairGluingComplex K) :=
      universalSemanticRepairObstructionTower_iff_of_dischargePrism
        (SemanticRepairObstructionTower.ofFiniteSemanticRepairGluingComplex K)
        (finiteGluingComplex_dischargePrism K hfaithful)
    _ <-> SemanticRepairGluingComplex.ObstructionClassVanishes K := by
      constructor
      · intro hvanishes
        exact
          (SemanticRepairObstructionTower.finiteGluingComplex_h1Vanishes_iff K).1
            hvanishes.1
      · intro hvanishes
        exact
          ⟨(SemanticRepairObstructionTower.finiteGluingComplex_h1Vanishes_iff K).2
              hvanishes,
            rfl, rfl, rfl⟩

/-! ## Non-hiddenness witness -/

/--
A small tower where the discharge prism exists but the selected residual is not
a boundary.  This witnesses that the prism does not hide `H1` vanishing.
-/
def selectedNonboundaryDischargeTower :
    SemanticRepairObstructionTower.FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0}
      PUnit where
  Chart := Unit
  chartOrder := [()]
  C0 := Empty
  C1 := Bool
  C2 := Unit
  c0Order := []
  c1Order := [false, true]
  c2Zero := ()
  delta0 := fun primitive => Empty.elim primitive
  delta1 := fun _ => ()
  delta1_delta0_zero := by
    intro primitive
    cases primitive
  residual := true
  residual_cocycle := rfl
  primitiveSemanticallyClosed := fun primitive => Empty.elim primitive
  torsorObstruction := false
  higherObstruction := false
  stackObstruction := false
  finiteShadow := fun _ => false
  finiteShadow_boundary_zero := by
    intro primitive
    cases primitive
  sourceTraceToken := fun _ => false

/-- Boundary certificate for the non-hiddenness witness tower. -/
def selectedNonboundaryBoundaryCertificate :
    FiniteBoundarySemanticClosureCertificate selectedNonboundaryDischargeTower where
  coverage := fun primitive => Empty.elim primitive
  faithfulness := fun primitive => Empty.elim primitive
  c0_complete := by
    intro primitive
    cases primitive
  coverage_of_listed_boundary := by
    intro primitive _hlisted _hboundary
    cases primitive
  faithfulness_of_listed_boundary := by
    intro primitive _hlisted _hboundary
    cases primitive
  semantic_closed_of_coverage_and_faithfulness := by
    intro primitive _hcoverage _hfaithfulness
    cases primitive

/-- Discharge prism for the non-hiddenness witness tower. -/
def selectedNonboundaryDischargePrism :
    LayeredRepairDischargePrism selectedNonboundaryDischargeTower where
  boundary := selectedNonboundaryBoundaryCertificate

/-- The witness tower's selected residual is not a first-layer boundary. -/
theorem selectedNonboundaryDischargePrism_not_h1Vanishes :
    Not (SemanticRepairObstructionTower.H1Vanishes
      selectedNonboundaryDischargeTower) := by
  intro hvanishes
  rcases hvanishes with ⟨primitive, hboundary⟩
  cases primitive

/-- The witness tower's obstruction tower does not vanish. -/
theorem selectedNonboundaryDischargePrism_not_obstructionTowerVanishes :
    Not (SemanticRepairObstructionTower.ObstructionTowerVanishes
      selectedNonboundaryDischargeTower) := by
  intro hvanishes
  exact selectedNonboundaryDischargePrism_not_h1Vanishes hvanishes.1

/-- The witness tower has no global semantic repair coherence. -/
theorem selectedNonboundaryDischargePrism_not_globalCoherent :
    Not (SemanticRepairObstructionTower.GlobalSemanticRepairCoherent
      selectedNonboundaryDischargeTower) := by
  intro hglobal
  rcases hglobal with
    ⟨primitive, hboundary, _hclosed, _htorsor, _hhigher, _hstack⟩
  exact selectedNonboundaryDischargePrism_not_h1Vanishes
    ⟨primitive, hboundary⟩

/-- The discharge prism does not imply first-layer `H1` vanishing. -/
theorem dischargePrism_not_h1Vanishes :
    exists T : SemanticRepairObstructionTower.FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0}
        PUnit,
      exists _prism : LayeredRepairDischargePrism T,
        Not (SemanticRepairObstructionTower.H1Vanishes T) := by
  exact
    ⟨selectedNonboundaryDischargeTower,
      selectedNonboundaryDischargePrism,
      selectedNonboundaryDischargePrism_not_h1Vanishes⟩

/-- The discharge prism does not imply tower vanishing. -/
theorem dischargePrism_not_obstructionTowerVanishes :
    exists T : SemanticRepairObstructionTower.FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0}
        PUnit,
      exists _prism : LayeredRepairDischargePrism T,
        Not (SemanticRepairObstructionTower.ObstructionTowerVanishes T) := by
  exact
    ⟨selectedNonboundaryDischargeTower,
      selectedNonboundaryDischargePrism,
      selectedNonboundaryDischargePrism_not_obstructionTowerVanishes⟩

/-- The discharge prism does not imply global semantic repair coherence. -/
theorem dischargePrism_not_globalCoherent :
    exists T : SemanticRepairObstructionTower.FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0}
        PUnit,
      exists _prism : LayeredRepairDischargePrism T,
        Not (SemanticRepairObstructionTower.GlobalSemanticRepairCoherent T) := by
  exact
    ⟨selectedNonboundaryDischargeTower,
      selectedNonboundaryDischargePrism,
      selectedNonboundaryDischargePrism_not_globalCoherent⟩

end SemanticRepairAdequacyDischarge
end QualitySurface
end Formal.AG.Research
