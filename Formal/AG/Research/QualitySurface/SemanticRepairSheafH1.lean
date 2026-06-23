import Formal.AG.Research.QualitySurface.SemanticRepairAdequacyDischarge

/-!
Cycle 5 evidence for `G-aat-quality-surface-04`.

This file raises the first layer of the finite obstruction tower from a bare
`B1` token to an explicit quotient-style sheaf `H1` envelope.  The envelope is
still finite/small: it records a semantic repair site, a residual coefficient
sheaf, Cech `Z1`/`B1` data, and an explicit cohomology-class relation.  The
exactness and semantic-faithfulness discharge are visible certificates; global
coherence, obstruction vanishing, finite-shadow completeness, ArchMap
correctness, runtime extraction completeness, and whole-codebase quality are
not fields.

The result is a target-support checkpoint.  It is not the full universal
obstruction tower theorem: nonabelian `H1`, higher / stacky descent, concrete
ArchSig finite-shadow adequacy, and target-strength universality remain
separate support nodes.
-/

universe u v w x y

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairSheafH1

open SemanticRepairObstructionTower

/-! ## Finite/small site and coefficient-sheaf envelope -/

/--
A finite/small semantic repair site.

This fixes only the input geometry and trace reading.  It does not assert a
global repair certificate or any obstruction vanishing.
-/
structure SemanticRepairSite
    (Atom : Type u) where
  Chart : Type v
  chartOrder : List Chart
  sourceTraceToken : Atom -> Bool

/--
A finite residual coefficient sheaf for semantic repair descent.

The differential law and selected residual cocycle are the first-layer sheaf
condition needed by this finite envelope.  No effective descent conclusion is
stored here.
-/
structure SemanticResidualCoefficientSheaf
    {Atom : Type u}
    (site : SemanticRepairSite.{u, v} Atom) where
  C0 : Type w
  C1 : Type x
  C2 : Type y
  c0Order : List C0
  c1Order : List C1
  zero1 : C1
  zero2 : C2
  delta0 : C0 -> C1
  delta1 : C1 -> C2
  zero1_cocycle : delta1 zero1 = zero2
  delta1_delta0_zero : forall primitive, delta1 (delta0 primitive) = zero2
  residual : C1
  residual_cocycle : delta1 residual = zero2

/--
The quotient-style first-layer `H1` envelope.

`cohomologous` is the explicit class relation.  The two exactness fields say
that boundaries are cohomologous to zero and that zero-class cocycles are
boundaries.  They do not mention global semantic repair coherence.
-/
structure SemanticRepairSheafH1Envelope
    (Atom : Type u) where
  site : SemanticRepairSite.{u, v} Atom
  coefficient : SemanticResidualCoefficientSheaf.{u, v, w, x, y} site
  primitiveSemanticallyClosed : coefficient.C0 -> Prop
  torsorObstruction : Bool
  higherObstruction : Bool
  stackObstruction : Bool
  finiteShadow : coefficient.C1 -> Bool
  finiteShadow_boundary_zero :
    forall primitive, finiteShadow (coefficient.delta0 primitive) = false
  cohomologous : coefficient.C1 -> coefficient.C1 -> Prop
  cohomologous_refl : forall cochain, cohomologous cochain cochain
  cohomologous_symm :
    forall {left right}, cohomologous left right -> cohomologous right left
  cohomologous_trans :
    forall {left middle right},
      cohomologous left middle ->
        cohomologous middle right ->
          cohomologous left right
  boundary_cohomologous_zero :
    forall primitive,
      cohomologous (coefficient.delta0 primitive) coefficient.zero1
  exact_boundary_of_cohomologous_zero :
    forall cochain,
      coefficient.delta1 cochain = coefficient.zero2 ->
        cohomologous cochain coefficient.zero1 ->
          exists primitive, coefficient.delta0 primitive = cochain

/-! ## Cech `H1` surface -/

/-- Cech-style 1-cocycles for the semantic repair coefficient sheaf. -/
def CechZ1
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (cochain : E.coefficient.C1) : Prop :=
  E.coefficient.delta1 cochain = E.coefficient.zero2

/-- Cech-style 1-boundaries for the semantic repair coefficient sheaf. -/
def CechB1
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (cochain : E.coefficient.C1) : Prop :=
  exists primitive, E.coefficient.delta0 primitive = cochain

/-- The explicit `H1` class relation. -/
def H1SameClass
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (left right : E.coefficient.C1) : Prop :=
  E.cohomologous left right

/-- The selected residual has zero first-layer sheaf `H1` class. -/
def SemanticRepairH1Zero
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) : Prop :=
  CechZ1 E E.coefficient.residual /\
    H1SameClass E E.coefficient.residual E.coefficient.zero1

/-- The selected residual has a nonzero first-layer sheaf `H1` class. -/
def SemanticRepairH1Nonzero
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) : Prop :=
  CechZ1 E E.coefficient.residual /\
    Not (H1SameClass E E.coefficient.residual E.coefficient.zero1)

/-- The finite zero cochain is a cocycle. -/
theorem semanticRepairSheafH1_zero_is_cocycle
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) :
    CechZ1 E E.coefficient.zero1 := by
  exact E.coefficient.zero1_cocycle

/-- The selected residual is a sheaf 1-cocycle. -/
theorem semanticRepairSheafH1_wellDefined
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) :
    CechZ1 E E.coefficient.residual := by
  exact E.coefficient.residual_cocycle

/-- Every finite boundary is a sheaf 1-cocycle. -/
theorem semanticRepairSheafH1_boundary_is_cocycle
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (primitive : E.coefficient.C0) :
    CechZ1 E (E.coefficient.delta0 primitive) := by
  exact E.coefficient.delta1_delta0_zero primitive

/-- Every finite boundary is zero in the quotient-style `H1` class relation. -/
theorem semanticRepairSheafH1_boundary_zero_class
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (primitive : E.coefficient.C0) :
    H1SameClass E (E.coefficient.delta0 primitive) E.coefficient.zero1 := by
  exact E.boundary_cohomologous_zero primitive

/--
The zero-class predicate is invariant under the explicit cohomology relation.

This is the quotient-style well-definedness surface; it uses the class relation
directly rather than a hidden global repair predicate.
-/
theorem semanticRepairSheafH1_zeroClass_respects_sameClass
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {left right : E.coefficient.C1}
    (hsame : H1SameClass E left right) :
    H1SameClass E left E.coefficient.zero1 <->
      H1SameClass E right E.coefficient.zero1 := by
  constructor
  · intro hleft
    exact E.cohomologous_trans (E.cohomologous_symm hsame) hleft
  · intro hright
    exact E.cohomologous_trans hsame hright

/-- Exactness: zero `H1` class gives an explicit boundary primitive. -/
theorem h1Boundary_of_sheafH1Zero
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) :
    SemanticRepairH1Zero E -> CechB1 E E.coefficient.residual := by
  intro hzero
  exact
    E.exact_boundary_of_cohomologous_zero
      E.coefficient.residual hzero.1 hzero.2

/-- Boundaries are zero in the quotient-style sheaf `H1` class. -/
theorem sheafH1Zero_of_h1Boundary
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) :
    CechB1 E E.coefficient.residual -> SemanticRepairH1Zero E := by
  intro hboundary
  rcases hboundary with ⟨primitive, hprimitive⟩
  refine ⟨E.coefficient.residual_cocycle, ?_⟩
  have hclass :
      H1SameClass E (E.coefficient.delta0 primitive)
        E.coefficient.zero1 :=
    E.boundary_cohomologous_zero primitive
  simpa [hprimitive] using hclass

/--
The quotient-style `H1` zero class is equivalent to finite boundary membership.

This is an exactness theorem, not a global semantic repair coherence theorem.
-/
theorem sheafH1Zero_iff_h1Boundary
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) :
    SemanticRepairH1Zero E <-> CechB1 E E.coefficient.residual := by
  constructor
  · exact h1Boundary_of_sheafH1Zero E
  · exact sheafH1Zero_of_h1Boundary E

/-! ## Comparison with the finite obstruction tower -/

/-- Forget the sheaf envelope down to the finite obstruction tower. -/
def toFiniteTower
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) :
    FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom where
  Chart := E.site.Chart
  chartOrder := E.site.chartOrder
  C0 := E.coefficient.C0
  C1 := E.coefficient.C1
  C2 := E.coefficient.C2
  c0Order := E.coefficient.c0Order
  c1Order := E.coefficient.c1Order
  c2Zero := E.coefficient.zero2
  delta0 := E.coefficient.delta0
  delta1 := E.coefficient.delta1
  delta1_delta0_zero := E.coefficient.delta1_delta0_zero
  residual := E.coefficient.residual
  residual_cocycle := E.coefficient.residual_cocycle
  primitiveSemanticallyClosed := E.primitiveSemanticallyClosed
  torsorObstruction := E.torsorObstruction
  higherObstruction := E.higherObstruction
  stackObstruction := E.stackObstruction
  finiteShadow := E.finiteShadow
  finiteShadow_boundary_zero := E.finiteShadow_boundary_zero
  sourceTraceToken := E.site.sourceTraceToken

/-- The sheaf zero class is exactly the first-layer boundary predicate in the tower shadow. -/
theorem h1Vanishes_iff_sheafH1Zero_of_exactEnvelope
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) :
    H1Vanishes (toFiniteTower E) <-> SemanticRepairH1Zero E := by
  constructor
  · intro hvanishes
    exact sheafH1Zero_of_h1Boundary E hvanishes
  · intro hzero
    exact h1Boundary_of_sheafH1Zero E hzero

/-- Nonzero sheaf `H1` class is exactly nonzero first-layer tower obstruction. -/
theorem h1Nonzero_iff_sheafH1Nonzero_of_exactEnvelope
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) :
    H1Nonzero (toFiniteTower E) <-> SemanticRepairH1Nonzero E := by
  constructor
  · intro hnonzero
    refine ⟨hnonzero.1, ?_⟩
    intro hzeroClass
    exact hnonzero.2
      (h1Boundary_of_sheafH1Zero E
        ⟨E.coefficient.residual_cocycle, hzeroClass⟩)
  · intro hnonzero
    refine ⟨hnonzero.1, ?_⟩
    intro hboundary
    exact hnonzero.2
      (sheafH1Zero_of_h1Boundary E hboundary).2

/-! ## Visible material premise discharge and effective descent -/

/--
Visible discharge certificate for the first sheaf `H1` layer.

It contains semantic faithfulness for boundary primitives only.  It does not
contain global coherence, `H1` zero, tower vanishing, reflection/completeness,
or the target equivalence.
-/
structure SemanticRepairSheafH1ExactnessDischarge
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) where
  semanticFaithful_of_boundary :
    forall primitive,
      E.coefficient.delta0 primitive = E.coefficient.residual ->
        E.primitiveSemanticallyClosed primitive

/-- The sheaf discharge gives the finite tower's layer-wise adequacy. -/
def layeredAdequacy_of_sheafH1Discharge
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (discharge : SemanticRepairSheafH1ExactnessDischarge E) :
    LayeredRepairAdequacy (toFiniteTower E) where
  semanticFaithful_of_boundary := by
    intro primitive hboundary
    exact discharge.semanticFaithful_of_boundary primitive hboundary
  torsorEffective_of_trivial := by
    intro h
    exact h
  torsorTrivial_of_effective := by
    intro h
    exact h
  higherEffective_of_vanishes := by
    intro h
    exact h
  higherVanishes_of_effective := by
    intro h
    exact h
  stackEffective_of_vanishes := by
    intro h
    exact h
  stackVanishes_of_effective := by
    intro h
    exact h

/-- Nonzero sheaf `H1` obstruction rules out global semantic repair coherence. -/
theorem no_globalRepairCoherent_of_nonzero_sheafH1
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E) :
    SemanticRepairH1Nonzero E ->
      Not (GlobalSemanticRepairCoherent (toFiniteTower E)) := by
  intro hnonzero hglobal
  have hnonzeroTower : H1Nonzero (toFiniteTower E) :=
    (h1Nonzero_iff_sheafH1Nonzero_of_exactEnvelope E).2 hnonzero
  exact
    no_globalRepairCoherent_of_nonzero_h1
      (toFiniteTower E)
      (layeredAdequacy_of_sheafH1Discharge discharge)
      hnonzeroTower hglobal

/--
Zero sheaf `H1` class plus later-layer vanishing gives global semantic repair
coherence through an explicit discharge certificate.
-/
theorem globalRepairCoherent_of_sheafH1_zero
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E)
    (hzero : SemanticRepairH1Zero E)
    (htorsor : NonabelianTorsorTrivial (toFiniteTower E))
    (hhigher : HigherCoherenceVanishes (toFiniteTower E))
    (hstack : StackEffectivelyVanishes (toFiniteTower E)) :
    GlobalSemanticRepairCoherent (toFiniteTower E) := by
  exact
    globalRepairCoherent_of_obstructionTowerVanishes
      (toFiniteTower E)
      (layeredAdequacy_of_sheafH1Discharge discharge)
      ⟨(h1Vanishes_iff_sheafH1Zero_of_exactEnvelope E).2 hzero,
        htorsor, hhigher, hstack⟩

/-- Finite shadow soundness inherited by the sheaf `H1` zero class. -/
theorem finiteTower_h1Shadow_of_sheafH1
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) :
    SemanticRepairH1Zero E ->
      FiniteShadowTrivial (toFiniteTower E) := by
  intro hzero
  exact
    semanticRepairFiniteShadow_sound (toFiniteTower E)
      ((h1Vanishes_iff_sheafH1Zero_of_exactEnvelope E).2 hzero)

/-- The first-layer sheaf `H1` exactness envelope theorem package. -/
theorem semanticRepairSheafH1ExactnessEnvelope_package
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E) :
    CechZ1 E E.coefficient.zero1 /\
      CechZ1 E E.coefficient.residual /\
      (forall primitive, CechZ1 E (E.coefficient.delta0 primitive)) /\
      (forall primitive,
        H1SameClass E (E.coefficient.delta0 primitive)
          E.coefficient.zero1) /\
      (SemanticRepairH1Zero E <-> CechB1 E E.coefficient.residual) /\
      (H1Vanishes (toFiniteTower E) <-> SemanticRepairH1Zero E) /\
      (H1Nonzero (toFiniteTower E) <-> SemanticRepairH1Nonzero E) /\
      (SemanticRepairH1Nonzero E ->
        Not (GlobalSemanticRepairCoherent (toFiniteTower E))) /\
      (SemanticRepairH1Zero E ->
        NonabelianTorsorTrivial (toFiniteTower E) ->
          HigherCoherenceVanishes (toFiniteTower E) ->
            StackEffectivelyVanishes (toFiniteTower E) ->
              GlobalSemanticRepairCoherent (toFiniteTower E)) /\
      (SemanticRepairH1Zero E -> FiniteShadowTrivial (toFiniteTower E)) := by
  exact
    ⟨semanticRepairSheafH1_zero_is_cocycle E,
      semanticRepairSheafH1_wellDefined E,
      semanticRepairSheafH1_boundary_is_cocycle E,
      semanticRepairSheafH1_boundary_zero_class E,
      sheafH1Zero_iff_h1Boundary E,
      h1Vanishes_iff_sheafH1Zero_of_exactEnvelope E,
      h1Nonzero_iff_sheafH1Nonzero_of_exactEnvelope E,
      no_globalRepairCoherent_of_nonzero_sheafH1 E discharge,
      globalRepairCoherent_of_sheafH1_zero E discharge,
      finiteTower_h1Shadow_of_sheafH1 E⟩

end SemanticRepairSheafH1
end QualitySurface
end Formal.AG.Research
