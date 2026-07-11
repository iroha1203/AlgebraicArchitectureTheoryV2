import ResearchLean.AG.QualitySurface.SemanticRepairAdequacyDischarge

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

namespace ResearchLean.AG
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

/-! ## Additive Cech `Z1 / B1` quotient surface -/

/--
Additive data needed to read the first sheaf layer as a target-strength Cech
`Z1 / B1` quotient.

This is intentionally separate from the existing explicit `cohomologous`
relation in `SemanticRepairSheafH1Envelope`: it does not store a zero-class
predicate, a residual primitive, global coherence, or semantic exactness.
-/
structure SemanticRepairAdditiveCechH1Data
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) where
  [c0AddCommGroup : AddCommGroup E.coefficient.C0]
  [c1AddCommGroup : AddCommGroup E.coefficient.C1]
  zero1_eq_zero :
    E.coefficient.zero1 = 0
  delta0_zero :
    E.coefficient.delta0 0 = 0
  delta0_add :
    forall left right,
      E.coefficient.delta0 (left + right) =
        E.coefficient.delta0 left + E.coefficient.delta0 right
  delta0_neg :
    forall primitive,
      E.coefficient.delta0 (-primitive) =
        -E.coefficient.delta0 primitive

/--
The target-strength additive same-class relation: two cocycles are identified
when their difference is a Cech boundary.
-/
def SemanticRepairAdditiveH1SameClass
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    (left right : E.coefficient.C1) : Prop :=
  letI := additive.c1AddCommGroup
  CechB1 E (left - right)

/-- Cocycles in the additive Cech `Z1 / B1` surface. -/
def SemanticRepairAdditiveH1Cocycle
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (_additive : SemanticRepairAdditiveCechH1Data E) : Type x :=
  {cochain : E.coefficient.C1 // CechZ1 E cochain}

theorem semanticRepairAdditiveH1SameClass_refl
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    (cochain : E.coefficient.C1) :
    SemanticRepairAdditiveH1SameClass additive cochain cochain := by
  letI := additive.c0AddCommGroup
  letI := additive.c1AddCommGroup
  refine ⟨0, ?_⟩
  simpa [SemanticRepairAdditiveH1SameClass] using additive.delta0_zero

theorem semanticRepairAdditiveH1SameClass_symm
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    {left right : E.coefficient.C1} :
    SemanticRepairAdditiveH1SameClass additive left right ->
      SemanticRepairAdditiveH1SameClass additive right left := by
  letI := additive.c0AddCommGroup
  letI := additive.c1AddCommGroup
  intro hsame
  rcases hsame with ⟨primitive, hprimitive⟩
  refine ⟨-primitive, ?_⟩
  calc
    E.coefficient.delta0 (-primitive) =
        -E.coefficient.delta0 primitive := additive.delta0_neg primitive
    _ = right - left := by
      rw [hprimitive]
      abel

theorem semanticRepairAdditiveH1SameClass_trans
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    {left middle right : E.coefficient.C1} :
    SemanticRepairAdditiveH1SameClass additive left middle ->
      SemanticRepairAdditiveH1SameClass additive middle right ->
        SemanticRepairAdditiveH1SameClass additive left right := by
  letI := additive.c0AddCommGroup
  letI := additive.c1AddCommGroup
  intro hleftMiddle hmiddleRight
  rcases hleftMiddle with ⟨leftPrimitive, hleftPrimitive⟩
  rcases hmiddleRight with ⟨rightPrimitive, hrightPrimitive⟩
  refine ⟨leftPrimitive + rightPrimitive, ?_⟩
  calc
    E.coefficient.delta0 (leftPrimitive + rightPrimitive) =
        E.coefficient.delta0 leftPrimitive +
          E.coefficient.delta0 rightPrimitive :=
      additive.delta0_add leftPrimitive rightPrimitive
    _ = left - right := by
      rw [hleftPrimitive, hrightPrimitive]
      abel

/-- Setoid quotient by the additive Cech coboundary relation. -/
def semanticRepairAdditiveH1CocycleSetoid
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E) :
    Setoid (SemanticRepairAdditiveH1Cocycle additive) where
  r left right :=
    SemanticRepairAdditiveH1SameClass additive left.1 right.1
  iseqv := by
    constructor
    · intro cocycle
      exact semanticRepairAdditiveH1SameClass_refl additive cocycle.1
    · intro left right hsame
      exact semanticRepairAdditiveH1SameClass_symm additive hsame
    · intro left middle right hleftMiddle hmiddleRight
      exact
        semanticRepairAdditiveH1SameClass_trans additive
          hleftMiddle hmiddleRight

/-- Target-strength additive first sheaf `H1 = Z1 / B1` class object. -/
abbrev SemanticRepairAdditiveH1Class
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E) : Type x :=
  Quotient (semanticRepairAdditiveH1CocycleSetoid additive)

/-- Build an additive sheaf `H1` class from a visible cocycle. -/
def semanticRepairAdditiveH1Class_mk
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    (cochain : E.coefficient.C1)
    (hclosed : CechZ1 E cochain) :
    SemanticRepairAdditiveH1Class additive :=
  Quotient.mk (semanticRepairAdditiveH1CocycleSetoid additive)
    ⟨cochain, hclosed⟩

/-- Same additive Cech class relation gives equal quotient classes. -/
theorem semanticRepairAdditiveH1Class_eq_of_sameClass
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    {left right : E.coefficient.C1}
    (hleft : CechZ1 E left)
    (hright : CechZ1 E right)
    (hsame : SemanticRepairAdditiveH1SameClass additive left right) :
    semanticRepairAdditiveH1Class_mk additive left hleft =
      semanticRepairAdditiveH1Class_mk additive right hright := by
  exact Quotient.sound hsame

/-- The selected residual as an additive Cech `H1` class. -/
def semanticRepairAdditiveResidualClass
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E) :
    SemanticRepairAdditiveH1Class additive :=
  semanticRepairAdditiveH1Class_mk additive
    E.coefficient.residual E.coefficient.residual_cocycle

/-- The additive zero Cech `H1` class. -/
def semanticRepairAdditiveZeroClass
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E) :
    SemanticRepairAdditiveH1Class additive :=
  semanticRepairAdditiveH1Class_mk additive
    E.coefficient.zero1 E.coefficient.zero1_cocycle

/-- The selected residual has zero additive Cech `H1` class. -/
def SemanticRepairAdditiveH1Zero
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E) : Prop :=
  semanticRepairAdditiveResidualClass additive =
    semanticRepairAdditiveZeroClass additive

/--
Quotient class equality is exactly the additive same-class relation between the
selected residual cocycle and the zero cocycle.
-/
theorem semanticRepairAdditiveH1Zero_iff_sameClass_zero
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E) :
    SemanticRepairAdditiveH1Zero additive <->
      SemanticRepairAdditiveH1SameClass additive
        E.coefficient.residual E.coefficient.zero1 := by
  constructor
  · intro hzero
    exact Quotient.exact hzero
  · intro hsame
    exact
      semanticRepairAdditiveH1Class_eq_of_sameClass additive
        E.coefficient.residual_cocycle E.coefficient.zero1_cocycle hsame

/--
The additive Cech `H1` class of the selected residual vanishes exactly when the
residual is a visible Cech boundary.
-/
theorem semanticRepairAdditiveH1Zero_iff_boundary
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E) :
    SemanticRepairAdditiveH1Zero additive <->
      CechB1 E E.coefficient.residual := by
  letI := additive.c1AddCommGroup
  constructor
  · intro hzero
    have hzero1 : E.coefficient.zero1 = 0 := additive.zero1_eq_zero
    rcases
      (semanticRepairAdditiveH1Zero_iff_sameClass_zero additive).1 hzero
        with ⟨primitive, hprimitive⟩
    exact
      ⟨primitive,
        by
          simpa [SemanticRepairAdditiveH1SameClass, hzero1] using hprimitive⟩
  · intro hboundary
    have hzero1 : E.coefficient.zero1 = 0 := additive.zero1_eq_zero
    rcases hboundary with ⟨primitive, hprimitive⟩
    apply (semanticRepairAdditiveH1Zero_iff_sameClass_zero additive).2
    exact
      ⟨primitive,
        by
          simpa [SemanticRepairAdditiveH1SameClass, hzero1] using hprimitive⟩

/-- Cycle 15 package: additive `Z1 / B1` quotient provenance for the residual. -/
theorem semanticRepairAdditiveH1Quotient_package
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E) :
    (forall left right : E.coefficient.C1,
      SemanticRepairAdditiveH1SameClass additive left right <->
        (letI := additive.c1AddCommGroup
         CechB1 E (left - right))) /\
      (SemanticRepairAdditiveH1Zero additive <->
        SemanticRepairAdditiveH1SameClass additive
          E.coefficient.residual E.coefficient.zero1) /\
      (SemanticRepairAdditiveH1Zero additive <->
        CechB1 E E.coefficient.residual) := by
  exact
    ⟨by
      intro left right
      rfl,
    semanticRepairAdditiveH1Zero_iff_sameClass_zero additive,
    semanticRepairAdditiveH1Zero_iff_boundary additive⟩

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

/--
The additive `Z1 / B1` zero class matches the existing sheaf `H1` zero predicate.

Both sides are reduced to the same visible boundary predicate; no boundary
detector or global repair predicate is used as a field.
-/
theorem semanticRepairH1Zero_iff_additiveH1Zero
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E) :
    SemanticRepairH1Zero E <-> SemanticRepairAdditiveH1Zero additive := by
  exact
    (sheafH1Zero_iff_h1Boundary E).trans
      (semanticRepairAdditiveH1Zero_iff_boundary additive).symm

/--
Additive zero `H1` class plus later-layer vanishings gives global semantic repair
coherence through the existing exactness discharge.
-/
theorem globalRepairCoherent_of_additiveH1_zero
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (additive : SemanticRepairAdditiveCechH1Data E)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E)
    (hzero : SemanticRepairAdditiveH1Zero additive)
    (htorsor : NonabelianTorsorTrivial (toFiniteTower E))
    (hhigher : HigherCoherenceVanishes (toFiniteTower E))
    (hstack : StackEffectivelyVanishes (toFiniteTower E)) :
    GlobalSemanticRepairCoherent (toFiniteTower E) := by
  exact
    globalRepairCoherent_of_sheafH1_zero E discharge
      ((semanticRepairH1Zero_iff_additiveH1Zero additive).2 hzero)
      htorsor hhigher hstack

/--
Global semantic repair coherence forces the selected residual to vanish in the
additive `Z1 / B1` quotient.
-/
theorem additiveH1Zero_of_globalRepairCoherent
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (additive : SemanticRepairAdditiveCechH1Data E)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E) :
    GlobalSemanticRepairCoherent (toFiniteTower E) ->
      SemanticRepairAdditiveH1Zero additive := by
  intro hglobal
  have hold : SemanticRepairH1Zero E := by
    have htower :
        ObstructionTowerVanishes (toFiniteTower E) :=
      globalRepairCoherent_forces_obstructionTowerVanishes
        (toFiniteTower E)
        (layeredAdequacy_of_sheafH1Discharge discharge)
        hglobal
    exact (h1Vanishes_iff_sheafH1Zero_of_exactEnvelope E).1 htower.1
  exact (semanticRepairH1Zero_iff_additiveH1Zero additive).1 hold

/--
Target-adjacent bridge: under the existing discharge and later-layer effective
descent evidence, global semantic repair coherence is equivalent to vanishing
of the selected residual's additive Cech `H1 = Z1 / B1` class.
-/
theorem globalRepairCoherent_iff_additiveH1Zero
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (additive : SemanticRepairAdditiveCechH1Data E)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E)
    (htorsor : NonabelianTorsorTrivial (toFiniteTower E))
    (hhigher : HigherCoherenceVanishes (toFiniteTower E))
    (hstack : StackEffectivelyVanishes (toFiniteTower E)) :
    GlobalSemanticRepairCoherent (toFiniteTower E) <->
      SemanticRepairAdditiveH1Zero additive := by
  constructor
  · exact additiveH1Zero_of_globalRepairCoherent E additive discharge
  · intro hzero
    exact
      globalRepairCoherent_of_additiveH1_zero E additive discharge hzero
        htorsor hhigher hstack

/-- Cycle 16 package: additive Cech `H1` zero is the global gluing obstruction. -/
theorem semanticRepairAdditiveH1GluingBridge_package
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (additive : SemanticRepairAdditiveCechH1Data E)
    (discharge : SemanticRepairSheafH1ExactnessDischarge E)
    (htorsor : NonabelianTorsorTrivial (toFiniteTower E))
    (hhigher : HigherCoherenceVanishes (toFiniteTower E))
    (hstack : StackEffectivelyVanishes (toFiniteTower E)) :
    (SemanticRepairH1Zero E <-> SemanticRepairAdditiveH1Zero additive) /\
      (SemanticRepairAdditiveH1Zero additive ->
        GlobalSemanticRepairCoherent (toFiniteTower E)) /\
      (GlobalSemanticRepairCoherent (toFiniteTower E) ->
        SemanticRepairAdditiveH1Zero additive) /\
      (GlobalSemanticRepairCoherent (toFiniteTower E) <->
        SemanticRepairAdditiveH1Zero additive) := by
  exact
    ⟨semanticRepairH1Zero_iff_additiveH1Zero additive,
      (fun hzero =>
        globalRepairCoherent_of_additiveH1_zero E additive discharge hzero
          htorsor hhigher hstack),
      additiveH1Zero_of_globalRepairCoherent E additive discharge,
      globalRepairCoherent_iff_additiveH1Zero E additive discharge
        htorsor hhigher hstack⟩

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
end ResearchLean.AG
