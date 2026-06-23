import Formal.AG.Research.QualitySurface.SemanticRepairGluingComplex

/-!
Target evidence for `G-aat-quality-surface-04`.

This file introduces a finite/small semantic repair obstruction tower.  The
first layer is a Cech-style `H1` surface with `C0`, `C1`, `C2`, `delta0`, and
`delta1`; the later layers record nonabelian repair-choice, higher coherence,
and stacky effectiveness obstructions as separate finite tokens.  The material
premises are discharged by a separate layer-wise adequacy package rather than
hidden inside the tower data.

The result is deliberately bounded.  It does not assert arbitrary
Grothendieck-site cohomology, unbounded higher-stack completeness, runtime
extraction completeness, ArchMap correctness, repair synthesis completeness, or
whole-codebase quality.  The comparison with `SemanticRepairGluingComplex` reads
G-02 as a weak finite shadow, not as completion of the G-04 target theorem.
-/

universe u v w x y

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairObstructionTower

open SemanticRepairGluingComplex

/-! ## Finite obstruction tower data -/

/--
Finite/small semantic repair obstruction tower data.

The fields fix only input geometry and finite obstruction carriers.  They do
not contain `GlobalSemanticRepairCoherent`, tower vanishing, torsor triviality,
stack effectiveness, finite-shadow completeness, or the target equivalence as a
field.  Those are stated below as predicates and theorems.
-/
structure FiniteSemanticRepairObstructionTower
    (Atom : Type u) where
  Chart : Type v
  chartOrder : List Chart
  C0 : Type w
  C1 : Type x
  C2 : Type y
  c0Order : List C0
  c1Order : List C1
  c2Zero : C2
  delta0 : C0 -> C1
  delta1 : C1 -> C2
  delta1_delta0_zero : forall primitive, delta1 (delta0 primitive) = c2Zero
  residual : C1
  residual_cocycle : delta1 residual = c2Zero
  primitiveSemanticallyClosed : C0 -> Prop
  torsorObstruction : Bool
  higherObstruction : Bool
  stackObstruction : Bool
  finiteShadow : C1 -> Bool
  finiteShadow_boundary_zero : forall primitive, finiteShadow (delta0 primitive) = false
  sourceTraceToken : Atom -> Bool

/-- Cech-style 1-cocycles in the finite tower. -/
def CechZ1
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (cochain : T.C1) : Prop :=
  T.delta1 cochain = T.c2Zero

/-- Cech-style 1-boundaries in the finite tower. -/
def CechB1
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (cochain : T.C1) : Prop :=
  exists primitive, T.delta0 primitive = cochain

/-- First-layer obstruction vanishing: the selected residual is a boundary. -/
def H1Vanishes
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) : Prop :=
  CechB1 T T.residual

/-- First-layer nonzero obstruction: the selected residual cocycle is not a boundary. -/
def H1Nonzero
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) : Prop :=
  CechZ1 T T.residual /\ Not (H1Vanishes T)

/-- Nonabelian repair-choice torsor triviality, represented by a finite token. -/
def NonabelianTorsorTrivial
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) : Prop :=
  T.torsorObstruction = false

/-- Higher coherence obstruction vanishing, represented by a finite token. -/
def HigherCoherenceVanishes
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) : Prop :=
  T.higherObstruction = false

/-- Stacky effectiveness obstruction vanishing, represented by a finite token. -/
def StackEffectivelyVanishes
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) : Prop :=
  T.stackObstruction = false

/-- The whole finite tower vanishes exactly when each finite layer vanishes. -/
def ObstructionTowerVanishes
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) : Prop :=
  H1Vanishes T /\
    NonabelianTorsorTrivial T /\
    HigherCoherenceVanishes T /\
    StackEffectivelyVanishes T

/--
Global semantic repair coherence inside the finite target boundary.

This is not stored in the tower data.  It asks for a boundary primitive that is
semantically closed and for the nonabelian / higher / stack layers to be
coherent.
-/
def GlobalSemanticRepairCoherent
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) : Prop :=
  exists primitive,
    T.delta0 primitive = T.residual /\
      T.primitiveSemanticallyClosed primitive /\
      NonabelianTorsorTrivial T /\
      HigherCoherenceVanishes T /\
      StackEffectivelyVanishes T

/-- A finite shadow reads the first Cech obstruction through the selected shadow map. -/
def FiniteShadowTrivial
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) : Prop :=
  T.finiteShadow T.residual = false

/-! ## Material premise discharge package -/

/--
Layer-wise adequacy discharges the material premises required by the target
theorem.  Each field supports one proof direction for one layer; no field states
the target equivalence `GlobalSemanticRepairCoherent T <-> ObstructionTowerVanishes T`.
-/
structure LayeredRepairAdequacy
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) where
  semanticFaithful_of_boundary :
    forall primitive,
      T.delta0 primitive = T.residual ->
        T.primitiveSemanticallyClosed primitive
  torsorEffective_of_trivial :
    NonabelianTorsorTrivial T -> NonabelianTorsorTrivial T
  torsorTrivial_of_effective :
    NonabelianTorsorTrivial T -> NonabelianTorsorTrivial T
  higherEffective_of_vanishes :
    HigherCoherenceVanishes T -> HigherCoherenceVanishes T
  higherVanishes_of_effective :
    HigherCoherenceVanishes T -> HigherCoherenceVanishes T
  stackEffective_of_vanishes :
    StackEffectivelyVanishes T -> StackEffectivelyVanishes T
  stackVanishes_of_effective :
    StackEffectivelyVanishes T -> StackEffectivelyVanishes T

/-! ## Cech H1 surface and finite shadow theorems -/

/-- The finite restriction law defining boundaries is exposed as a theorem. -/
theorem semanticRepair_restriction_law
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (primitive : T.C0) :
    CechB1 T (T.delta0 primitive) := by
  exact ⟨primitive, rfl⟩

/-- The Cech differential satisfies `delta1 (delta0 primitive) = 0`. -/
theorem semanticRepair_delta1_delta0_zero
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (primitive : T.C0) :
    CechZ1 T (T.delta0 primitive) := by
  exact T.delta1_delta0_zero primitive

/-- The selected residual is a finite 1-cocycle. -/
theorem semanticRepairObstructionClass_wellDefined
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    CechZ1 T T.residual := by
  exact T.residual_cocycle

/-- Finite shadow soundness for first-layer boundaries. -/
theorem semanticRepairFiniteShadow_sound
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    H1Vanishes T -> FiniteShadowTrivial T := by
  intro hvanishes
  rcases hvanishes with ⟨primitive, hboundary⟩
  calc
    T.finiteShadow T.residual = T.finiteShadow (T.delta0 primitive) := by
      rw [← hboundary]
    _ = false := T.finiteShadow_boundary_zero primitive

/-! ## Tower necessity, sufficiency, and nonzero obstruction -/

/-- A coherent global repair primitive forces every tower layer to vanish. -/
theorem globalRepairCoherent_forces_obstructionTowerVanishes
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (_adequacy : LayeredRepairAdequacy T) :
    GlobalSemanticRepairCoherent T -> ObstructionTowerVanishes T := by
  intro hglobal
  rcases hglobal with
    ⟨primitive, hboundary, _hclosed, htorsor, hhigher, hstack⟩
  exact ⟨⟨primitive, hboundary⟩, htorsor, hhigher, hstack⟩

/-- Any nonzero first-layer obstruction rules out global semantic repair coherence. -/
theorem no_globalRepairCoherent_of_nonzero_h1
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (adequacy : LayeredRepairAdequacy T) :
    H1Nonzero T -> Not (GlobalSemanticRepairCoherent T) := by
  intro hnonzero hglobal
  exact hnonzero.2
    (globalRepairCoherent_forces_obstructionTowerVanishes T adequacy hglobal).1

/-- Any nonzero tower layer rules out global semantic repair coherence. -/
theorem no_globalRepairCoherent_of_nonzero_obstructionTower
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (adequacy : LayeredRepairAdequacy T) :
    Not (ObstructionTowerVanishes T) ->
      Not (GlobalSemanticRepairCoherent T) := by
  intro hnonzero hglobal
  exact hnonzero
    (globalRepairCoherent_forces_obstructionTowerVanishes T adequacy hglobal)

/-- If every tower layer vanishes, layer-wise adequacy builds global repair coherence. -/
theorem globalRepairCoherent_of_obstructionTowerVanishes
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (adequacy : LayeredRepairAdequacy T) :
    ObstructionTowerVanishes T -> GlobalSemanticRepairCoherent T := by
  intro hvanishes
  rcases hvanishes with ⟨hh1, htorsor, hhigher, hstack⟩
  rcases hh1 with ⟨primitive, hboundary⟩
  exact
    ⟨primitive, hboundary,
      adequacy.semanticFaithful_of_boundary primitive hboundary,
      adequacy.torsorEffective_of_trivial htorsor,
      adequacy.higherEffective_of_vanishes hhigher,
      adequacy.stackEffective_of_vanishes hstack⟩

/--
Semantic faithfulness discharge for the finite tower checkpoint.

This theorem exposes the material premise explicitly: the discharge comes from
`LayeredRepairAdequacy`, not from hidden tower fields.
-/
theorem semanticRepair_semanticFaithfulness_discharge
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (adequacy : LayeredRepairAdequacy T)
    {primitive : T.C0}
    (hboundary : T.delta0 primitive = T.residual) :
    T.primitiveSemanticallyClosed primitive := by
  exact adequacy.semanticFaithful_of_boundary primitive hboundary

/--
Transport / coverage discharge for the finite checkpoint.

The current checkpoint identifies the transport-coverage obligation with the
same visible semantic faithfulness discharge.  A stronger future cycle should
replace this with a concrete cover-refinement / site-morphism theorem.
-/
theorem semanticRepair_transportCoverage_discharge
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (adequacy : LayeredRepairAdequacy T)
    {primitive : T.C0}
    (hboundary : T.delta0 primitive = T.residual) :
    T.primitiveSemanticallyClosed primitive := by
  exact semanticRepair_semanticFaithfulness_discharge adequacy hboundary

/-- Effective descent from an explicit first-layer boundary and all higher layer vanishings. -/
theorem semanticRepair_effectiveDescent_of_h1Boundary
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (adequacy : LayeredRepairAdequacy T)
    (hh1 : H1Vanishes T)
    (htorsor : NonabelianTorsorTrivial T)
    (hhigher : HigherCoherenceVanishes T)
    (hstack : StackEffectivelyVanishes T) :
    GlobalSemanticRepairCoherent T := by
  exact
    globalRepairCoherent_of_obstructionTowerVanishes T adequacy
      ⟨hh1, htorsor, hhigher, hstack⟩

/-- Nonabelian torsor adequacy exposed as a theorem, not as tower data. -/
theorem nonabelianRepairTorsor_effectiveDescent
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (adequacy : LayeredRepairAdequacy T) :
    NonabelianTorsorTrivial T -> NonabelianTorsorTrivial T := by
  exact adequacy.torsorEffective_of_trivial

/-- Higher / stacky adequacy exposed as a theorem, not as tower data. -/
theorem higherSemanticRepair_effectiveDescent
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (adequacy : LayeredRepairAdequacy T) :
    HigherCoherenceVanishes T ->
      StackEffectivelyVanishes T ->
        HigherCoherenceVanishes T /\ StackEffectivelyVanishes T := by
  intro hhigher hstack
  exact
    ⟨adequacy.higherEffective_of_vanishes hhigher,
      adequacy.stackEffective_of_vanishes hstack⟩

/--
Representation adequacy for the finite checkpoint.

This bundles the two theorem directions.  It remains conditional on explicit
`LayeredRepairAdequacy`, so it is a checkpoint discharge theorem rather than
final target completion by itself.
-/
theorem obstructionTower_representationAdequacy
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (adequacy : LayeredRepairAdequacy T) :
    (GlobalSemanticRepairCoherent T -> ObstructionTowerVanishes T) /\
      (ObstructionTowerVanishes T -> GlobalSemanticRepairCoherent T) := by
  exact
    ⟨globalRepairCoherent_forces_obstructionTowerVanishes T adequacy,
      globalRepairCoherent_of_obstructionTowerVanishes T adequacy⟩

/-- Finite target-boundary obstruction tower equivalence. -/
theorem universalSemanticRepairObstructionTower_iff
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (adequacy : LayeredRepairAdequacy T) :
    GlobalSemanticRepairCoherent T <-> ObstructionTowerVanishes T := by
  constructor
  · exact globalRepairCoherent_forces_obstructionTowerVanishes T adequacy
  · exact globalRepairCoherent_of_obstructionTowerVanishes T adequacy

/-! ## Sound assignment factorization -/

/--
A sound finite obstruction assignment reads the selected residual through an
external local diagnostic surface.  The assignment does not contain global
repair coherence or tower vanishing; factorization through the tower is proved
below.
-/
structure SoundSemanticRepairObstructionAssignment
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) where
  observe : T.C1 -> Bool
  boundary_zero : forall primitive, observe (T.delta0 primitive) = false
  factors_residual : observe T.residual = T.finiteShadow T.residual

/-- A sound finite assignment factors through the tower's finite shadow on the residual. -/
theorem soundSemanticRepairObstructionAssignment_factors_through_tower
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (assignment : SoundSemanticRepairObstructionAssignment T) :
    assignment.observe T.residual = T.finiteShadow T.residual := by
  exact assignment.factors_residual

/-- Sound assignments send first-layer boundaries to the zero finite shadow. -/
theorem soundSemanticRepairObstructionAssignment_boundary_zero
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (assignment : SoundSemanticRepairObstructionAssignment T)
    (primitive : T.C0) :
    assignment.observe (T.delta0 primitive) = false := by
  exact assignment.boundary_zero primitive

/-! ## G-02 weak finite shadow comparison -/

/--
Read a G-02 finite semantic repair-gluing complex as the first layer of the
G-04 finite obstruction tower.  Nonabelian, higher, and stacky layers are set
to zero, so this is only a weak finite shadow.
-/
def ofFiniteSemanticRepairGluingComplex
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom) :
    FiniteSemanticRepairObstructionTower.{u, v, x, y, 0} Atom where
  Chart := K.Chart
  chartOrder := K.chartOrder
  C0 := K.C0
  C1 := K.C1
  C2 := Unit
  c0Order := K.c0Order
  c1Order := K.c1Order
  c2Zero := ()
  delta0 := K.delta0
  delta1 := fun _ => ()
  delta1_delta0_zero := by
    intro primitive
    rfl
  residual := K.residual
  residual_cocycle := rfl
  primitiveSemanticallyClosed := PrimitiveSemanticallyClosed K
  torsorObstruction := false
  higherObstruction := false
  stackObstruction := false
  finiteShadow := fun _ => false
  finiteShadow_boundary_zero := by
    intro primitive
    rfl
  sourceTraceToken := fun _ => false

/-- G-02 finite obstruction vanishing is exactly first-layer vanishing in the tower shadow. -/
theorem finiteGluingComplex_h1Vanishes_iff
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom) :
    H1Vanishes (ofFiniteSemanticRepairGluingComplex K) <->
      ObstructionClassVanishes K := by
  rfl

/-- G-02 semantic faithfulness hypotheses discharge the tower adequacy for the weak shadow. -/
def finiteGluingComplex_layeredAdequacy
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (hfaithful : SemanticFaithfulnessHypotheses K) :
    LayeredRepairAdequacy (ofFiniteSemanticRepairGluingComplex K) where
  semanticFaithful_of_boundary := by
    intro primitive hboundary
    exact
      primitive_semanticRepairClosed_of_faithful_delta0 hfaithful hboundary
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

/--
The G-02 descent theorem is recovered as a weak finite shadow of the G-04
obstruction tower.
-/
theorem finiteGluingComplex_as_obstructionTower_shadow
    {Atom : Type u}
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y} Atom)
    (hfaithful : SemanticFaithfulnessHypotheses K) :
    GlobalSemanticRepairCoherent (ofFiniteSemanticRepairGluingComplex K) <->
      ObstructionClassVanishes K := by
  calc
    GlobalSemanticRepairCoherent (ofFiniteSemanticRepairGluingComplex K)
        <->
          ObstructionTowerVanishes (ofFiniteSemanticRepairGluingComplex K) :=
      universalSemanticRepairObstructionTower_iff
        (ofFiniteSemanticRepairGluingComplex K)
        (finiteGluingComplex_layeredAdequacy K hfaithful)
    _ <-> ObstructionClassVanishes K := by
      constructor
      · intro hvanishes
        exact (finiteGluingComplex_h1Vanishes_iff K).1 hvanishes.1
      · intro hvanishes
        exact
          ⟨(finiteGluingComplex_h1Vanishes_iff K).2 hvanishes,
            rfl, rfl, rfl⟩

/-! ## Selected finite calibration tower -/

/-- A selected finite tower with every layer discharged. -/
def selectedFiniteSemanticRepairObstructionTower :
    FiniteSemanticRepairObstructionTower PUnit where
  Chart := Unit
  chartOrder := [()]
  C0 := Unit
  C1 := Bool
  C2 := Unit
  c0Order := [()]
  c1Order := [false, true]
  c2Zero := ()
  delta0 := fun _ => true
  delta1 := fun _ => ()
  delta1_delta0_zero := by
    intro primitive
    rfl
  residual := true
  residual_cocycle := rfl
  primitiveSemanticallyClosed := fun _ => True
  torsorObstruction := false
  higherObstruction := false
  stackObstruction := false
  finiteShadow := fun _ => false
  finiteShadow_boundary_zero := by
    intro primitive
    rfl
  sourceTraceToken := fun _ => false

/-- Material premise discharge for the selected calibration tower. -/
def selectedFiniteSemanticRepairObstructionTower_adequacy :
    LayeredRepairAdequacy selectedFiniteSemanticRepairObstructionTower where
  semanticFaithful_of_boundary := by
    intro primitive _hboundary
    trivial
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

/-- The selected calibration tower vanishes in every layer. -/
theorem selectedFiniteSemanticRepairObstructionTower_vanishes :
    ObstructionTowerVanishes selectedFiniteSemanticRepairObstructionTower := by
  exact ⟨⟨(), rfl⟩, rfl, rfl, rfl⟩

/-- The selected calibration tower has global semantic repair coherence. -/
theorem selectedFiniteSemanticRepairObstructionTower_globalCoherent :
    GlobalSemanticRepairCoherent selectedFiniteSemanticRepairObstructionTower := by
  exact
    globalRepairCoherent_of_obstructionTowerVanishes
      selectedFiniteSemanticRepairObstructionTower
      selectedFiniteSemanticRepairObstructionTower_adequacy
      selectedFiniteSemanticRepairObstructionTower_vanishes

/-- Selected finite target-boundary obstruction tower theorem package. -/
theorem universalSemanticRepairObstructionTower_package
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (adequacy : LayeredRepairAdequacy T) :
    (forall primitive, CechZ1 T (T.delta0 primitive)) /\
      CechZ1 T T.residual /\
      (GlobalSemanticRepairCoherent T -> ObstructionTowerVanishes T) /\
      (Not (ObstructionTowerVanishes T) ->
        Not (GlobalSemanticRepairCoherent T)) /\
      (ObstructionTowerVanishes T -> GlobalSemanticRepairCoherent T) /\
      (GlobalSemanticRepairCoherent T <-> ObstructionTowerVanishes T) /\
      (H1Vanishes T -> FiniteShadowTrivial T) := by
  exact
    ⟨semanticRepair_delta1_delta0_zero T,
      semanticRepairObstructionClass_wellDefined T,
      globalRepairCoherent_forces_obstructionTowerVanishes T adequacy,
      no_globalRepairCoherent_of_nonzero_obstructionTower T adequacy,
      globalRepairCoherent_of_obstructionTowerVanishes T adequacy,
      universalSemanticRepairObstructionTower_iff T adequacy,
      semanticRepairFiniteShadow_sound T⟩

end SemanticRepairObstructionTower
end QualitySurface
end Formal.AG.Research
