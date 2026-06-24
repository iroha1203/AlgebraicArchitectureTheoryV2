import Formal.AG.Research.QualitySurface.SemanticRepairUniversalShadow
import Formal.AG.Research.QualitySurface.SemanticRepairAdequacyDischarge
import Formal.AG.Research.QualitySurface.SemanticRepairStackyH2

/-!
Cycle 9 evidence for `G-aat-quality-surface-04`.

This file discharges the finite-shadow reflection premise that remained visible
after Cycle 8.  The key move is to build the finite shadow from a finite
boundary decision procedure.  Reflection is then a theorem about that exact
shadow, not a field hidden inside an artifact or assignment.

The final package remains inside the finite/small target boundary.  It does
not assert Rust ArchSig implementation correctness, runtime extraction
completeness, ArchMap validation, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairTargetCompletion

open SemanticRepairObstructionTower
open SemanticRepairAdequacyDischarge
open SemanticRepairUniversalShadow
open SemanticRepairSheafH1
open SemanticRepairNonabelianTorsor
open SemanticRepairStackyH2

universe u v w x y z r s

/-! ## Exact finite boundary shadow -/

/--
The exact finite first-layer shadow induced by a finite boundary decision.

It returns `false` exactly on finite first-layer boundaries.  The decision
procedure is finite-computability input geometry; it does not assert that the
selected residual is a boundary.
-/
def exactBoundaryFiniteShadow
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain))
    (cochain : T.C1) : Bool :=
  match decideBoundary cochain with
  | isTrue _ => false
  | isFalse _ => true

/-- Exact finite boundary shadows send boundaries to zero. -/
theorem exactBoundaryFiniteShadow_boundary_zero
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain))
    (primitive : T.C0) :
    exactBoundaryFiniteShadow T decideBoundary (T.delta0 primitive) = false := by
  unfold exactBoundaryFiniteShadow
  have hboundary : CechB1 T (T.delta0 primitive) :=
    semanticRepair_restriction_law T primitive
  generalize decideBoundary (T.delta0 primitive) = decision
  cases decision with
  | isTrue h =>
      rfl
  | isFalse hnot =>
      exact False.elim (hnot hboundary)

/-- Zero exact finite shadow reflects first-layer vanishing. -/
theorem h1Vanishes_of_exactBoundaryFiniteShadow_zero
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain)) :
    exactBoundaryFiniteShadow T decideBoundary T.residual = false ->
      H1Vanishes T := by
  intro hzero
  unfold exactBoundaryFiniteShadow at hzero
  generalize decideBoundary T.residual = decision at hzero
  cases decision with
  | isTrue hboundary =>
      exact hboundary
  | isFalse _hnot =>
      cases hzero

/-- The exact finite first-layer shadow is zero iff the first obstruction vanishes. -/
theorem exactBoundaryFiniteShadow_zero_iff_h1Vanishes
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain)) :
    exactBoundaryFiniteShadow T decideBoundary T.residual = false <->
      H1Vanishes T := by
  constructor
  · exact h1Vanishes_of_exactBoundaryFiniteShadow_zero T decideBoundary
  · intro hvanishes
    rcases hvanishes with ⟨primitive, hboundary⟩
    calc
      exactBoundaryFiniteShadow T decideBoundary T.residual =
          exactBoundaryFiniteShadow T decideBoundary (T.delta0 primitive) := by
            rw [hboundary]
      _ = false := exactBoundaryFiniteShadow_boundary_zero T decideBoundary primitive

/-! ## Finite-list boundary decision -/

/-- Boundary membership restricted to an explicit finite list of primitives. -/
def ListedBoundaryFrom
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    List T.C0 -> T.C1 -> Prop
  | [], _ => False
  | primitive :: rest, cochain =>
      T.delta0 primitive = cochain \/ ListedBoundaryFrom T rest cochain

/-- Finite-list boundary membership is decidable when cochain equality is decidable. -/
def listedBoundaryFromDecision
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    [DecidableEq T.C1] :
    (listed : List T.C0) ->
      (cochain : T.C1) -> Decidable (ListedBoundaryFrom T listed cochain)
  | [], _ => isFalse (by intro h; exact h)
  | primitive :: rest, cochain =>
      match decEq (T.delta0 primitive) cochain with
      | isTrue hhead => isTrue (Or.inl hhead)
      | isFalse hhead =>
          match listedBoundaryFromDecision T rest cochain with
          | isTrue htail => isTrue (Or.inr htail)
          | isFalse htail =>
              isFalse (by
                intro hlisted
                cases hlisted with
                | inl h => exact hhead h
                | inr h => exact htail h)

/-- A listed boundary is a Cech boundary. -/
theorem listedBoundaryFrom_sound
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    {listed : List T.C0}
    {cochain : T.C1} :
    ListedBoundaryFrom T listed cochain -> CechB1 T cochain := by
  intro hlisted
  induction listed with
  | nil =>
      exact False.elim hlisted
  | cons primitive rest ih =>
      cases hlisted with
      | inl hboundary =>
          exact ⟨primitive, hboundary⟩
      | inr htail =>
          exact ih htail

/-- A boundary whose primitive is in the finite list is listed. -/
theorem listedBoundaryFrom_of_mem
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    {listed : List T.C0}
    {primitive : T.C0}
    {cochain : T.C1}
    (hmem : primitive ∈ listed)
    (hboundary : T.delta0 primitive = cochain) :
    ListedBoundaryFrom T listed cochain := by
  induction listed with
  | nil =>
      cases hmem
  | cons head rest ih =>
      cases hmem with
      | head hhead =>
          exact Or.inl hboundary
      | tail _ htail =>
          exact Or.inr (ih htail)

/-- Finite-list completeness turns every Cech boundary into a listed boundary. -/
theorem listedBoundaryFrom_complete_of_certificate
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (certificate : FiniteBoundarySemanticClosureCertificate T)
    {cochain : T.C1} :
    CechB1 T cochain -> ListedBoundaryFrom T T.c0Order cochain := by
  intro hboundary
  rcases hboundary with ⟨primitive, hprimitive⟩
  exact
    listedBoundaryFrom_of_mem T
      (certificate.c0_complete primitive) hprimitive

/--
Construct a boundary decision procedure from finite primitive-list
completeness and decidable equality on `C1`.
-/
def finiteBoundaryDecisionOfCertificate
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    [DecidableEq T.C1]
    (certificate : FiniteBoundarySemanticClosureCertificate T) :
    (cochain : T.C1) -> Decidable (CechB1 T cochain) := by
  intro cochain
  exact
    match listedBoundaryFromDecision T T.c0Order cochain with
    | isTrue hlisted =>
        isTrue (listedBoundaryFrom_sound T hlisted)
    | isFalse hnotListed =>
        isFalse (by
          intro hboundary
          exact hnotListed
            (listedBoundaryFrom_complete_of_certificate
              certificate hboundary))

/-- Replace a tower's finite shadow by the exact finite boundary shadow. -/
def withExactBoundaryFiniteShadow
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain)) :
    FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom where
  Chart := T.Chart
  chartOrder := T.chartOrder
  C0 := T.C0
  C1 := T.C1
  C2 := T.C2
  c0Order := T.c0Order
  c1Order := T.c1Order
  c2Zero := T.c2Zero
  delta0 := T.delta0
  delta1 := T.delta1
  delta1_delta0_zero := T.delta1_delta0_zero
  residual := T.residual
  residual_cocycle := T.residual_cocycle
  primitiveSemanticallyClosed := T.primitiveSemanticallyClosed
  torsorObstruction := T.torsorObstruction
  higherObstruction := T.higherObstruction
  stackObstruction := T.stackObstruction
  finiteShadow := exactBoundaryFiniteShadow T decideBoundary
  finiteShadow_boundary_zero :=
    exactBoundaryFiniteShadow_boundary_zero T decideBoundary
  sourceTraceToken := T.sourceTraceToken

/-- The exact-shadow tower has first-layer finite-shadow reflection. -/
theorem withExactBoundaryFiniteShadow_reflection
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain)) :
    FiniteTowerShadowReflection
      (withExactBoundaryFiniteShadow T decideBoundary) where
  h1_vanishes_of_shadow_zero := by
    intro hzero
    change exactBoundaryFiniteShadow T decideBoundary T.residual = false at hzero
    have hh1 :=
      h1Vanishes_of_exactBoundaryFiniteShadow_zero T decideBoundary hzero
    change CechB1 T T.residual
    exact hh1

/-- Exact finite shadow triviality is equivalent to first-layer vanishing. -/
theorem withExactBoundaryFiniteShadow_h1_iff_shadow_zero
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain)) :
    FiniteShadowTrivial (withExactBoundaryFiniteShadow T decideBoundary) <->
      H1Vanishes (withExactBoundaryFiniteShadow T decideBoundary) := by
  constructor
  · intro hshadow
    change exactBoundaryFiniteShadow T decideBoundary T.residual = false at hshadow
    have hh1 :=
      h1Vanishes_of_exactBoundaryFiniteShadow_zero T decideBoundary hshadow
    change CechB1 T T.residual
    exact hh1
  · intro hh1
    change CechB1 T T.residual at hh1
    change exactBoundaryFiniteShadow T decideBoundary T.residual = false
    exact
      (exactBoundaryFiniteShadow_zero_iff_h1Vanishes T decideBoundary).2 hh1

/-- Exact canonical all-layer shadow zero is equivalent to tower vanishing. -/
theorem withExactBoundaryFiniteShadow_shadowZero_iff_towerVanishes
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain)) :
    FiniteTowerLayerShadowZero
      (canonicalTowerLayerShadow
        (withExactBoundaryFiniteShadow T decideBoundary)) <->
      ObstructionTowerVanishes
        (withExactBoundaryFiniteShadow T decideBoundary) := by
  constructor
  · exact
      canonicalShadowZero_to_obstructionTowerVanishes
        (withExactBoundaryFiniteShadow T decideBoundary)
        (withExactBoundaryFiniteShadow_reflection T decideBoundary)
  · exact
      obstructionTowerVanishes_to_canonicalShadowZero
        (withExactBoundaryFiniteShadow T decideBoundary)

/-! ## Discharge-prism transport to the exact-shadow tower -/

/-- Reuse a finite boundary certificate after replacing the shadow map. -/
def exactShadowBoundaryCertificate
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain))
    (certificate : FiniteBoundarySemanticClosureCertificate T) :
    FiniteBoundarySemanticClosureCertificate
      (withExactBoundaryFiniteShadow T decideBoundary) where
  coverage := certificate.coverage
  faithfulness := certificate.faithfulness
  c0_complete := by
    intro primitive
    exact certificate.c0_complete primitive
  coverage_of_listed_boundary := by
    intro primitive hlisted hboundary
    exact certificate.coverage_of_listed_boundary primitive hlisted hboundary
  faithfulness_of_listed_boundary := by
    intro primitive hlisted hboundary
    exact certificate.faithfulness_of_listed_boundary primitive hlisted hboundary
  semantic_closed_of_coverage_and_faithfulness := by
    intro primitive hcoverage hfaithfulness
    exact
      certificate.semantic_closed_of_coverage_and_faithfulness
        primitive hcoverage hfaithfulness

/-- Reuse a discharge prism after replacing the shadow map. -/
def exactShadowDischargePrism
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain))
    (prism : LayeredRepairDischargePrism T) :
    LayeredRepairDischargePrism
      (withExactBoundaryFiniteShadow T decideBoundary) where
  boundary := exactShadowBoundaryCertificate decideBoundary prism.boundary

/-- The exact-shadow tower gets `LayeredRepairAdequacy` from the finite prism. -/
def exactShadowLayeredRepairAdequacy
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain))
    (prism : LayeredRepairDischargePrism T) :
    LayeredRepairAdequacy
      (withExactBoundaryFiniteShadow T decideBoundary) :=
  layeredRepairAdequacy_of_dischargePrism
    (exactShadowDischargePrism decideBoundary prism)

/-! ## Canonical artifact adequacy -/

/-- The canonical bounded artifact built from a tower is adequate for that tower. -/
def canonicalArchSigStyleArtifactAdequacy
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    ArchSigStyleFiniteShadowAdequacy T (archSigStyleArtifactOfTower T) where
  h1_matches := rfl
  torsor_matches := rfl
  higher_matches := rfl
  stack_matches := rfl
  bounded_evidence_recorded := rfl
  non_conclusions_recorded := rfl

/-- The canonical bounded artifact matches every selected tower layer. -/
theorem canonicalArchSigStyleArtifact_matches_tower_layers
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    (archSigStyleArtifactShadow (archSigStyleArtifactOfTower T)).h1 =
        (canonicalTowerLayerShadow T).h1 /\
      (archSigStyleArtifactShadow (archSigStyleArtifactOfTower T)).torsor =
        (canonicalTowerLayerShadow T).torsor /\
      (archSigStyleArtifactShadow (archSigStyleArtifactOfTower T)).higher =
        (canonicalTowerLayerShadow T).higher /\
      (archSigStyleArtifactShadow (archSigStyleArtifactOfTower T)).stack =
        (canonicalTowerLayerShadow T).stack :=
  archSigStyleArtifact_matches_tower_layers
    (canonicalArchSigStyleArtifactAdequacy T)

/-! ## Universal factorization through canonical shadows -/

/-- A representative finite tower for any all-layer finite shadow. -/
def representativeTowerOfShadow
    {Atom : Type u}
    (shadow : FiniteTowerLayerShadow) :
    FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom where
  Chart := PUnit.{v + 1}
  chartOrder := [PUnit.unit]
  C0 := PUnit.{w + 1}
  C1 := ULift.{x} Bool
  C2 := PUnit.{y + 1}
  c0Order := [PUnit.unit]
  c1Order := [ULift.up false, ULift.up true]
  c2Zero := PUnit.unit
  delta0 := fun _ => ULift.up false
  delta1 := fun _ => PUnit.unit
  delta1_delta0_zero := by
    intro primitive
    rfl
  residual := ULift.up shadow.h1
  residual_cocycle := rfl
  primitiveSemanticallyClosed := fun _ => True
  torsorObstruction := shadow.torsor
  higherObstruction := shadow.higher
  stackObstruction := shadow.stack
  finiteShadow := fun cochain => cochain.down
  finiteShadow_boundary_zero := by
    intro primitive
    rfl
  sourceTraceToken := fun _ => false

/-- The representative tower has exactly the requested canonical shadow. -/
theorem canonicalShadow_representativeTowerOfShadow
    {Atom : Type u}
    (shadow : FiniteTowerLayerShadow) :
    canonicalTowerLayerShadow
      (representativeTowerOfShadow
        (Atom := Atom) shadow) =
      shadow := by
  cases shadow
  rfl

/-- An observation is extensional if equal canonical shadows force equal readings. -/
def ShadowExtensionalTowerObservation
    {Atom : Type u}
    {Obs : Type z}
    (observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs) :
    Prop :=
  forall left right,
    canonicalTowerLayerShadow left = canonicalTowerLayerShadow right ->
      observe left = observe right

/-- The canonical factor induced by choosing representatives for finite shadows. -/
def canonicalShadowFactor
    {Atom : Type u}
    {Obs : Type z}
    (observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs)
    (shadow : FiniteTowerLayerShadow) : Obs :=
  observe
    (representativeTowerOfShadow
      (Atom := Atom) shadow)

/-- Every shadow-extensional observation factors through the canonical shadow. -/
theorem shadowExtensionalObservation_factors
    {Atom : Type u}
    {Obs : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs}
    (extensional : ShadowExtensionalTowerObservation observe)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    observe T = canonicalShadowFactor observe (canonicalTowerLayerShadow T) := by
  exact
    extensional T
      (representativeTowerOfShadow
        (Atom := Atom) (canonicalTowerLayerShadow T))
      (by
        rw [canonicalShadow_representativeTowerOfShadow])

/--
The representative-induced factor is pointwise unique among factors through the
canonical shadow.  The statement avoids function extensionality by using
pointwise equality.
-/
theorem shadowExtensionalObservation_factor_pointwise_unique
    {Atom : Type u}
    {Obs : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs}
    {factor : FiniteTowerLayerShadow -> Obs}
    (hfactor :
      forall T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) :
    forall shadow,
      factor shadow = canonicalShadowFactor observe shadow := by
  intro shadow
  have hrepresentative :=
    hfactor
      (representativeTowerOfShadow
        (Atom := Atom) shadow)
  rw [canonicalShadow_representativeTowerOfShadow] at hrepresentative
  exact hrepresentative.symm

/-- Universal factorization theorem for shadow-extensional finite observations. -/
theorem shadowExtensionalObservation_universalFactorization
    {Atom : Type u}
    {Obs : Type z}
    (observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs)
    (extensional : ShadowExtensionalTowerObservation observe) :
    (forall T,
      observe T = canonicalShadowFactor observe (canonicalTowerLayerShadow T)) /\
      (forall factor : FiniteTowerLayerShadow -> Obs,
        (forall T :
          FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
            observe T = factor (canonicalTowerLayerShadow T)) ->
          forall shadow,
            factor shadow = canonicalShadowFactor observe shadow) := by
  exact
    ⟨shadowExtensionalObservation_factors extensional,
      fun factor hfactor =>
        shadowExtensionalObservation_factor_pointwise_unique hfactor⟩

/-! ## Integrated target-completion package for the exact finite boundary shadow -/

/--
Integrated finite/small target theorem package after exact finite-shadow
reflection discharge.

The remaining inputs are finite target-boundary data: a tower, a finite
boundary decision procedure, and a discharge prism for boundary-local coverage
and faithfulness.  The theorem does not take `LayeredRepairAdequacy`,
`FiniteTowerShadowReflection`, or ArchSig artifact adequacy as assumptions.
-/
theorem universalSemanticRepairTargetCompletion_package
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (decideBoundary :
      (cochain : T.C1) -> Decidable (CechB1 T cochain))
    (prism : LayeredRepairDischargePrism T) :
    (GlobalSemanticRepairCoherent
        (withExactBoundaryFiniteShadow T decideBoundary) <->
      ObstructionTowerVanishes
        (withExactBoundaryFiniteShadow T decideBoundary)) /\
      (ObstructionTowerVanishes
          (withExactBoundaryFiniteShadow T decideBoundary) <->
        FiniteTowerLayerShadowZero
          (canonicalTowerLayerShadow
            (withExactBoundaryFiniteShadow T decideBoundary))) /\
      (FiniteShadowTrivial
          (withExactBoundaryFiniteShadow T decideBoundary) <->
        H1Vanishes
          (withExactBoundaryFiniteShadow T decideBoundary)) /\
      (archSigStyleArtifactShadow
          (archSigStyleArtifactOfTower
            (withExactBoundaryFiniteShadow T decideBoundary)) =
        canonicalTowerLayerShadow
          (withExactBoundaryFiniteShadow T decideBoundary)) /\
      ArchSigStyleFiniteShadowAdequacy
        (withExactBoundaryFiniteShadow T decideBoundary)
        (archSigStyleArtifactOfTower
          (withExactBoundaryFiniteShadow T decideBoundary)) /\
      (forall assignment : SoundAllLayerObstructionAssignment,
        assignmentLayerShadow assignment
            (withExactBoundaryFiniteShadow T decideBoundary) =
          assignmentReadsShadow assignment
            (canonicalTowerLayerShadow
              (withExactBoundaryFiniteShadow T decideBoundary))) /\
      (forall (Obs : Type z)
          (observe :
            FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs),
        ShadowExtensionalTowerObservation observe ->
          (forall U,
            observe U =
              canonicalShadowFactor observe (canonicalTowerLayerShadow U)) /\
          (forall factor : FiniteTowerLayerShadow -> Obs,
            (forall U :
              FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
                observe U = factor (canonicalTowerLayerShadow U)) ->
              forall shadow,
                factor shadow =
                  canonicalShadowFactor observe shadow)) := by
  exact
    ⟨universalSemanticRepairObstructionTower_iff
        (withExactBoundaryFiniteShadow T decideBoundary)
        (exactShadowLayeredRepairAdequacy decideBoundary prism),
      by
        constructor
        · exact
            obstructionTowerVanishes_to_canonicalShadowZero
              (withExactBoundaryFiniteShadow T decideBoundary)
        · exact
            canonicalShadowZero_to_obstructionTowerVanishes
              (withExactBoundaryFiniteShadow T decideBoundary)
              (withExactBoundaryFiniteShadow_reflection T decideBoundary),
      withExactBoundaryFiniteShadow_h1_iff_shadow_zero T decideBoundary,
      archSigStyleArtifactOfTower_factors_through_tower
        (withExactBoundaryFiniteShadow T decideBoundary),
      canonicalArchSigStyleArtifactAdequacy
        (withExactBoundaryFiniteShadow T decideBoundary),
      fun assignment =>
        soundAllLayerAssignment_factors_through_tower assignment
          (withExactBoundaryFiniteShadow T decideBoundary),
      fun Obs observe extensional =>
        shadowExtensionalObservation_universalFactorization
          (Obs := Obs) observe extensional⟩

/-- Exact-shadow tower built from finite primitive-list completeness. -/
def withFiniteCertificateExactShadow
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    [DecidableEq T.C1]
    (prism : LayeredRepairDischargePrism T) :
    FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom :=
  withExactBoundaryFiniteShadow T
    (finiteBoundaryDecisionOfCertificate prism.boundary)

/--
Final finite/small target theorem package from concrete finite certificates.

Compared with `universalSemanticRepairTargetCompletion_package`, this version
does not take an arbitrary boundary decision procedure.  It constructs the
exact boundary decision from finite primitive-list completeness and decidable
cochain equality.
-/
theorem universalSemanticRepairTargetCompletion_package_of_finiteCertificate
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    [DecidableEq T.C1]
    (prism : LayeredRepairDischargePrism T) :
    (GlobalSemanticRepairCoherent
        (withFiniteCertificateExactShadow T prism) <->
      ObstructionTowerVanishes
        (withFiniteCertificateExactShadow T prism)) /\
      (ObstructionTowerVanishes
          (withFiniteCertificateExactShadow T prism) <->
        FiniteTowerLayerShadowZero
          (canonicalTowerLayerShadow
            (withFiniteCertificateExactShadow T prism))) /\
      (FiniteShadowTrivial
          (withFiniteCertificateExactShadow T prism) <->
        H1Vanishes
          (withFiniteCertificateExactShadow T prism)) /\
      (archSigStyleArtifactShadow
          (archSigStyleArtifactOfTower
            (withFiniteCertificateExactShadow T prism)) =
        canonicalTowerLayerShadow
          (withFiniteCertificateExactShadow T prism)) /\
      ArchSigStyleFiniteShadowAdequacy
        (withFiniteCertificateExactShadow T prism)
        (archSigStyleArtifactOfTower
          (withFiniteCertificateExactShadow T prism)) /\
      (forall assignment : SoundAllLayerObstructionAssignment,
        assignmentLayerShadow assignment
            (withFiniteCertificateExactShadow T prism) =
          assignmentReadsShadow assignment
            (canonicalTowerLayerShadow
              (withFiniteCertificateExactShadow T prism))) /\
      (forall (Obs : Type z)
          (observe :
            FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs),
        ShadowExtensionalTowerObservation observe ->
          (forall U,
            observe U =
              canonicalShadowFactor observe (canonicalTowerLayerShadow U)) /\
          (forall factor : FiniteTowerLayerShadow -> Obs,
            (forall U :
              FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
                observe U = factor (canonicalTowerLayerShadow U)) ->
              forall shadow,
                factor shadow =
                  canonicalShadowFactor observe shadow)) := by
  exact
    universalSemanticRepairTargetCompletion_package
      T (finiteBoundaryDecisionOfCertificate prism.boundary) prism

/-! ## Integrated sheaf / torsor / stack completion surface -/

/--
Integrated finite/small semantic repair obstruction theorem over the explicit
sheaf `H1`, pointed nonabelian torsor, and stacky `H2` envelopes.

This theorem keeps the material bridge data visible: first-layer semantic
faithfulness, nonabelian torsor descent, and stacky descent are supplied by
separate discharge/comparison certificates.  The statement does not take
`GlobalSemanticRepairCoherent`, tower vanishing, torsor triviality, stack
effectiveness, or finite-shadow reflection as hidden structure fields.
-/
theorem universalSemanticRepairSheafTorsorStackCompletion_package
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (sheafDischarge : SemanticRepairSheafH1ExactnessDischarge E)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    (torsorDischarge : NonabelianRepairTorsorDescentDischarge torsor)
    (torsorComparison : NonabelianTorsorTowerComparison E torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    (stackDischarge : StackyRepairDescentDischarge stack)
    (stackComparison : StackyH2TowerComparison E stack) :
    (SemanticRepairH1Zero E <-> H1Vanishes (toFiniteTower E)) /\
      (NonabelianRepairH1Zero torsor <->
        EffectiveNonabelianRepairDescent torsor) /\
      (StackyRepairH2Zero stack <->
        EffectiveStackyRepairDescent stack) /\
      (GlobalSemanticRepairCoherent (toFiniteTower E) <->
        SemanticRepairH1Zero E /\
          EffectiveNonabelianRepairDescent torsor /\
          StackyRepairH2Zero stack /\
          EffectiveStackyRepairDescent stack) /\
      (SemanticRepairH1Nonzero E ->
        Not (GlobalSemanticRepairCoherent (toFiniteTower E))) /\
      (NonabelianRepairH1Nonzero torsor ->
        Not (GlobalSemanticRepairCoherent (toFiniteTower E))) /\
      (StackyRepairH2Nonzero stack ->
        Not (GlobalSemanticRepairCoherent (toFiniteTower E))) /\
      (forall assignment : SoundAllLayerObstructionAssignment,
        assignmentLayerShadow assignment (toFiniteTower E) =
          assignmentReadsShadow assignment
            (canonicalTowerLayerShadow (toFiniteTower E))) /\
      (forall (Obs : Type s)
          (observe :
            FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs),
        ShadowExtensionalTowerObservation observe ->
          (forall U,
            observe U =
              canonicalShadowFactor observe (canonicalTowerLayerShadow U)) /\
          (forall factor : FiniteTowerLayerShadow -> Obs,
            (forall U :
              FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
                observe U = factor (canonicalTowerLayerShadow U)) ->
              forall shadow,
                factor shadow =
                  canonicalShadowFactor observe shadow)) := by
  refine
    ⟨(h1Vanishes_iff_sheafH1Zero_of_exactEnvelope E).symm,
      (effectiveNonabelianRepairDescent_iff_nonabelianH1Zero
        torsor torsorDischarge).symm,
      (effectiveStackyRepairDescent_iff_stackyH2Zero
        stack stackDischarge).symm,
      ?_,
      no_globalRepairCoherent_of_nonzero_sheafH1 E sheafDischarge,
      no_globalRepairCoherent_of_nonzero_nonabelianH1
        E sheafDischarge torsor torsorComparison,
      no_globalRepairCoherent_of_nonzero_stackyH2
        E sheafDischarge stack stackComparison,
      ?_,
      ?_⟩
  · constructor
    · intro hglobal
      have htower :
          ObstructionTowerVanishes (toFiniteTower E) :=
        globalRepairCoherent_forces_obstructionTowerVanishes
          (toFiniteTower E)
          (layeredAdequacy_of_sheafH1Discharge sheafDischarge)
          hglobal
      have hsheaf : SemanticRepairH1Zero E :=
        (h1Vanishes_iff_sheafH1Zero_of_exactEnvelope E).1 htower.1
      have htorsorTrivial : PointedTorsorTrivial torsor :=
        (towerNonabelianToken_iff_pointedTorsorTrivial
          torsorComparison).1 htower.2.1
      have htorsorEffective : EffectiveNonabelianRepairDescent torsor :=
        (pointedTorsorTrivial_iff_effectiveNonabelianRepairDescent
          torsor torsorDischarge).1 htorsorTrivial
      have hstackH2 : StackyRepairH2Zero stack :=
        (towerHigherToken_iff_stackyH2Zero
          stackComparison).1 htower.2.2.1
      have hstackEffective : EffectiveStackyRepairDescent stack :=
        (towerStackToken_iff_effectiveStackyRepairDescent
          stackComparison).1 htower.2.2.2
      exact ⟨hsheaf, htorsorEffective, hstackH2, hstackEffective⟩
    · intro hdata
      exact
        globalRepairCoherent_of_sheafH1_nonabelian_and_stackyDescent
          E sheafDischarge torsor torsorComparison stack stackComparison
          hdata.1 hdata.2.1 hdata.2.2.2
  · intro assignment
    exact
      soundAllLayerAssignment_factors_through_tower assignment
        (toFiniteTower E)
  · intro Obs observe extensional
    exact
      shadowExtensionalObservation_universalFactorization
        (Obs := Obs) observe extensional

/-! ## Comparison-free integrated layer tower -/

/--
Boolean token used by the integrated finite tower.

It is false exactly when the represented layer predicate holds.  This is a
finite decision procedure for a layer predicate, not a claim that the predicate
already holds for the selected repair data.
-/
def falseWhen
    (P : Prop)
    [decidableP : Decidable P] : Bool :=
  match decidableP with
  | isTrue _ => false
  | isFalse _ => true

theorem falseWhen_false_iff
    (P : Prop)
    [decidableP : Decidable P] :
    falseWhen P = false <-> P := by
  unfold falseWhen
  cases decidableP with
  | isTrue h =>
      change false = false <-> P
      constructor
      · intro _hfalse
        exact h
      · intro _h
        rfl
  | isFalse hnot =>
      change true = false <-> P
      constructor
      · intro hfalse
        cases hfalse
      · intro h
        exact False.elim (hnot h)

/--
The finite tower induced directly by a sheaf `H1` envelope, a pointed
nonabelian torsor, and a stacky `H2` envelope.

Unlike `universalSemanticRepairSheafTorsorStackCompletion_package`, this
construction does not require external tower comparison certificates.  The
nonabelian and stacky tower tokens are the finite decisions for the torsor and
stack descent predicates themselves.
-/
def toIntegratedSheafTorsorStackTower
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
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
  torsorObstruction := falseWhen (EffectiveNonabelianRepairDescent torsor)
  higherObstruction := falseWhen (StackyRepairH2Zero stack)
  stackObstruction := falseWhen (EffectiveStackyRepairDescent stack)
  finiteShadow := E.finiteShadow
  finiteShadow_boundary_zero := E.finiteShadow_boundary_zero
  sourceTraceToken := E.site.sourceTraceToken

theorem integratedTower_h1_iff_sheafH1Zero
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    H1Vanishes (toIntegratedSheafTorsorStackTower E torsor stack) <->
      SemanticRepairH1Zero E := by
  exact h1Vanishes_iff_sheafH1Zero_of_exactEnvelope E

theorem integratedTower_torsor_iff_effectiveNonabelianDescent
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    NonabelianTorsorTrivial
        (toIntegratedSheafTorsorStackTower E torsor stack) <->
      EffectiveNonabelianRepairDescent torsor := by
  change
    falseWhen (EffectiveNonabelianRepairDescent torsor) = false <->
      EffectiveNonabelianRepairDescent torsor
  exact falseWhen_false_iff (EffectiveNonabelianRepairDescent torsor)

theorem integratedTower_higher_iff_stackyH2Zero
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    HigherCoherenceVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack) <->
      StackyRepairH2Zero stack := by
  change
    falseWhen (StackyRepairH2Zero stack) = false <->
      StackyRepairH2Zero stack
  exact falseWhen_false_iff (StackyRepairH2Zero stack)

theorem integratedTower_stack_iff_effectiveStackyDescent
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    StackEffectivelyVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack) <->
      EffectiveStackyRepairDescent stack := by
  change
    falseWhen (EffectiveStackyRepairDescent stack) = false <->
      EffectiveStackyRepairDescent stack
  exact falseWhen_false_iff (EffectiveStackyRepairDescent stack)

theorem integratedTower_vanishes_iff_layers
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    ObstructionTowerVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack) <->
      SemanticRepairH1Zero E /\
        EffectiveNonabelianRepairDescent torsor /\
        StackyRepairH2Zero stack /\
        EffectiveStackyRepairDescent stack := by
  constructor
  · intro hvanishes
    exact
      ⟨(integratedTower_h1_iff_sheafH1Zero E torsor stack).1
          hvanishes.1,
        (integratedTower_torsor_iff_effectiveNonabelianDescent
          E torsor stack).1 hvanishes.2.1,
        (integratedTower_higher_iff_stackyH2Zero
          E torsor stack).1 hvanishes.2.2.1,
        (integratedTower_stack_iff_effectiveStackyDescent
          E torsor stack).1 hvanishes.2.2.2⟩
  · intro hlayers
    exact
      ⟨(integratedTower_h1_iff_sheafH1Zero E torsor stack).2
          hlayers.1,
        (integratedTower_torsor_iff_effectiveNonabelianDescent
          E torsor stack).2 hlayers.2.1,
        (integratedTower_higher_iff_stackyH2Zero
          E torsor stack).2 hlayers.2.2.1,
        (integratedTower_stack_iff_effectiveStackyDescent
          E torsor stack).2 hlayers.2.2.2⟩

def integratedLayeredRepairAdequacy
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (sheafDischarge : SemanticRepairSheafH1ExactnessDischarge E)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    LayeredRepairAdequacy
      (toIntegratedSheafTorsorStackTower E torsor stack) where
  semanticFaithful_of_boundary := by
    intro primitive hboundary
    exact sheafDischarge.semanticFaithful_of_boundary primitive hboundary
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

def sheafH1ExactnessDischarge_of_finiteBoundaryCertificate
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (certificate :
      FiniteBoundarySemanticClosureCertificate (toFiniteTower E)) :
    SemanticRepairSheafH1ExactnessDischarge E where
  semanticFaithful_of_boundary := by
    intro primitive hboundary
    exact
      boundarySemanticClosed_of_finiteBoundaryCertificate
        certificate hboundary

def sheafH1ExactnessDischarge_of_dischargePrism
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom}
    (prism : LayeredRepairDischargePrism (toFiniteTower E)) :
    SemanticRepairSheafH1ExactnessDischarge E :=
  sheafH1ExactnessDischarge_of_finiteBoundaryCertificate prism.boundary

/-! ## Finite decision certificates for layer predicates -/

/-- Listed effective nonabelian repair witnesses. -/
def ListedEffectiveNonabelianRepair
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) :
    List Repair -> Prop
  | [] => False
  | repair :: rest =>
      (torsor.effectiveRepair repair /\
        torsor.gauge repair = torsor.selectedTransition) \/
        ListedEffectiveNonabelianRepair torsor rest

def listedEffectiveNonabelianRepairDecision
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair)
    [DecidableEq Choice]
    [decidableEffective :
      forall repair, Decidable (torsor.effectiveRepair repair)] :
    (listed : List Repair) ->
      Decidable (ListedEffectiveNonabelianRepair torsor listed)
  | [] => isFalse (by intro h; exact h)
  | repair :: rest =>
      match decidableEffective repair with
      | isTrue heffective =>
          match decEq (torsor.gauge repair) torsor.selectedTransition with
          | isTrue hgauge => isTrue (Or.inl ⟨heffective, hgauge⟩)
          | isFalse hgaugeNot =>
              match listedEffectiveNonabelianRepairDecision torsor rest with
              | isTrue htail => isTrue (Or.inr htail)
              | isFalse htailNot =>
                  isFalse (by
                    intro hlisted
                    cases hlisted with
                    | inl hhead => exact hgaugeNot hhead.2
                    | inr htail => exact htailNot htail)
      | isFalse heffectiveNot =>
          match listedEffectiveNonabelianRepairDecision torsor rest with
          | isTrue htail => isTrue (Or.inr htail)
          | isFalse htailNot =>
              isFalse (by
                intro hlisted
                cases hlisted with
                | inl hhead => exact heffectiveNot hhead.1
                | inr htail => exact htailNot htail)

theorem listedEffectiveNonabelianRepair_sound
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair)
    {listed : List Repair} :
    ListedEffectiveNonabelianRepair torsor listed ->
      EffectiveNonabelianRepairDescent torsor := by
  intro hlisted
  induction listed with
  | nil =>
      exact False.elim hlisted
  | cons repair rest ih =>
      cases hlisted with
      | inl hhead =>
          exact ⟨repair, hhead.1, hhead.2⟩
      | inr htail =>
          exact ih htail

theorem listedEffectiveNonabelianRepair_of_mem
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair)
    {listed : List Repair}
    {repair : Repair}
    (hmem : repair ∈ listed)
    (heffective : torsor.effectiveRepair repair)
    (hgauge : torsor.gauge repair = torsor.selectedTransition) :
    ListedEffectiveNonabelianRepair torsor listed := by
  induction listed with
  | nil =>
      cases hmem
  | cons head rest ih =>
      cases hmem with
      | head =>
          exact Or.inl ⟨heffective, hgauge⟩
      | tail _ htail =>
          exact Or.inr (ih htail)

structure FiniteNonabelianRepairDecisionCertificate
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair) where
  repair_complete : forall repair, repair ∈ torsor.repairOrder

theorem listedEffectiveNonabelianRepair_complete_of_certificate
    {Choice : Type z}
    {Repair : Type r}
    {torsor : FinitePointedRepairTorsor Choice Repair}
    (certificate : FiniteNonabelianRepairDecisionCertificate torsor) :
    EffectiveNonabelianRepairDescent torsor ->
      ListedEffectiveNonabelianRepair torsor torsor.repairOrder := by
  intro heffective
  rcases heffective with ⟨repair, heff, hgauge⟩
  exact
    listedEffectiveNonabelianRepair_of_mem torsor
      (certificate.repair_complete repair) heff hgauge

def effectiveNonabelianRepairDescentDecisionOfCertificate
    {Choice : Type z}
    {Repair : Type r}
    (torsor : FinitePointedRepairTorsor Choice Repair)
    [DecidableEq Choice]
    [forall repair, Decidable (torsor.effectiveRepair repair)]
    (certificate : FiniteNonabelianRepairDecisionCertificate torsor) :
    Decidable (EffectiveNonabelianRepairDescent torsor) :=
  match
    listedEffectiveNonabelianRepairDecision torsor torsor.repairOrder with
  | isTrue hlisted =>
      isTrue (listedEffectiveNonabelianRepair_sound torsor hlisted)
  | isFalse hnotListed =>
      isFalse (by
        intro heffective
        exact hnotListed
          (listedEffectiveNonabelianRepair_complete_of_certificate
            certificate heffective))

/-- Listed stacky `H2` boundary witnesses. -/
def ListedStackyBoundary
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) :
    List Repair -> Prop
  | [] => False
  | repair :: rest =>
      stack.boundary2 repair = stack.selected2Cocycle \/
        ListedStackyBoundary stack rest

def listedStackyBoundaryDecision
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    [DecidableEq Coherence] :
    (listed : List Repair) -> Decidable (ListedStackyBoundary stack listed)
  | [] => isFalse (by intro h; exact h)
  | repair :: rest =>
      match decEq (stack.boundary2 repair) stack.selected2Cocycle with
      | isTrue hboundary => isTrue (Or.inl hboundary)
      | isFalse hboundaryNot =>
          match listedStackyBoundaryDecision stack rest with
          | isTrue htail => isTrue (Or.inr htail)
          | isFalse htailNot =>
              isFalse (by
                intro hlisted
                cases hlisted with
                | inl hhead => exact hboundaryNot hhead
                | inr htail => exact htailNot htail)

theorem listedStackyBoundary_sound
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    {listed : List Repair} :
    ListedStackyBoundary stack listed -> StackyCechB2 stack stack.selected2Cocycle := by
  intro hlisted
  induction listed with
  | nil =>
      exact False.elim hlisted
  | cons repair rest ih =>
      cases hlisted with
      | inl hhead =>
          exact ⟨repair, hhead⟩
      | inr htail =>
          exact ih htail

theorem listedStackyBoundary_of_mem
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    {listed : List Repair}
    {repair : Repair}
    (hmem : repair ∈ listed)
    (hboundary : stack.boundary2 repair = stack.selected2Cocycle) :
    ListedStackyBoundary stack listed := by
  induction listed with
  | nil =>
      cases hmem
  | cons head rest ih =>
      cases hmem with
      | head =>
          exact Or.inl hboundary
      | tail _ htail =>
          exact Or.inr (ih htail)

structure FiniteStackyRepairDecisionCertificate
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) where
  repair_complete : forall repair, repair ∈ stack.repairOrder

theorem listedStackyBoundary_complete_of_certificate
    {Coherence : Type z}
    {Repair : Type r}
    {stack : FiniteStackyRepairH2Envelope Coherence Repair}
    (certificate : FiniteStackyRepairDecisionCertificate stack) :
    StackyCechB2 stack stack.selected2Cocycle ->
      ListedStackyBoundary stack stack.repairOrder := by
  intro hboundary
  rcases hboundary with ⟨repair, hrepair⟩
  exact
    listedStackyBoundary_of_mem stack
      (certificate.repair_complete repair) hrepair

def stackyRepairH2ZeroDecisionOfCertificate
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    [DecidableEq Coherence]
    (certificate : FiniteStackyRepairDecisionCertificate stack) :
    Decidable (StackyRepairH2Zero stack) :=
  match listedStackyBoundaryDecision stack stack.repairOrder with
  | isTrue hlisted =>
      isTrue
        ⟨stack.selected2_cocycle,
          listedStackyBoundary_sound stack hlisted⟩
  | isFalse hnotListed =>
      isFalse (by
        intro hzero
        exact hnotListed
          (listedStackyBoundary_complete_of_certificate
            certificate hzero.2))

/-- Listed effective stacky repair witnesses. -/
def ListedEffectiveStackyRepair
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair) :
    List Repair -> Prop
  | [] => False
  | repair :: rest =>
      (stack.effectiveRepair repair /\
        stack.boundary2 repair = stack.selected2Cocycle) \/
        ListedEffectiveStackyRepair stack rest

def listedEffectiveStackyRepairDecision
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    [DecidableEq Coherence]
    [decidableEffective :
      forall repair, Decidable (stack.effectiveRepair repair)] :
    (listed : List Repair) ->
      Decidable (ListedEffectiveStackyRepair stack listed)
  | [] => isFalse (by intro h; exact h)
  | repair :: rest =>
      match decidableEffective repair with
      | isTrue heffective =>
          match decEq (stack.boundary2 repair) stack.selected2Cocycle with
          | isTrue hboundary => isTrue (Or.inl ⟨heffective, hboundary⟩)
          | isFalse hboundaryNot =>
              match listedEffectiveStackyRepairDecision stack rest with
              | isTrue htail => isTrue (Or.inr htail)
              | isFalse htailNot =>
                  isFalse (by
                    intro hlisted
                    cases hlisted with
                    | inl hhead => exact hboundaryNot hhead.2
                    | inr htail => exact htailNot htail)
      | isFalse heffectiveNot =>
          match listedEffectiveStackyRepairDecision stack rest with
          | isTrue htail => isTrue (Or.inr htail)
          | isFalse htailNot =>
              isFalse (by
                intro hlisted
                cases hlisted with
                | inl hhead => exact heffectiveNot hhead.1
                | inr htail => exact htailNot htail)

theorem listedEffectiveStackyRepair_sound
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    {listed : List Repair} :
    ListedEffectiveStackyRepair stack listed ->
      EffectiveStackyRepairDescent stack := by
  intro hlisted
  induction listed with
  | nil =>
      exact False.elim hlisted
  | cons repair rest ih =>
      cases hlisted with
      | inl hhead =>
          exact ⟨repair, hhead.1, hhead.2⟩
      | inr htail =>
          exact ih htail

theorem listedEffectiveStackyRepair_of_mem
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    {listed : List Repair}
    {repair : Repair}
    (hmem : repair ∈ listed)
    (heffective : stack.effectiveRepair repair)
    (hboundary : stack.boundary2 repair = stack.selected2Cocycle) :
    ListedEffectiveStackyRepair stack listed := by
  induction listed with
  | nil =>
      cases hmem
  | cons head rest ih =>
      cases hmem with
      | head =>
          exact Or.inl ⟨heffective, hboundary⟩
      | tail _ htail =>
          exact Or.inr (ih htail)

theorem listedEffectiveStackyRepair_complete_of_certificate
    {Coherence : Type z}
    {Repair : Type r}
    {stack : FiniteStackyRepairH2Envelope Coherence Repair}
    (certificate : FiniteStackyRepairDecisionCertificate stack) :
    EffectiveStackyRepairDescent stack ->
      ListedEffectiveStackyRepair stack stack.repairOrder := by
  intro heffective
  rcases heffective with ⟨repair, heff, hboundary⟩
  exact
    listedEffectiveStackyRepair_of_mem stack
      (certificate.repair_complete repair) heff hboundary

def effectiveStackyRepairDescentDecisionOfCertificate
    {Coherence : Type z}
    {Repair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence Repair)
    [DecidableEq Coherence]
    [forall repair, Decidable (stack.effectiveRepair repair)]
    (certificate : FiniteStackyRepairDecisionCertificate stack) :
    Decidable (EffectiveStackyRepairDescent stack) :=
  match
    listedEffectiveStackyRepairDecision stack stack.repairOrder with
  | isTrue hlisted =>
      isTrue (listedEffectiveStackyRepair_sound stack hlisted)
  | isFalse hnotListed =>
      isFalse (by
        intro heffective
        exact hnotListed
          (listedEffectiveStackyRepair_complete_of_certificate
            certificate heffective))

theorem integratedTower_globalCoherent_iff_layers
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (sheafDischarge : SemanticRepairSheafH1ExactnessDischarge E)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    GlobalSemanticRepairCoherent
        (toIntegratedSheafTorsorStackTower E torsor stack) <->
      SemanticRepairH1Zero E /\
        EffectiveNonabelianRepairDescent torsor /\
        StackyRepairH2Zero stack /\
        EffectiveStackyRepairDescent stack := by
  constructor
  · intro hglobal
    exact
      (integratedTower_vanishes_iff_layers E torsor stack).1
        (globalRepairCoherent_forces_obstructionTowerVanishes
          (toIntegratedSheafTorsorStackTower E torsor stack)
          (integratedLayeredRepairAdequacy sheafDischarge torsor stack)
          hglobal)
  · intro hlayers
    exact
      globalRepairCoherent_of_obstructionTowerVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack)
        (integratedLayeredRepairAdequacy sheafDischarge torsor stack)
        ((integratedTower_vanishes_iff_layers E torsor stack).2 hlayers)

theorem universalSemanticRepairIntegratedLayerCompletion_package
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (sheafDischarge : SemanticRepairSheafH1ExactnessDischarge E)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    (ObstructionTowerVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack) <->
      SemanticRepairH1Zero E /\
        EffectiveNonabelianRepairDescent torsor /\
        StackyRepairH2Zero stack /\
        EffectiveStackyRepairDescent stack) /\
      (GlobalSemanticRepairCoherent
          (toIntegratedSheafTorsorStackTower E torsor stack) <->
        SemanticRepairH1Zero E /\
          EffectiveNonabelianRepairDescent torsor /\
          StackyRepairH2Zero stack /\
          EffectiveStackyRepairDescent stack) /\
      (forall assignment : SoundAllLayerObstructionAssignment,
        assignmentLayerShadow assignment
            (toIntegratedSheafTorsorStackTower E torsor stack) =
          assignmentReadsShadow assignment
            (canonicalTowerLayerShadow
              (toIntegratedSheafTorsorStackTower E torsor stack))) /\
      (forall (Obs : Type s)
          (observe :
            FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs),
        ShadowExtensionalTowerObservation observe ->
          (forall U,
            observe U =
              canonicalShadowFactor observe (canonicalTowerLayerShadow U)) /\
          (forall factor : FiniteTowerLayerShadow -> Obs,
            (forall U :
              FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
                observe U = factor (canonicalTowerLayerShadow U)) ->
              forall shadow,
                factor shadow =
                  canonicalShadowFactor observe shadow)) := by
  exact
    ⟨integratedTower_vanishes_iff_layers E torsor stack,
      integratedTower_globalCoherent_iff_layers
        E sheafDischarge torsor stack,
      fun assignment =>
        soundAllLayerAssignment_factors_through_tower assignment
          (toIntegratedSheafTorsorStackTower E torsor stack),
      fun Obs observe extensional =>
        shadowExtensionalObservation_universalFactorization
          (Obs := Obs) observe extensional⟩

def toIntegratedSheafTorsorStackTowerOfFiniteCertificates
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (boundaryCertificate :
      FiniteBoundarySemanticClosureCertificate (toFiniteTower E))
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (torsor.effectiveRepair repair)]
    (torsorCertificate :
      FiniteNonabelianRepairDecisionCertificate torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    [DecidableEq Coherence]
    [forall repair, Decidable (stack.effectiveRepair repair)]
    (stackCertificate : FiniteStackyRepairDecisionCertificate stack) :
    FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom := by
  let _boundaryCertificate := boundaryCertificate
  letI : Decidable (EffectiveNonabelianRepairDescent torsor) :=
    effectiveNonabelianRepairDescentDecisionOfCertificate
      torsor torsorCertificate
  letI : Decidable (StackyRepairH2Zero stack) :=
    stackyRepairH2ZeroDecisionOfCertificate
      stack stackCertificate
  letI : Decidable (EffectiveStackyRepairDescent stack) :=
    effectiveStackyRepairDescentDecisionOfCertificate
      stack stackCertificate
  exact toIntegratedSheafTorsorStackTower E torsor stack

theorem universalSemanticRepairIntegratedLayerCompletion_package_of_finiteCertificates
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (boundaryCertificate :
      FiniteBoundarySemanticClosureCertificate (toFiniteTower E))
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (torsor.effectiveRepair repair)]
    (torsorCertificate :
      FiniteNonabelianRepairDecisionCertificate torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    [DecidableEq Coherence]
    [forall repair, Decidable (stack.effectiveRepair repair)]
    (stackCertificate : FiniteStackyRepairDecisionCertificate stack) :
    (ObstructionTowerVanishes
        (toIntegratedSheafTorsorStackTowerOfFiniteCertificates
          E boundaryCertificate torsor torsorCertificate stack stackCertificate) <->
      SemanticRepairH1Zero E /\
        EffectiveNonabelianRepairDescent torsor /\
        StackyRepairH2Zero stack /\
        EffectiveStackyRepairDescent stack) /\
      (GlobalSemanticRepairCoherent
          (toIntegratedSheafTorsorStackTowerOfFiniteCertificates
            E boundaryCertificate torsor torsorCertificate stack stackCertificate) <->
        SemanticRepairH1Zero E /\
          EffectiveNonabelianRepairDescent torsor /\
          StackyRepairH2Zero stack /\
          EffectiveStackyRepairDescent stack) /\
      (forall assignment : SoundAllLayerObstructionAssignment,
        assignmentLayerShadow assignment
            (toIntegratedSheafTorsorStackTowerOfFiniteCertificates
              E boundaryCertificate torsor torsorCertificate stack stackCertificate) =
          assignmentReadsShadow assignment
            (canonicalTowerLayerShadow
              (toIntegratedSheafTorsorStackTowerOfFiniteCertificates
                E boundaryCertificate torsor torsorCertificate stack stackCertificate))) /\
      (forall (Obs : Type s)
          (observe :
            FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs),
        ShadowExtensionalTowerObservation observe ->
          (forall U,
            observe U =
              canonicalShadowFactor observe (canonicalTowerLayerShadow U)) /\
          (forall factor : FiniteTowerLayerShadow -> Obs,
            (forall U :
              FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
                observe U = factor (canonicalTowerLayerShadow U)) ->
              forall shadow,
                factor shadow =
                  canonicalShadowFactor observe shadow)) := by
  letI : Decidable (EffectiveNonabelianRepairDescent torsor) :=
    effectiveNonabelianRepairDescentDecisionOfCertificate
      torsor torsorCertificate
  letI : Decidable (StackyRepairH2Zero stack) :=
    stackyRepairH2ZeroDecisionOfCertificate
      stack stackCertificate
  letI : Decidable (EffectiveStackyRepairDescent stack) :=
    effectiveStackyRepairDescentDecisionOfCertificate
      stack stackCertificate
  simpa [toIntegratedSheafTorsorStackTowerOfFiniteCertificates]
    using
      universalSemanticRepairIntegratedLayerCompletion_package
        E
        (sheafH1ExactnessDischarge_of_finiteBoundaryCertificate
          boundaryCertificate)
        torsor stack

end SemanticRepairTargetCompletion
end QualitySurface
end Formal.AG.Research
