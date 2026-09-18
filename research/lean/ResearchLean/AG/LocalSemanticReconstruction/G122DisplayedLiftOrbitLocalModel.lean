import ResearchLean.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldCanonicalSectionSourceObligation
import Formal.Util.AssertStandardAxioms

/-!
# Local reconstruction of the displayed G-122 lift orbit

For every normalized bottom comparison, the displayed source C2 fragment acts
simply transitively on the canonical lift's actual two-point orbit.  This file
constructs source-to-orbit assembly, proves injectivity, surjectivity, unique
source readback, and compatibility with source multiplication and the
opposite-kernel action.

At normalized identity the construction agrees with the existing source lift.
It is then combined with the primitive fixed-comparison reconstruction into
one product equivalence, so comparison reading and displayed-lift reading have
both inverse laws on one surface.

The result covers only the accepted displayed C2 subgroup and its orbit.  It
does not classify the full comparison group, the full restriction kernel, the
full lift fiber, or arbitrary expanded G-122 morphisms.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FiniteAxisFoldBottomRestrictionKernel
open AAT.AG.RealizationReconstruction.FiniteAxisFoldBottomKernelInvolution
open AAT.AG.RealizationReconstruction.FiniteAxisFoldBottomKernelOrbit
open AAT.AG.RealizationReconstruction.FiniteAxisFoldDisplayedKernelEquiv
open AAT.AG.RealizationReconstruction.FiniteAxisFoldCanonicalSectionSourceObligation
open TransportCoherence FullGeometryNormalization

namespace G122DisplayedLiftOrbitLocalModel

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 500000

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance displayedLiftOrbitAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The actual bottom-qualified lift fiber over a normalized comparison. -/
abbrev LiftFiber (t : NormalizedBottomComparison) :=
  AuthoredExactCanonicalBottomComparisonLiftFiber
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible t

/-- The orbit of the canonical lift under the accepted displayed involution. -/
def DisplayedOrbit (t : NormalizedBottomComparison) :=
  { lift : LiftFiber t //
    lift ∈ MulAction.orbit displayedInvolutionSubgroup (canonicalLift t) }

/-- Evaluate a source C2 term in the opposite displayed subgroup that acts on
the lift fiber. -/
noncomputable def sourceActingElement (g : sourceSubgroup) :
    displayedInvolutionSubgroup := by
  refine ⟨MulOpposite.op (toActual g).1, ?_⟩
  rcases g.property with identity | generator
  · have g_eq : g = 1 := Subtype.ext identity
    subst g
    exact Or.inl (by simp [toActual])
  · have g_eq : g = sourceGenerator := Subtype.ext generator
    subst g
    exact Or.inr (by
      simp [toActual, sourceGenerator, actualGenerator,
        ambientComparisonElement_ne_one])

/-- The source identity evaluates to the acting identity. -/
theorem sourceActingElement_one : sourceActingElement 1 = 1 := by
  apply Subtype.ext
  simp [sourceActingElement, toActual]

/-- The source generator evaluates to the displayed acting involution. -/
theorem sourceActingElement_generator :
    sourceActingElement sourceGenerator =
      ⟨MulOpposite.op element, Or.inr rfl⟩ := by
  apply Subtype.ext
  simp [sourceActingElement, toActual, sourceGenerator, actualGenerator,
    ambientComparisonElement_ne_one]

/-- Assemble a source C2 term into the displayed orbit over `t`. -/
noncomputable def assembleOrbit (t : NormalizedBottomComparison)
    (g : sourceSubgroup) : DisplayedOrbit t :=
  ⟨sourceActingElement g • canonicalLift t,
    MulAction.mem_orbit _ _⟩

/-- Orbit assembly sends source identity to the canonical lift. -/
theorem assembleOrbit_one (t : NormalizedBottomComparison) :
    assembleOrbit t 1 = ⟨canonicalLift t, by
      exact MulAction.mem_orbit_self
        (M := displayedInvolutionSubgroup) (canonicalLift t)⟩ := by
  apply Subtype.ext
  simp [assembleOrbit, sourceActingElement_one]

/-- Orbit assembly sends the source generator to the shifted lift. -/
theorem assembleOrbit_generator (t : NormalizedBottomComparison) :
    (assembleOrbit t sourceGenerator).1 = shiftedLift t := by
  change (sourceActingElement sourceGenerator : displayedInvolutionSubgroup) •
      canonicalLift t = shiftedLift t
  rw [sourceActingElement_generator]
  rfl

/-- Distinct source C2 terms assemble to distinct orbit lifts. -/
theorem assembleOrbit_injective (t : NormalizedBottomComparison) :
    Function.Injective (assembleOrbit t) := by
  intro first second equality
  rcases first.property with firstId | firstGen <;>
    rcases second.property with secondId | secondGen
  · exact Subtype.ext (firstId.trans secondId.symm)
  · exfalso
    have first_eq : first = 1 := Subtype.ext firstId
    have second_eq : second = sourceGenerator := Subtype.ext secondGen
    subst first; subst second
    have underlying := congrArg Subtype.val equality
    rw [assembleOrbit_generator] at underlying
    have oneUnderlying := congrArg Subtype.val (assembleOrbit_one t)
    exact shiftedLift_ne_canonicalLift t (underlying.symm.trans oneUnderlying)
  · exfalso
    have first_eq : first = sourceGenerator := Subtype.ext firstGen
    have second_eq : second = 1 := Subtype.ext secondId
    subst first; subst second
    have underlying := congrArg Subtype.val equality
    rw [assembleOrbit_generator] at underlying
    have oneUnderlying := congrArg Subtype.val (assembleOrbit_one t)
    exact shiftedLift_ne_canonicalLift t (underlying.trans oneUnderlying)
  · exact Subtype.ext (firstGen.trans secondGen.symm)

/-- Every lift in the displayed orbit is assembled by a source C2 term. -/
theorem assembleOrbit_surjective (t : NormalizedBottomComparison) :
    Function.Surjective (assembleOrbit t) := by
  intro lift
  have membership : lift.1 ∈
      (canonicalShiftedPair t : Set (LiftFiber t)) := by
    rw [← orbit_canonicalLift_eq_pair]
    exact lift.2
  simp only [canonicalShiftedPair, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at membership
  rcases membership with canonical | shifted
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [canonical]
    exact congrArg Subtype.val (assembleOrbit_one t)
  · refine ⟨sourceGenerator, ?_⟩
    apply Subtype.ext
    rw [shifted]
    exact assembleOrbit_generator t

/-- The source C2 fragment is equivalent to the displayed lift orbit over
every normalized bottom comparison. -/
noncomputable def sourceOrbitEquiv (t : NormalizedBottomComparison) :
    sourceSubgroup ≃ DisplayedOrbit t :=
  Equiv.ofBijective (assembleOrbit t)
    ⟨assembleOrbit_injective t, assembleOrbit_surjective t⟩

/-- Source multiplication becomes the opposite-order multiplication required
by the right action on lifts. -/
theorem sourceActingElement_mul (a b : sourceSubgroup) :
    sourceActingElement (a * b) =
      sourceActingElement b * sourceActingElement a := by
  apply Subtype.ext
  change MulOpposite.op (toActual (a * b)).1 =
    MulOpposite.op (toActual b).1 * MulOpposite.op (toActual a).1
  rw [toActual_mul]
  rfl

/-- Assembly intertwines source multiplication with the displayed lift
action, with the order reversal forced by the opposite kernel action. -/
theorem assembleOrbit_mul (t : NormalizedBottomComparison)
    (a b : sourceSubgroup) :
    (assembleOrbit t (a * b)).1 =
      sourceActingElement b • (assembleOrbit t a).1 := by
  change sourceActingElement (a * b) • canonicalLift t =
    sourceActingElement b •
      (sourceActingElement a • canonicalLift t)
  calc
    sourceActingElement (a * b) • canonicalLift t =
        (sourceActingElement b * sourceActingElement a) •
          canonicalLift t := congrArg
            (fun acting : displayedInvolutionSubgroup =>
              acting • canonicalLift t) (sourceActingElement_mul a b)
    _ = sourceActingElement b •
        (sourceActingElement a • canonicalLift t) := mul_smul _ _ _

/-- Every displayed-orbit lift has a unique source C2 term. -/
theorem existsUnique_source_of_orbit (t : NormalizedBottomComparison)
    (lift : DisplayedOrbit t) :
    ∃! g : sourceSubgroup, assembleOrbit t g = lift := by
  rcases assembleOrbit_surjective t lift with ⟨g, equality⟩
  refine ⟨g, equality, ?_⟩
  intro candidate candidateEquality
  exact assembleOrbit_injective t (candidateEquality.trans equality.symm)

/-- At normalized identity, the orbit assembly is the previously constructed
source-evaluated lift. -/
theorem assembleOrbit_atOne_eq_sourceLiftAtOne (g : sourceSubgroup) :
    (assembleOrbit (1 : NormalizedBottomComparison) g).1 =
      sourceLiftAtOne g := by
  rcases g.property with identity | generator
  · have g_eq : g = 1 := Subtype.ext identity
    subst g
    exact (congrArg Subtype.val
      (assembleOrbit_one (1 : NormalizedBottomComparison))).trans
        sourceLiftAtOne_identity.symm
  · have g_eq : g = sourceGenerator := Subtype.ext generator
    subst g
    exact (assembleOrbit_generator (1 : NormalizedBottomComparison)).trans
      sourceLiftAtOne_sourceGenerator.symm

open G122FixedComparisonLocalSlice G122PrimitiveComparisonProbe

/-- The fixed comparison image paired with the displayed identity-lift orbit. -/
abbrev CombinedSemanticSurface :=
  SemanticImage × DisplayedOrbit (1 : NormalizedBottomComparison)

/-- The corresponding primitive comparison value and source C2 syntax. -/
abbrev CombinedLocalSurface := LocalValue × sourceSubgroup

/-- Read both the primitive fixed comparison and its displayed lift orbit. -/
noncomputable def combinedRead (input : CombinedSemanticSurface) :
    CombinedLocalSurface :=
  (primitiveRead input.1,
    (sourceOrbitEquiv (1 : NormalizedBottomComparison)).symm input.2)

/-- Assemble the fixed comparison and displayed source lift together. -/
noncomputable def combinedAssemble (input : CombinedLocalSurface) :
    CombinedSemanticSurface :=
  (assemble input.1,
    sourceOrbitEquiv (1 : NormalizedBottomComparison) input.2)

/-- Reading after combined assembly is the identity on the local product. -/
@[simp] theorem combinedRead_assemble (input : CombinedLocalSurface) :
    combinedRead (combinedAssemble input) = input := by
  rcases input with ⟨value, source⟩
  simp [combinedRead, combinedAssemble]

/-- Combined assembly after reading recovers the whole semantic product. -/
@[simp] theorem combinedAssemble_read (input : CombinedSemanticSurface) :
    combinedAssemble (combinedRead input) = input := by
  rcases input with ⟨morphism, lift⟩
  simp [combinedRead, combinedAssemble]

/-- The primitive fixed comparison and its displayed lift orbit are jointly
equivalent to their finite local syntax. -/
noncomputable def combinedSemanticEquivLocal :
    CombinedSemanticSurface ≃ CombinedLocalSurface where
  toFun := combinedRead
  invFun := combinedAssemble
  left_inv := combinedAssemble_read
  right_inv := combinedRead_assemble

end
end G122DisplayedLiftOrbitLocalModel
end AAT.AG.LocalSemanticReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel
