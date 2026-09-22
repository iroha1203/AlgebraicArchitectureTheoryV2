import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.CategoryTheory.SingleObj
import ResearchLean.AG.TransportCoherence.ArbitraryObstruction
import ResearchLean.AG.TransportCoherence.FiniteWitnesses

/-!
# Nonvacuity witnesses for arbitrary-functor transport obstruction

This module supplies positive and negative instances for the predicates added
in `ArbitraryObstruction`.  The positive disk has an explicit absorbing edge
choice.  The negative double diamond has two incompatible authored comparisons.
Both are transported through the proved package-fiber equivalence, so they are
actual instances of the arbitrary-functor definitions rather than restatements
of the package-specific conclusions.

A one-object groupoid over the terminal category realizes the manuscript's
two-edge noncommutative calculation with actual `LiftData`, reselections, and
`pathReselectionTransition`; the `S₃` instance witnesses dependence on the
current second-edge choice.

A second double diamond with two identity authored comparisons supplies a
nonempty positive 3-cell syzygy.  Thus positive syzygy compatibility is not
obtained from an empty family of 3-cells.
-/

namespace AAT.AG.TransportCoherence.Arbitrary.Witnesses

universe u

open CategoryTheory
open AtomFoundation
open AAT.AG.TransportCoherence

/-! ## The two-edge one-object groupoid calculation -/

/-- One vertex, two loop edges, and no declared faces. -/
abbrev twoLoopPresentation : FiniteTransportTwoPresentation.{0} where
  Vertex := Unit
  vertexFintype := inferInstance
  Edge := fun _ _ => Bool
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Empty
  twoCellFintype := inferInstance
  twoSource := fun cell => nomatch cell
  twoTarget := fun cell => nomatch cell
  twoLeft := fun cell => nomatch cell
  twoRight := fun cell => nomatch cell

/-- The functor from a one-object groupoid to the terminal category. -/
def singleObjToTerminal (H : Type u) [Group H] :
    SingleObj H ⥤ Discrete PUnit :=
  (Functor.const (SingleObj H)).obj (Discrete.mk PUnit.unit)

/-- Identify group elements with automorphisms of the unique object. -/
def singleObjAutEquiv (H : Type u) [Group H] :
    H ≃* Aut (SingleObj.star H) :=
  toUnits.trans (Units.toAut H)

/-- Every automorphism in the one-object model lies over the terminal identity. -/
def singleObjFiberAutEquiv (H : Type u) [Group H] :
    H ≃* FiberAut (singleObjToTerminal H) (SingleObj.star H) where
  toFun element :=
    ⟨singleObjAutEquiv H element, Subsingleton.elim _ _⟩
  invFun automorphism := (singleObjAutEquiv H).symm automorphism.1
  left_inv element := (singleObjAutEquiv H).left_inv element
  right_inv automorphism := by
    apply Subtype.ext
    exact (singleObjAutEquiv H).right_inv automorphism.1
  map_mul' left right := by
    apply Subtype.ext
    exact map_mul (singleObjAutEquiv H) left right

/-- Both initial loop-edge lifts are identities, as in the manuscript model. -/
noncomputable def twoLoopLiftData (H : Type u) [Group H] :
    LiftData twoLoopPresentation (singleObjToTerminal H) where
  object := fun _ => SingleObj.star H
  edgeBase := fun _ => 𝟙 _
  edgeLift := fun _ => 𝟙 _
  edgeStrong := by
    intro i j edge
    letI : (singleObjToTerminal H).IsHomLift
        (𝟙 ((singleObjToTerminal H).obj (SingleObj.star H)))
        (Iso.refl (SingleObj.star H)).hom :=
      CategoryTheory.IsHomLift.id rfl
    exact CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      (singleObjToTerminal H)
      (𝟙 ((singleObjToTerminal H).obj (SingleObj.star H)))
      (Iso.refl (SingleObj.star H))

/-- Edge values `(a₁,a₂)` as an actual reselection of the two loop lifts. -/
def twoLoopReselection (H : Type u) [Group H] (first second : H) :
    EdgeReselection (twoLoopLiftData H) :=
  fun _ _ edge =>
    singleObjFiberAutEquiv H (if edge then second else first)

/-- The path that traverses loop edge 1 and then loop edge 2. -/
def twoLoopPath : twoLoopPresentation.Path Unit.unit Unit.unit :=
  @PresentedPath.cons Unit (fun _ _ => Bool) Unit.unit Unit.unit Unit.unit
    false
    (@PresentedPath.cons Unit (fun _ _ => Bool)
      Unit.unit Unit.unit Unit.unit true
      (@PresentedPath.nil Unit (fun _ _ => Bool) Unit.unit))

/-- The actual reselected path lift is `a₂a₁`. -/
theorem twoLoop_reselectedPathLift
    (H : Type u) [Group H] (a₁ a₂ : H) :
    reselectedPathLift (twoLoopLiftData H)
        (twoLoopReselection H a₁ a₂) twoLoopPath =
      FiberAut.hom (singleObjFiberAutEquiv H (a₂ * a₁)) := by
  simpa only [twoLoopPath, twoLoopReselection, Bool.false_eq_true,
      if_false, if_true, map_mul] using
    (reselectedPathLift_two_edges (twoLoopLiftData H)
      (twoLoopReselection H a₁ a₂) false true rfl rfl)

/-- After reselection by `(b₁,b₂)`, the actual path lift is `b₂a₂b₁a₁`. -/
theorem twoLoop_reselectedPathLift_mul
    (H : Type u) [Group H] (a₁ a₂ b₁ b₂ : H) :
    reselectedPathLift (twoLoopLiftData H)
        (twoLoopReselection H b₁ b₂ * twoLoopReselection H a₁ a₂)
        twoLoopPath =
      FiberAut.hom
        (singleObjFiberAutEquiv H (b₂ * a₂ * b₁ * a₁)) := by
  simpa only [twoLoopPath, twoLoopReselection, Bool.false_eq_true,
      if_false, if_true, map_mul] using
    (reselectedPathLift_two_edges_mul (twoLoopLiftData H)
      (twoLoopReselection H a₁ a₂) (twoLoopReselection H b₁ b₂)
      false true rfl rfl)

/-- The actual endpoint transition in the model is `b₂a₂b₁a₂⁻¹`. -/
theorem twoLoop_pathReselectionTransition
    (H : Type u) [Group H] (a₁ a₂ b₁ b₂ : H) :
    pathReselectionTransition (twoLoopLiftData H)
        (twoLoopReselection H a₁ a₂)
        (twoLoopReselection H b₁ b₂) twoLoopPath =
      singleObjFiberAutEquiv H (b₂ * a₂ * b₁ * a₂⁻¹) := by
  simpa only [twoLoopPath, twoLoopReselection, Bool.false_eq_true,
      if_false, if_true, map_mul, map_inv] using
    (pathReselectionTransition_two_edges (twoLoopLiftData H)
      (twoLoopReselection H a₁ a₂) (twoLoopReselection H b₁ b₂)
      false true rfl rfl)

/-- In the concrete `S₃` model, the actual transition changes with `a₂`. -/
theorem finThree_twoLoopTransition_depends_on_current :
    let b₁ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let b₂ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    let a₂ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
    pathReselectionTransition
        (twoLoopLiftData (Equiv.Perm (Fin 3)))
        (twoLoopReselection (Equiv.Perm (Fin 3)) 1 a₂)
        (twoLoopReselection (Equiv.Perm (Fin 3)) b₁ b₂) twoLoopPath ≠
      pathReselectionTransition
        (twoLoopLiftData (Equiv.Perm (Fin 3)))
        (twoLoopReselection (Equiv.Perm (Fin 3)) 1 1)
        (twoLoopReselection (Equiv.Perm (Fin 3)) b₁ b₂) twoLoopPath := by
  dsimp
  rw [twoLoop_pathReselectionTransition,
    twoLoop_pathReselectionTransition]
  exact (singleObjFiberAutEquiv (Equiv.Perm (Fin 3))).injective.ne
    finThree_twoEdgeTransition_depends_on_current

/-! ## Coherence and syzygy nonvacuity witnesses -/

/-- The package single disk gives a concrete coherent arbitrary-functor coordinate. -/
theorem packageSingleDisk_coherentAt
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    Arbitrary.CoherentAt (Arbitrary.packageTransportData data)
      (Arbitrary.packageEdgeReselection data.lift
        (singleDiskAbsorbingReselection data)) :=
  (Arbitrary.package_coherentAt_iff data
    (singleDiskAbsorbingReselection data)).mpr
      (singleDisk_coherentAt_absorbingReselection data)

/-- The package single disk is a positive coherentizability instance. -/
theorem packageSingleDisk_coherentizable
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    Arbitrary.Coherentizable (Arbitrary.packageTransportData data) :=
  (Arbitrary.package_coherentizable_iff data).mpr
    (singleDisk_coherentizable data)

/-- The package single disk is a positive obstruction-vanishing instance. -/
theorem packageSingleDisk_obstruction_vanishes
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    Arbitrary.TransportObstructionVanishes
      (Arbitrary.packageTransportData data) :=
  (Arbitrary.package_transportObstructionVanishes_iff data).mpr
    (singleDisk_obstruction_vanishes data)

/-- The concrete double diamond is not coherent at the mapped identity coordinate. -/
theorem packageFiniteDoubleDiamond_not_coherentAt_identity :
    ¬ Arbitrary.CoherentAt
      (Arbitrary.packageTransportData finiteDoubleDiamondData)
      (Arbitrary.packageEdgeReselection finiteDoubleDiamondData.lift 1) := by
  intro coherent
  exact finiteDoubleDiamond_not_coherentizable
    ⟨1, (Arbitrary.package_coherentAt_iff
      finiteDoubleDiamondData 1).mp coherent⟩

/-- The concrete double diamond is a negative coherentizability instance. -/
theorem packageFiniteDoubleDiamond_not_coherentizable :
    ¬ Arbitrary.Coherentizable
      (Arbitrary.packageTransportData finiteDoubleDiamondData) := by
  intro coherentizable
  exact finiteDoubleDiamond_not_coherentizable
    ((Arbitrary.package_coherentizable_iff
      finiteDoubleDiamondData).mp coherentizable)

/-- The concrete double diamond is a negative obstruction-vanishing instance. -/
theorem packageFiniteDoubleDiamond_obstruction_does_not_vanish :
    ¬ Arbitrary.TransportObstructionVanishes
      (Arbitrary.packageTransportData finiteDoubleDiamondData) := by
  intro vanishes
  exact finiteDoubleDiamond_obstruction_does_not_vanish
    ((Arbitrary.package_transportObstructionVanishes_iff
      finiteDoubleDiamondData).mp vanishes)

/--
The double-diamond geometry with both authored face comparisons set to the
identity.

Implementation notes: this deliberately reuses the existing nonidentity edge
lifts and base equalities.  Only the authored comparison input is changed, so
the witness tests the comparison equations rather than replacing the geometry
by a terminal or singleton presentation.  The alternative empty-3-cell disk is
not used because it would make syzygy compatibility vacuous.
-/
noncomputable def coherentDoubleDiamondData :
    AdmissibleTransportData
      (doubleDiamondPresentation FiniteModel.carrier.Atom)
      FiniteModel.carrier where
  lift := finiteDoubleDiamondLiftData
  twoCellBase := finiteDoubleDiamondData.twoCellBase
  comparator := fun _ => 1

/-- Both identity-authored diamond faces are coherent at one explicit edge choice. -/
theorem coherentDoubleDiamond_coherentAt :
    AAT.AG.TransportCoherence.CoherentAt coherentDoubleDiamondData
      (finiteDoubleDiamondFaceReselection .first) := by
  intro cell
  have firstCoherent := finiteDoubleDiamond_face_coherent
    DoubleDiamondTwoCell.first
  cases cell <;>
    simpa only [coherentDoubleDiamondData] using firstCoherent

/-- The coherent double diamond supplies a positive, nonempty 3-cell syzygy. -/
theorem coherentDoubleDiamond_syzygyCompatible :
    AAT.AG.TransportCoherence.SyzygyCompatible coherentDoubleDiamondData
      (finiteDoubleDiamondFaceReselection .first) :=
  AAT.AG.TransportCoherence.syzygyCompatible_of_coherentAt
    coherentDoubleDiamondData
    (finiteDoubleDiamondFaceReselection .first)
    coherentDoubleDiamond_coherentAt

/-- The positive double-diamond syzygy remains positive for the arbitrary functor. -/
theorem packageCoherentDoubleDiamond_syzygyCompatible :
    Arbitrary.SyzygyCompatible
      (Arbitrary.packageTransportData coherentDoubleDiamondData)
      (Arbitrary.packageEdgeReselection coherentDoubleDiamondData.lift
        (finiteDoubleDiamondFaceReselection .first)) :=
  (Arbitrary.package_syzygyCompatible_iff coherentDoubleDiamondData
    (finiteDoubleDiamondFaceReselection .first)).mpr
      coherentDoubleDiamond_syzygyCompatible

/-- The incompatible double diamond is a negative arbitrary-functor syzygy instance. -/
theorem packageFiniteDoubleDiamond_not_syzygyCompatible :
    ¬ Arbitrary.SyzygyCompatible
      (Arbitrary.packageTransportData finiteDoubleDiamondData)
      (Arbitrary.packageEdgeReselection finiteDoubleDiamondData.lift 1) := by
  intro compatible
  exact finiteDoubleDiamond_not_syzygyCompatible 1
    ((Arbitrary.package_syzygyCompatible_iff
      finiteDoubleDiamondData 1).mp compatible)

end AAT.AG.TransportCoherence.Arbitrary.Witnesses

#assert_standard_axioms_only AAT.AG.TransportCoherence.Arbitrary.Witnesses
