import ResearchLean.AG.TransportCoherence.FinitePresentation

/-!
# Vanishing, coherentizability, and single-disk absorption

This module supplies the G-106/J2 equivalence.  `CoherentAt` is stated as the
authored package-level comparison equation after an edge reselection, while
`TransportObstructionVanishes` remains the independently defined orbit predicate
from J1.  Their equivalence is proved through G-101 strongly-cocartesian
uniqueness and noncommutative group cancellation; it is not definitional.

The second half constructs the fixed positive example required by G-106(i): on
the disk presentation with two boundary edges and one declared 2-cell, a gauge
on one boundary edge absorbs every authored defect.
-/

namespace AAT.AG.TransportCoherence

universe u

open CategoryTheory
open AtomFoundation

/-! ## Independent coherence equation and vanishing equivalence -/

/--
The authored comparator is coherent at one edge-reselection coordinate when it
actually identifies the two reselected path lifts for every declared 2-cell.
-/
def CoherentAt {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) : Prop :=
  ∀ cell : G.TwoCell,
    (reselectedPathLift data.lift reselection (G.twoLeft cell)).comp
        (PackageFiberAut.hom (data.comparator cell)) =
      reselectedPathLift data.lift reselection (G.twoRight cell)

/-- Existence of a coherent authored comparison inside the allowed edge orbit. -/
def Coherentizable {G : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : AdmissibleTransportData G U) : Prop :=
  ∃ reselection : EdgeReselection data.lift, CoherentAt data reselection

/--
One raw defect is identity exactly when its authored comparator equals the
G-101-generated canonical comparator.  This uses group cancellation rather
than identifying the two definitions.
-/
theorem rawTwoCellDefect_eq_one_iff
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) (cell : G.TwoCell) :
    rawTwoCellDefect data reselection cell = 1 ↔
      data.comparator cell = canonicalTwoCellComparator data reselection cell := by
  unfold rawTwoCellDefect
  constructor
  · intro equality
    calc
      data.comparator cell =
          (data.comparator cell *
            (canonicalTwoCellComparator data reselection cell)⁻¹) *
              canonicalTwoCellComparator data reselection cell := by
        simp [mul_assoc]
      _ = 1 * canonicalTwoCellComparator data reselection cell :=
        congrArg
          (fun automorphism =>
            automorphism * canonicalTwoCellComparator data reselection cell)
          equality
      _ = canonicalTwoCellComparator data reselection cell := one_mul _
  · intro equality
    rw [equality]
    exact mul_inv_cancel _

/--
At a fixed coordinate, the path-factorization coherence equations are
equivalent to equality of the raw cochain with the independent identity
cochain.
-/
theorem coherentAt_iff_rawDefectCochain_eq_identity
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) :
    CoherentAt data reselection ↔
      rawDefectCochain data reselection = identityDefectCochain data := by
  constructor
  · intro coherent
    funext cell
    letI : (packageProjection U).IsStronglyCocartesian
        (reselectedPathLift data.lift reselection (G.twoLeft cell)).base
        (reselectedPathLift data.lift reselection (G.twoLeft cell)) :=
      reselectedPathLift_isStronglyCocartesian
        data.lift reselection (G.twoLeft cell)
    have authoredEqCanonical :
        data.comparator cell =
          canonicalTwoCellComparator data reselection cell := by
      apply PackageFiberAut.ext_of_strong_fac
        (reselectedPathLift data.lift reselection (G.twoLeft cell))
      exact (coherent cell).trans
        (canonicalTwoCellComparator_fac data reselection cell).symm
    change rawTwoCellDefect data reselection cell = 1
    exact (rawTwoCellDefect_eq_one_iff data reselection cell).2
      authoredEqCanonical
  · intro rawIdentity cell
    have rawCellIdentity : rawTwoCellDefect data reselection cell = 1 := by
      exact congrFun rawIdentity cell
    have authoredEqCanonical :
        data.comparator cell =
          canonicalTwoCellComparator data reselection cell :=
      (rawTwoCellDefect_eq_one_iff data reselection cell).1 rawCellIdentity
    rw [authoredEqCanonical]
    exact canonicalTwoCellComparator_fac data reselection cell

/--
G-106/J2 vanishing equivalence on every finite presentation over an arbitrary
carrier.  The left side is the J1 orbit predicate; the right side is existence
of a coordinate satisfying the independent package-level coherence equations.
-/
theorem transportObstructionVanishes_iff_coherentizable
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) :
    TransportObstructionVanishes data ↔ Coherentizable data := by
  constructor
  · rintro ⟨reselection, rawIdentity⟩
    exact ⟨reselection,
      (coherentAt_iff_rawDefectCochain_eq_identity data reselection).2
        rawIdentity⟩
  · rintro ⟨reselection, coherent⟩
    exact ⟨reselection,
      (coherentAt_iff_rawDefectCochain_eq_identity data reselection).1
        coherent⟩

/-! ## The single-2-cell disk and absorption by a boundary-edge gauge -/

/-- The two vertices of the minimal directed disk presentation. -/
inductive SingleDiskVertex (Marker : Type u) : Type u
  | source
  | target
  deriving DecidableEq

noncomputable instance singleDiskVertexFintype (Marker : Type u) :
    Fintype (SingleDiskVertex Marker) := by
  classical
  exact
    { elems := {(SingleDiskVertex.source : SingleDiskVertex Marker),
        (SingleDiskVertex.target : SingleDiskVertex Marker)}
      complete := by
        intro vertex
        cases vertex <;> simp }

/-- The two parallel boundary edges of the minimal directed disk. -/
inductive SingleDiskEdge {Marker : Type u} :
    SingleDiskVertex Marker → SingleDiskVertex Marker → Type u
  | left : SingleDiskEdge .source .target
  | right : SingleDiskEdge .source .target
  deriving DecidableEq

instance singleDiskEdgeFinite (Marker : Type u)
    (i j : SingleDiskVertex Marker) :
    Finite (@SingleDiskEdge Marker i j) := by
  apply Finite.of_injective
    (fun edge => match edge with
      | .left => false
      | .right => true)
  intro first second equality
  cases first <;> cases second <;> simp_all

/-- The unique declared 2-cell filling the two-edge disk. -/
inductive SingleDiskTwoCell (Marker : Type u) : Type u
  | face
  deriving DecidableEq

instance singleDiskTwoCellFintype (Marker : Type u) :
    Fintype (SingleDiskTwoCell Marker) where
  elems := {(SingleDiskTwoCell.face : SingleDiskTwoCell Marker)}
  complete := by
    intro cell
    cases cell
    simp

/-- The disk has no declared 3-cell; this type is the universe-polymorphic empty family. -/
inductive SingleDiskThreeCell (Marker : Type u) : Type u

instance singleDiskThreeCellFintype (Marker : Type u) :
    Fintype (SingleDiskThreeCell Marker) where
  elems := ∅
  complete := by
    intro cell
    cases cell

/-- The left boundary path of the single-cell disk. -/
def singleDiskLeftPath (Marker : Type u) :
    PresentedPath (@SingleDiskEdge Marker)
      (SingleDiskVertex.source : SingleDiskVertex Marker)
      (SingleDiskVertex.target : SingleDiskVertex Marker) :=
  .cons .left (.nil SingleDiskVertex.target)

/-- The right boundary path of the single-cell disk. -/
def singleDiskRightPath (Marker : Type u) :
    PresentedPath (@SingleDiskEdge Marker)
      (SingleDiskVertex.source : SingleDiskVertex Marker)
      (SingleDiskVertex.target : SingleDiskVertex Marker) :=
  .cons .right (.nil SingleDiskVertex.target)

/--
The finite disk presentation with two boundary edges, one declared 2-cell, and
no 3-cell relation.  It is used only for the positive absorption theorem, not
as a nonvanishing witness or a vacuous cocycle claim.
-/
noncomputable def singleDiskPresentation (Marker : Type u) :
    FiniteTransportPresentation.{u} where
  Vertex := SingleDiskVertex Marker
  vertexFintype := Fintype.ofFinite _
  Edge := @SingleDiskEdge Marker
  edgeFintype := fun _ _ => Fintype.ofFinite _
  TwoCell := SingleDiskTwoCell Marker
  twoCellFintype := Fintype.ofFinite _
  twoSource := fun _ => .source
  twoTarget := fun _ => .target
  twoLeft := fun _ => singleDiskLeftPath Marker
  twoRight := fun _ => singleDiskRightPath Marker
  ThreeCell := SingleDiskThreeCell Marker
  threeCellFintype := inferInstance
  threeSource := fun cell => nomatch cell
  threeTarget := fun cell => nomatch cell
  threeStart := fun cell => nomatch cell
  threeFinish := fun cell => nomatch cell
  threeLeft := fun cell => nomatch cell
  threeRight := fun cell => nomatch cell

/-- The lift of a one-edge path is exactly the selected edge lift. -/
@[simp]
theorem pathLift_singleEdge
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleLiftData G U) {i j : G.Vertex}
    (edge : G.Edge i j) :
    data.pathLift (.cons edge (.nil j)) = data.edgeLift edge := by
  change (data.edgeLift edge).comp (𝟙 (data.package j)) = data.edgeLift edge
  exact (@Category.comp_id
    (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
    (data.package i) (data.package j) (data.edgeLift edge))

/-- A reselected one-edge path is exactly the reselected edge lift. -/
@[simp]
theorem reselectedPathLift_singleEdge
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleLiftData G U)
    (reselection : EdgeReselection data) {i j : G.Vertex}
    (edge : G.Edge i j) :
    reselectedPathLift data reselection (.cons edge (.nil j)) =
      reselectedEdgeLift data reselection edge := by
  change (reselectedEdgeLift data reselection edge).comp
      (𝟙 (data.package j)) = reselectedEdgeLift data reselection edge
  exact (@Category.comp_id
    (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
    (data.package i) (data.package j)
    (reselectedEdgeLift data reselection edge))

/--
At the baseline coordinate, the G-101-generated endpoint transition along a
one-edge path is the edge's assigned fiber automorphism itself.
-/
theorem pathReselectionTransition_singleEdge
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleLiftData G U)
    (reselection : EdgeReselection data) {i j : G.Vertex}
    (edge : G.Edge i j) :
    pathReselectionTransition data 1 reselection (.cons edge (.nil j)) =
      reselection i j edge := by
  letI : (packageProjection U).IsStronglyCocartesian
      (reselectedPathLift data 1 (.cons edge (.nil j))).base
      (reselectedPathLift data 1 (.cons edge (.nil j))) :=
    reselectedPathLift_isStronglyCocartesian data 1 (.cons edge (.nil j))
  apply PackageFiberAut.ext_of_strong_fac
    (reselectedPathLift data 1 (.cons edge (.nil j)))
  rw [pathReselectionTransition_fac, mul_one,
    reselectedPathLift_singleEdge, reselectedPathLift_one,
    pathLift_singleEdge]
  rfl

/--
The boundary-edge gauge that absorbs the unique disk defect.  The left edge is
unchanged; the right edge receives the baseline raw defect.
-/
noncomputable def singleDiskAbsorbingReselection
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    EdgeReselection data.lift :=
  fun _ _ edge =>
    match edge with
    | .left => 1
    | .right => rawTwoCellDefect data 1 SingleDiskTwoCell.face

/-- The absorbing reselection induces no endpoint gauge on the left edge. -/
theorem singleDisk_leftTransition
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    pathReselectionTransition data.lift 1
        (singleDiskAbsorbingReselection data) (singleDiskLeftPath U.Atom) =
      1 := by
  change pathReselectionTransition data.lift 1
      (singleDiskAbsorbingReselection data)
        (PresentedPath.cons SingleDiskEdge.left
          (.nil (SingleDiskVertex.target : SingleDiskVertex U.Atom))) = 1
  rw [pathReselectionTransition_singleEdge]
  rfl

/-- The right-edge endpoint gauge is exactly the baseline disk defect. -/
theorem singleDisk_rightTransition
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    pathReselectionTransition data.lift 1
        (singleDiskAbsorbingReselection data) (singleDiskRightPath U.Atom) =
      rawTwoCellDefect data 1 SingleDiskTwoCell.face := by
  change pathReselectionTransition data.lift 1
      (singleDiskAbsorbingReselection data)
        (PresentedPath.cons SingleDiskEdge.right
          (.nil (SingleDiskVertex.target : SingleDiskVertex U.Atom))) = _
  rw [pathReselectionTransition_singleEdge]
  rfl

/-- After the absorbing boundary gauge, the canonical disk comparator is authored. -/
theorem singleDisk_canonicalComparator_after_absorption
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    canonicalTwoCellComparator data (singleDiskAbsorbingReselection data)
        SingleDiskTwoCell.face =
      data.comparator SingleDiskTwoCell.face := by
  let reselection := singleDiskAbsorbingReselection data
  have transformed :=
    canonicalTwoCellComparator_transition data 1 reselection
      SingleDiskTwoCell.face
  change canonicalTwoCellComparator data reselection SingleDiskTwoCell.face =
    data.comparator SingleDiskTwoCell.face
  rw [← mul_one reselection]
  rw [transformed]
  rw [show (singleDiskPresentation U.Atom).twoRight
      SingleDiskTwoCell.face = singleDiskRightPath U.Atom by rfl]
  rw [show (singleDiskPresentation U.Atom).twoLeft
      SingleDiskTwoCell.face = singleDiskLeftPath U.Atom by rfl]
  rw [singleDisk_rightTransition, singleDisk_leftTransition]
  change (rawTwoCellDefect data 1 SingleDiskTwoCell.face) *
      canonicalTwoCellComparator data 1 SingleDiskTwoCell.face * (1)⁻¹ =
    data.comparator SingleDiskTwoCell.face
  simp only [inv_one, mul_one, rawTwoCellDefect]
  simp [mul_assoc]

/--
Every authored defect on the single-2-cell disk is absorbed by the explicitly
constructed gauge on its right boundary edge.
-/
theorem singleDisk_obstruction_vanishes
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    TransportObstructionVanishes data := by
  refine ⟨singleDiskAbsorbingReselection data, ?_⟩
  funext cell
  cases cell
  change rawTwoCellDefect data (singleDiskAbsorbingReselection data)
    SingleDiskTwoCell.face = 1
  exact (rawTwoCellDefect_eq_one_iff data
    (singleDiskAbsorbingReselection data) SingleDiskTwoCell.face).2
      (singleDisk_canonicalComparator_after_absorption data).symm

/-- The same explicit boundary gauge makes the authored disk equation coherent. -/
theorem singleDisk_coherentAt_absorbingReselection
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    CoherentAt data (singleDiskAbsorbingReselection data) := by
  intro cell
  cases cell
  rw [← singleDisk_canonicalComparator_after_absorption]
  exact canonicalTwoCellComparator_fac data
    (singleDiskAbsorbingReselection data) SingleDiskTwoCell.face

/-- The explicit disk gauge supplies a coherent authored comparison. -/
theorem singleDisk_coherentizable
    {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (singleDiskPresentation U.Atom) U) :
    Coherentizable data :=
  ⟨singleDiskAbsorbingReselection data,
    singleDisk_coherentAt_absorbingReselection data⟩

end AAT.AG.TransportCoherence

#assert_standard_axioms_only AAT.AG.TransportCoherence
