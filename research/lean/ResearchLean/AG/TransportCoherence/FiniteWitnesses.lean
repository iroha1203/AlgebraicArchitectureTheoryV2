import ResearchLean.AG.TransportCoherence.PastingObstruction
import ResearchLean.AG.AtomFoundation.FiniteTransportWitness

/-!
# Finite nonvanishing transport-coherence witnesses

This module realizes the two closed G-106/J3 witnesses over
`FiniteModel.carrier`.  Their edges are copies of the existing nonidentity
canonical finite transport, while endpoint automorphisms act on a three-axis
signature whose coordinates visibly record the selected axis.
-/

namespace AAT.AG.TransportCoherence

universe u

open CategoryTheory
open AtomFoundation

/-! ## A nontrivial finite endpoint fiber -/

/-- Three selected signature axes, each visibly recorded as its own coordinate. -/
def finiteWitnessSignature : ArchitectureSignature FiniteModel.carrier where
  Axis := Fin 3
  Coordinate _ := Fin 3
  selected _ := True
  coordinate _ axis := axis

/-- The existing finite reading with only its signature replaced by three axes. -/
noncomputable def finiteWitnessSourceReading :
    CoreReading FiniteModel.carrier :=
  { FiniteModel.coreReading with
    signatureReading := finiteWitnessSignature }

/-- Source package generated from the finite AAT axioms and the three-axis reading. -/
noncomputable def finiteWitnessSourcePackage :
    AATCorePackage FiniteModel.carrier :=
  AATCorePackage.generate FiniteModel.axiomSystem finiteWitnessSourceReading

/-- Target package produced by the existing nonidentity canonical transport. -/
noncomputable abbrev finiteWitnessTargetPackage :
    AATCorePackage FiniteModel.carrier :=
  transportAlong finiteWitnessSourcePackage finiteTransportExactDoctrineHom

/-- The nonidentity canonical transport used by every witness edge. -/
noncomputable abbrev finiteWitnessTransportHom :
    PackageTotalHom finiteWitnessSourcePackage finiteWitnessTargetPackage :=
  transportAlongHom finiteWitnessSourcePackage finiteTransportExactDoctrineHom

/-- Every witness edge is strongly cocartesian by the canonical construction. -/
theorem finiteWitnessTransportHom_isStronglyCocartesian :
    (packageProjection FiniteModel.carrier).IsStronglyCocartesian
      finiteWitnessTransportHom.base finiteWitnessTransportHom :=
  transportAlongHom_isStronglyCocartesian
    finiteWitnessSourcePackage finiteTransportExactDoctrineHom

/-- Witness edges have the existing nonidentity primitive Atom equivalence. -/
theorem finiteWitnessTransportHom_atomEquiv_ne_refl :
    finiteWitnessTransportHom.upper.atomEquiv ≠
      Equiv.refl FiniteModel.carrier.Atom := by
  simpa [finiteWitnessTransportHom] using
    finiteTransportAtomEquiv_nonidentity

/-- Self-change of the target package induced by a permutation of its three axes. -/
noncomputable def finiteWitnessPermutationUpper (permutation : Equiv.Perm (Fin 3)) :
    SignedExactCoreReadingHom finiteWitnessTargetPackage
      finiteWitnessTargetPackage :=
  { SignedExactCoreReadingHom.refl finiteWitnessTargetPackage with
    axisMap := permutation
    coordinateEquiv := fun _ => permutation
    axis_selected_iff := fun _ => Iff.rfl
    coordinate_eq := by
      intro object axis
      rfl }

/-- The same axis permutation as a total morphism over the identity base. -/
noncomputable def finiteWitnessPermutationTotal (permutation : Equiv.Perm (Fin 3)) :
    PackageTotalHom finiteWitnessTargetPackage finiteWitnessTargetPackage where
  base := ExtInstHom.id (packagePoint finiteWitnessTargetPackage)
  upper := finiteWitnessPermutationUpper permutation
  atomEquiv_eq := rfl

/-- Total morphism composition follows permutation composition. -/
theorem finiteWitnessPermutationTotal_comp
    (first second : Equiv.Perm (Fin 3)) :
    (finiteWitnessPermutationTotal first).comp
        (finiteWitnessPermutationTotal second) =
      finiteWitnessPermutationTotal (first.trans second) := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  · apply SignedExactCoreReadingHom.ext
    · apply Equiv.ext
      intro atom
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

/-- The identity axis permutation gives the identity total morphism. -/
theorem finiteWitnessPermutationTotal_refl :
    finiteWitnessPermutationTotal (Equiv.refl (Fin 3)) =
      PackageTotalHom.id finiteWitnessTargetPackage := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  · apply SignedExactCoreReadingHom.ext
    · apply Equiv.ext
      intro atom
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

/-- Every three-axis permutation yields an invertible package self-map. -/
noncomputable def finiteWitnessPermutationIso
    (permutation : Equiv.Perm (Fin 3)) : Aut finiteWitnessTargetPackage where
  hom := finiteWitnessPermutationTotal permutation
  inv := finiteWitnessPermutationTotal permutation.symm
  hom_inv_id := by
    change (finiteWitnessPermutationTotal permutation).comp
        (finiteWitnessPermutationTotal permutation.symm) =
      PackageTotalHom.id finiteWitnessTargetPackage
    rw [finiteWitnessPermutationTotal_comp]
    rw [show permutation.trans permutation.symm = Equiv.refl (Fin 3) by
      apply Equiv.ext
      intro axis
      exact permutation.symm_apply_apply axis]
    exact finiteWitnessPermutationTotal_refl
  inv_hom_id := by
    change (finiteWitnessPermutationTotal permutation.symm).comp
        (finiteWitnessPermutationTotal permutation) =
      PackageTotalHom.id finiteWitnessTargetPackage
    rw [finiteWitnessPermutationTotal_comp]
    rw [show permutation.symm.trans permutation = Equiv.refl (Fin 3) by
      apply Equiv.ext
      intro axis
      exact permutation.apply_symm_apply axis]
    exact finiteWitnessPermutationTotal_refl

/-- The permutation lies in the endpoint fiber because its base is identity. -/
noncomputable def finiteWitnessFiberPermutation
    (permutation : Equiv.Perm (Fin 3)) :
    PackageFiberAut finiteWitnessTargetPackage :=
  ⟨finiteWitnessPermutationIso permutation, rfl⟩

/-- The fiber construction remembers the complete axis permutation. -/
theorem finiteWitnessFiberPermutation_injective :
    Function.Injective finiteWitnessFiberPermutation := by
  intro first second equality
  apply Equiv.ext
  intro axis
  have axisEquality := congrArg
    (fun automorphism : PackageFiberAut finiteWitnessTargetPackage =>
      (PackageFiberAut.hom automorphism).upper.axisMap axis) equality
  exact axisEquality

/-- Adjacent transpositions supplying the concrete noncommutative witness. -/
noncomputable def finiteWitnessSwap01 : PackageFiberAut finiteWitnessTargetPackage :=
  finiteWitnessFiberPermutation (Equiv.swap (0 : Fin 3) 1)

noncomputable def finiteWitnessSwap12 : PackageFiberAut finiteWitnessTargetPackage :=
  finiteWitnessFiberPermutation (Equiv.swap (1 : Fin 3) 2)

/-- Fiber permutations multiply by the corresponding reversed-hom composition. -/
theorem finiteWitnessFiberPermutation_mul
    (first second : Equiv.Perm (Fin 3)) :
    finiteWitnessFiberPermutation first * finiteWitnessFiberPermutation second =
      finiteWitnessFiberPermutation (second.trans first) := by
  apply Subtype.ext
  apply Iso.ext
  change (finiteWitnessPermutationTotal second).comp
      (finiteWitnessPermutationTotal first) =
    finiteWitnessPermutationTotal (second.trans first)
  exact finiteWitnessPermutationTotal_comp second first

/-- The identity axis permutation is the identity fiber automorphism. -/
theorem finiteWitnessFiberPermutation_refl :
    finiteWitnessFiberPermutation (Equiv.refl (Fin 3)) = 1 := by
  apply Subtype.ext
  apply Iso.ext
  exact finiteWitnessPermutationTotal_refl

/-- The first adjacent transposition is a genuinely nonidentity fiber element. -/
theorem finiteWitnessSwap01_ne_one : finiteWitnessSwap01 ≠ 1 := by
  intro equality
  have permutationEquality :
      Equiv.swap (0 : Fin 3) 1 = Equiv.refl (Fin 3) := by
    apply finiteWitnessFiberPermutation_injective
    exact equality.trans finiteWitnessFiberPermutation_refl.symm
  have pointEquality := Equiv.congr_fun permutationEquality (0 : Fin 3)
  simp at pointEquality

/-- The two visible adjacent transpositions do not commute in the target fiber. -/
theorem finiteWitness_swaps_do_not_commute :
    finiteWitnessSwap12 * finiteWitnessSwap01 ≠
      finiteWitnessSwap01 * finiteWitnessSwap12 := by
  intro equality
  rw [finiteWitnessSwap01, finiteWitnessSwap12,
    finiteWitnessFiberPermutation_mul,
    finiteWitnessFiberPermutation_mul] at equality
  have permutationEquality :
      (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2) =
        (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 1) :=
    finiteWitnessFiberPermutation_injective equality
  have pointEquality := Equiv.congr_fun permutationEquality (0 : Fin 3)
  change (Equiv.swap (1 : Fin 3) 2) ((Equiv.swap (0 : Fin 3) 1) 0) =
      (Equiv.swap (0 : Fin 3) 1) ((Equiv.swap (1 : Fin 3) 2) 0) at pointEquality
  have rightValue :
      (Equiv.swap (0 : Fin 3) 1) ((Equiv.swap (1 : Fin 3) 2) 0) = 1 := by
    decide
  rw [rightValue] at pointEquality
  have leftValue :
      (Equiv.swap (1 : Fin 3) 2) ((Equiv.swap (0 : Fin 3) 1) 0) = 2 := by
    decide
  rw [leftValue] at pointEquality
  omega

/-! ## Closed double-2-cell diamond -/

/-- Two distinct authored faces with the same pair of boundary paths. -/
inductive DoubleDiamondTwoCell (Marker : Type u) : Type u
  | first
  | second
  deriving DecidableEq

/-- Boolean enumeration of the two double-diamond faces. -/
def doubleDiamondTwoCellEquiv (Marker : Type u) :
    Bool ≃ DoubleDiamondTwoCell Marker where
  toFun
    | false => .first
    | true => .second
  invFun
    | .first => false
    | .second => true
  left_inv value := by cases value <;> rfl
  right_inv cell := by cases cell <;> rfl

noncomputable instance doubleDiamondTwoCellFintype (Marker : Type u) :
    Fintype (DoubleDiamondTwoCell Marker) :=
  Fintype.ofEquiv Bool (doubleDiamondTwoCellEquiv Marker)

/-- The unique 3-cell compares the two one-face fillings of the same diamond. -/
inductive DoubleDiamondThreeCell (Marker : Type u) : Type u
  | comparison
  deriving DecidableEq

/-- Unit enumeration of the unique double-diamond 3-cell. -/
def doubleDiamondThreeCellEquiv (Marker : Type u) :
    PUnit ≃ DoubleDiamondThreeCell Marker where
  toFun _ := .comparison
  invFun _ := PUnit.unit
  left_inv value := by cases value; rfl
  right_inv cell := by cases cell; rfl

noncomputable instance doubleDiamondThreeCellFintype (Marker : Type u) :
    Fintype (DoubleDiamondThreeCell Marker) where
  elems := { .comparison }
  complete cell := by cases cell; simp

/-- The finite 2-skeleton of the closed double diamond. -/
noncomputable def doubleDiamondTwoPresentation (Marker : Type u) :
    FiniteTransportTwoPresentation.{u} where
  Vertex := SingleDiskVertex Marker
  vertexFintype := Fintype.ofFinite _
  Edge := @SingleDiskEdge Marker
  edgeFintype := fun _ _ => Fintype.ofFinite _
  TwoCell := DoubleDiamondTwoCell Marker
  twoCellFintype := Fintype.ofFinite _
  twoSource := fun _ => .source
  twoTarget := fun _ => .target
  twoLeft := fun _ => singleDiskLeftPath Marker
  twoRight := fun _ => singleDiskRightPath Marker

/-- One forward face of the double diamond, with empty outer whiskers. -/
def doubleDiamondFace (Marker : Type u) (cell : DoubleDiamondTwoCell Marker) :
    WhiskeredFace (doubleDiamondTwoPresentation Marker)
      (SingleDiskVertex.source : SingleDiskVertex Marker)
      (SingleDiskVertex.target : SingleDiskVertex Marker) where
  cell := cell
  incoming := .nil
    (SingleDiskVertex.source : SingleDiskVertex Marker)
  outgoing := .nil
    (SingleDiskVertex.target : SingleDiskVertex Marker)
  orientation := .forward

/-- The indexed rewrite step represented by one double-diamond face. -/
def doubleDiamondStep (Marker : Type u) (cell : DoubleDiamondTwoCell Marker) :
    RewriteStep (doubleDiamondTwoPresentation Marker)
      (singleDiskLeftPath Marker) (singleDiskRightPath Marker) where
  face := doubleDiamondFace Marker cell
  before_eq := by
    simp [doubleDiamondFace, WhiskeredFace.before,
      WhiskeredFace.localBefore, doubleDiamondTwoPresentation,
      PresentedPath.append]
  after_eq := by
    simp [doubleDiamondFace, WhiskeredFace.after,
      WhiskeredFace.localAfter, doubleDiamondTwoPresentation,
      PresentedPath.append]

/-- A one-face filling of the double diamond. -/
def doubleDiamondPasting (Marker : Type u) (cell : DoubleDiamondTwoCell Marker) :
    RewritePasting (doubleDiamondTwoPresentation Marker)
      (singleDiskLeftPath Marker) (singleDiskRightPath Marker) :=
  .cons (doubleDiamondStep Marker cell)
    (@RewritePasting.nil (doubleDiamondTwoPresentation Marker)
      (SingleDiskVertex.source : SingleDiskVertex Marker)
      (SingleDiskVertex.target : SingleDiskVertex Marker)
      (singleDiskRightPath Marker))

/--
The closed double-diamond presentation.  Its sole 3-cell compares the two
distinct declared 2-cells rather than accepting their compatibility.
-/
noncomputable def doubleDiamondPresentation (Marker : Type u) :
    FiniteTransportPresentation.{u} where
  toFiniteTransportTwoPresentation := doubleDiamondTwoPresentation Marker
  ThreeCell := DoubleDiamondThreeCell Marker
  threeCellFintype := Fintype.ofFinite _
  threeSource := fun _ => .source
  threeTarget := fun _ => .target
  threeStart := fun _ => singleDiskLeftPath Marker
  threeFinish := fun _ => singleDiskRightPath Marker
  threeLeft := fun _ => doubleDiamondPasting Marker .first
  threeRight := fun _ => doubleDiamondPasting Marker .second

/-- Coherence of both fillings forces their authored comparators to agree. -/
theorem doubleDiamond_comparator_eq_of_coherentAt
    {Marker : Type u} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData (doubleDiamondPresentation Marker) U)
    (reselection : EdgeReselection data.lift)
    (coherent : CoherentAt data reselection) :
    data.comparator .first = data.comparator .second := by
  letI : (packageProjection U).IsStronglyCocartesian
      (reselectedPathLift data.lift reselection
        (singleDiskLeftPath Marker)).base
      (reselectedPathLift data.lift reselection
        (singleDiskLeftPath Marker)) :=
    reselectedPathLift_isStronglyCocartesian data.lift reselection
      (singleDiskLeftPath Marker)
  apply PackageFiberAut.ext_of_strong_fac
    (reselectedPathLift data.lift reselection (singleDiskLeftPath Marker))
  exact (coherent .first).trans (coherent .second).symm

/-- The concrete double-diamond lift interprets both edges by nonidentity transport. -/
noncomputable def finiteDoubleDiamondLiftData :
    AdmissibleLiftData
      (doubleDiamondPresentation FiniteModel.carrier.Atom)
      FiniteModel.carrier where
  package
    | .source => finiteWitnessSourcePackage
    | .target => finiteWitnessTargetPackage
  edgeLift := fun edge =>
    match edge with
    | .left => finiteWitnessTransportHom
    | .right => finiteWitnessTransportHom
  edgeStrong := by
    intro _ _ edge
    cases edge <;> exact finiteWitnessTransportHom_isStronglyCocartesian

/-- Concrete authored translations: identity on the first face and a visible swap on the second. -/
noncomputable def finiteDoubleDiamondData :
    AdmissibleTransportData
      (doubleDiamondPresentation FiniteModel.carrier.Atom)
      FiniteModel.carrier where
  lift := finiteDoubleDiamondLiftData
  twoCellBase := by
    intro cell
    cases cell <;> rfl
  comparator
    | .first => 1
    | .second => finiteWitnessSwap01

/-- Reselection making one chosen diamond filling coherent in isolation. -/
noncomputable def finiteDoubleDiamondFaceReselection
    (cell : DoubleDiamondTwoCell FiniteModel.carrier.Atom) :
    EdgeReselection finiteDoubleDiamondData.lift :=
  fun _ _ edge =>
    match cell, edge with
    | .first, .left => 1
    | .first, .right => 1
    | .second, .left => 1
    | .second, .right => finiteWitnessSwap01

/--
Each of the two authored diamond fillings is separately coherent under its own
explicit edge coordinate; their closed ratio is the simultaneous obstruction.
-/
theorem finiteDoubleDiamond_face_coherent
    (cell : DoubleDiamondTwoCell FiniteModel.carrier.Atom) :
    (reselectedPathLift finiteDoubleDiamondData.lift
        (finiteDoubleDiamondFaceReselection cell)
        ((doubleDiamondPresentation FiniteModel.carrier.Atom).twoLeft
          cell)).comp
      (PackageFiberAut.hom (finiteDoubleDiamondData.comparator cell)) =
    reselectedPathLift finiteDoubleDiamondData.lift
      (finiteDoubleDiamondFaceReselection cell)
      ((doubleDiamondPresentation FiniteModel.carrier.Atom).twoRight
        cell) := by
  cases cell <;>
    simp only [doubleDiamondPresentation, doubleDiamondTwoPresentation,
      singleDiskLeftPath, singleDiskRightPath, finiteDoubleDiamondData] <;>
    rw [reselectedPathLift_singleEdge, reselectedPathLift_singleEdge] <;>
    simp [reselectedEdgeLift, finiteDoubleDiamondFaceReselection,
      finiteDoubleDiamondLiftData]
  exact @Category.comp_id
    (AATCorePackage FiniteModel.carrier)
    (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
    finiteWitnessSourcePackage finiteWitnessTargetPackage
    finiteWitnessTransportHom
  rw [show PackageFiberAut.hom
      (1 : PackageFiberAut finiteWitnessTargetPackage) =
    PackageTotalHom.id finiteWitnessTargetPackage by rfl]
  rw [show finiteWitnessTransportHom.comp
        (PackageTotalHom.id finiteWitnessTargetPackage) =
      finiteWitnessTransportHom from
    @Category.comp_id
      (AATCorePackage FiniteModel.carrier)
      (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      finiteWitnessSourcePackage finiteWitnessTargetPackage
      finiteWitnessTransportHom]

/-- The two concrete authored comparators are unequal by an explicit axis computation. -/
theorem finiteDoubleDiamond_comparators_ne :
    finiteDoubleDiamondData.comparator .first ≠
      finiteDoubleDiamondData.comparator .second := by
  change (1 : PackageFiberAut finiteWitnessTargetPackage) ≠ finiteWitnessSwap01
  exact Ne.symm finiteWitnessSwap01_ne_one

/-- No edge reselection can make both double-diamond faces coherent. -/
theorem finiteDoubleDiamond_not_coherentizable :
    ¬ Coherentizable finiteDoubleDiamondData := by
  rintro ⟨reselection, coherent⟩
  exact finiteDoubleDiamond_comparators_ne
    (doubleDiamond_comparator_eq_of_coherentAt
      finiteDoubleDiamondData reselection coherent)

/-- The double-diamond raw obstruction does not vanish anywhere in its orbit. -/
theorem finiteDoubleDiamond_obstruction_does_not_vanish :
    ¬ TransportObstructionVanishes finiteDoubleDiamondData := by
  intro vanishes
  exact finiteDoubleDiamond_not_coherentizable
    ((transportObstructionVanishes_iff_coherentizable
      finiteDoubleDiamondData).mp vanishes)

/-- The first authored route is the identity at every edge coordinate. -/
@[simp]
theorem finiteDoubleDiamond_firstAuthoredPasting
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :
    authoredPastingComparator finiteDoubleDiamondData reselection
        ((doubleDiamondPresentation FiniteModel.carrier.Atom).threeLeft
          DoubleDiamondThreeCell.comparison) = 1 := by
  simp [doubleDiamondPresentation, doubleDiamondPasting,
    doubleDiamondStep, doubleDiamondFace, authoredPastingComparator,
    pastingComparator, orientedFaceComparator, authoredComparatorFamily,
    finiteDoubleDiamondData]
  exact whiskerFiberAut_nil finiteDoubleDiamondLiftData reselection
    (vertex := SingleDiskVertex.target) 1

/-- The second authored route is the visible adjacent transposition. -/
@[simp]
theorem finiteDoubleDiamond_secondAuthoredPasting
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :
    authoredPastingComparator finiteDoubleDiamondData reselection
        ((doubleDiamondPresentation FiniteModel.carrier.Atom).threeRight
          DoubleDiamondThreeCell.comparison) = finiteWitnessSwap01 := by
  simp [doubleDiamondPresentation, doubleDiamondPasting,
    doubleDiamondStep, doubleDiamondFace, authoredPastingComparator,
    pastingComparator, orientedFaceComparator, authoredComparatorFamily,
    finiteDoubleDiamondData]
  exact whiskerFiberAut_nil finiteDoubleDiamondLiftData reselection
    (vertex := SingleDiskVertex.target) finiteWitnessSwap01

/-- Specialized raw closed obstruction of the concrete double diamond. -/
noncomputable def finiteDoubleDiamondRawObstruction
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :=
  closedPastingRawObstruction finiteDoubleDiamondData reselection
    DoubleDiamondThreeCell.comparison

/-- Specialized conjugacy class of the concrete double-diamond obstruction. -/
noncomputable def finiteDoubleDiamondObstructionClass
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :=
  closedPastingObstructionClass finiteDoubleDiamondData reselection
    DoubleDiamondThreeCell.comparison

/-- The diamond class is the fixed class of the inverse visible swap. -/
theorem finiteDoubleDiamond_class_eq_swapInverse
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :
    finiteDoubleDiamondObstructionClass reselection =
      ConjClasses.mk finiteWitnessSwap01⁻¹ := by
  rw [finiteDoubleDiamondObstructionClass,
    closedPastingObstructionClass_eq_authoredMismatchClass]
  simp [authoredPastingMismatch]

/-- The closed diamond conjugacy class is independent of edge reselection. -/
theorem finiteDoubleDiamond_class_reselection_invariant
    (first second : EdgeReselection finiteDoubleDiamondData.lift) :
    finiteDoubleDiamondObstructionClass first =
      finiteDoubleDiamondObstructionClass second := by
  rw [finiteDoubleDiamond_class_eq_swapInverse,
    finiteDoubleDiamond_class_eq_swapInverse]

/-- Every edge coordinate has a nonidentity double-diamond obstruction class. -/
theorem finiteDoubleDiamond_class_nonvanishing
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :
    finiteDoubleDiamondObstructionClass reselection ≠ ConjClasses.mk 1 := by
  apply closedPastingObstructionClass_ne_identity
  rw [finiteDoubleDiamond_firstAuthoredPasting,
    finiteDoubleDiamond_secondAuthoredPasting]
  exact Ne.symm finiteWitnessSwap01_ne_one

/-- The concrete closed 3-cell is not syzygy-compatible at any coordinate. -/
theorem finiteDoubleDiamond_not_syzygyCompatible
    (reselection : EdgeReselection finiteDoubleDiamondData.lift) :
    ¬ SyzygyCompatible finiteDoubleDiamondData reselection := by
  intro compatible
  have authoredEquality := compatible DoubleDiamondThreeCell.comparison
  rw [finiteDoubleDiamond_firstAuthoredPasting,
    finiteDoubleDiamond_secondAuthoredPasting] at authoredEquality
  exact finiteWitnessSwap01_ne_one authoredEquality.symm

/-! ## Closed three-reading triangle -/

/-- Three parallel nonidentity transport edges between the two finite packages. -/
inductive TransportTriangleEdge {Marker : Type u} :
    SingleDiskVertex Marker → SingleDiskVertex Marker → Type u
  | e0 : TransportTriangleEdge .source .target
  | e1 : TransportTriangleEdge .source .target
  | e2 : TransportTriangleEdge .source .target
  deriving DecidableEq

instance transportTriangleEdgeFinite (Marker : Type u)
    (i j : SingleDiskVertex Marker) :
    Finite (@TransportTriangleEdge Marker i j) := by
  apply Finite.of_injective
    (fun edge => match edge with
      | .e0 => (0 : Fin 3)
      | .e1 => (1 : Fin 3)
      | .e2 => (2 : Fin 3))
  intro first second equality
  cases first <;> cases second <;> simp_all

/-- The three pairwise authored translation cells. -/
inductive TransportTriangleTwoCell (Marker : Type u) : Type u
  | c01
  | c12
  | c02
  deriving DecidableEq

instance transportTriangleTwoCellFinite (Marker : Type u) :
    Finite (TransportTriangleTwoCell Marker) := by
  apply Finite.of_injective
    (fun cell => match cell with
      | .c01 => (0 : Fin 3)
      | .c12 => (1 : Fin 3)
      | .c02 => (2 : Fin 3))
  intro first second equality
  cases first <;> cases second <;> simp_all

/-- The genuine 3-cell compares the indirect and direct pairwise translations. -/
inductive TransportTriangleThreeCell (Marker : Type u) : Type u
  | triangle
  deriving DecidableEq

noncomputable instance transportTriangleThreeCellFintype (Marker : Type u) :
    Fintype (TransportTriangleThreeCell Marker) where
  elems := {(TransportTriangleThreeCell.triangle :
    TransportTriangleThreeCell Marker)}
  complete cell := by cases cell; simp

/-- The single-edge path represented by one of the three parallel edges. -/
def transportTrianglePath (Marker : Type u)
    (edge : @TransportTriangleEdge Marker .source .target) :
    PresentedPath (@TransportTriangleEdge Marker)
      (SingleDiskVertex.source : SingleDiskVertex Marker)
      (SingleDiskVertex.target : SingleDiskVertex Marker) :=
  .cons edge (.nil SingleDiskVertex.target)

/-- The finite pairwise-translation 2-skeleton. -/
noncomputable def transportTriangleTwoPresentation (Marker : Type u) :
    FiniteTransportTwoPresentation.{u} where
  Vertex := SingleDiskVertex Marker
  vertexFintype := Fintype.ofFinite _
  Edge := @TransportTriangleEdge Marker
  edgeFintype := fun _ _ => Fintype.ofFinite _
  TwoCell := TransportTriangleTwoCell Marker
  twoCellFintype := Fintype.ofFinite _
  twoSource := fun _ => .source
  twoTarget := fun _ => .target
  twoLeft
    | .c01 => transportTrianglePath Marker .e0
    | .c12 => transportTrianglePath Marker .e1
    | .c02 => transportTrianglePath Marker .e0
  twoRight
    | .c01 => transportTrianglePath Marker .e1
    | .c12 => transportTrianglePath Marker .e2
    | .c02 => transportTrianglePath Marker .e2

/-- One forward pairwise-translation face with empty outer whiskers. -/
def transportTriangleFace (Marker : Type u)
    (cell : TransportTriangleTwoCell Marker) :
    WhiskeredFace (transportTriangleTwoPresentation Marker)
      (SingleDiskVertex.source : SingleDiskVertex Marker)
      (SingleDiskVertex.target : SingleDiskVertex Marker) where
  cell := cell
  incoming := .nil SingleDiskVertex.source
  outgoing := .nil SingleDiskVertex.target
  orientation := .forward

/-- The typed rewrite step represented by one pairwise translation. -/
def transportTriangleStep (Marker : Type u)
    (cell : TransportTriangleTwoCell Marker) :
    RewriteStep (transportTriangleTwoPresentation Marker)
      ((transportTriangleTwoPresentation Marker).twoLeft cell)
      ((transportTriangleTwoPresentation Marker).twoRight cell) where
  face := transportTriangleFace Marker cell
  before_eq := by
    simp [transportTriangleFace, WhiskeredFace.before,
      WhiskeredFace.localBefore, PresentedPath.append]
    exact (PresentedPath.append_nil _).symm
  after_eq := by
    simp [transportTriangleFace, WhiskeredFace.after,
      WhiskeredFace.localAfter, PresentedPath.append]
    exact (PresentedPath.append_nil _).symm

/-- The two-step route `c01` followed by `c12`. -/
noncomputable def transportTriangleIndirectPasting (Marker : Type u) :
    RewritePasting (transportTriangleTwoPresentation Marker)
      (transportTrianglePath Marker .e0)
      (transportTrianglePath Marker .e2) :=
  .cons (transportTriangleStep Marker .c01)
    (.cons (transportTriangleStep Marker .c12)
      (@RewritePasting.nil (transportTriangleTwoPresentation Marker)
        (SingleDiskVertex.source : SingleDiskVertex Marker)
        (SingleDiskVertex.target : SingleDiskVertex Marker)
        (transportTrianglePath Marker .e2)))

/-- The one-step direct route `c02`. -/
noncomputable def transportTriangleDirectPasting (Marker : Type u) :
    RewritePasting (transportTriangleTwoPresentation Marker)
      (transportTrianglePath Marker .e0)
      (transportTrianglePath Marker .e2) :=
  .cons (transportTriangleStep Marker .c02)
    (@RewritePasting.nil (transportTriangleTwoPresentation Marker)
      (SingleDiskVertex.source : SingleDiskVertex Marker)
      (SingleDiskVertex.target : SingleDiskVertex Marker)
      (transportTrianglePath Marker .e2))

/--
The closed three-reading presentation: its sole 3-cell compares the indirect
pairwise translation with the direct pairwise translation.
-/
noncomputable def transportTrianglePresentation (Marker : Type u) :
    FiniteTransportPresentation.{u} where
  toFiniteTransportTwoPresentation := transportTriangleTwoPresentation Marker
  ThreeCell := TransportTriangleThreeCell Marker
  threeCellFintype := Fintype.ofFinite _
  threeSource := fun _ => .source
  threeTarget := fun _ => .target
  threeStart := fun _ => transportTrianglePath Marker .e0
  threeFinish := fun _ => transportTrianglePath Marker .e2
  threeLeft := fun _ => transportTriangleIndirectPasting Marker
  threeRight := fun _ => transportTriangleDirectPasting Marker

/-- Every triangle edge is the same existing nonidentity canonical transport. -/
noncomputable def finiteTransportTriangleLiftData :
    AdmissibleLiftData
      (transportTrianglePresentation FiniteModel.carrier.Atom)
      FiniteModel.carrier where
  package
    | .source => finiteWitnessSourcePackage
    | .target => finiteWitnessTargetPackage
  edgeLift := fun edge =>
    match edge with
    | .e0 => finiteWitnessTransportHom
    | .e1 => finiteWitnessTransportHom
    | .e2 => finiteWitnessTransportHom
  edgeStrong := by
    intro _ _ edge
    cases edge <;> exact finiteWitnessTransportHom_isStronglyCocartesian

/--
The concrete pairwise translators are two adjacent swaps and their direct
product; the indirect temporal composite has the opposite noncommutative order.
-/
noncomputable def finiteTransportTriangleData :
    AdmissibleTransportData
      (transportTrianglePresentation FiniteModel.carrier.Atom)
      FiniteModel.carrier where
  lift := finiteTransportTriangleLiftData
  twoCellBase := by
    intro cell
    cases cell <;> rfl
  comparator
    | .c01 => finiteWitnessSwap01
    | .c12 => finiteWitnessSwap12
    | .c02 => finiteWitnessSwap01 * finiteWitnessSwap12

/--
For one chosen pairwise cell, reselect only its right edge by the authored
comparator.  The other edge coordinates are irrelevant to that one equation.
-/
noncomputable def finiteTransportTrianglePairReselection
    (cell : TransportTriangleTwoCell FiniteModel.carrier.Atom) :
    EdgeReselection finiteTransportTriangleData.lift :=
  fun _ _ edge =>
    match cell, edge with
    | .c01, .e0 => 1
    | .c01, .e1 => finiteWitnessSwap01
    | .c01, .e2 => 1
    | .c12, .e0 => 1
    | .c12, .e1 => 1
    | .c12, .e2 => finiteWitnessSwap12
    | .c02, .e0 => 1
    | .c02, .e1 => 1
    | .c02, .e2 => finiteWitnessSwap01 * finiteWitnessSwap12

/--
Each declared pairwise translation is individually realizable by its explicit
edge reselection; the obstruction is therefore simultaneous three-way
compatibility, not absence of a pairwise translator.
-/
theorem finiteTransportTriangle_pairwise_coherent
    (cell : TransportTriangleTwoCell FiniteModel.carrier.Atom) :
    (reselectedPathLift finiteTransportTriangleData.lift
        (finiteTransportTrianglePairReselection cell)
        ((transportTrianglePresentation FiniteModel.carrier.Atom).twoLeft
          cell)).comp
      (PackageFiberAut.hom (finiteTransportTriangleData.comparator cell)) =
    reselectedPathLift finiteTransportTriangleData.lift
      (finiteTransportTrianglePairReselection cell)
      ((transportTrianglePresentation FiniteModel.carrier.Atom).twoRight
        cell) := by
  cases cell <;>
    simp only [transportTrianglePresentation, transportTriangleTwoPresentation,
      transportTrianglePath, finiteTransportTriangleData] <;>
    rw [reselectedPathLift_singleEdge, reselectedPathLift_singleEdge] <;>
    simp [reselectedEdgeLift, finiteTransportTrianglePairReselection,
      finiteTransportTriangleLiftData]
  all_goals
    rw [show PackageFiberAut.hom
        (1 : PackageFiberAut finiteWitnessTargetPackage) =
      PackageTotalHom.id finiteWitnessTargetPackage by rfl]
    rw [show finiteWitnessTransportHom.comp
          (PackageTotalHom.id finiteWitnessTargetPackage) =
        finiteWitnessTransportHom from
      @Category.comp_id
        (AATCorePackage FiniteModel.carrier)
        (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
        finiteWitnessSourcePackage finiteWitnessTargetPackage
        finiteWitnessTransportHom]

/-- Every geometric triangle edge uses the fixed nonidentity Atom transport. -/
theorem finiteTransportTriangle_edge_atomEquiv_ne_refl
    {i j : SingleDiskVertex FiniteModel.carrier.Atom}
    (edge : @TransportTriangleEdge FiniteModel.carrier.Atom i j) :
    (finiteTransportTriangleLiftData.edgeLift edge).upper.atomEquiv ≠
      Equiv.refl FiniteModel.carrier.Atom := by
  cases edge <;> exact finiteWitnessTransportHom_atomEquiv_ne_refl

/-- The indirect authored route has the temporal product `u12 * u01`. -/
@[simp]
theorem finiteTransportTriangle_indirectAuthoredPasting
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    authoredPastingComparator finiteTransportTriangleData reselection
        ((transportTrianglePresentation FiniteModel.carrier.Atom).threeLeft
          TransportTriangleThreeCell.triangle) =
      finiteWitnessSwap12 * finiteWitnessSwap01 := by
  simp [transportTrianglePresentation, transportTriangleIndirectPasting,
    transportTriangleStep, transportTriangleFace,
    authoredPastingComparator, pastingComparator, orientedFaceComparator,
    authoredComparatorFamily, finiteTransportTriangleData]
  rw [whiskerFiberAut_nil finiteTransportTriangleLiftData reselection
      (vertex := SingleDiskVertex.target) finiteWitnessSwap12,
    whiskerFiberAut_nil finiteTransportTriangleLiftData reselection
      (vertex := SingleDiskVertex.target) finiteWitnessSwap01]

/-- The direct authored route has the declared product `u01 * u12`. -/
@[simp]
theorem finiteTransportTriangle_directAuthoredPasting
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    authoredPastingComparator finiteTransportTriangleData reselection
        ((transportTrianglePresentation FiniteModel.carrier.Atom).threeRight
          TransportTriangleThreeCell.triangle) =
      finiteWitnessSwap01 * finiteWitnessSwap12 := by
  simp [transportTrianglePresentation, transportTriangleDirectPasting,
    transportTriangleStep, transportTriangleFace,
    authoredPastingComparator, pastingComparator, orientedFaceComparator,
    authoredComparatorFamily, finiteTransportTriangleData]
  exact whiskerFiberAut_nil finiteTransportTriangleLiftData reselection
    (vertex := SingleDiskVertex.target)
    (finiteWitnessSwap01 * finiteWitnessSwap12)

/-- No single edge reselection can make all three pairwise translations coherent. -/
theorem finiteTransportTriangle_not_coherentizable :
    ¬ Coherentizable finiteTransportTriangleData := by
  rintro ⟨reselection, coherent⟩
  have compatible := syzygyCompatible_of_coherentAt
    finiteTransportTriangleData reselection coherent
  have authoredEquality := compatible TransportTriangleThreeCell.triangle
  rw [finiteTransportTriangle_indirectAuthoredPasting,
    finiteTransportTriangle_directAuthoredPasting] at authoredEquality
  exact finiteWitness_swaps_do_not_commute authoredEquality

/-- The three-reading raw obstruction cannot vanish in the reselection orbit. -/
theorem finiteTransportTriangle_obstruction_does_not_vanish :
    ¬ TransportObstructionVanishes finiteTransportTriangleData := by
  intro vanishes
  exact finiteTransportTriangle_not_coherentizable
    ((transportObstructionVanishes_iff_coherentizable
      finiteTransportTriangleData).mp vanishes)

/-- Specialized raw closed obstruction of the three-reading triangle. -/
noncomputable def finiteTransportTriangleRawObstruction
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :=
  closedPastingRawObstruction finiteTransportTriangleData reselection
    TransportTriangleThreeCell.triangle

/-- Specialized conjugacy class of the three-reading triangle obstruction. -/
noncomputable def finiteTransportTriangleObstructionClass
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :=
  closedPastingObstructionClass finiteTransportTriangleData reselection
    TransportTriangleThreeCell.triangle

/-- The fixed noncommutative mismatch between direct and indirect routes. -/
noncomputable def finiteTransportTriangleAuthoredMismatch :
    PackageFiberAut finiteWitnessTargetPackage :=
  (finiteWitnessSwap01 * finiteWitnessSwap12)⁻¹ *
    (finiteWitnessSwap12 * finiteWitnessSwap01)

/-- Every triangle coordinate represents the class of the same route mismatch. -/
theorem finiteTransportTriangle_class_eq_authoredMismatch
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    finiteTransportTriangleObstructionClass reselection =
      ConjClasses.mk finiteTransportTriangleAuthoredMismatch := by
  rw [finiteTransportTriangleObstructionClass,
    closedPastingObstructionClass_eq_authoredMismatchClass]
  simp [authoredPastingMismatch, finiteTransportTriangleAuthoredMismatch]

/-- The three-reading conjugacy class is independent of edge reselection. -/
theorem finiteTransportTriangle_class_reselection_invariant
    (first second : EdgeReselection finiteTransportTriangleData.lift) :
    finiteTransportTriangleObstructionClass first =
      finiteTransportTriangleObstructionClass second := by
  rw [finiteTransportTriangle_class_eq_authoredMismatch,
    finiteTransportTriangle_class_eq_authoredMismatch]

/-- Every edge coordinate has a nonidentity three-reading obstruction class. -/
theorem finiteTransportTriangle_class_nonvanishing
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    finiteTransportTriangleObstructionClass reselection ≠ ConjClasses.mk 1 := by
  apply closedPastingObstructionClass_ne_identity
  rw [finiteTransportTriangle_indirectAuthoredPasting,
    finiteTransportTriangle_directAuthoredPasting]
  exact finiteWitness_swaps_do_not_commute

/-- The triangle 3-cell is not syzygy-compatible at any edge coordinate. -/
theorem finiteTransportTriangle_not_syzygyCompatible
    (reselection : EdgeReselection finiteTransportTriangleData.lift) :
    ¬ SyzygyCompatible finiteTransportTriangleData reselection := by
  intro compatible
  have authoredEquality := compatible TransportTriangleThreeCell.triangle
  rw [finiteTransportTriangle_indirectAuthoredPasting,
    finiteTransportTriangle_directAuthoredPasting] at authoredEquality
  exact finiteWitness_swaps_do_not_commute authoredEquality

end AAT.AG.TransportCoherence

#assert_standard_axioms_only AAT.AG.TransportCoherence
