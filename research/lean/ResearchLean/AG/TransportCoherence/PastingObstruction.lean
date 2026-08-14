import ResearchLean.AG.TransportCoherence.VanishingCoherence

/-!
# Noncommutative transport obstruction for typed 3-cell pastings

For a multi-face pasting, multiplying the individual raw defects loses the
canonical comparison factors between successive faces.  This module instead
composes the authored and canonical face comparators separately, in temporal
order, and takes their quotient only after the complete route has been formed.

Backward faces are treated in the same way: the authored and canonical local
comparators are inverted separately before whiskering.  This preserves the
noncommutative order required by G-106.
-/

namespace AAT.AG.TransportCoherence

universe u

open CategoryTheory
open AtomFoundation

/-- A family of endpoint-fiber comparators indexed by the declared 2-cells. -/
abbrev TwoCellComparatorFamily
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) :=
  DefectCochain data

/-- The authored comparator family, independent of edge reselection. -/
def authoredComparatorFamily
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) :
    TwoCellComparatorFamily data :=
  data.comparator

/-- The canonical G-101 comparator family at one edge coordinate. -/
noncomputable def canonicalComparatorFamily
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) :
    TwoCellComparatorFamily data :=
  canonicalTwoCellComparator data reselection

/--
Whisker one local comparator to the target of an oriented face.  A backward
face first inverts the local comparator and then transports that inverse.
-/
noncomputable def orientedFaceComparator
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    (family : TwoCellComparatorFamily data)
    {source target : G.Vertex}
    (face : WhiskeredFace G.toFiniteTransportTwoPresentation source target) :
    PackageFiberAut (data.lift.package target) :=
  let localComparator :=
    match face.orientation with
    | .forward => family face.cell
    | .backward => (family face.cell)⁻¹
  whiskerFiberAut data.lift reselection localComparator face.outgoing

/-- The authored comparator carried by one oriented whiskered face. -/
noncomputable def orientedFaceAuthoredComparator
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex}
    (face : WhiskeredFace G.toFiniteTransportTwoPresentation source target) :
    PackageFiberAut (data.lift.package target) :=
  orientedFaceComparator data reselection
    (authoredComparatorFamily data) face

/-- The canonical comparator carried by one oriented whiskered face. -/
noncomputable def orientedFaceCanonicalComparator
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex}
    (face : WhiskeredFace G.toFiniteTransportTwoPresentation source target) :
    PackageFiberAut (data.lift.package target) :=
  orientedFaceComparator data reselection
    (canonicalComparatorFamily data reselection) face

/--
The correctly oriented one-face raw defect: authored comparator followed by
the inverse canonical comparator.  The two factors are oriented separately.
-/
noncomputable def orientedFaceDefect
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex}
    (face : WhiskeredFace G.toFiniteTransportTwoPresentation source target) :
    PackageFiberAut (data.lift.package target) :=
  orientedFaceAuthoredComparator data reselection face *
    (orientedFaceCanonicalComparator data reselection face)⁻¹

/--
Temporal composition of a comparator family along a typed rewrite pasting.
The tail factor is on the left because multiplication in `Aut` reverses the
order of the underlying categorical composites.
-/
noncomputable def pastingComparator
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    (family : TwoCellComparatorFamily data)
    {source target : G.Vertex} {before finish : G.Path source target}
    (pasting : RewritePasting G.toFiniteTransportTwoPresentation before finish) :
    PackageFiberAut (data.lift.package target) :=
  match pasting with
  | .nil _ => 1
  | .cons step tail =>
      pastingComparator data reselection family tail *
        orientedFaceComparator data reselection family step.face

/-- Complete authored route comparator of a typed pasting. -/
noncomputable def authoredPastingComparator
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex} {before finish : G.Path source target}
    (pasting : RewritePasting G.toFiniteTransportTwoPresentation before finish) :
    PackageFiberAut (data.lift.package target) :=
  pastingComparator data reselection (authoredComparatorFamily data) pasting

/-- Complete canonical route comparator of a typed pasting. -/
noncomputable def canonicalPastingComparator
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex} {before finish : G.Path source target}
    (pasting : RewritePasting G.toFiniteTransportTwoPresentation before finish) :
    PackageFiberAut (data.lift.package target) :=
  pastingComparator data reselection
    (canonicalComparatorFamily data reselection) pasting

/-- Raw defect of a complete route, formed only after both routes are composed. -/
noncomputable def pastingRawDefect
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex} {before finish : G.Path source target}
    (pasting : RewritePasting G.toFiniteTransportTwoPresentation before finish) :
    PackageFiberAut (data.lift.package target) :=
  authoredPastingComparator data reselection pasting *
    (canonicalPastingComparator data reselection pasting)⁻¹

/-- Public cocycle evaluator retained under the Cycle-2 name. -/
noncomputable def defectPastingProduct
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex} {before finish : G.Path source target}
    (pasting : RewritePasting G.toFiniteTransportTwoPresentation before finish) :
    PackageFiberAut (data.lift.package target) :=
  pastingRawDefect data reselection pasting

/-- The inverse canonical local comparator factors the reverse path relation. -/
theorem canonicalTwoCellComparator_inv_fac
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) (cell : G.TwoCell) :
    (reselectedPathLift data.lift reselection (G.twoRight cell)).comp
        (PackageFiberAut.hom
          (canonicalTwoCellComparator data reselection cell)⁻¹) =
      reselectedPathLift data.lift reselection (G.twoLeft cell) := by
  let comparator := canonicalTwoCellComparator data reselection cell
  change (reselectedPathLift data.lift reselection (G.twoRight cell)).comp
      (PackageFiberAut.inv comparator) = _
  calc
    _ = ((reselectedPathLift data.lift reselection (G.twoLeft cell)).comp
          (PackageFiberAut.hom comparator)).comp
        (PackageFiberAut.inv comparator) := by
      exact congrArg
        (fun morphism => morphism.comp (PackageFiberAut.inv comparator))
        (canonicalTwoCellComparator_fac data reselection cell).symm
    _ = (reselectedPathLift data.lift reselection (G.twoLeft cell)).comp
        ((PackageFiberAut.hom comparator).comp
          (PackageFiberAut.inv comparator)) :=
      @Category.assoc
        (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
        _ _ _ _
        (reselectedPathLift data.lift reselection (G.twoLeft cell))
        (PackageFiberAut.hom comparator) (PackageFiberAut.inv comparator)
    _ = (reselectedPathLift data.lift reselection (G.twoLeft cell)).comp
        (𝟙 (data.lift.package (G.twoTarget cell))) := by
      exact congrArg
        (fun morphism =>
          (reselectedPathLift data.lift reselection
            (G.twoLeft cell)).comp morphism)
        comparator.1.hom_inv_id
    _ = _ := @Category.comp_id
      (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
      _ _ (reselectedPathLift data.lift reselection (G.twoLeft cell))

/-- The oriented canonical face comparator identifies its two complete paths. -/
theorem orientedFaceCanonicalComparator_fac
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex}
    (face : WhiskeredFace G.toFiniteTransportTwoPresentation source target) :
    (reselectedPathLift data.lift reselection face.before).comp
        (PackageFiberAut.hom
          (orientedFaceCanonicalComparator data reselection face)) =
      reselectedPathLift data.lift reselection face.after := by
  rcases face with ⟨cell, incoming, outgoing, orientation⟩
  cases orientation <;>
    simp only [WhiskeredFace.before, WhiskeredFace.after,
      WhiskeredFace.localBefore, WhiskeredFace.localAfter,
      orientedFaceCanonicalComparator, orientedFaceComparator,
      canonicalComparatorFamily]
  · rw [reselectedPathLift_append, reselectedPathLift_append,
      reselectedPathLift_append, reselectedPathLift_append]
    calc
      _ = (reselectedPathLift data.lift reselection incoming).comp
          (((reselectedPathLift data.lift reselection
              (G.twoLeft cell)).comp
            (reselectedPathLift data.lift reselection outgoing)).comp
            (PackageFiberAut.hom
              (whiskerFiberAut data.lift reselection
                (canonicalTwoCellComparator data reselection cell)
                outgoing))) :=
        @Category.assoc
          (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
          _ _ _ _ _ _ _
      _ = (reselectedPathLift data.lift reselection incoming).comp
          ((reselectedPathLift data.lift reselection
              (G.twoLeft cell)).comp
            ((reselectedPathLift data.lift reselection outgoing).comp
              (PackageFiberAut.hom
                (whiskerFiberAut data.lift reselection
                  (canonicalTwoCellComparator data reselection cell)
                  outgoing)))) := by
        exact congrArg
          (fun morphism =>
            (reselectedPathLift data.lift reselection incoming).comp morphism)
          (@Category.assoc
            (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
            _ _ _ _ _ _ _)
      _ = (reselectedPathLift data.lift reselection incoming).comp
          ((reselectedPathLift data.lift reselection
              (G.twoLeft cell)).comp
            ((PackageFiberAut.hom
              (canonicalTwoCellComparator data reselection cell)).comp
              (reselectedPathLift data.lift reselection outgoing))) := by
        rw [whiskerFiberAut_fac]
        rfl
      _ = (reselectedPathLift data.lift reselection incoming).comp
          (((reselectedPathLift data.lift reselection
              (G.twoLeft cell)).comp
            (PackageFiberAut.hom
              (canonicalTwoCellComparator data reselection cell))).comp
            (reselectedPathLift data.lift reselection outgoing)) := by
        exact congrArg
          (fun morphism =>
            (reselectedPathLift data.lift reselection incoming).comp morphism)
          (@Category.assoc
            (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
            _ _ _ _ _ _ _).symm
      _ = _ := by rw [canonicalTwoCellComparator_fac]
  · rw [reselectedPathLift_append, reselectedPathLift_append,
      reselectedPathLift_append, reselectedPathLift_append]
    calc
      _ = (reselectedPathLift data.lift reselection incoming).comp
          (((reselectedPathLift data.lift reselection
              (G.twoRight cell)).comp
            (reselectedPathLift data.lift reselection outgoing)).comp
            (PackageFiberAut.hom
              (whiskerFiberAut data.lift reselection
                (canonicalTwoCellComparator data reselection cell)⁻¹
                outgoing))) :=
        @Category.assoc
          (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
          _ _ _ _ _ _ _
      _ = (reselectedPathLift data.lift reselection incoming).comp
          ((reselectedPathLift data.lift reselection
              (G.twoRight cell)).comp
            ((reselectedPathLift data.lift reselection outgoing).comp
              (PackageFiberAut.hom
                (whiskerFiberAut data.lift reselection
                  (canonicalTwoCellComparator data reselection cell)⁻¹
                  outgoing)))) := by
        exact congrArg
          (fun morphism =>
            (reselectedPathLift data.lift reselection incoming).comp morphism)
          (@Category.assoc
            (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
            _ _ _ _ _ _ _)
      _ = (reselectedPathLift data.lift reselection incoming).comp
          ((reselectedPathLift data.lift reselection
              (G.twoRight cell)).comp
            ((PackageFiberAut.hom
              (canonicalTwoCellComparator data reselection cell)⁻¹).comp
              (reselectedPathLift data.lift reselection outgoing))) := by
        rw [whiskerFiberAut_fac]
        rfl
      _ = (reselectedPathLift data.lift reselection incoming).comp
          (((reselectedPathLift data.lift reselection
              (G.twoRight cell)).comp
            (PackageFiberAut.hom
              (canonicalTwoCellComparator data reselection cell)⁻¹)).comp
            (reselectedPathLift data.lift reselection outgoing)) := by
        exact congrArg
          (fun morphism =>
            (reselectedPathLift data.lift reselection incoming).comp morphism)
          (@Category.assoc
            (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
            _ _ _ _ _ _ _).symm
      _ = _ := by rw [canonicalTwoCellComparator_inv_fac]

/-- A typed rewrite step's canonical comparator identifies its indexed paths. -/
theorem rewriteStepCanonicalComparator_fac
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex} {before finish : G.Path source target}
    (step : RewriteStep G.toFiniteTransportTwoPresentation before finish) :
    (reselectedPathLift data.lift reselection before).comp
        (PackageFiberAut.hom
          (orientedFaceCanonicalComparator data reselection step.face)) =
      reselectedPathLift data.lift reselection finish := by
  rcases step with ⟨face, beforeEq, finishEq⟩
  subst before
  subst finish
  exact orientedFaceCanonicalComparator_fac data reselection face

/-- The canonical comparator of an entire typed pasting factors its endpoints. -/
theorem canonicalPastingComparator_fac
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex} {before finish : G.Path source target}
    (pasting : RewritePasting G.toFiniteTransportTwoPresentation before finish) :
    (reselectedPathLift data.lift reselection before).comp
        (PackageFiberAut.hom
          (canonicalPastingComparator data reselection pasting)) =
      reselectedPathLift data.lift reselection finish := by
  induction pasting with
  | nil path =>
      change (reselectedPathLift data.lift reselection path).comp
          (𝟙 (data.lift.package target)) = _
      exact (@Category.comp_id
        (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
        _ _ (reselectedPathLift data.lift reselection path))
  | cons step tail inductionHypothesis =>
      simp only [canonicalPastingComparator, pastingComparator]
      change (reselectedPathLift data.lift reselection _).comp
          ((PackageFiberAut.hom
              (orientedFaceCanonicalComparator data reselection step.face)).comp
            (PackageFiberAut.hom
              (pastingComparator data reselection
                (canonicalComparatorFamily data reselection) tail))) = _
      calc
        _ = ((reselectedPathLift data.lift reselection _).comp
              (PackageFiberAut.hom
                (orientedFaceCanonicalComparator data reselection step.face))).comp
            (PackageFiberAut.hom
              (pastingComparator data reselection
                (canonicalComparatorFamily data reselection) tail)) :=
          (@Category.assoc
            (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
            _ _ _ _
            (reselectedPathLift data.lift reselection _)
            (PackageFiberAut.hom
              (orientedFaceCanonicalComparator data reselection step.face))
            (PackageFiberAut.hom
              (pastingComparator data reselection
                (canonicalComparatorFamily data reselection) tail))).symm
        _ = _ := by
          rw [rewriteStepCanonicalComparator_fac]
          exact inductionHypothesis

/-- Canonical route comparison is independent of the selected typed pasting. -/
theorem canonicalPastingComparator_unique
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    {source target : G.Vertex} {before finish : G.Path source target}
    (left right :
      RewritePasting G.toFiniteTransportTwoPresentation before finish) :
    canonicalPastingComparator data reselection left =
      canonicalPastingComparator data reselection right := by
  letI : (packageProjection U).IsStronglyCocartesian
      (reselectedPathLift data.lift reselection before).base
      (reselectedPathLift data.lift reselection before) :=
    reselectedPathLift_isStronglyCocartesian data.lift reselection before
  apply PackageFiberAut.ext_of_strong_fac
    (reselectedPathLift data.lift reselection before)
  exact (canonicalPastingComparator_fac data reselection left).trans
    (canonicalPastingComparator_fac data reselection right).symm

/-- Transport along an empty suffix leaves a fiber automorphism unchanged. -/
@[simp]
theorem whiskerFiberAut_nil
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleLiftData G U)
    (reselection : EdgeReselection data) {vertex : G.Vertex}
    (automorphism : PackageFiberAut (data.package vertex)) :
    whiskerFiberAut data reselection automorphism (.nil vertex) =
      automorphism := by
  letI : (packageProjection U).IsStronglyCocartesian
      (reselectedPathLift data reselection (.nil vertex)).base
      (reselectedPathLift data reselection (.nil vertex)) :=
    reselectedPathLift_isStronglyCocartesian data reselection (.nil vertex)
  apply PackageFiberAut.ext_of_strong_fac
    (reselectedPathLift data reselection (.nil vertex))
  calc
    _ = fiberAutThenPath data reselection automorphism (.nil vertex) :=
      whiskerFiberAut_fac data reselection automorphism (.nil vertex)
    _ = PackageFiberAut.hom automorphism := by
      change (PackageFiberAut.hom automorphism).comp
          (PackageTotalHom.id (data.package vertex)) = _
      exact (@Category.comp_id
        (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
        _ _ (PackageFiberAut.hom automorphism))
    _ = _ := by
      change _ = (PackageTotalHom.id (data.package vertex)).comp
        (PackageFiberAut.hom automorphism)
      exact (@Category.id_comp
        (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
        _ _ (PackageFiberAut.hom automorphism)).symm

/--
The G-106 syzygy direction hypothesis compares the authored route
comparators of the two declared pastings; it contains no raw-vanishing or
coherentizability certificate.
-/
def SyzygyCompatible
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) : Prop :=
  ∀ cell : G.ThreeCell,
    authoredPastingComparator data reselection (G.threeLeft cell) =
      authoredPastingComparator data reselection (G.threeRight cell)

/--
Pointwise coherence of every authored 2-cell forces every declared 3-cell
pasting to be syzygy-compatible.  The proof first identifies the authored
family with the independently generated G-101 canonical family, then uses
canonical uniqueness for the two complete routes.
-/
theorem syzygyCompatible_of_coherentAt
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    (coherent : CoherentAt data reselection) :
    SyzygyCompatible data reselection := by
  have familyEquality :
      authoredComparatorFamily data =
        canonicalComparatorFamily data reselection := by
    funext cell
    letI : (packageProjection U).IsStronglyCocartesian
        (reselectedPathLift data.lift reselection (G.twoLeft cell)).base
        (reselectedPathLift data.lift reselection (G.twoLeft cell)) :=
      reselectedPathLift_isStronglyCocartesian
        data.lift reselection (G.twoLeft cell)
    apply PackageFiberAut.ext_of_strong_fac
      (reselectedPathLift data.lift reselection (G.twoLeft cell))
    exact (coherent cell).trans
      (canonicalTwoCellComparator_fac data reselection cell).symm
  intro cell
  change pastingComparator data reselection (authoredComparatorFamily data)
      (G.threeLeft cell) =
    pastingComparator data reselection (authoredComparatorFamily data)
      (G.threeRight cell)
  rw [familyEquality]
  exact canonicalPastingComparator_unique data reselection
    (G.threeLeft cell) (G.threeRight cell)

/--
Authored syzygy compatibility implies equality of the two complete route
defects because G-101 uniqueness independently identifies the canonical routes.
-/
theorem rawDefect_cocycle_of_syzygy
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    (compatible : SyzygyCompatible data reselection)
    (cell : G.ThreeCell) :
    defectPastingProduct data reselection (G.threeLeft cell) =
      defectPastingProduct data reselection (G.threeRight cell) := by
  unfold defectPastingProduct pastingRawDefect
  rw [compatible cell]
  rw [canonicalPastingComparator_unique data reselection
    (G.threeLeft cell) (G.threeRight cell)]

/-- Closed route obstruction comparing the two pastings of a declared 3-cell. -/
noncomputable def closedPastingRawObstruction
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) (cell : G.ThreeCell) :
    PackageFiberAut (data.lift.package (G.threeTarget cell)) :=
  (pastingRawDefect data reselection (G.threeRight cell))⁻¹ *
    pastingRawDefect data reselection (G.threeLeft cell)

/-- Authored route mismatch of the two pastings of one declared 3-cell. -/
noncomputable def authoredPastingMismatch
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) (cell : G.ThreeCell) :
    PackageFiberAut (data.lift.package (G.threeTarget cell)) :=
  (authoredPastingComparator data reselection (G.threeRight cell))⁻¹ *
    authoredPastingComparator data reselection (G.threeLeft cell)

/-- The closed raw obstruction is a conjugate of the authored route mismatch. -/
theorem closedPastingRawObstruction_eq_conjugate
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) (cell : G.ThreeCell) :
    closedPastingRawObstruction data reselection cell =
      canonicalPastingComparator data reselection (G.threeLeft cell) *
        authoredPastingMismatch data reselection cell *
          (canonicalPastingComparator data reselection
            (G.threeLeft cell))⁻¹ := by
  unfold closedPastingRawObstruction pastingRawDefect
  unfold authoredPastingMismatch
  rw [← canonicalPastingComparator_unique data reselection
    (G.threeLeft cell) (G.threeRight cell)]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

/-- Closed obstruction is identity exactly when the authored routes agree. -/
theorem closedPastingRawObstruction_eq_one_iff
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) (cell : G.ThreeCell) :
    closedPastingRawObstruction data reselection cell = 1 ↔
      authoredPastingComparator data reselection (G.threeLeft cell) =
        authoredPastingComparator data reselection (G.threeRight cell) := by
  rw [closedPastingRawObstruction_eq_conjugate]
  let canonical :=
    canonicalPastingComparator data reselection (G.threeLeft cell)
  let mismatch := authoredPastingMismatch data reselection cell
  change canonical * mismatch * canonical⁻¹ = 1 ↔ _
  constructor
  · intro equality
    have mismatchIdentity := congrArg
      (fun element => canonical⁻¹ * element * canonical) equality
    have mismatchEq : mismatch = 1 := by
      simpa [mul_assoc] using mismatchIdentity
    have authoredEq := congrArg
      (fun element =>
        authoredPastingComparator data reselection (G.threeRight cell) *
          element) mismatchEq
    simpa [mismatch, authoredPastingMismatch, mul_assoc] using authoredEq
  · intro authoredEq
    dsimp [mismatch, authoredPastingMismatch]
    rw [authoredEq]
    simp

/-- Conjugacy class of the closed route obstruction at one edge coordinate. -/
noncomputable def closedPastingObstructionClass
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) (cell : G.ThreeCell) :
    ConjClasses
      (PackageFiberAut (data.lift.package (G.threeTarget cell))) :=
  ConjClasses.mk (closedPastingRawObstruction data reselection cell)

/--
The closed raw class is exactly the conjugacy class of the authored route
mismatch at the given edge coordinate.  Concrete witnesses with empty outgoing
whiskers prove cross-reselection invariance separately.
-/
theorem closedPastingObstructionClass_eq_authoredMismatchClass
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) (cell : G.ThreeCell) :
    closedPastingObstructionClass data reselection cell =
      ConjClasses.mk (authoredPastingMismatch data reselection cell) := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  rw [closedPastingRawObstruction_eq_conjugate]
  apply IsConj.symm
  exact isConj_iff.mpr
    ⟨canonicalPastingComparator data reselection (G.threeLeft cell), rfl⟩

/-- Unequal authored routes give a nonidentity closed conjugacy class. -/
theorem closedPastingObstructionClass_ne_identity
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift) (cell : G.ThreeCell)
    (authoredNe :
      authoredPastingComparator data reselection (G.threeLeft cell) ≠
        authoredPastingComparator data reselection (G.threeRight cell)) :
    closedPastingObstructionClass data reselection cell ≠
      ConjClasses.mk 1 := by
  intro classIdentity
  have conjugateIdentity :
      IsConj (closedPastingRawObstruction data reselection cell) 1 :=
    ConjClasses.mk_eq_mk_iff_isConj.mp classIdentity
  have rawIdentity :
      closedPastingRawObstruction data reselection cell = 1 :=
    isConj_one_left.mp conjugateIdentity
  exact authoredNe
    ((closedPastingRawObstruction_eq_one_iff data reselection cell).mp
      rawIdentity)

/-- A compatible authored 3-cell has identity closed route obstruction. -/
theorem closedPastingRawObstruction_eq_one_of_syzygy
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (reselection : EdgeReselection data.lift)
    (compatible : SyzygyCompatible data reselection)
    (cell : G.ThreeCell) :
    closedPastingRawObstruction data reselection cell = 1 := by
  have cocycle :=
    rawDefect_cocycle_of_syzygy data reselection compatible cell
  change pastingRawDefect data reselection (G.threeLeft cell) =
      pastingRawDefect data reselection (G.threeRight cell) at cocycle
  unfold closedPastingRawObstruction
  rw [cocycle]
  exact inv_mul_cancel _

end AAT.AG.TransportCoherence

#assert_standard_axioms_only AAT.AG.TransportCoherence
