import ResearchLean.AG.RelativeRepairComposition.SubdivisionOriginalTower

/-!
# Both complete original authored three-cell routes after subdivision

The copied route keeps every oriented face occurrence and complete outgoing
word. Full actual path equality identifies its transported full fiber
comparator. Ordered route induction then identifies both original authored
route comparators and preserves each actual three-cell Law.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)

/-- Every full original fiber automorphism has the same actual transport along its full substituted reference word. -/
theorem whisker_substitute {i j : K.Vertex}
    (a : FiberAut (p ⋙ q) (T.original.object i)) (w : K.Path i j) :
    Arbitrary.whiskerFiberAut (originalTower T chosen F).toTower.upper 1
      (i := Sum.inl i) (j := Sum.inl j) a (substitutePath K chosen w) =
      Arbitrary.whiskerFiberAut T.toTower.upper 1 (i := i) (j := j) a w := by
  apply FiberAut.ext_of_strong_fac (T.toTower.upper.pathLift w)
    (T.toTower.upper.pathLift_isStronglyCocartesian w)
  have hn := Arbitrary.whiskerFiberAut_fac (originalTower T chosen F).toTower.upper 1
    (i := Sum.inl i) (j := Sum.inl j) a
    (substitutePath K chosen w)
  simp only [Arbitrary.fiberAutThenPath,Arbitrary.reselectedPathLift_one,originalTower_selected_path] at hn
  have ho := Arbitrary.whiskerFiberAut_fac T.toTower.upper 1 (i := i) (j := j) a w
  simp only [Arbitrary.fiberAutThenPath,Arbitrary.reselectedPathLift_one] at ho
  exact hn.trans ho.symm

/-- Each full copied oriented face occurrence has exactly the same original authored full fiber comparison. -/
theorem oriented_authored_substitute {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    orientedFaceAuthoredComparator (originalTower T chosen F).toTower.toTransportData 1
      (substituteFace K chosen f) =
      orientedFaceAuthoredComparator T.toTower.toTransportData 1 f := by
  change Arbitrary.whiskerFiberAut (originalTower T chosen F).toTower.upper 1
    (i := Sum.inl (K.twoTarget f.cell)) (j := Sum.inl j)
    (match f.orientation with
     | .forward => T.comparator f.cell
     | .backward => (T.comparator f.cell)⁻¹) (substitutePath K chosen f.outgoing) =
    Arbitrary.whiskerFiberAut T.toTower.upper 1 (i := K.twoTarget f.cell) (j := j)
      (match f.orientation with
       | .forward => T.comparator f.cell
       | .backward => (T.comparator f.cell)⁻¹) f.outgoing
  exact whisker_substitute T chosen F _ f.outgoing

/-- All ordered original authored route steps retain exactly their full actual route comparator. -/
theorem authored_route_substitute {i j : K.Vertex} {w z : K.Path i j}
    (t : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    authoredPastingComparator (originalTower T chosen F).toTower.toTransportData 1
      (substitutePasting K chosen t) =
      authoredPastingComparator T.toTower.toTransportData 1 t := by
  induction t with
  | nil _ => rfl
  | cons s t ih =>
    change authoredPastingComparator (originalTower T chosen F).toTower.toTransportData 1
        (substitutePasting K chosen t) *
      orientedFaceAuthoredComparator (originalTower T chosen F).toTower.toTransportData 1
        (substituteFace K chosen s.face) =
      authoredPastingComparator T.toTower.toTransportData 1 t *
        orientedFaceAuthoredComparator T.toTower.toTransportData 1 s.face
    rw [ih,oriented_authored_substitute]

/-- Actual equality of any two complete original authored routes is equivalent to equality of their full copied routes. -/
theorem authored_syzygy_substitute {i j : K.Vertex} {w z : K.Path i j}
    (a b : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    AuthoredSyzygy (originalTower T chosen F).toTower.toTransportData 1
      (substitutePasting K chosen a) (substitutePasting K chosen b) ↔
      AuthoredSyzygy T.toTower.toTransportData 1 a b := by
  change authoredPastingComparator (originalTower T chosen F).toTower.toTransportData 1
      (substitutePasting K chosen a) =
    authoredPastingComparator (originalTower T chosen F).toTower.toTransportData 1
      (substitutePasting K chosen b) ↔ _
  rw [authored_route_substitute,authored_route_substitute]
  rfl

/-- Every actual original three-cell Law holds on its same named complete pair of copied routes. -/
theorem three_laws
    (h : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTower.toTransportData 1 (K.threeLeft s) (K.threeRight s)) :
    ∀ s : (presentation K chosen).ThreeCell,
      AuthoredSyzygy (originalTower T chosen F).toTower.toTransportData 1
        ((presentation K chosen).threeLeft s) ((presentation K chosen).threeRight s) := by
  intro s
  exact (authored_syzygy_substitute T chosen F (K.threeLeft s) (K.threeRight s)).mpr (h s)

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
