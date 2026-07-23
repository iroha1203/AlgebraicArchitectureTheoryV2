import ResearchLean.AG.QualitySurface.SemanticRepairLawEquationWitnessInstance

/-!
G-06 review obligation 2: the `H1` comparison exercised on a nonzero class.

The rejected final review after Cycle 350 required a finite instance with a
nonzero cover-relative residual class, on which the zero-predicate equivalence
`semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero` demonstrably transfers
nonzero-ness in both directions.

This file builds that instance over the finite-model site with the
law-equation obstruction-quotient coefficient.  The cover-relative complex is
the selected circle nerve: two vertices, two edges with opposite orientations,
and no selected simplices in degree two or higher.  The coefficient group at
every overlap is the law-equation quotient `ℤ ⧸ I_Ob`, so the nonzero residual
class reduces exactly to the Cycle 349 nondegeneracy witness: the class of the
defect `1` is nonzero.

Boundary discipline: the circle nerve is selected simplicial data over the
singleton finite-model cover, in the same selected-data position as every
`CoverRelativeCechCover` simplex family; it is not claimed to be generated
from atom-level chart intersections.  The residual is a `1`-cocycle because
the selected complex has no degree-`2` simplices; this is stated, not hidden.
What the instance demonstrates is precisely what obligation 2 asks: the
semantic-additive and cover-relative `H1` zero predicates agree on a class
that is provably nonzero on both sides.
-/

noncomputable section

universe u v w x y z r a b

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairCechGrounding

open CategoryTheory
open Opposite
open SemanticRepairSheafH1
open SemanticRepairTrueSheafH1
open SemanticRepairObstructionTower

namespace SemanticRepairCoverRelativeCochainRealization
namespace CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis

open CoverRelativeCechGeneratedSemanticCoefficient

/-! ## The selected circle nerve over the finite-model site -/

/--
The selected circle-nerve cover-relative cover: two vertices, two edges with
opposite orientations, no simplices in degree two or higher.  Charts and
overlaps are the singleton finite-model context; the simplicial structure is
selected data.
-/
def circleNerveCover :
    AAT.AG.Cohomology.CoverRelativeCechCover AAT.AG.FiniteModel.site where
  base := AAT.AG.FiniteModel.siteBase
  Index := Bool
  chart := fun _ => AAT.AG.FiniteModel.siteBase
  inclusion := fun _ => CategoryStruct.id AAT.AG.FiniteModel.siteBase
  simplex := fun n =>
    match n with
    | 0 => Bool
    | 1 => Bool
    | _ + 2 => Empty
  overlap := fun _ _ => AAT.AG.FiniteModel.siteBase
  face := fun n =>
    match n with
    | 0 => fun i sigma => if i = (0 : Fin 2) then sigma else !sigma
    | _ + 1 => fun _ sigma => Empty.elim sigma
  faceRestriction := fun n =>
    match n with
    | 0 => fun _ _ => CategoryStruct.id AAT.AG.FiniteModel.siteBase
    | _ + 1 => fun _ sigma => Empty.elim sigma

/-- Shorthand for the law-equation obstruction coefficient over the finite model. -/
abbrev finiteModelObstructionCoefficient :
    AAT.AG.Cohomology.ObstructionSheaf AAT.AG.FiniteModel.site :=
  finiteModelLawEquationGeometry.lawEquationObstructionSheaf

/-- The selected circle-nerve cochain groups are pointwise additive groups. -/
instance circleCochainAddCommGroup (n : Nat) :
    AddCommGroup
      (AAT.AG.Cohomology.CoverRelativeCechCochain circleNerveCover
        finiteModelObstructionCoefficient n) :=
  Pi.addCommGroup

/-- The degree-`0` circle-nerve differential: the alternating face combination. -/
def circleDifferentialZero :
    AAT.AG.Cohomology.CoverRelativeCechCochain circleNerveCover
        finiteModelObstructionCoefficient 0 →+
      AAT.AG.Cohomology.CoverRelativeCechCochain circleNerveCover
        finiteModelObstructionCoefficient 1 :=
  AddMonoidHom.mk'
    (fun c => fun sigma =>
      finiteModelObstructionCoefficient.carrier.toPresheaf.map
          (circleNerveCover.faceRestriction 0 0 sigma).op
          (c (circleNerveCover.face 0 0 sigma)) -
        finiteModelObstructionCoefficient.carrier.toPresheaf.map
          (circleNerveCover.faceRestriction 0 1 sigma).op
          (c (circleNerveCover.face 0 1 sigma)))
    (by
      intro c c'
      funext sigma
      show
        finiteModelObstructionCoefficient.carrier.toPresheaf.map
            (circleNerveCover.faceRestriction 0 0 sigma).op
            (c (circleNerveCover.face 0 0 sigma) +
              c' (circleNerveCover.face 0 0 sigma)) -
          finiteModelObstructionCoefficient.carrier.toPresheaf.map
            (circleNerveCover.faceRestriction 0 1 sigma).op
            (c (circleNerveCover.face 0 1 sigma) +
              c' (circleNerveCover.face 0 1 sigma)) =
        (finiteModelObstructionCoefficient.carrier.toPresheaf.map
            (circleNerveCover.faceRestriction 0 0 sigma).op
            (c (circleNerveCover.face 0 0 sigma)) -
          finiteModelObstructionCoefficient.carrier.toPresheaf.map
            (circleNerveCover.faceRestriction 0 1 sigma).op
            (c (circleNerveCover.face 0 1 sigma))) +
        (finiteModelObstructionCoefficient.carrier.toPresheaf.map
            (circleNerveCover.faceRestriction 0 0 sigma).op
            (c' (circleNerveCover.face 0 0 sigma)) -
          finiteModelObstructionCoefficient.carrier.toPresheaf.map
            (circleNerveCover.faceRestriction 0 1 sigma).op
            (c' (circleNerveCover.face 0 1 sigma)))
      rw [finiteModelObstructionCoefficient.map_add,
        finiteModelObstructionCoefficient.map_add]
      abel)

/--
The selected circle-nerve cover-relative Cech complex over the law-equation
obstruction-quotient coefficient.  The degree-`0` differential is the
alternating face combination; the higher differentials are zero because no
higher simplices are selected.
-/
def circleNerveComplex :
    AAT.AG.Cohomology.CoverRelativeCechComplex circleNerveCover
      finiteModelObstructionCoefficient where
  cochainAddCommGroup := fun _ => inferInstance
  alternatingFaceCombination := fun n =>
    match n with
    | 0 => fun terms => fun sigma => terms sigma 0 - terms sigma 1
    | _ + 1 => fun _ => 0
  differential := fun n =>
    match n with
    | 0 => circleDifferentialZero
    | _ + 1 => 0
  differential_eq_alternatingFaceCombination := fun n =>
    match n with
    | 0 => fun _ => rfl
    | _ + 1 => fun _ => rfl
  differential_comp := fun n =>
    match n with
    | 0 => fun _ => rfl
    | _ + 1 => fun _ => rfl

/-- The section carrier shared by all circle-nerve vertices, edges, and charts. -/
abbrev CircleSection : Type :=
  finiteModelObstructionCoefficient.carrier.toPresheaf.obj
    (op AAT.AG.FiniteModel.siteBase)

/-- The nonzero witness section: the obstruction-quotient class of the defect `1`. -/
def circleDefectOneSection : CircleSection :=
  finiteModelLawEquationGeometry.toObstructionSection
    AAT.AG.FiniteModel.siteBase
    (Ideal.Quotient.mk
      (AAT.AG.FiniteModel.site.equationSystem.obstructionIdeal
        AAT.AG.FiniteModel.siteBase)
      (1 : ℤ))

/-- Read a degree-`0` circle cochain at a vertex, in the shared section carrier. -/
def circleVertexValue (primitive : circleNerveComplex.Cn 0) (vertex : Bool) :
    CircleSection :=
  primitive vertex

/-- The zeroth face of a circle edge is the edge itself (its target vertex). -/
theorem circle_face_zero (sigma : Bool) :
    circleNerveCover.face 0 0 sigma = sigma :=
  rfl

/-- The first face of a circle edge is its negation (its source vertex). -/
theorem circle_face_one (sigma : Bool) :
    circleNerveCover.face 0 1 sigma = !sigma :=
  rfl

/--
The degree-`0` circle differential evaluates to the difference of the vertex
values at the target and source of each edge.
-/
theorem circleDifferentialZero_apply
    (primitive : circleNerveComplex.Cn 0) (sigma : Bool) :
    circleNerveComplex.d 0 primitive sigma =
      circleVertexValue primitive sigma -
        circleVertexValue primitive (!sigma) := by
  show
    finiteModelObstructionCoefficient.carrier.toPresheaf.map
        (CategoryStruct.id AAT.AG.FiniteModel.siteBase).op
        (primitive sigma) -
      finiteModelObstructionCoefficient.carrier.toPresheaf.map
        (CategoryStruct.id AAT.AG.FiniteModel.siteBase).op
        (primitive (!sigma)) =
    circleVertexValue primitive sigma - circleVertexValue primitive (!sigma)
  simp only [CategoryTheory.op_id, CategoryTheory.Functor.map_id,
    CategoryTheory.types_id_apply]
  rfl

/--
The selected nonzero residual `1`-cochain: the class of the defect `1` on the
first edge and zero on the second.
-/
def circleResidual : circleNerveComplex.Cn 1 :=
  fun sigma => cond sigma circleDefectOneSection 0

/--
Nonzero-ness at the cover-relative level: the circle residual is not a
degree-`0` coboundary.  The proof reduces to the Cycle 349 nondegeneracy
witness: the two edge equations force the class of the defect `1` to vanish,
which is impossible.
-/
theorem circleResidual_not_coboundary :
    ¬ Exists fun primitive : circleNerveComplex.Cn 0 =>
        circleNerveComplex.d 0 primitive = circleResidual := by
  rintro ⟨primitive, hprimitive⟩
  have htrue :
      circleVertexValue primitive true - circleVertexValue primitive false =
        circleDefectOneSection := by
    have h := (circleDifferentialZero_apply primitive true).symm.trans
      (congrFun hprimitive true)
    exact h
  have hfalse :
      circleVertexValue primitive false - circleVertexValue primitive true =
        0 := by
    have h := (circleDifferentialZero_apply primitive false).symm.trans
      (congrFun hprimitive false)
    exact h
  have heq : circleVertexValue primitive false = circleVertexValue primitive true :=
    sub_eq_zero.mp hfalse
  rw [heq, sub_self] at htrue
  exact
    finiteModel_defectOne_class_ne_zero AAT.AG.FiniteModel.siteBase htrue.symm

/-! ## Semantic envelope, additive data, and the identity comparison -/

/--
The semantic repair sheaf `H1` envelope of the circle instance: carriers are
the circle-nerve cochain groups, the differentials are the circle-nerve
differentials, and the selected residual is the nonzero circle residual.
The cohomologous relation is the additive boundary relation.
-/
def circleEnvelope :
    SemanticRepairSheafH1Envelope.{0, 0, 0, 0, 0}
      AAT.AG.FiniteModel.carrier.Atom where
  site := finiteModelSemanticRepairSite
  coefficient :=
    { C0 := circleNerveComplex.Cn 0
      C1 := circleNerveComplex.Cn 1
      C2 := circleNerveComplex.Cn 2
      c0Order := []
      c1Order := []
      zero1 := 0
      zero2 := 0
      delta0 := fun primitive => circleNerveComplex.d 0 primitive
      delta1 := fun cochain => circleNerveComplex.d 1 cochain
      zero1_cocycle := map_zero (circleNerveComplex.d 1)
      delta1_delta0_zero := fun primitive =>
        circleNerveComplex.differential_comp 0 primitive
      residual := circleResidual
      residual_cocycle := rfl }
  primitiveSemanticallyClosed := fun _ => True
  torsorObstruction := false
  higherObstruction := false
  stackObstruction := false
  finiteShadow := fun _ => false
  finiteShadow_boundary_zero := fun _ => rfl
  cohomologous := fun left right =>
    Exists fun primitive : circleNerveComplex.Cn 0 =>
      circleNerveComplex.d 0 primitive = left - right
  cohomologous_refl := fun cochain =>
    ⟨0, by rw [map_zero, sub_self]⟩
  cohomologous_symm := by
    rintro left right ⟨primitive, hprimitive⟩
    exact ⟨-primitive, by rw [map_neg, hprimitive, neg_sub]⟩
  cohomologous_trans := by
    rintro left middle right ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨p + q, ?_⟩
    rw [map_add, hp, hq]
    abel
  boundary_cohomologous_zero := fun primitive =>
    ⟨primitive, by rw [sub_zero]⟩
  exact_boundary_of_cohomologous_zero := by
    rintro cochain _hcocycle ⟨primitive, hprimitive⟩
    rw [sub_zero] at hprimitive
    exact ⟨primitive, hprimitive⟩

/-- The additive Cech `H1` data of the circle envelope. -/
def circleAdditive : SemanticRepairAdditiveCechH1Data circleEnvelope where
  c0AddCommGroup := circleCochainAddCommGroup 0
  c1AddCommGroup := circleCochainAddCommGroup 1
  zero1_eq_zero := rfl
  delta0_zero := map_zero (circleNerveComplex.d 0)
  delta0_add := map_add (circleNerveComplex.d 0)
  delta0_neg := map_neg (circleNerveComplex.d 0)

/--
The identity cochain-level comparison between the circle envelope and the
circle-nerve cover-relative complex.  Every map is the identity and every law
is definitional; the comparison is therefore maximally transparent.
-/
def circleComparison :
    SemanticRepairCoverRelativeH1Comparison circleAdditive circleNerveComplex where
  toC0 := id
  fromC0 := id
  toC1 := id
  fromC1 := id
  toC2 := id
  fromC2 := id
  fromC1_toC1 := fun _ => rfl
  toC1_fromC1 := fun _ => rfl
  toC1_sub := fun _ _ => rfl
  fromC1_sub := fun _ _ => rfl
  toC2_zero := rfl
  fromC2_zero := rfl
  d0_to := fun _ => rfl
  d0_from := fun _ => rfl
  d1_to := fun _ => rfl
  d1_from := fun _ => rfl

/-! ## Nonzero-ness and its transfer through the zero-predicate equivalence -/

/-- The semantic additive `H1` class of the circle residual is nonzero. -/
theorem circle_semanticAdditiveH1_ne_zero :
    ¬ SemanticRepairAdditiveH1Zero circleAdditive := by
  intro hzero
  have hsame :=
    (semanticRepairAdditiveH1Zero_iff_sameClass_zero circleAdditive).1 hzero
  rcases hsame with ⟨primitive, hprimitive⟩
  refine circleResidual_not_coboundary ⟨primitive, ?_⟩
  letI := circleAdditive.c1AddCommGroup
  have hsub :
      circleEnvelope.coefficient.residual - circleEnvelope.coefficient.zero1 =
        circleResidual := by
    show circleResidual - (0 : circleNerveComplex.Cn 1) = circleResidual
    rw [sub_zero]
  rw [← hsub]
  exact hprimitive

/--
Nonzero-ness transfers to the cover-relative side through the zero-predicate
equivalence: the general cover-relative `H1` class of the circle residual is
also nonzero.
-/
theorem circle_coverRelativeH1_ne_zero :
    ¬ circleComparison.CoverRelativeResidualH1Zero := fun hzero =>
  circle_semanticAdditiveH1_ne_zero
    ((SemanticRepairCoverRelativeH1Comparison.semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero
      circleComparison).2 hzero)

/--
G-06 review obligation 2 packet: the zero-predicate equivalence holds on the
circle instance, and both its sides are provably nonzero.  The `H1`
comparison surface is therefore demonstrated on non-boundary content: it
transfers nonzero-ness in both directions, not only the trivial zero case.
-/
theorem circle_nonzeroClass_transfer_packet :
    (SemanticRepairAdditiveH1Zero circleAdditive <->
        circleComparison.CoverRelativeResidualH1Zero) /\
      ¬ SemanticRepairAdditiveH1Zero circleAdditive /\
      ¬ circleComparison.CoverRelativeResidualH1Zero :=
  ⟨SemanticRepairCoverRelativeH1Comparison.semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero
      circleComparison,
    circle_semanticAdditiveH1_ne_zero,
    circle_coverRelativeH1_ne_zero⟩

end CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis
end SemanticRepairCoverRelativeCochainRealization

end SemanticRepairCechGrounding
end QualitySurface
end ResearchLean.AG
