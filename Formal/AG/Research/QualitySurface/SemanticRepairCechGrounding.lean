import Formal.AG.Cohomology.CechComplex
import Formal.AG.Research.QualitySurface.SemanticRepairTrueSheafH1

/-!
G-06 evidence for the AAT site/sheaf/Cech `H1` grounding theorem.

This file connects the G-05 semantic repair additive `Z1 / B1` surface to the
general AAT cover-relative Cech complex API.  The comparison data records only
cochain-level equivalences and differential compatibility; it does not store
zero `H1`, global semantic repair coherence, full sheaf cohomology comparison,
or effective descent conclusions.
-/

noncomputable section

universe u v w x y z r

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairCechGrounding

open CategoryTheory
open Opposite
open SemanticRepairSheafH1
open SemanticRepairTrueSheafH1

/-! ## Atom-generated coverage and selected AAT topology -/

/--
G-06 bridge: an AAT admissible coverage family generates a cover in the
selected `AATGrothendieckTopology`.
-/
theorem atomGeneratedCoverage_generates_AATGrothendieckTopology
    {U : AAT.AG.AtomCarrier.{u}} {A : AAT.AG.ArchitectureObject U}
    {C : AAT.AG.Site.ContextPreorderCategory A}
    {LU : AAT.AG.LawUniverse U}
    {Sig : AAT.AG.ArchitectureSignature U}
    {R : AAT.AG.Site.CoverageRequirements A LU Sig}
    {P : AAT.AG.Site.ContextOverlapPullback C}
    {base : AAT.AG.Site.ContextCategoryObject C}
    (family : AAT.AG.Site.AATCoverageFamily R P base) :
    Sieve.generate family.presieve ∈
      AAT.AG.Site.AATGrothendieckTopology R P base :=
  AAT.AG.Site.AATGrothendieckTopology.generate_mem family

/-- G-06 bridge: an `AATSite` topology is definitionally the generated `J_U`. -/
theorem selectedAATSiteTopology_eq_atomGeneratedGrothendieckTopology
    {U : AAT.AG.AtomCarrier.{u}} {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A) :
    S.topology =
      AAT.AG.Site.AATGrothendieckTopology S.requirements S.overlap :=
  AAT.AG.Site.AATSite.topology_eq S

/-! ## Semantic repair covers as cover-relative Cech covers -/

/--
Selected bridge from a G-05 semantic repair cover to the general AAT
cover-relative Cech cover API.

The fields are provenance maps from typed semantic cover components into the
general cover's selected simplices.  They are input geometry only and do not
store Cech cohomology, zero-class, or gluing conclusions.
-/
structure SemanticRepairCoverRelativeCoverBridge
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    (cover : SemanticRepairCover.{u, v, w} site)
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A) where
  coverRelative : AAT.AG.Cohomology.CoverRelativeCechCover S
  chartSimplex : cover.CoverChart -> coverRelative.simplex 0
  overlapSimplex :
    (Sigma fun pair : cover.CoverChart × cover.CoverChart =>
      cover.Overlap pair.1 pair.2) -> coverRelative.simplex 1
  tripleSimplex :
    (Sigma fun triple : cover.CoverChart × cover.CoverChart × cover.CoverChart =>
      cover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
        coverRelative.simplex 2

namespace SemanticRepairCover

/-- Read a semantic repair cover through the selected general cover-relative target. -/
def toCoverRelativeCechCover
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {cover : SemanticRepairCover.{u, v, w} site}
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    (bridge : SemanticRepairCoverRelativeCoverBridge cover S) :
    AAT.AG.Cohomology.CoverRelativeCechCover S :=
  bridge.coverRelative

end SemanticRepairCover

/--
The G-05 cover nerve's `True` component predicates are justified by typed
component encoding: every edge is literally a selected pairwise-overlap
component, and every face is literally a selected triple-overlap component with
typed boundary edges.
-/
theorem coverNerve_typedComponent_adequacy
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    (cover : SemanticRepairCover.{u, v, w} site) :
    (forall edge : (toCoverNerve cover).EdgeComponent,
      exists pair : cover.CoverChart × cover.CoverChart,
      exists overlap : cover.Overlap pair.1 pair.2,
        edge = Sigma.mk pair overlap /\
          (toCoverNerve cover).edgeLeft edge = pair.1 /\
          (toCoverNerve cover).edgeRight edge = pair.2) /\
      (forall face : (toCoverNerve cover).FaceComponent,
        exists tripleIndex : cover.CoverChart × cover.CoverChart × cover.CoverChart,
        exists triple :
          cover.TripleOverlap tripleIndex.1 tripleIndex.2.1 tripleIndex.2.2,
          face = Sigma.mk tripleIndex triple /\
            (toCoverNerve cover).faceEdge0 face =
              Sigma.mk (tripleIndex.1, tripleIndex.2.1)
                (cover.tripleEdge01 triple) /\
            (toCoverNerve cover).faceEdge1 face =
              Sigma.mk (tripleIndex.2.1, tripleIndex.2.2)
                (cover.tripleEdge12 triple) /\
            (toCoverNerve cover).faceEdge2 face =
              Sigma.mk (tripleIndex.1, tripleIndex.2.2)
                (cover.tripleEdge02 triple)) := by
  constructor
  · intro edge
    rcases edge with ⟨⟨left, right⟩, overlap⟩
    exact ⟨(left, right), overlap, rfl, rfl, rfl⟩
  · intro face
    rcases face with ⟨⟨i, j, k⟩, triple⟩
    exact ⟨(i, j, k), triple, rfl, rfl, rfl, rfl⟩

/-! ## Coefficient, restriction, and additive Cech comparison data -/

/--
Cochain-level comparison between the semantic repair additive Cech data and a
general cover-relative AAT Cech complex.

The fields are equivalences and differential compatibility for degrees 0, 1,
and 2.  They do not store quotient equality, zero-class equality, global
semantic repair coherence, full sheaf cohomology equivalence, or effective
descent.
-/
structure SemanticRepairCoverRelativeH1Comparison
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {cover : AAT.AG.Cohomology.CoverRelativeCechCover S}
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex cover Ob) where
  toC0 : E.coefficient.C0 -> K.Cn 0
  fromC0 : K.Cn 0 -> E.coefficient.C0
  toC1 : E.coefficient.C1 -> K.Cn 1
  fromC1 : K.Cn 1 -> E.coefficient.C1
  toC2 : E.coefficient.C2 -> K.Cn 2
  fromC2 : K.Cn 2 -> E.coefficient.C2
  fromC1_toC1 : forall c : E.coefficient.C1, fromC1 (toC1 c) = c
  toC1_fromC1 : forall c : K.Cn 1, toC1 (fromC1 c) = c
  toC1_sub :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall left right : E.coefficient.C1,
      toC1 (left - right) = toC1 left - toC1 right
  fromC1_sub :
    letI := K.cochainAddCommGroup 1
    letI := additive.c1AddCommGroup
    forall left right : K.Cn 1,
      fromC1 (left - right) = fromC1 left - fromC1 right
  toC2_zero :
    letI := K.cochainAddCommGroup 2
    toC2 E.coefficient.zero2 = 0
  fromC2_zero :
    letI := K.cochainAddCommGroup 2
    fromC2 0 = E.coefficient.zero2
  d0_to :
    forall primitive : E.coefficient.C0,
      K.d 0 (toC0 primitive) = toC1 (E.coefficient.delta0 primitive)
  d0_from :
    forall primitive : K.Cn 0,
      E.coefficient.delta0 (fromC0 primitive) = fromC1 (K.d 0 primitive)
  d1_to :
    forall cochain : E.coefficient.C1,
      K.d 1 (toC1 cochain) = toC2 (E.coefficient.delta1 cochain)
  d1_from :
    forall cochain : K.Cn 1,
      E.coefficient.delta1 (fromC1 cochain) = fromC2 (K.d 1 cochain)

/--
Degree-wise cochain realization of the semantic additive Cech data inside a
selected general cover-relative Cech complex.

This is lower-level provenance than the `H1` comparison package: it records
cochain equivalences and differential compatibility only.  It does not store an
`H1` equivalence, zero-class equality, global semantic repair coherence, full
sheaf cohomology comparison, or effective descent conclusion.
-/
structure SemanticRepairCoverRelativeCochainRealization
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {cover : AAT.AG.Cohomology.CoverRelativeCechCover S}
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex cover Ob) where
  c0Equiv :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    E.coefficient.C0 ≃+ K.Cn 0
  c1Equiv :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    E.coefficient.C1 ≃+ K.Cn 1
  c2Equiv : E.coefficient.C2 ≃ K.Cn 2
  c2Equiv_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv E.coefficient.zero2 = 0
  c2Equiv_symm_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv.symm 0 = E.coefficient.zero2
  d0_to :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : E.coefficient.C0,
      K.d 0 (c0Equiv primitive) = c1Equiv (E.coefficient.delta0 primitive)
  d0_from :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : K.Cn 0,
      E.coefficient.delta0 (c0Equiv.symm primitive) =
        c1Equiv.symm (K.d 0 primitive)
  d1_to :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : E.coefficient.C1,
      K.d 1 (c1Equiv cochain) = c2Equiv (E.coefficient.delta1 cochain)
  d1_from :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : K.Cn 1,
      E.coefficient.delta1 (c1Equiv.symm cochain) =
        c2Equiv.symm (K.d 1 cochain)

namespace SemanticRepairCoverRelativeCochainRealization

variable {Atom : Type u}
variable {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
variable {additive : SemanticRepairAdditiveCechH1Data E}
variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}
variable {cover : AAT.AG.Cohomology.CoverRelativeCechCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex cover Ob}

/--
Construct the selected semantic/general `H1` comparison from degree-wise
cochain realization data.

The inverse and subtraction laws in the resulting comparison are derived from
the additive equivalence on degree one; they are not supplied as independent
`H1` comparison facts.
-/
def toH1Comparison
    (realization : SemanticRepairCoverRelativeCochainRealization additive K) :
    SemanticRepairCoverRelativeH1Comparison additive K where
  toC0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact fun primitive => realization.c0Equiv primitive
  fromC0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact fun primitive => realization.c0Equiv.symm primitive
  toC1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact fun cochain => realization.c1Equiv cochain
  fromC1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact fun cochain => realization.c1Equiv.symm cochain
  toC2 := realization.c2Equiv
  fromC2 := realization.c2Equiv.symm
  fromC1_toC1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    intro cochain
    exact realization.c1Equiv.left_inv cochain
  toC1_fromC1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    intro cochain
    exact realization.c1Equiv.right_inv cochain
  toC1_sub := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    intro left right
    exact AddEquiv.map_sub realization.c1Equiv left right
  fromC1_sub := by
    letI := K.cochainAddCommGroup 1
    letI := additive.c1AddCommGroup
    intro left right
    exact AddEquiv.map_sub realization.c1Equiv.symm left right
  toC2_zero := realization.c2Equiv_zero
  fromC2_zero := realization.c2Equiv_symm_zero
  d0_to := realization.d0_to
  d0_from := realization.d0_from
  d1_to := realization.d1_to
  d1_from := realization.d1_from

end SemanticRepairCoverRelativeCochainRealization

namespace SemanticRepairCoverRelativeH1Comparison

variable {Atom : Type u}
variable {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
variable {additive : SemanticRepairAdditiveCechH1Data E}
variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}
variable {cover : AAT.AG.Cohomology.CoverRelativeCechCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex cover Ob}

/-- Semantic cocycles map to degree-one cocycles in the general Cech complex. -/
def toCoverRelativeCocycle
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (cocycle : SemanticRepairAdditiveH1Cocycle additive) :
    K.CechCocycle 1 := by
  refine ⟨comparison.toC1 cocycle.1, ?_⟩
  rw [comparison.d1_to cocycle.1, cocycle.2, comparison.toC2_zero]

/-- General degree-one Cech cocycles map back to semantic repair cocycles. -/
def fromCoverRelativeCocycle
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (cocycle : K.CechCocycle 1) :
    SemanticRepairAdditiveH1Cocycle additive := by
  refine ⟨comparison.fromC1 cocycle.1, ?_⟩
  change E.coefficient.delta1 (comparison.fromC1 cocycle.1) =
    E.coefficient.zero2
  rw [comparison.d1_from cocycle.1, cocycle.2, comparison.fromC2_zero]

/--
The semantic additive same-class relation is equivalent to the general
cover-relative Cech coboundary relation in degree one.
-/
theorem semantic_sameClass_iff_coverRelative_sameClass
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    {left right : E.coefficient.C1}
    (hleft : CechZ1 E left) (hright : CechZ1 E right) :
    SemanticRepairAdditiveH1SameClass additive left right <->
      (K.CechCoboundarySetoidSucc 0).r
        (comparison.toCoverRelativeCocycle ⟨left, hleft⟩)
        (comparison.toCoverRelativeCocycle ⟨right, hright⟩) := by
  letI := additive.c1AddCommGroup
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  constructor
  · intro hsame
    rcases hsame with ⟨primitive, hprimitive⟩
    refine ⟨comparison.toC0 primitive, ?_⟩
    calc
      comparison.toC1 left - comparison.toC1 right =
          comparison.toC1 (left - right) := by
            rw [comparison.toC1_sub]
      _ = comparison.toC1 (E.coefficient.delta0 primitive) := by
            rw [← hprimitive]
      _ = K.d 0 (comparison.toC0 primitive) := by
            rw [comparison.d0_to]
  · intro hgeneral
    rcases hgeneral with ⟨primitive, hprimitive⟩
    have hprimitive' :
        comparison.toC1 left - comparison.toC1 right = K.d 0 primitive := by
      exact hprimitive
    refine ⟨comparison.fromC0 primitive, ?_⟩
    calc
      E.coefficient.delta0 (comparison.fromC0 primitive) =
          comparison.fromC1 (K.d 0 primitive) :=
            comparison.d0_from primitive
      _ = comparison.fromC1
            (comparison.toC1 left - comparison.toC1 right) := by
            rw [hprimitive']
      _ = comparison.fromC1 (comparison.toC1 left) -
            comparison.fromC1 (comparison.toC1 right) := by
            rw [comparison.fromC1_sub]
      _ = left - right := by
            rw [comparison.fromC1_toC1 left, comparison.fromC1_toC1 right]

/-- Map the semantic additive `H1` quotient to general cover-relative `H1`. -/
def semanticRepairAdditiveH1Class_to_coverRelativeH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    SemanticRepairAdditiveH1Class additive -> K.CechCohomologySucc 0 :=
  Quotient.lift
    (fun cocycle =>
      K.cohomologyClassSucc 0 (comparison.toCoverRelativeCocycle cocycle))
    (by
      intro left right hsame
      exact
        Quotient.sound
          ((comparison.semantic_sameClass_iff_coverRelative_sameClass
            left.2 right.2).1 hsame))

/-- Map general cover-relative `H1` back to the semantic additive quotient. -/
def coverRelativeH1_to_semanticRepairAdditiveH1Class
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    K.CechCohomologySucc 0 -> SemanticRepairAdditiveH1Class additive :=
  Quotient.lift
    (fun cocycle =>
      semanticRepairAdditiveH1Class_mk additive
        (comparison.fromC1 cocycle.1)
        (comparison.fromCoverRelativeCocycle cocycle).2)
    (by
      intro left right hsame
      have hgeneral :
          (K.CechCoboundarySetoidSucc 0).r
            (comparison.toCoverRelativeCocycle
              (comparison.fromCoverRelativeCocycle left))
            (comparison.toCoverRelativeCocycle
              (comparison.fromCoverRelativeCocycle right)) := by
        letI := K.cochainAddCommGroup 1
        rcases hsame with ⟨primitive, hprimitive⟩
        refine ⟨primitive, ?_⟩
        change
          comparison.toC1 (comparison.fromC1 left.1) -
              comparison.toC1 (comparison.fromC1 right.1) =
            K.d 0 primitive
        rw [comparison.toC1_fromC1 left.1, comparison.toC1_fromC1 right.1]
        exact hprimitive
      exact
        semanticRepairAdditiveH1Class_eq_of_sameClass additive
          (comparison.fromCoverRelativeCocycle left).2
          (comparison.fromCoverRelativeCocycle right).2
          ((comparison.semantic_sameClass_iff_coverRelative_sameClass
            (comparison.fromCoverRelativeCocycle left).2
            (comparison.fromCoverRelativeCocycle right).2).2 hgeneral))

/--
The two selected comparison maps are inverse on the semantic additive quotient.

This is a quotient-level proof, not a structure field: it follows from the
cochain inverse law `fromC1_toC1`.
-/
theorem coverRelative_to_semanticRepairAdditiveH1Class_left_inverse
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    Function.LeftInverse
      comparison.coverRelativeH1_to_semanticRepairAdditiveH1Class
      comparison.semanticRepairAdditiveH1Class_to_coverRelativeH1 := by
  intro semanticClass
  refine Quotient.inductionOn semanticClass ?_
  intro cocycle
  exact
    semanticRepairAdditiveH1Class_eq_of_sameClass additive
      (comparison.fromCoverRelativeCocycle
        (comparison.toCoverRelativeCocycle cocycle)).2
      cocycle.2
      (by
        letI := additive.c0AddCommGroup
        letI := additive.c1AddCommGroup
        refine ⟨(0 : E.coefficient.C0), ?_⟩
        calc
          E.coefficient.delta0 (0 : E.coefficient.C0) = 0 := additive.delta0_zero
          _ = comparison.fromC1 (comparison.toC1 cocycle.1) - cocycle.1 := by
            rw [comparison.fromC1_toC1 cocycle.1]
            simp)

/--
The selected comparison maps are inverse on the general cover-relative `H1`
quotient.

This proof uses only the cochain inverse law `toC1_fromC1` and the general
Cech coboundary setoid's zero boundary.
-/
theorem semanticRepairAdditiveH1Class_to_coverRelative_right_inverse
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    Function.RightInverse
      comparison.coverRelativeH1_to_semanticRepairAdditiveH1Class
      comparison.semanticRepairAdditiveH1Class_to_coverRelativeH1 := by
  intro coverClass
  refine Quotient.inductionOn coverClass ?_
  intro cocycle
  apply Quotient.sound
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  refine ⟨0, ?_⟩
  change
    comparison.toC1 (comparison.fromC1 cocycle.1) - cocycle.1 =
      K.d 0 0
  rw [comparison.toC1_fromC1 cocycle.1]
  simp

/--
Selected equivalence between the G-05 semantic additive `H1` quotient and the
general cover-relative Cech `H1` surface.

The equivalence is constructed from cochain-level compatibility and quotient
proofs; it is not supplied as a certificate field.
-/
def semanticRepairAdditiveH1_equiv_coverRelativeH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    SemanticRepairAdditiveH1Class additive ≃ K.CechCohomologySucc 0 where
  toFun := comparison.semanticRepairAdditiveH1Class_to_coverRelativeH1
  invFun := comparison.coverRelativeH1_to_semanticRepairAdditiveH1Class
  left_inv :=
    comparison.coverRelative_to_semanticRepairAdditiveH1Class_left_inverse
  right_inv :=
    comparison.semanticRepairAdditiveH1Class_to_coverRelative_right_inverse

/-- The selected residual zero predicate in the general cover-relative `H1`. -/
def CoverRelativeResidualH1Zero
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) : Prop :=
  K.cohomologyClassSucc 0
      (comparison.toCoverRelativeCocycle
        ⟨E.coefficient.residual, E.coefficient.residual_cocycle⟩) =
    K.cohomologyClassSucc 0
      (comparison.toCoverRelativeCocycle
        ⟨E.coefficient.zero1, E.coefficient.zero1_cocycle⟩)

/--
Zero of the G-05 semantic additive class is equivalent to zero of the selected
general cover-relative Cech `H1` class.
-/
theorem semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    SemanticRepairAdditiveH1Zero additive <->
      comparison.CoverRelativeResidualH1Zero := by
  constructor
  · intro hzero
    have hsame :
        SemanticRepairAdditiveH1SameClass additive
          E.coefficient.residual E.coefficient.zero1 :=
      (semanticRepairAdditiveH1Zero_iff_sameClass_zero additive).1 hzero
    exact
      Quotient.sound
        ((comparison.semantic_sameClass_iff_coverRelative_sameClass
          E.coefficient.residual_cocycle E.coefficient.zero1_cocycle).1 hsame)
  · intro hzero
    apply (semanticRepairAdditiveH1Zero_iff_sameClass_zero additive).2
    exact
      ((comparison.semantic_sameClass_iff_coverRelative_sameClass
        E.coefficient.residual_cocycle E.coefficient.zero1_cocycle).2
          (Quotient.exact hzero))

/--
The comparison theorem package: semantic additive `H1`, general cover-relative
`H1`, and the residual zero predicates agree under the cochain-level
comparison.
-/
structure SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    Type (max u v w x y z r) where
  toCoverRelativeH1 :
    SemanticRepairAdditiveH1Class additive -> K.CechCohomologySucc 0
  fromCoverRelativeH1 :
    K.CechCohomologySucc 0 -> SemanticRepairAdditiveH1Class additive
  h1Equiv :
    SemanticRepairAdditiveH1Class additive ≃ K.CechCohomologySucc 0
  sameClass_iff_coverRelative :
    forall {left right : E.coefficient.C1}
      (hleft : CechZ1 E left) (hright : CechZ1 E right),
      SemanticRepairAdditiveH1SameClass additive left right <->
        (K.CechCoboundarySetoidSucc 0).r
          (comparison.toCoverRelativeCocycle ⟨left, hleft⟩)
          (comparison.toCoverRelativeCocycle ⟨right, hright⟩)
  zero_iff_coverRelativeZero :
    SemanticRepairAdditiveH1Zero additive <->
      comparison.CoverRelativeResidualH1Zero

/-- Concrete comparison package constructed from cochain-level compatibility. -/
def semanticRepairAdditiveH1_coverRelativeH1_comparison_packageData
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage comparison where
  toCoverRelativeH1 :=
    comparison.semanticRepairAdditiveH1Class_to_coverRelativeH1
  fromCoverRelativeH1 :=
    comparison.coverRelativeH1_to_semanticRepairAdditiveH1Class
  h1Equiv :=
    comparison.semanticRepairAdditiveH1_equiv_coverRelativeH1
  sameClass_iff_coverRelative := by
    intro left right hleft hright
    exact comparison.semantic_sameClass_iff_coverRelative_sameClass hleft hright
  zero_iff_coverRelativeZero :=
    comparison.semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero

/-- The comparison package exists without storing zero-class or gluing conclusions. -/
theorem semanticRepairAdditiveH1_coverRelativeH1_comparison_package
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    Nonempty (SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage comparison) :=
  ⟨comparison.semanticRepairAdditiveH1_coverRelativeH1_comparison_packageData⟩

end SemanticRepairCoverRelativeH1Comparison

namespace SemanticRepairCoverRelativeCochainRealization

variable {Atom : Type u}
variable {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
variable {additive : SemanticRepairAdditiveCechH1Data E}
variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}
variable {cover : AAT.AG.Cohomology.CoverRelativeCechCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex cover Ob}

/--
The selected cover-relative grounding package follows from cochain realization
data plus the existing quotient-level comparison theorem.
-/
theorem grounded_package_of_cochain_realization
    (realization : SemanticRepairCoverRelativeCochainRealization additive K) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        realization.toH1Comparison) :=
  realization.toH1Comparison.semanticRepairAdditiveH1_coverRelativeH1_comparison_package

end SemanticRepairCoverRelativeCochainRealization

/-! ## Presheaf restriction, sheaf condition, descent, and claim boundaries -/

/-- Obstruction sheaves expose presheaf restriction maps preserving zero. -/
theorem semanticResidualCoefficient_presheafRestriction_zero
    {U : AAT.AG.AtomCarrier.{u}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    (Ob : AAT.AG.Cohomology.ObstructionSheaf S)
    {source target : S.category} (f : source ⟶ target) :
    letI := Ob.addCommGroup target
    letI := Ob.addCommGroup source
    Ob.carrier.toPresheaf.map f.op 0 = 0 :=
  Ob.map_zero f

/-- Obstruction sheaves expose additive restriction laws. -/
theorem semanticResidualCoefficient_presheafRestriction_add
    {U : AAT.AG.AtomCarrier.{u}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    (Ob : AAT.AG.Cohomology.ObstructionSheaf S)
    {source target : S.category} (f : source ⟶ target)
    (x y : Ob.carrier.toPresheaf.obj (op target)) :
    letI := Ob.addCommGroup target
    letI := Ob.addCommGroup source
    Ob.carrier.toPresheaf.map f.op (x + y) =
      Ob.carrier.toPresheaf.map f.op x +
        Ob.carrier.toPresheaf.map f.op y :=
  Ob.map_add f x y

/--
Mathlib-backed AAT sheaf condition plus selected cover membership gives
cover-wise descent and an effective global gluing section for any compatible
local family.
-/
theorem aatSheafCondition_coverMembership_descent_effectiveGluing
    {U : AAT.AG.AtomCarrier.{u}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A} {F : AAT.AG.Site.AATPresheaf S}
    (hSheaf : AAT.AG.Site.AATSheafCondition S F)
    {base : S.category} (cover : Sieve base)
    (hcover : cover ∈ S.topology base)
    (data : AAT.AG.Site.AATGluingData S F cover) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      ∃! globalSection : F.obj (op base),
        AAT.AG.Site.AATGlobalSectionRealizes data globalSection := by
  let hFor := AAT.AG.Site.AATSheafCondition.cover hSheaf cover hcover
  let hDescent := AAT.AG.Site.AATSheafConditionFor.descent hFor
  exact ⟨hFor, hDescent, hDescent data⟩

/--
Extra data required before cover-relative Cech `H1` can be compared with a full
sheaf cohomology surface.  G-06 constructs no inhabitant of this structure.
-/
structure CoverRelativeCechH1FullSheafCohomologyComparison
    {U : AAT.AG.AtomCarrier.{u}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {cover : AAT.AG.Cohomology.CoverRelativeCechCover S}
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (_K : AAT.AG.Cohomology.CoverRelativeCechComplex cover Ob)
    (FullSheafH1 : Type u) where
  toFullSheafH1 : _K.CechCohomologySucc 0 -> FullSheafH1
  fromFullSheafH1 : FullSheafH1 -> _K.CechCohomologySucc 0

/--
G-06 boundary theorem: this package is cover-relative Cech `H1` only.  A full
sheaf cohomology comparison is visible as additional data, not an unconditional
consequence of the grounding package.
-/
theorem coverRelativeCechH1_requires_explicit_fullSheafCohomologyComparison
    {U : AAT.AG.AtomCarrier.{u}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {cover : AAT.AG.Cohomology.CoverRelativeCechCover S}
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    {K : AAT.AG.Cohomology.CoverRelativeCechComplex cover Ob}
    {FullSheafH1 : Type u}
    (comparison :
      CoverRelativeCechH1FullSheafCohomologyComparison K FullSheafH1) :
    Nonempty
      (CoverRelativeCechH1FullSheafCohomologyComparison K FullSheafH1) :=
  ⟨comparison⟩

/-- Extra data required for general cover-refinement naturality. -/
structure CoverRefinementNaturalityComparison
    {Atom : Type u}
    (coarse fine : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom) where
  pullbackC1 : coarse.coefficient.C1 -> fine.coefficient.C1
  preservesResidual :
    pullbackC1 coarse.coefficient.residual = fine.coefficient.residual
  preservesZero :
    pullbackC1 coarse.coefficient.zero1 = fine.coefficient.zero1

/--
G-06 boundary theorem: this file fixes selected-comparison naturality.  A
general cover-refinement functoriality theorem is outside this package unless
an explicit refinement comparison is supplied.
-/
theorem coverRefinementNaturality_requires_explicit_comparison
    {Atom : Type u}
    {coarse fine : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
    (comparison : CoverRefinementNaturalityComparison coarse fine) :
    Nonempty (CoverRefinementNaturalityComparison coarse fine) :=
  ⟨comparison⟩

/--
Final G-06 Lean package surface.  It intentionally returns cover-relative Cech
`H1` comparison and zero equivalence, plus proof-use surfaces for selected
topology, presheaf restriction, sheaf descent, and cover-nerve provenance.  It
does not return a full sheaf cohomology equivalence or an unconditional
refinement theorem.
-/
theorem trueSheafH1_grounded_in_coverRelativeCechH1_package
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
    {additive : SemanticRepairAdditiveCechH1Data E}
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {cover : AAT.AG.Cohomology.CoverRelativeCechCover S}
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    {K : AAT.AG.Cohomology.CoverRelativeCechComplex cover Ob}
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        comparison) :=
  comparison.semanticRepairAdditiveH1_coverRelativeH1_comparison_package

/--
G-06 fail-closed boundary: the selected cover-relative Cech `H1` grounding
requires explicit provenance for the semantic-to-general cochain comparison.

The quotient equivalence above is theorem-level once this comparison is
available, but this theorem deliberately does not construct the comparison from
only a semantic repair cover, residual coefficient surface, or arbitrary general
cover-relative complex.
-/
theorem trueSheafH1_grounding_requires_explicit_comparison_provenance
    {Atom : Type u}
    {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
    {additive : SemanticRepairAdditiveCechH1Data E}
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {cover : AAT.AG.Cohomology.CoverRelativeCechCover S}
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    {K : AAT.AG.Cohomology.CoverRelativeCechComplex cover Ob}
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    Nonempty (SemanticRepairCoverRelativeH1Comparison additive K) :=
  ⟨comparison⟩

/--
G-06 cochain-level fail-closed boundary: simplex-level cover provenance alone is
not the same as degree-wise cochain realization provenance.

The semantic cover bridge records how charts, overlaps, and triple-overlaps land
in a selected cover-relative Cech cover.  To ground the semantic additive `H1`
surface in the general cover-relative Cech complex, one must also supply or
construct equivalences between the semantic `C0/C1/C2` carriers and the selected
section-family cochains, together with zero and differential compatibility.
-/
theorem trueSheafH1_grounding_requires_explicit_cochain_realization_provenance
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
    {additive : SemanticRepairAdditiveCechH1Data E}
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    {K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob}
    (realization :
      SemanticRepairCoverRelativeCochainRealization additive K) :
    Nonempty (SemanticRepairCoverRelativeCochainRealization additive K) :=
  ⟨realization⟩

end SemanticRepairCechGrounding
end QualitySurface
end Formal.AG.Research
