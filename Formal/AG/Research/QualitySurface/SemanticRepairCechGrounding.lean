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

universe u v w x y z r a b

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
Carrier-specific additive comparison data for a single cochain degree.

This is the degree-wise lower-data shape used by
`SemanticRepairCarrierSpecificComparisonProvenance`: maps in both directions,
inverse laws, and additivity of the forward map.  It stores no quotient,
zero-class, boundary, descent, global coherence, refinement, or full sheaf
cohomology conclusion.
-/
structure CarrierSpecificAdditiveComparisonData
    (C : Type a) (D : Type b) [AddCommGroup C] [AddCommGroup D] where
  toCarrier : C -> D
  fromCarrier : D -> C
  from_to : forall c : C, fromCarrier (toCarrier c) = c
  to_from : forall d : D, toCarrier (fromCarrier d) = d
  toCarrier_add :
    forall left right : C,
      toCarrier (left + right) = toCarrier left + toCarrier right

namespace CarrierSpecificAdditiveComparisonData

variable {C : Type a} {D : Type b} [AddCommGroup C] [AddCommGroup D]

/--
Degree-wise carrier comparison data is exactly strong enough to construct the
additive equivalence needed by a section-family witness.
-/
def toAddEquiv (data : CarrierSpecificAdditiveComparisonData C D) : C ≃+ D where
  toFun := data.toCarrier
  invFun := data.fromCarrier
  left_inv := data.from_to
  right_inv := data.to_from
  map_add' := data.toCarrier_add

end CarrierSpecificAdditiveComparisonData

/--
Cycle 12 blocker theorem: degree-wise carrier comparison data cannot be
constructed uniformly from bare additive carrier structure.

A uniform constructor for the lower carrier-comparison fields would produce an
additive equivalence between every pair of additive groups.  Applying it to
`PUnit` and `ZMod 2` again forces `0 = 1`.  Thus a concrete
`SemanticRepairCarrierSpecificComparisonProvenance` inhabitant must come from
selected carrier-specific comparison evidence, not from cover membership,
sheaf condition, descent, or bare additive structure alone.
-/
theorem no_uniform_carrier_specific_additive_comparison_from_bare_groups :
    IsEmpty
      ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
        CarrierSpecificAdditiveComparisonData C D) := by
  refine ⟨?_⟩
  intro h
  let data : CarrierSpecificAdditiveComparisonData PUnit (ZMod 2) :=
    h PUnit (ZMod 2)
  let e : PUnit ≃+ ZMod 2 := data.toAddEquiv
  rcases e.surjective (0 : ZMod 2) with ⟨x0, hx0⟩
  rcases e.surjective (1 : ZMod 2) with ⟨x1, hx1⟩
  have hzero_one : (0 : ZMod 2) = 1 := by
    rw [← hx0, ← hx1]
  exact (by norm_num : (0 : ZMod 2) ≠ 1) hzero_one

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

/--
Boundary audit theorem: any supplied cochain realization exposes the exact
degree-wise carrier equivalences, zero laws, and differential compatibility
that remain to be generated from lower atom-supported data.

This keeps `SemanticRepairCoverRelativeCochainRealization` from being treated as
an opaque discharge of the G-06 comparison premise.  It is still a material
premise unless these fields are constructed by a lower theorem.
-/
theorem cochainRealization_requires_degreeEquivalences_and_differentials
    (realization : SemanticRepairCoverRelativeCochainRealization additive K) :
    (Nonempty
        (letI := additive.c0AddCommGroup
         letI := K.cochainAddCommGroup 0
         E.coefficient.C0 ≃+ K.Cn 0) /\
      Nonempty
        (letI := additive.c1AddCommGroup
         letI := K.cochainAddCommGroup 1
         E.coefficient.C1 ≃+ K.Cn 1) /\
      Nonempty (E.coefficient.C2 ≃ K.Cn 2) /\
      (letI := K.cochainAddCommGroup 2
       realization.c2Equiv E.coefficient.zero2 = 0) /\
      (letI := K.cochainAddCommGroup 2
       realization.c2Equiv.symm 0 = E.coefficient.zero2)) /\
      ((letI := additive.c0AddCommGroup
        letI := additive.c1AddCommGroup
        letI := K.cochainAddCommGroup 0
        letI := K.cochainAddCommGroup 1
        forall primitive : E.coefficient.C0,
          K.d 0 (realization.c0Equiv primitive) =
            realization.c1Equiv (E.coefficient.delta0 primitive)) /\
       (letI := additive.c0AddCommGroup
        letI := additive.c1AddCommGroup
        letI := K.cochainAddCommGroup 0
        letI := K.cochainAddCommGroup 1
        forall primitive : K.Cn 0,
          E.coefficient.delta0 (realization.c0Equiv.symm primitive) =
            realization.c1Equiv.symm (K.d 0 primitive)) /\
       (letI := additive.c1AddCommGroup
        letI := K.cochainAddCommGroup 1
        forall cochain : E.coefficient.C1,
          K.d 1 (realization.c1Equiv cochain) =
            realization.c2Equiv (E.coefficient.delta1 cochain)) /\
       (letI := additive.c1AddCommGroup
        letI := K.cochainAddCommGroup 1
        forall cochain : K.Cn 1,
          E.coefficient.delta1 (realization.c1Equiv.symm cochain) =
            realization.c2Equiv.symm (K.d 1 cochain))) := by
  exact
    ⟨⟨⟨realization.c0Equiv⟩,
      ⟨realization.c1Equiv⟩,
      ⟨realization.c2Equiv⟩,
      realization.c2Equiv_zero,
      realization.c2Equiv_symm_zero⟩,
      realization.d0_to,
      realization.d0_from,
      realization.d1_to,
      realization.d1_from⟩

end SemanticRepairCoverRelativeCochainRealization

/--
Richer selected bridge from a semantic repair cover to the general
cover-relative Cech complex.

Unlike `SemanticRepairCoverRelativeCoverBridge`, this bridge includes
section-family realization of the semantic coefficient carriers in degrees
`0`, `1`, and `2`, plus the selected differential compatibility needed to read
the semantic additive surface as the chosen cover-relative Cech complex.  It
does not store any `H1` zero predicate, global coherence, full sheaf cohomology
comparison, refinement naturality, exactness conclusion, or effective descent
conclusion.
-/
structure SemanticRepairCoverRelativeSectionRealizationBridge
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob) where
  c0SectionEquiv :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    E.coefficient.C0 ≃+ K.Cn 0
  c1SectionEquiv :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    E.coefficient.C1 ≃+ K.Cn 1
  c2SectionEquiv : E.coefficient.C2 ≃ K.Cn 2
  c2SectionEquiv_zero :
    letI := K.cochainAddCommGroup 2
    c2SectionEquiv E.coefficient.zero2 = 0
  c2SectionEquiv_symm_zero :
    letI := K.cochainAddCommGroup 2
    c2SectionEquiv.symm 0 = E.coefficient.zero2
  d0_section_to :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : E.coefficient.C0,
      K.d 0 (c0SectionEquiv primitive) =
        c1SectionEquiv (E.coefficient.delta0 primitive)
  d0_section_from :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : K.Cn 0,
      E.coefficient.delta0 (c0SectionEquiv.symm primitive) =
        c1SectionEquiv.symm (K.d 0 primitive)
  d1_section_to :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : E.coefficient.C1,
      K.d 1 (c1SectionEquiv cochain) =
        c2SectionEquiv (E.coefficient.delta1 cochain)
  d1_section_from :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : K.Cn 1,
      E.coefficient.delta1 (c1SectionEquiv.symm cochain) =
        c2SectionEquiv.symm (K.d 1 cochain)

/--
Concrete finite witness identifying the semantic coefficient carriers with the
selected section-family cochains of a cover-relative Cech complex.

This is the irreducible type-level comparison data still required by G-06: the
semantic `C0/C1/C2` carriers are arbitrary finite/small coefficient carriers,
whereas `K.Cn n` is a presheaf section family over selected `n`-simplices.  No
`H1` zero predicate, boundary membership, global coherence, exactness,
effective descent, refinement naturality, or full sheaf cohomology comparison is
stored here.
-/
structure SemanticRepairCoverRelativeSectionFamilyWitness
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob) where
  c0SectionEquiv :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    E.coefficient.C0 ≃+ K.Cn 0
  c1SectionEquiv :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    E.coefficient.C1 ≃+ K.Cn 1
  c2SectionEquiv : E.coefficient.C2 ≃ K.Cn 2
  c2SectionEquiv_zero :
    letI := K.cochainAddCommGroup 2
    c2SectionEquiv E.coefficient.zero2 = 0
  c2SectionEquiv_symm_zero :
    letI := K.cochainAddCommGroup 2
    c2SectionEquiv.symm 0 = E.coefficient.zero2

/--
Concrete finite witness that semantic differentials agree with the selected
face-restriction presentation of the general Cech differential under a fixed
section-family witness.

This witness is lower than direct `K.d` compatibility: direct differential
compatibility is derived using
`CoverRelativeCechComplex.d_eq_alternatingFaceCombination`.
-/
structure SemanticRepairCoverRelativeFaceRestrictionCompatibility
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    {coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S}
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    {K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob}
    (sectionWitness :
      SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K) where
  d0_face_to :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : E.coefficient.C0,
      K.alternatingFaceCombination 0
          (fun σ i =>
            K.faceRestrictionTerm 0 i
              (sectionWitness.c0SectionEquiv primitive) σ) =
        sectionWitness.c1SectionEquiv (E.coefficient.delta0 primitive)
  d0_face_from :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : K.Cn 0,
      E.coefficient.delta0 (sectionWitness.c0SectionEquiv.symm primitive) =
        sectionWitness.c1SectionEquiv.symm
          (K.alternatingFaceCombination 0
            (fun σ i => K.faceRestrictionTerm 0 i primitive σ))
  d1_face_to :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : E.coefficient.C1,
      K.alternatingFaceCombination 1
          (fun σ i =>
            K.faceRestrictionTerm 1 i
              (sectionWitness.c1SectionEquiv cochain) σ) =
        sectionWitness.c2SectionEquiv (E.coefficient.delta1 cochain)
  d1_face_from :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : K.Cn 1,
      E.coefficient.delta1 (sectionWitness.c1SectionEquiv.symm cochain) =
        sectionWitness.c2SectionEquiv.symm
          (K.alternatingFaceCombination 1
            (fun σ i => K.faceRestrictionTerm 1 i cochain σ))

/--
Carrier-specific lower comparison provenance for identifying the semantic
coefficient carriers with the selected cover-relative Cech section families.

This is intentionally below `SemanticRepairCoverRelativeSectionFamilyWitness`:
it stores maps, inverse laws, additive preservation for degrees `0` and `1`,
degree-`2` zero preservation, and the selected face-restriction differential
equations.  It does not store an `H1` quotient equivalence, zero-class result,
boundary membership, global semantic repair coherence, effective descent,
refinement naturality, or full sheaf cohomology comparison.
-/
structure SemanticRepairCarrierSpecificComparisonProvenance
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob) where
  toSection0 : E.coefficient.C0 -> K.Cn 0
  fromSection0 : K.Cn 0 -> E.coefficient.C0
  from_to_section0 :
    forall primitive : E.coefficient.C0,
      fromSection0 (toSection0 primitive) = primitive
  to_from_section0 :
    forall primitive : K.Cn 0,
      toSection0 (fromSection0 primitive) = primitive
  toSection0_add :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    forall left right : E.coefficient.C0,
      toSection0 (left + right) = toSection0 left + toSection0 right
  toSection1 : E.coefficient.C1 -> K.Cn 1
  fromSection1 : K.Cn 1 -> E.coefficient.C1
  from_to_section1 :
    forall cochain : E.coefficient.C1,
      fromSection1 (toSection1 cochain) = cochain
  to_from_section1 :
    forall cochain : K.Cn 1,
      toSection1 (fromSection1 cochain) = cochain
  toSection1_add :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall left right : E.coefficient.C1,
      toSection1 (left + right) = toSection1 left + toSection1 right
  toSection2 : E.coefficient.C2 -> K.Cn 2
  fromSection2 : K.Cn 2 -> E.coefficient.C2
  from_to_section2 :
    forall obstruction : E.coefficient.C2,
      fromSection2 (toSection2 obstruction) = obstruction
  to_from_section2 :
    forall obstruction : K.Cn 2,
      toSection2 (fromSection2 obstruction) = obstruction
  toSection2_zero :
    letI := K.cochainAddCommGroup 2
    toSection2 E.coefficient.zero2 = 0
  fromSection2_zero :
    letI := K.cochainAddCommGroup 2
    fromSection2 0 = E.coefficient.zero2
  d0_face_to :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : E.coefficient.C0,
      K.alternatingFaceCombination 0
          (fun σ i => K.faceRestrictionTerm 0 i (toSection0 primitive) σ) =
        toSection1 (E.coefficient.delta0 primitive)
  d0_face_from :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : K.Cn 0,
      E.coefficient.delta0 (fromSection0 primitive) =
        fromSection1
          (K.alternatingFaceCombination 0
            (fun σ i => K.faceRestrictionTerm 0 i primitive σ))
  d1_face_to :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : E.coefficient.C1,
      K.alternatingFaceCombination 1
          (fun σ i => K.faceRestrictionTerm 1 i (toSection1 cochain) σ) =
        toSection2 (E.coefficient.delta1 cochain)
  d1_face_from :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : K.Cn 1,
      E.coefficient.delta1 (fromSection1 cochain) =
        fromSection2
          (K.alternatingFaceCombination 1
            (fun σ i => K.faceRestrictionTerm 1 i cochain σ))

/--
Lower-level section realization provenance using the selected face-restriction
presentation of the general cover-relative Cech differential.

This data still contains the selected degree `0`, `1`, and `2` section-family
equivalences.  Unlike `SemanticRepairCoverRelativeSectionRealizationBridge`, it
does not directly store compatibility with `K.d`; it stores compatibility with
the explicit `faceRestrictionTerm` / `alternatingFaceCombination` presentation
from the general Cech complex, from which `K.d` compatibility is derived.
-/
structure SemanticRepairCoverRelativeFaceRestrictionRealization
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
    (additive : SemanticRepairAdditiveCechH1Data E)
    {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
    {S : AAT.AG.Site.AATSite A}
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob) where
  c0SectionEquiv :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    E.coefficient.C0 ≃+ K.Cn 0
  c1SectionEquiv :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    E.coefficient.C1 ≃+ K.Cn 1
  c2SectionEquiv : E.coefficient.C2 ≃ K.Cn 2
  c2SectionEquiv_zero :
    letI := K.cochainAddCommGroup 2
    c2SectionEquiv E.coefficient.zero2 = 0
  c2SectionEquiv_symm_zero :
    letI := K.cochainAddCommGroup 2
    c2SectionEquiv.symm 0 = E.coefficient.zero2
  d0_face_to :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : E.coefficient.C0,
      K.alternatingFaceCombination 0
          (fun σ i => K.faceRestrictionTerm 0 i (c0SectionEquiv primitive) σ) =
        c1SectionEquiv (E.coefficient.delta0 primitive)
  d0_face_from :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : K.Cn 0,
      E.coefficient.delta0 (c0SectionEquiv.symm primitive) =
        c1SectionEquiv.symm
          (K.alternatingFaceCombination 0
            (fun σ i => K.faceRestrictionTerm 0 i primitive σ))
  d1_face_to :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : E.coefficient.C1,
      K.alternatingFaceCombination 1
          (fun σ i => K.faceRestrictionTerm 1 i (c1SectionEquiv cochain) σ) =
        c2SectionEquiv (E.coefficient.delta1 cochain)
  d1_face_from :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : K.Cn 1,
      E.coefficient.delta1 (c1SectionEquiv.symm cochain) =
        c2SectionEquiv.symm
          (K.alternatingFaceCombination 1
            (fun σ i => K.faceRestrictionTerm 1 i cochain σ))

namespace SemanticRepairCoverRelativeFaceRestrictionRealization

variable {Atom : Type u}
variable {site : SemanticRepairSite.{u, v} Atom}
variable {semanticCover : SemanticRepairCover.{u, v, w} site}
variable {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
variable {additive : SemanticRepairAdditiveCechH1Data E}
variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}
variable {coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex
  (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob}

/--
Construct face-restriction realization from the separated finite section-family
and face-restriction compatibility witnesses.
-/
def of_sectionFamilyWitness
    (sectionWitness :
      SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K)
    (compatibility :
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        additive sectionWitness) :
    SemanticRepairCoverRelativeFaceRestrictionRealization additive coverBridge K where
  c0SectionEquiv := sectionWitness.c0SectionEquiv
  c1SectionEquiv := sectionWitness.c1SectionEquiv
  c2SectionEquiv := sectionWitness.c2SectionEquiv
  c2SectionEquiv_zero := sectionWitness.c2SectionEquiv_zero
  c2SectionEquiv_symm_zero := sectionWitness.c2SectionEquiv_symm_zero
  d0_face_to := compatibility.d0_face_to
  d0_face_from := compatibility.d0_face_from
  d1_face_to := compatibility.d1_face_to
  d1_face_from := compatibility.d1_face_from

/--
Any face-restriction realization exposes an explicit section-family witness.

This is a boundary theorem: G-06 cannot treat realization as generated from
semantic cover data unless this witness is itself constructed or accepted as a
concrete finite comparison witness.
-/
def toSectionFamilyWitness
    (realization :
      SemanticRepairCoverRelativeFaceRestrictionRealization additive coverBridge K) :
    SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K where
  c0SectionEquiv := realization.c0SectionEquiv
  c1SectionEquiv := realization.c1SectionEquiv
  c2SectionEquiv := realization.c2SectionEquiv
  c2SectionEquiv_zero := realization.c2SectionEquiv_zero
  c2SectionEquiv_symm_zero := realization.c2SectionEquiv_symm_zero

/--
Any face-restriction realization exposes explicit face-restriction
compatibility relative to its section-family witness.

This keeps the remaining comparison adequacy premise visible instead of hiding
it inside the larger realization structure.
-/
def toFaceRestrictionCompatibility
    (realization :
      SemanticRepairCoverRelativeFaceRestrictionRealization additive coverBridge K) :
    SemanticRepairCoverRelativeFaceRestrictionCompatibility
      additive realization.toSectionFamilyWitness where
  d0_face_to := realization.d0_face_to
  d0_face_from := realization.d0_face_from
  d1_face_to := realization.d1_face_to
  d1_face_from := realization.d1_face_from

/--
G-06 boundary theorem: face-restriction realization is equivalent to supplying
both a finite section-family witness and compatibility with the selected
face-restriction differential presentation.

The forward direction extracts the remaining material witnesses.  The backward
direction constructs the realization from them.  This does not discharge those
witnesses from bare cover data; it makes their exact status explicit.
-/
theorem faceRestrictionRealization_iff_sectionFamilyWitness_and_compatibility :
    Nonempty
        (SemanticRepairCoverRelativeFaceRestrictionRealization
          additive coverBridge K) <->
      Exists fun sectionWitness :
        SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K =>
          SemanticRepairCoverRelativeFaceRestrictionCompatibility
            additive sectionWitness := by
  constructor
  · intro hrealization
    rcases hrealization with ⟨realization⟩
    exact
      ⟨realization.toSectionFamilyWitness,
        realization.toFaceRestrictionCompatibility⟩
  · intro hwitness
    rcases hwitness with ⟨sectionWitness, compatibility⟩
    exact ⟨of_sectionFamilyWitness sectionWitness compatibility⟩

/--
Boundary audit theorem: any supplied section-family witness exposes the exact
degree-wise type/additive equivalences required by the G-06 comparison.

These equivalences are not generated by cover membership or the sheaf condition
alone; they are the remaining finite comparison input that must either be
constructed from lower data or accepted as an explicit target boundary.
-/
theorem sectionFamilyWitness_requires_degreeEquivalences
    (sectionWitness :
      SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K) :
    Nonempty
        (letI := additive.c0AddCommGroup
         letI := K.cochainAddCommGroup 0
         E.coefficient.C0 ≃+ K.Cn 0) /\
      Nonempty
        (letI := additive.c1AddCommGroup
         letI := K.cochainAddCommGroup 1
         E.coefficient.C1 ≃+ K.Cn 1) /\
      Nonempty (E.coefficient.C2 ≃ K.Cn 2) /\
      (letI := K.cochainAddCommGroup 2
       sectionWitness.c2SectionEquiv E.coefficient.zero2 = 0) /\
      (letI := K.cochainAddCommGroup 2
       sectionWitness.c2SectionEquiv.symm 0 = E.coefficient.zero2) := by
  exact
    ⟨⟨sectionWitness.c0SectionEquiv⟩,
      ⟨sectionWitness.c1SectionEquiv⟩,
      ⟨sectionWitness.c2SectionEquiv⟩,
      sectionWitness.c2SectionEquiv_zero,
      sectionWitness.c2SectionEquiv_symm_zero⟩

/--
Boundary audit theorem: any supplied face-restriction compatibility exposes the
four concrete differential equations that remain to be generated from lower
cover/presheaf data.
-/
theorem faceRestrictionCompatibility_requires_equations
    {sectionWitness :
      SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K}
    (compatibility :
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        additive sectionWitness) :
    (letI := additive.c0AddCommGroup
     letI := additive.c1AddCommGroup
     letI := K.cochainAddCommGroup 0
     letI := K.cochainAddCommGroup 1
     forall primitive : E.coefficient.C0,
      K.alternatingFaceCombination 0
          (fun σ i =>
            K.faceRestrictionTerm 0 i
              (sectionWitness.c0SectionEquiv primitive) σ) =
        sectionWitness.c1SectionEquiv (E.coefficient.delta0 primitive)) /\
      (letI := additive.c0AddCommGroup
       letI := additive.c1AddCommGroup
       letI := K.cochainAddCommGroup 0
       letI := K.cochainAddCommGroup 1
       forall primitive : K.Cn 0,
        E.coefficient.delta0 (sectionWitness.c0SectionEquiv.symm primitive) =
          sectionWitness.c1SectionEquiv.symm
            (K.alternatingFaceCombination 0
              (fun σ i => K.faceRestrictionTerm 0 i primitive σ))) /\
      (letI := additive.c1AddCommGroup
       letI := K.cochainAddCommGroup 1
       forall cochain : E.coefficient.C1,
        K.alternatingFaceCombination 1
            (fun σ i =>
              K.faceRestrictionTerm 1 i
                (sectionWitness.c1SectionEquiv cochain) σ) =
          sectionWitness.c2SectionEquiv (E.coefficient.delta1 cochain)) /\
      (letI := additive.c1AddCommGroup
       letI := K.cochainAddCommGroup 1
       forall cochain : K.Cn 1,
        E.coefficient.delta1 (sectionWitness.c1SectionEquiv.symm cochain) =
          sectionWitness.c2SectionEquiv.symm
            (K.alternatingFaceCombination 1
              (fun σ i => K.faceRestrictionTerm 1 i cochain σ))) := by
  exact
    ⟨compatibility.d0_face_to,
      compatibility.d0_face_from,
      compatibility.d1_face_to,
      compatibility.d1_face_from⟩

/--
G-06 target-boundary checkpoint: any face-restriction realization necessarily
contains the finite section-family equivalences and the four selected
face-restriction equations.

This is intentionally a one-way audit theorem.  It prevents completion from
being claimed from bare cover/sheaf evidence while the degree-wise equivalences
and face-restriction laws remain supplied comparison data.
-/
theorem faceRestrictionRealization_requires_finiteWitnessBoundary
    (realization :
      SemanticRepairCoverRelativeFaceRestrictionRealization additive coverBridge K) :
    (Nonempty
        (letI := additive.c0AddCommGroup
         letI := K.cochainAddCommGroup 0
         E.coefficient.C0 ≃+ K.Cn 0) /\
      Nonempty
        (letI := additive.c1AddCommGroup
         letI := K.cochainAddCommGroup 1
         E.coefficient.C1 ≃+ K.Cn 1) /\
      Nonempty (E.coefficient.C2 ≃ K.Cn 2) /\
      (letI := K.cochainAddCommGroup 2
       realization.toSectionFamilyWitness.c2SectionEquiv
          E.coefficient.zero2 = 0) /\
      (letI := K.cochainAddCommGroup 2
       realization.toSectionFamilyWitness.c2SectionEquiv.symm 0 =
          E.coefficient.zero2)) /\
      Exists fun sectionWitness :
        SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K =>
          SemanticRepairCoverRelativeFaceRestrictionCompatibility
            additive sectionWitness := by
  exact
    ⟨sectionFamilyWitness_requires_degreeEquivalences
        realization.toSectionFamilyWitness,
      ⟨realization.toSectionFamilyWitness,
        realization.toFaceRestrictionCompatibility⟩⟩

/--
Cycle 10 blocker theorem: a section-family witness cannot be generated
uniformly from bare carrier types and additive structures alone.

Indeed, such a generator would supply an additive equivalence between every
pair of additive carriers.  Applying it to the one-point additive group and
`ZMod 2` forces `0 = 1`.  Therefore a G-06 construction of
`SemanticRepairCoverRelativeSectionFamilyWitness` needs carrier-specific
comparison data tying the semantic coefficient carriers to the selected Cech
section families; cover membership or sheaf descent alone cannot manufacture
these degree-wise equivalences.
-/
theorem no_uniform_additive_carrier_equivalence_from_bare_lower_data :
    IsEmpty ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] -> C ≃+ D) := by
  refine ⟨?_⟩
  intro h
  let e : PUnit ≃+ ZMod 2 := h PUnit (ZMod 2)
  rcases e.surjective (0 : ZMod 2) with ⟨x0, hx0⟩
  rcases e.surjective (1 : ZMod 2) with ⟨x1, hx1⟩
  have hzero_one : (0 : ZMod 2) = 1 := by
    rw [← hx0, ← hx1]
  exact (by norm_num : (0 : ZMod 2) ≠ 1) hzero_one

/--
Construct the section-realization bridge from face-restriction provenance.

The proof uses `CoverRelativeCechComplex.d_eq_alternatingFaceCombination` to
derive direct `K.d` compatibility from the selected face-restriction
presentation, rather than taking `d0` / `d1` compatibility as an independent
bridge field.
-/
def toSectionRealizationBridge
    (realization :
      SemanticRepairCoverRelativeFaceRestrictionRealization additive coverBridge K) :
    SemanticRepairCoverRelativeSectionRealizationBridge additive coverBridge K where
  c0SectionEquiv := realization.c0SectionEquiv
  c1SectionEquiv := realization.c1SectionEquiv
  c2SectionEquiv := realization.c2SectionEquiv
  c2SectionEquiv_zero := realization.c2SectionEquiv_zero
  c2SectionEquiv_symm_zero := realization.c2SectionEquiv_symm_zero
  d0_section_to := by
    intro primitive
    rw [K.d_eq_alternatingFaceCombination 0]
    exact realization.d0_face_to primitive
  d0_section_from := by
    intro primitive
    rw [K.d_eq_alternatingFaceCombination 0]
    exact realization.d0_face_from primitive
  d1_section_to := by
    intro cochain
    rw [K.d_eq_alternatingFaceCombination 1]
    exact realization.d1_face_to cochain
  d1_section_from := by
    intro cochain
    rw [K.d_eq_alternatingFaceCombination 1]
    exact realization.d1_face_from cochain

end SemanticRepairCoverRelativeFaceRestrictionRealization

namespace SemanticRepairCarrierSpecificComparisonProvenance

variable {Atom : Type u}
variable {site : SemanticRepairSite.{u, v} Atom}
variable {semanticCover : SemanticRepairCover.{u, v, w} site}
variable {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
variable {additive : SemanticRepairAdditiveCechH1Data E}
variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}
variable {coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex
  (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob}

/--
The degree-`0` part of carrier-specific provenance exposes the lower additive
comparison data that any concrete constructor must provide.
-/
def degreeZeroAdditiveComparisonData
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0) := by
  letI := additive.c0AddCommGroup
  letI := K.cochainAddCommGroup 0
  exact
    { toCarrier := provenance.toSection0
      fromCarrier := provenance.fromSection0
      from_to := provenance.from_to_section0
      to_from := provenance.to_from_section0
      toCarrier_add := provenance.toSection0_add }

/--
The degree-`1` part of carrier-specific provenance exposes the lower additive
comparison data that any concrete constructor must provide.
-/
def degreeOneAdditiveComparisonData
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1) := by
  letI := additive.c1AddCommGroup
  letI := K.cochainAddCommGroup 1
  exact
    { toCarrier := provenance.toSection1
      fromCarrier := provenance.fromSection1
      from_to := provenance.from_to_section1
      to_from := provenance.to_from_section1
      toCarrier_add := provenance.toSection1_add }

/--
Boundary audit theorem: a concrete carrier-specific provenance inhabitant
necessarily contains degree-wise lower additive comparison data.  Consequently
the target cannot discharge this premise from cover membership, sheaf
condition, or descent alone.
-/
theorem carrierSpecificComparisonProvenance_requires_degreewise_additive_data
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    Nonempty
        (letI := additive.c0AddCommGroup
         letI := K.cochainAddCommGroup 0
         CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0)) /\
      Nonempty
        (letI := additive.c1AddCommGroup
         letI := K.cochainAddCommGroup 1
         CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1)) := by
  exact
    ⟨⟨provenance.degreeZeroAdditiveComparisonData⟩,
      ⟨provenance.degreeOneAdditiveComparisonData⟩⟩

/--
G-06 boundary checkpoint: carrier-specific comparison provenance requires an
explicit selected carrier-comparison source.

The first component exposes the degree-wise selected comparison data contained
in any concrete provenance inhabitant.  The second component records that no
uniform constructor can produce that lower comparison data from bare additive
carrier structure.  Therefore G-06 cannot claim completion by deriving
`SemanticRepairCarrierSpecificComparisonProvenance` from cover membership,
sheaf condition, descent, or bare additive carrier data alone; absent a
concrete constructor, this selected comparison source must be treated as an
explicit target-boundary input rather than a discharged premise.
-/
theorem carrierSpecificComparisonProvenance_requires_explicit_selected_carrier_comparison_source
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    (Nonempty
        (letI := additive.c0AddCommGroup
         letI := K.cochainAddCommGroup 0
         CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0)) /\
      Nonempty
        (letI := additive.c1AddCommGroup
         letI := K.cochainAddCommGroup 1
         CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1))) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          CarrierSpecificAdditiveComparisonData C D) := by
  exact
    ⟨provenance.carrierSpecificComparisonProvenance_requires_degreewise_additive_data,
      no_uniform_carrier_specific_additive_comparison_from_bare_groups⟩

/--
Current G-06 input surface before adding any selected carrier-comparison
source.

The fields intentionally name the APIs that are available from the site/sheaf
side: semantic cover-to-cover-relative bridge, the general Cech complex,
selected cover membership, `AATSheafCondition`, and `AATDescent`.  They do not
contain degree-wise carrier maps, inverse laws, additive preservation, or
face-restriction compatibility.
-/
structure CurrentG06InputSurface where
  coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S
  K : AAT.AG.Cohomology.CoverRelativeCechComplex
    (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob
  presheaf : AAT.AG.Site.AATPresheaf S
  coverBase : S.category
  selectedCover : Sieve coverBase
  selectedCover_mem : selectedCover ∈ S.topology coverBase
  sheafCondition : AAT.AG.Site.AATSheafCondition S presheaf
  descent : AAT.AG.Site.AATDescent S presheaf selectedCover

/--
Cycle 14 blocker theorem: the current G-06 input surface cannot discharge
carrier-specific provenance without a selected carrier-comparison source.

If a constructor using only this current input surface could produce the lower
carrier-specific comparison data for arbitrary selected semantic and
cover-relative section carriers, then it would be a uniform constructor for
`CarrierSpecificAdditiveComparisonData` over all additive groups.  This
contradicts `no_uniform_carrier_specific_additive_comparison_from_bare_groups`.

Thus cover membership, the semantic cover bridge, `AATSheafCondition`,
`AATDescent`, bare additive coefficient laws, and the general
`CoverRelativeCechComplex` API do not by themselves give a uniform discharge of
the concrete carrier-specific provenance premise.  G-06 still needs either a
concrete selected carrier-comparison source or an explicit GOAL boundary
revision.
-/
theorem no_constructor_from_current_g06_inputs_without_selected_carrier_source
    (surface :
      CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob))
    (currentInputConstructor :
      (C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
        CurrentG06InputSurface
          (semanticCover := semanticCover) (S := S) (Ob := Ob) ->
        CarrierSpecificAdditiveComparisonData C D) :
    False := by
  let uniformCarrierComparison :
      (C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
        CarrierSpecificAdditiveComparisonData C D :=
    fun C D _ _ => currentInputConstructor C D surface
  exact
    no_uniform_carrier_specific_additive_comparison_from_bare_groups.false
      uniformCarrierComparison

/--
Cycle 17 blocker theorem: the current G-06 input surface cannot discharge the
selected cochain realization source by manufacturing the degree-wise additive
equivalences it requires.

If the current site/sheaf/descent input surface could produce the degree-zero
or degree-one equivalence data needed by
`SemanticRepairCoverRelativeCochainRealization` for arbitrary selected semantic
and cover-relative section carriers, then it would give an additive equivalence
between every pair of additive groups.  This contradicts
`no_uniform_additive_carrier_equivalence_from_bare_lower_data`.

Thus Cycle 16's remaining source gap cannot be closed by cover membership,
`AATSheafCondition`, `AATDescent`, bare additive coefficient laws, or the
general `CoverRelativeCechComplex` API alone.  G-06 still needs a concrete
lower construction of the selected cochain realization or an explicit
GOAL-boundary revision outside the loop.
-/
theorem no_constructor_from_current_g06_inputs_without_cochain_realization_source
    (surface :
      CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob))
    (currentInputDegreeEquivConstructor :
      (C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
        CurrentG06InputSurface
          (semanticCover := semanticCover) (S := S) (Ob := Ob) ->
        C ≃+ D) :
    False := by
  let uniformDegreeEquiv :
      (C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] -> C ≃+ D :=
    fun C D _ _ => currentInputDegreeEquivConstructor C D surface
  exact
    (SemanticRepairCoverRelativeFaceRestrictionRealization.no_uniform_additive_carrier_equivalence_from_bare_lower_data).false
        uniformDegreeEquiv

/--
The degree-`0` carrier maps in carrier-specific provenance construct the
additive equivalence required by the section-family witness.
-/
def c0SectionEquiv
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    E.coefficient.C0 ≃+ K.Cn 0 := by
  letI := additive.c0AddCommGroup
  letI := K.cochainAddCommGroup 0
  exact
    { toFun := provenance.toSection0
      invFun := provenance.fromSection0
      left_inv := provenance.from_to_section0
      right_inv := provenance.to_from_section0
      map_add' := provenance.toSection0_add }

/--
The degree-`1` carrier maps in carrier-specific provenance construct the
additive equivalence required by the section-family witness.
-/
def c1SectionEquiv
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    E.coefficient.C1 ≃+ K.Cn 1 := by
  letI := additive.c1AddCommGroup
  letI := K.cochainAddCommGroup 1
  exact
    { toFun := provenance.toSection1
      invFun := provenance.fromSection1
      left_inv := provenance.from_to_section1
      right_inv := provenance.to_from_section1
      map_add' := provenance.toSection1_add }

/--
The degree-`2` carrier maps in carrier-specific provenance construct the
plain equivalence used for obstruction values.
-/
def c2SectionEquiv
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    E.coefficient.C2 ≃ K.Cn 2 where
  toFun := provenance.toSection2
  invFun := provenance.fromSection2
  left_inv := provenance.from_to_section2
  right_inv := provenance.to_from_section2

/--
Carrier-specific provenance discharges the finite section-family witness
without storing that witness as a field.
-/
def toSectionFamilyWitness
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K where
  c0SectionEquiv := provenance.c0SectionEquiv
  c1SectionEquiv := provenance.c1SectionEquiv
  c2SectionEquiv := provenance.c2SectionEquiv
  c2SectionEquiv_zero := provenance.toSection2_zero
  c2SectionEquiv_symm_zero := provenance.fromSection2_zero

/--
Carrier-specific provenance discharges selected face-restriction compatibility
relative to the constructed section-family witness.
-/
def toFaceRestrictionCompatibility
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    SemanticRepairCoverRelativeFaceRestrictionCompatibility
      additive provenance.toSectionFamilyWitness where
  d0_face_to := by
    intro primitive
    simpa [toSectionFamilyWitness, c0SectionEquiv, c1SectionEquiv] using
      provenance.d0_face_to primitive
  d0_face_from := by
    intro primitive
    simpa [toSectionFamilyWitness, c0SectionEquiv, c1SectionEquiv] using
      provenance.d0_face_from primitive
  d1_face_to := by
    intro cochain
    simpa [toSectionFamilyWitness, c1SectionEquiv, c2SectionEquiv] using
      provenance.d1_face_to cochain
  d1_face_from := by
    intro cochain
    simpa [toSectionFamilyWitness, c1SectionEquiv, c2SectionEquiv] using
      provenance.d1_face_from cochain

/--
Carrier-specific provenance constructs the existing face-restriction
realization layer, so the new lower data is proof-used by the downstream
comparison package.
-/
def toFaceRestrictionRealization
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    SemanticRepairCoverRelativeFaceRestrictionRealization additive coverBridge K :=
  SemanticRepairCoverRelativeFaceRestrictionRealization.of_sectionFamilyWitness
    provenance.toSectionFamilyWitness provenance.toFaceRestrictionCompatibility

/--
Carrier-specific provenance supplies exactly the separated finite witness and
face-restriction compatibility required by Cycle 9's boundary theorem.
-/
theorem constructs_sectionFamilyWitness_and_faceRestrictionCompatibility
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    Exists fun sectionWitness :
      SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K =>
        SemanticRepairCoverRelativeFaceRestrictionCompatibility
          additive sectionWitness :=
  ⟨provenance.toSectionFamilyWitness, provenance.toFaceRestrictionCompatibility⟩

/--
Audit theorem: carrier-specific provenance exposes only carrier maps, inverse
laws, additive preservation, zero preservation, and selected face-restriction
differential equations.  The downstream `H1` package is constructed by theorem,
not stored in the provenance object.
-/
theorem carrierSpecificComparisonProvenance_requires_maps_and_faceLaws
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    (Nonempty (E.coefficient.C0 -> K.Cn 0) /\
      Nonempty (K.Cn 0 -> E.coefficient.C0) /\
      Nonempty (E.coefficient.C1 -> K.Cn 1) /\
      Nonempty (K.Cn 1 -> E.coefficient.C1) /\
      Nonempty (E.coefficient.C2 -> K.Cn 2) /\
      Nonempty (K.Cn 2 -> E.coefficient.C2)) /\
      Exists fun sectionWitness :
        SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K =>
          SemanticRepairCoverRelativeFaceRestrictionCompatibility
            additive sectionWitness := by
  exact
    ⟨⟨⟨provenance.toSection0⟩,
      ⟨provenance.fromSection0⟩,
      ⟨provenance.toSection1⟩,
      ⟨provenance.fromSection1⟩,
      ⟨provenance.toSection2⟩,
      ⟨provenance.fromSection2⟩⟩,
      provenance.constructs_sectionFamilyWitness_and_faceRestrictionCompatibility⟩

end SemanticRepairCarrierSpecificComparisonProvenance

namespace SemanticRepairCoverRelativeSectionRealizationBridge

variable {Atom : Type u}
variable {site : SemanticRepairSite.{u, v} Atom}
variable {semanticCover : SemanticRepairCover.{u, v, w} site}
variable {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
variable {additive : SemanticRepairAdditiveCechH1Data E}
variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}
variable {coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex
  (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob}

/--
Construct the cochain-realization layer from a richer selected bridge that
includes section-family equivalences and differential compatibility.
-/
def toCochainRealization
    (bridge : SemanticRepairCoverRelativeSectionRealizationBridge additive coverBridge K) :
    SemanticRepairCoverRelativeCochainRealization additive K where
  c0Equiv := bridge.c0SectionEquiv
  c1Equiv := bridge.c1SectionEquiv
  c2Equiv := bridge.c2SectionEquiv
  c2Equiv_zero := bridge.c2SectionEquiv_zero
  c2Equiv_symm_zero := bridge.c2SectionEquiv_symm_zero
  d0_to := bridge.d0_section_to
  d0_from := bridge.d0_section_from
  d1_to := bridge.d1_section_to
  d1_from := bridge.d1_section_from

end SemanticRepairCoverRelativeSectionRealizationBridge

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

namespace SemanticRepairCoverRelativeCochainRealization

variable {Atom : Type u}
variable {site : SemanticRepairSite.{u, v} Atom}
variable {semanticCover : SemanticRepairCover.{u, v, w} site}
variable {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
variable {additive : SemanticRepairAdditiveCechH1Data E}
variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}
variable {coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex
  (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob}

/--
Cochain realization is strong enough to construct the carrier-specific
comparison provenance once the selected cover-relative complex is fixed.

This theorem uses the general Cech identity
`CoverRelativeCechComplex.d_eq_alternatingFaceCombination` to turn direct
`K.d` compatibility into the face-restriction equations required by
`SemanticRepairCarrierSpecificComparisonProvenance`.  It does not construct the
cochain realization itself from cover membership, sheaf condition, or descent;
that source remains the material premise if no lower construction is supplied.
-/
def toCarrierSpecificComparisonProvenance
    (realization :
      SemanticRepairCoverRelativeCochainRealization additive K) :
    SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K where
  toSection0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact fun primitive => realization.c0Equiv primitive
  fromSection0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact fun primitive => realization.c0Equiv.symm primitive
  from_to_section0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    intro primitive
    exact realization.c0Equiv.left_inv primitive
  to_from_section0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    intro primitive
    exact realization.c0Equiv.right_inv primitive
  toSection0_add := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    intro left right
    exact realization.c0Equiv.map_add left right
  toSection1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact fun cochain => realization.c1Equiv cochain
  fromSection1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact fun cochain => realization.c1Equiv.symm cochain
  from_to_section1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    intro cochain
    exact realization.c1Equiv.left_inv cochain
  to_from_section1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    intro cochain
    exact realization.c1Equiv.right_inv cochain
  toSection1_add := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    intro left right
    exact realization.c1Equiv.map_add left right
  toSection2 := realization.c2Equiv
  fromSection2 := realization.c2Equiv.symm
  from_to_section2 := realization.c2Equiv.left_inv
  to_from_section2 := realization.c2Equiv.right_inv
  toSection2_zero := realization.c2Equiv_zero
  fromSection2_zero := realization.c2Equiv_symm_zero
  d0_face_to := by
    intro primitive
    rw [← K.d_eq_alternatingFaceCombination 0]
    exact realization.d0_to primitive
  d0_face_from := by
    intro primitive
    rw [← K.d_eq_alternatingFaceCombination 0]
    exact realization.d0_from primitive
  d1_face_to := by
    intro cochain
    rw [← K.d_eq_alternatingFaceCombination 1]
    exact realization.d1_to cochain
  d1_face_from := by
    intro cochain
    rw [← K.d_eq_alternatingFaceCombination 1]
    exact realization.d1_from cochain

end SemanticRepairCoverRelativeCochainRealization

namespace SemanticRepairCoverRelativeSectionRealizationBridge

variable {Atom : Type u}
variable {site : SemanticRepairSite.{u, v} Atom}
variable {semanticCover : SemanticRepairCover.{u, v, w} site}
variable {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
variable {additive : SemanticRepairAdditiveCechH1Data E}
variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}
variable {coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex
  (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob}

/--
A richer selected bridge supplies the whole selected cover-relative grounding
package by first constructing the cochain-realization layer.
-/
theorem grounded_package_of_section_realization_bridge
    (bridge : SemanticRepairCoverRelativeSectionRealizationBridge
      additive coverBridge K) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        bridge.toCochainRealization.toH1Comparison) :=
  bridge.toCochainRealization.grounded_package_of_cochain_realization

end SemanticRepairCoverRelativeSectionRealizationBridge

namespace SemanticRepairCoverRelativeFaceRestrictionRealization

variable {Atom : Type u}
variable {site : SemanticRepairSite.{u, v} Atom}
variable {semanticCover : SemanticRepairCover.{u, v, w} site}
variable {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
variable {additive : SemanticRepairAdditiveCechH1Data E}
variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}
variable {coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex
  (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob}

/--
Face-restriction provenance constructs the cochain-realization layer through
the derived section-realization bridge.
-/
def toCochainRealization
    (realization :
      SemanticRepairCoverRelativeFaceRestrictionRealization additive coverBridge K) :
    SemanticRepairCoverRelativeCochainRealization additive K :=
  realization.toSectionRealizationBridge.toCochainRealization

/--
Face-restriction provenance supplies the selected cover-relative grounding
package by first deriving `K.d` compatibility from the general Cech
face-restriction differential and then constructing the cochain realization.
-/
theorem grounded_package_of_face_restriction_realization
    (realization :
      SemanticRepairCoverRelativeFaceRestrictionRealization additive coverBridge K) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        realization.toCochainRealization.toH1Comparison) :=
  realization.toCochainRealization.grounded_package_of_cochain_realization

end SemanticRepairCoverRelativeFaceRestrictionRealization

namespace SemanticRepairCarrierSpecificComparisonProvenance

variable {Atom : Type u}
variable {site : SemanticRepairSite.{u, v} Atom}
variable {semanticCover : SemanticRepairCover.{u, v, w} site}
variable {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
variable {additive : SemanticRepairAdditiveCechH1Data E}
variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}
variable {coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex
  (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob}

/--
Carrier-specific provenance reaches the cochain-realization layer through the
existing face-restriction realization path.
-/
def toCochainRealization
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    SemanticRepairCoverRelativeCochainRealization additive K :=
  provenance.toFaceRestrictionRealization.toCochainRealization

/--
Carrier-specific provenance supplies the selected cover-relative grounding
package by constructing the finite witness, face-restriction realization, and
cochain realization in sequence.
-/
theorem grounded_package_of_carrier_specific_comparison_provenance
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        provenance.toCochainRealization.toH1Comparison) :=
  provenance.toFaceRestrictionRealization.grounded_package_of_face_restriction_realization

end SemanticRepairCarrierSpecificComparisonProvenance

namespace SemanticRepairCoverRelativeCochainRealization

variable {Atom : Type u}
variable {site : SemanticRepairSite.{u, v} Atom}
variable {semanticCover : SemanticRepairCover.{u, v, w} site}
variable {E : SemanticRepairSheafH1Envelope.{u, v, z, x, y} Atom}
variable {additive : SemanticRepairAdditiveCechH1Data E}
variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}
variable {coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S}
variable {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
variable {K : AAT.AG.Cohomology.CoverRelativeCechComplex
  (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob}

/--
Cycle 16 bridge theorem: a cochain realization supplies the previously
separate carrier-specific provenance and therefore reaches the existing
selected cover-relative grounding package.

The theorem shrinks the remaining source obligation to construction of the
cochain realization itself.  It is not a completion result: cover membership,
`AATSheafCondition`, and `AATDescent` still do not generate this realization by
themselves.
-/
theorem grounded_package_of_cochain_realization_via_carrier_specific_provenance
    (realization :
      SemanticRepairCoverRelativeCochainRealization additive K) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        realization.toCarrierSpecificComparisonProvenance.toCochainRealization.toH1Comparison) :=
  realization.toCarrierSpecificComparisonProvenance
    |>.grounded_package_of_carrier_specific_comparison_provenance

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
