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
open SemanticRepairObstructionTower

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
Carrier-only lower model for the selected semantic section-family comparison.

This is below `SemanticRepairCoverRelativeSectionFamilyWitness`: it stores the
degree `0` and `1` additive carrier identifications, the degree `2` plain
carrier identification, and the two degree-`2` zero laws.  It stores no
differential compatibility, `H1` equivalence, zero-class result, boundary
membership, global coherence, effective descent, refinement naturality, or full
sheaf cohomology comparison.
-/
structure SelectedSectionFamilyCarrierModel
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
  c0Carrier :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0)
  c1Carrier :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1)
  c2Equiv : E.coefficient.C2 ≃ K.Cn 2
  c2Equiv_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv E.coefficient.zero2 = 0
  c2Equiv_symm_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv.symm 0 = E.coefficient.zero2

namespace SelectedSectionFamilyCarrierModel

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

/-- Degree-zero carrier data yields the additive equivalence used by the witness. -/
def c0SectionEquiv
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K) :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    E.coefficient.C0 ≃+ K.Cn 0 := by
  letI := additive.c0AddCommGroup
  letI := K.cochainAddCommGroup 0
  exact model.c0Carrier.toAddEquiv

/-- Degree-one carrier data yields the additive equivalence used by the witness. -/
def c1SectionEquiv
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K) :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    E.coefficient.C1 ≃+ K.Cn 1 := by
  letI := additive.c1AddCommGroup
  letI := K.cochainAddCommGroup 1
  exact model.c1Carrier.toAddEquiv

/--
Audit theorem for the selected carrier model source.

Any selected section-family carrier model necessarily exposes exactly the
degree-`0` and degree-`1` carrier-specific additive comparison data, plus the
degree-`2` carrier equivalence and zero laws.  It does not expose
face-restriction compatibility, quotient comparison, zero `H1`, boundary
membership, global coherence, descent, refinement naturality, or full sheaf
cohomology comparison.
-/
theorem requires_degreewise_carrier_data_and_c2_zero_equivalence
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K) :
    Nonempty
        (letI := additive.c0AddCommGroup
         letI := K.cochainAddCommGroup 0
         CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0)) /\
      Nonempty
        (letI := additive.c1AddCommGroup
         letI := K.cochainAddCommGroup 1
         CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1)) /\
      Exists fun c2Equiv : E.coefficient.C2 ≃ K.Cn 2 =>
        (letI := K.cochainAddCommGroup 2
         c2Equiv E.coefficient.zero2 = 0) /\
          (letI := K.cochainAddCommGroup 2
           c2Equiv.symm 0 = E.coefficient.zero2) := by
  exact
    ⟨⟨model.c0Carrier⟩,
      ⟨model.c1Carrier⟩,
      ⟨model.c2Equiv, model.c2Equiv_zero, model.c2Equiv_symm_zero⟩⟩

/--
Selected section-family carrier models require an explicit carrier-comparison
source.

The first component extracts the finite carrier source from any concrete model.
The second component records the uniform-constructor obstruction for the
degree-wise additive carrier data.  Thus the current G-06 proof cannot count a
selected carrier model as discharged merely from cover membership,
`AATSheafCondition`, `AATDescent`, or bare additive group structure; it still
needs a concrete selected carrier source or an explicit GOAL-boundary revision.
-/
theorem requires_explicit_selected_carrier_source
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K) :
    (Nonempty
        (letI := additive.c0AddCommGroup
         letI := K.cochainAddCommGroup 0
         CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0)) /\
      Nonempty
        (letI := additive.c1AddCommGroup
         letI := K.cochainAddCommGroup 1
         CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1)) /\
      Exists fun c2Equiv : E.coefficient.C2 ≃ K.Cn 2 =>
        (letI := K.cochainAddCommGroup 2
         c2Equiv E.coefficient.zero2 = 0) /\
          (letI := K.cochainAddCommGroup 2
           c2Equiv.symm 0 = E.coefficient.zero2)) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          CarrierSpecificAdditiveComparisonData C D) := by
  exact
    ⟨model.requires_degreewise_carrier_data_and_c2_zero_equivalence,
      no_uniform_carrier_specific_additive_comparison_from_bare_groups⟩

/--
Construct the selected section-family carrier model from the explicit finite
carrier witness data.

This is the constructive converse to
`requires_degreewise_carrier_data_and_c2_zero_equivalence`: the model is not an
opaque certificate, but exactly the degree-`0` and degree-`1` additive carrier
comparisons plus the degree-`2` carrier equivalence and zero laws.  No
differential compatibility, `H1` zero, boundary membership, global coherence,
descent, refinement naturality, or full sheaf cohomology comparison is added.
-/
def of_degreewise_carrier_data_and_c2_zero_equivalence
    (c0Carrier :
      letI := additive.c0AddCommGroup
      letI := K.cochainAddCommGroup 0
      CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0))
    (c1Carrier :
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1))
    (c2Equiv : E.coefficient.C2 ≃ K.Cn 2)
    (c2Equiv_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv E.coefficient.zero2 = 0)
    (c2Equiv_symm_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv.symm 0 = E.coefficient.zero2) :
    SelectedSectionFamilyCarrierModel additive coverBridge K where
  c0Carrier := c0Carrier
  c1Carrier := c1Carrier
  c2Equiv := c2Equiv
  c2Equiv_zero := c2Equiv_zero
  c2Equiv_symm_zero := c2Equiv_symm_zero

/--
The explicit finite carrier witness constructs the selected section-family
carrier model required by the downstream G-06 comparison path.
-/
theorem degreewise_carrier_data_and_c2_zero_equivalence_constructs_selectedSectionFamilyCarrierModel
    (c0Carrier :
      letI := additive.c0AddCommGroup
      letI := K.cochainAddCommGroup 0
      CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0))
    (c1Carrier :
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1))
    (c2Equiv : E.coefficient.C2 ≃ K.Cn 2)
    (c2Equiv_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv E.coefficient.zero2 = 0)
    (c2Equiv_symm_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv.symm 0 = E.coefficient.zero2) :
    Nonempty (SelectedSectionFamilyCarrierModel additive coverBridge K) :=
  ⟨of_degreewise_carrier_data_and_c2_zero_equivalence
    c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero⟩

/--
The selected section-family carrier model is exactly finite degree-wise
carrier comparison data plus the degree-`2` zero-preserving equivalence.

The equivalence is a provenance audit theorem.  It keeps the carrier source
visible and does not make carrier comparison an ambient boundary.
-/
theorem selectedSectionFamilyCarrierModel_iff_degreewise_carrier_data_and_c2_zero_equivalence :
    Nonempty (SelectedSectionFamilyCarrierModel additive coverBridge K) <->
      Exists fun _ :
        letI := additive.c0AddCommGroup
        letI := K.cochainAddCommGroup 0
        CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0) =>
      Exists fun _ :
        letI := additive.c1AddCommGroup
        letI := K.cochainAddCommGroup 1
        CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1) =>
      Exists fun c2Equiv : E.coefficient.C2 ≃ K.Cn 2 =>
        (letI := K.cochainAddCommGroup 2
         c2Equiv E.coefficient.zero2 = 0) /\
          (letI := K.cochainAddCommGroup 2
           c2Equiv.symm 0 = E.coefficient.zero2) := by
  constructor
  · intro hmodel
    rcases hmodel with ⟨model⟩
    exact
      ⟨model.c0Carrier,
        model.c1Carrier,
        model.c2Equiv,
        model.c2Equiv_zero,
        model.c2Equiv_symm_zero⟩
  · intro hwitness
    rcases hwitness with
      ⟨c0Carrier, c1Carrier, c2Equiv, c2Equiv_zero, c2Equiv_symm_zero⟩
    exact
      ⟨of_degreewise_carrier_data_and_c2_zero_equivalence
        c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero⟩

end SelectedSectionFamilyCarrierModel

namespace SemanticRepairCoverRelativeSectionFamilyWitness

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
Construct the selected section-family witness from carrier-only finite model
data.  This discharges the section-family witness relative to its lower carrier
source without adding differential, `H1`, zero-class, global-coherence, descent,
refinement, or full-sheaf-cohomology fields.
-/
def of_selectedSectionFamilyCarrierModel
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K) :
    SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K where
  c0SectionEquiv := model.c0SectionEquiv
  c1SectionEquiv := model.c1SectionEquiv
  c2SectionEquiv := model.c2Equiv
  c2SectionEquiv_zero := model.c2Equiv_zero
  c2SectionEquiv_symm_zero := model.c2Equiv_symm_zero

/--
Any section-family witness exposes exactly the carrier-only model required to
reconstruct it.  The model is intentionally carrier-level only: face laws remain
the separate `SemanticRepairCoverRelativeFaceRestrictionCompatibility`
obligation.
-/
def toSelectedSectionFamilyCarrierModel
    (sectionWitness :
      SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K) :
    SelectedSectionFamilyCarrierModel additive coverBridge K where
  c0Carrier := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact
      { toCarrier := sectionWitness.c0SectionEquiv
        fromCarrier := sectionWitness.c0SectionEquiv.symm
        from_to := sectionWitness.c0SectionEquiv.left_inv
        to_from := sectionWitness.c0SectionEquiv.right_inv
        toCarrier_add := sectionWitness.c0SectionEquiv.map_add }
  c1Carrier := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact
      { toCarrier := sectionWitness.c1SectionEquiv
        fromCarrier := sectionWitness.c1SectionEquiv.symm
        from_to := sectionWitness.c1SectionEquiv.left_inv
        to_from := sectionWitness.c1SectionEquiv.right_inv
        toCarrier_add := sectionWitness.c1SectionEquiv.map_add }
  c2Equiv := sectionWitness.c2SectionEquiv
  c2Equiv_zero := sectionWitness.c2SectionEquiv_zero
  c2Equiv_symm_zero := sectionWitness.c2SectionEquiv_symm_zero

/--
The selected section-family witness is equivalent to the lower carrier-only
model.  This theorem pushes the remaining provenance obligation down to finite
carrier identifications and zero laws, without folding in face-restriction
compatibility or any `H1` conclusion.
-/
theorem sectionFamilyWitness_iff_selectedSectionFamilyCarrierModel :
    Nonempty
        (SemanticRepairCoverRelativeSectionFamilyWitness
          additive coverBridge K) <->
      Nonempty (SelectedSectionFamilyCarrierModel additive coverBridge K) := by
  constructor
  · intro hwitness
    rcases hwitness with ⟨sectionWitness⟩
    exact ⟨sectionWitness.toSelectedSectionFamilyCarrierModel⟩
  · intro hmodel
    rcases hmodel with ⟨model⟩
    exact ⟨of_selectedSectionFamilyCarrierModel model⟩

end SemanticRepairCoverRelativeSectionFamilyWitness

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

namespace SemanticRepairCoverRelativeFaceRestrictionCompatibility

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
variable {sectionWitness :
  SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K}

/--
Construct face-restriction compatibility from the four explicit selected
face-restriction equations.

This is a provenance-expansion constructor: the compatibility object stores no
more and no less than these equations.  It does not introduce `H1` zero,
boundary membership, global coherence, descent, refinement naturality, or full
sheaf cohomology comparison.
-/
def of_explicit_face_restriction_equations
    (d0_face_to :
      letI := additive.c0AddCommGroup
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      forall primitive : E.coefficient.C0,
        K.alternatingFaceCombination 0
            (fun σ i =>
              K.faceRestrictionTerm 0 i
                (sectionWitness.c0SectionEquiv primitive) σ) =
          sectionWitness.c1SectionEquiv (E.coefficient.delta0 primitive))
    (d0_face_from :
      letI := additive.c0AddCommGroup
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      forall primitive : K.Cn 0,
        E.coefficient.delta0 (sectionWitness.c0SectionEquiv.symm primitive) =
          sectionWitness.c1SectionEquiv.symm
            (K.alternatingFaceCombination 0
              (fun σ i => K.faceRestrictionTerm 0 i primitive σ)))
    (d1_face_to :
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      forall cochain : E.coefficient.C1,
        K.alternatingFaceCombination 1
            (fun σ i =>
              K.faceRestrictionTerm 1 i
                (sectionWitness.c1SectionEquiv cochain) σ) =
          sectionWitness.c2SectionEquiv (E.coefficient.delta1 cochain))
    (d1_face_from :
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      forall cochain : K.Cn 1,
        E.coefficient.delta1 (sectionWitness.c1SectionEquiv.symm cochain) =
          sectionWitness.c2SectionEquiv.symm
            (K.alternatingFaceCombination 1
              (fun σ i => K.faceRestrictionTerm 1 i cochain σ))) :
    SemanticRepairCoverRelativeFaceRestrictionCompatibility
      additive sectionWitness where
  d0_face_to := d0_face_to
  d0_face_from := d0_face_from
  d1_face_to := d1_face_to
  d1_face_from := d1_face_from

/--
The face-restriction compatibility object is equivalent to the four explicit
selected face-restriction equations.

This theorem prevents the compatibility structure from acting as an opaque
certificate: completion must still discharge the four equations from concrete
semantic-delta / presheaf-restriction data.
-/
theorem faceRestrictionCompatibility_iff_explicit_face_restriction_equations :
    Nonempty
        (SemanticRepairCoverRelativeFaceRestrictionCompatibility
          additive sectionWitness) <->
      ((letI := additive.c0AddCommGroup
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
                (fun σ i => K.faceRestrictionTerm 1 i cochain σ)))) := by
  constructor
  · intro hcompatibility
    rcases hcompatibility with ⟨compatibility⟩
    exact
      ⟨compatibility.d0_face_to,
        compatibility.d0_face_from,
        compatibility.d1_face_to,
        compatibility.d1_face_from⟩
  · intro hequations
    exact
      ⟨of_explicit_face_restriction_equations
        hequations.1 hequations.2.1 hequations.2.2.1 hequations.2.2.2⟩

end SemanticRepairCoverRelativeFaceRestrictionCompatibility

/--
Direct selected differential compatibility relative to a fixed section-family
witness.

This is a deliberately separated law source: it talks only about the selected
cover-relative Cech differential `K.d`, not about `H1`, zero classes, global
coherence, effective descent, refinement naturality, or full sheaf cohomology.
The bridge below turns these direct laws into face-restriction laws by using
the general Cech identity `K.d_eq_alternatingFaceCombination`.
-/
structure SemanticRepairCoverRelativeDirectDifferentialCompatibility
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
  d0_direct_to :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : E.coefficient.C0,
      K.d 0 (sectionWitness.c0SectionEquiv primitive) =
        sectionWitness.c1SectionEquiv (E.coefficient.delta0 primitive)
  d0_direct_from :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : K.Cn 0,
      E.coefficient.delta0 (sectionWitness.c0SectionEquiv.symm primitive) =
        sectionWitness.c1SectionEquiv.symm (K.d 0 primitive)
  d1_direct_to :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : E.coefficient.C1,
      K.d 1 (sectionWitness.c1SectionEquiv cochain) =
        sectionWitness.c2SectionEquiv (E.coefficient.delta1 cochain)
  d1_direct_from :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : K.Cn 1,
      E.coefficient.delta1 (sectionWitness.c1SectionEquiv.symm cochain) =
        sectionWitness.c2SectionEquiv.symm (K.d 1 cochain)

namespace SemanticRepairCoverRelativeDirectDifferentialCompatibility

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
variable {sectionWitness :
  SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K}

/--
Direct selected differential laws construct the face-restriction compatibility
needed by the G-06 grounding path.

The proof does not assume the face equations separately: it rewrites `K.d`
through `K.d_eq_alternatingFaceCombination`, so the compatibility is explicitly
read through the selected presheaf face-restriction presentation.
-/
def toFaceRestrictionCompatibility
    (direct :
      SemanticRepairCoverRelativeDirectDifferentialCompatibility
        additive sectionWitness) :
    SemanticRepairCoverRelativeFaceRestrictionCompatibility
      additive sectionWitness where
  d0_face_to := by
    intro primitive
    rw [← K.d_eq_alternatingFaceCombination 0]
    exact direct.d0_direct_to primitive
  d0_face_from := by
    intro primitive
    rw [← K.d_eq_alternatingFaceCombination 0]
    exact direct.d0_direct_from primitive
  d1_face_to := by
    intro cochain
    rw [← K.d_eq_alternatingFaceCombination 1]
    exact direct.d1_direct_to cochain
  d1_face_from := by
    intro cochain
    rw [← K.d_eq_alternatingFaceCombination 1]
    exact direct.d1_direct_from cochain

end SemanticRepairCoverRelativeDirectDifferentialCompatibility

namespace SemanticRepairCoverRelativeFaceRestrictionCompatibility

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
variable {sectionWitness :
  SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K}

/--
Face-restriction compatibility also yields the direct selected differential
laws, again by the same general Cech identity.
-/
def toDirectDifferentialCompatibility
    (compatibility :
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        additive sectionWitness) :
    SemanticRepairCoverRelativeDirectDifferentialCompatibility
      additive sectionWitness where
  d0_direct_to := by
    intro primitive
    rw [K.d_eq_alternatingFaceCombination 0]
    exact compatibility.d0_face_to primitive
  d0_direct_from := by
    intro primitive
    rw [K.d_eq_alternatingFaceCombination 0]
    exact compatibility.d0_face_from primitive
  d1_direct_to := by
    intro cochain
    rw [K.d_eq_alternatingFaceCombination 1]
    exact compatibility.d1_face_to cochain
  d1_direct_from := by
    intro cochain
    rw [K.d_eq_alternatingFaceCombination 1]
    exact compatibility.d1_face_from cochain

/--
The selected face-restriction equations are equivalent to direct differential
compatibility once the cover-relative Cech complex fixes
`d = alternating face combination`.

This equivalence is a source-normalization theorem only.  It does not turn the
direct laws into an ambient boundary and it does not store `H1` conclusions.
-/
theorem faceRestrictionCompatibility_iff_directDifferentialCompatibility :
    Nonempty
        (SemanticRepairCoverRelativeFaceRestrictionCompatibility
          additive sectionWitness) <->
      Nonempty
        (SemanticRepairCoverRelativeDirectDifferentialCompatibility
          additive sectionWitness) := by
  constructor
  · intro hcompatibility
    rcases hcompatibility with ⟨compatibility⟩
    exact ⟨compatibility.toDirectDifferentialCompatibility⟩
  · intro hdirect
    rcases hdirect with ⟨direct⟩
    exact ⟨direct.toFaceRestrictionCompatibility⟩

end SemanticRepairCoverRelativeFaceRestrictionCompatibility

namespace SemanticRepairCoverRelativeDirectDifferentialCompatibility

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
variable {sectionWitness :
  SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K}

/--
Cycle 29 blocker theorem: direct selected differential compatibility remains
an explicit selected differential-law source.

The theorem exposes the four `K.d` equations contained in any direct
compatibility witness and records that the face-restriction presentation is
equivalent to the direct presentation by `K.d_eq_alternatingFaceCombination`.
Thus Cycle 28's normalization cannot be counted as a lower discharge of the
direct laws; the next discharge must construct these equations from genuinely
lower selected semantic-delta / presheaf restriction data, or keep this premise
as an explicit boundary.
-/
theorem requires_explicit_selected_differential_law_source
    (direct :
      SemanticRepairCoverRelativeDirectDifferentialCompatibility
        additive sectionWitness) :
    ((letI := additive.c0AddCommGroup
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      forall primitive : E.coefficient.C0,
        K.d 0 (sectionWitness.c0SectionEquiv primitive) =
          sectionWitness.c1SectionEquiv (E.coefficient.delta0 primitive)) /\
      (letI := additive.c0AddCommGroup
       letI := additive.c1AddCommGroup
       letI := K.cochainAddCommGroup 0
       letI := K.cochainAddCommGroup 1
       forall primitive : K.Cn 0,
        E.coefficient.delta0 (sectionWitness.c0SectionEquiv.symm primitive) =
          sectionWitness.c1SectionEquiv.symm (K.d 0 primitive)) /\
      (letI := additive.c1AddCommGroup
       letI := K.cochainAddCommGroup 1
       forall cochain : E.coefficient.C1,
        K.d 1 (sectionWitness.c1SectionEquiv cochain) =
          sectionWitness.c2SectionEquiv (E.coefficient.delta1 cochain)) /\
      (letI := additive.c1AddCommGroup
       letI := K.cochainAddCommGroup 1
       forall cochain : K.Cn 1,
        E.coefficient.delta1 (sectionWitness.c1SectionEquiv.symm cochain) =
          sectionWitness.c2SectionEquiv.symm (K.d 1 cochain))) /\
      Nonempty
        (SemanticRepairCoverRelativeFaceRestrictionCompatibility
          additive sectionWitness) /\
      (Nonempty
          (SemanticRepairCoverRelativeFaceRestrictionCompatibility
            additive sectionWitness) <->
        Nonempty
          (SemanticRepairCoverRelativeDirectDifferentialCompatibility
            additive sectionWitness)) := by
  exact
    ⟨⟨direct.d0_direct_to,
      direct.d0_direct_from,
      direct.d1_direct_to,
      direct.d1_direct_from⟩,
      ⟨direct.toFaceRestrictionCompatibility⟩,
      SemanticRepairCoverRelativeFaceRestrictionCompatibility.faceRestrictionCompatibility_iff_directDifferentialCompatibility⟩

end SemanticRepairCoverRelativeDirectDifferentialCompatibility

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
Lower selected carrier geometry for the semantic residual coefficient surface.

This is below `SemanticRepairCarrierSpecificComparisonProvenance`: it contains
only the degree-wise carrier identifications and the degree-`2` zero laws.  It
does not contain selected differential equations, quotient comparison, zero
`H1`, boundary membership, global semantic repair coherence, effective
descent, refinement naturality, or full sheaf cohomology comparison.
-/
structure SemanticRepairSelectedCarrierGeometry
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
  c0Carrier :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0)
  c1Carrier :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1)
  c2Equiv : E.coefficient.C2 ≃ K.Cn 2
  c2Equiv_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv E.coefficient.zero2 = 0
  c2Equiv_symm_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv.symm 0 = E.coefficient.zero2

/--
Selected Cech face laws for a fixed lower carrier geometry.

These laws are the actual presheaf / selected Cech face-compatibility part of
the lower source.  They are separated from carrier geometry so G-06 cannot
count carrier identification alone as differential compatibility.  The
structure still stores no `H1` zero, global coherence, descent conclusion,
refinement naturality, or full sheaf cohomology comparison.
-/
structure SemanticRepairSelectedCechFaceLawSource
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
    (geometry :
      SemanticRepairSelectedCarrierGeometry additive coverBridge K) where
  d0_face_to :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : E.coefficient.C0,
      K.alternatingFaceCombination 0
          (fun σ i =>
            K.faceRestrictionTerm 0 i
              (geometry.c0Carrier.toCarrier primitive) σ) =
        geometry.c1Carrier.toCarrier (E.coefficient.delta0 primitive)
  d0_face_from :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : K.Cn 0,
      E.coefficient.delta0 (geometry.c0Carrier.fromCarrier primitive) =
        geometry.c1Carrier.fromCarrier
          (K.alternatingFaceCombination 0
            (fun σ i => K.faceRestrictionTerm 0 i primitive σ))
  d1_face_to :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : E.coefficient.C1,
      K.alternatingFaceCombination 1
          (fun σ i =>
            K.faceRestrictionTerm 1 i
              (geometry.c1Carrier.toCarrier cochain) σ) =
        geometry.c2Equiv (E.coefficient.delta1 cochain)
  d1_face_from :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : K.Cn 1,
      E.coefficient.delta1 (geometry.c1Carrier.fromCarrier cochain) =
        geometry.c2Equiv.symm
          (K.alternatingFaceCombination 1
            (fun σ i => K.faceRestrictionTerm 1 i cochain σ))

namespace SemanticRepairSelectedCarrierGeometry

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
Construct selected carrier geometry from the concrete carrier-only section
family model.

This is the Cycle 26 lower-construction theorem for the carrier-geometry node:
the selected geometry used by Cycle 25 is generated from the already separated
finite carrier source.  The source is still carrier comparison data, not bare
cover membership, and it stores no face laws, `H1` zero, global coherence,
effective descent, refinement naturality, or full sheaf cohomology comparison.
-/
def of_selectedSectionFamilyCarrierModel
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K) :
    SemanticRepairSelectedCarrierGeometry additive coverBridge K where
  c0Carrier := model.c0Carrier
  c1Carrier := model.c1Carrier
  c2Equiv := model.c2Equiv
  c2Equiv_zero := model.c2Equiv_zero
  c2Equiv_symm_zero := model.c2Equiv_symm_zero

/--
Every selected carrier geometry exposes the concrete carrier-only model from
which it can be reconstructed.

This keeps the carrier comparison provenance visible instead of allowing
`SemanticRepairSelectedCarrierGeometry` to become an opaque certificate.
-/
def toSelectedSectionFamilyCarrierModel
    (geometry : SemanticRepairSelectedCarrierGeometry additive coverBridge K) :
    SelectedSectionFamilyCarrierModel additive coverBridge K where
  c0Carrier := geometry.c0Carrier
  c1Carrier := geometry.c1Carrier
  c2Equiv := geometry.c2Equiv
  c2Equiv_zero := geometry.c2Equiv_zero
  c2Equiv_symm_zero := geometry.c2Equiv_symm_zero

/--
The selected carrier geometry node is equivalent to the concrete carrier-only
section-family model.

The equivalence is carrier-only.  It does not discharge the remaining selected
Cech face laws, and it does not introduce any target conclusion as a structure
field.
-/
theorem selectedCarrierGeometry_iff_selectedSectionFamilyCarrierModel :
    Nonempty
        (SemanticRepairSelectedCarrierGeometry additive coverBridge K) <->
      Nonempty (SelectedSectionFamilyCarrierModel additive coverBridge K) := by
  constructor
  · intro hgeometry
    rcases hgeometry with ⟨geometry⟩
    exact ⟨geometry.toSelectedSectionFamilyCarrierModel⟩
  · intro hmodel
    rcases hmodel with ⟨model⟩
    exact ⟨of_selectedSectionFamilyCarrierModel model⟩

/--
The concrete carrier-only model constructs the selected carrier geometry used
by the carrier-specific comparison provenance path.
-/
theorem selectedSectionFamilyCarrierModel_constructs_selectedCarrierGeometry
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K) :
    Nonempty
      (SemanticRepairSelectedCarrierGeometry additive coverBridge K) :=
  ⟨of_selectedSectionFamilyCarrierModel model⟩

/--
Boundary audit for selected carrier geometry: supplying the geometry is exactly
supplying the explicit carrier comparison source already isolated by
`SelectedSectionFamilyCarrierModel`.
-/
theorem requires_explicit_selected_carrier_source
    (geometry : SemanticRepairSelectedCarrierGeometry additive coverBridge K) :
    (Nonempty
        (letI := additive.c0AddCommGroup
         letI := K.cochainAddCommGroup 0
         CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0)) /\
      Nonempty
        (letI := additive.c1AddCommGroup
         letI := K.cochainAddCommGroup 1
         CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1)) /\
      Exists fun c2Equiv : E.coefficient.C2 ≃ K.Cn 2 =>
        (letI := K.cochainAddCommGroup 2
         c2Equiv E.coefficient.zero2 = 0) /\
          (letI := K.cochainAddCommGroup 2
           c2Equiv.symm 0 = E.coefficient.zero2)) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          CarrierSpecificAdditiveComparisonData C D) :=
  geometry.toSelectedSectionFamilyCarrierModel.requires_explicit_selected_carrier_source

end SemanticRepairSelectedCarrierGeometry

namespace SemanticRepairSelectedCechFaceLawSource

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
Construct the selected Cech face-law source for the carrier geometry built from
a concrete carrier-only model.

The lower source is the actual face-restriction compatibility witness relative
to the section-family witness constructed from the same carrier model.  This
does not generate the face laws from bare site/sheaf/descent data; it moves the
Cycle 25 selected face-law premise down to the already separated
face-restriction compatibility witness and keeps that witness explicit.
-/
def of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K)
    (compatibility :
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        additive
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    SemanticRepairSelectedCechFaceLawSource
      additive
      (SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
        model) where
  d0_face_to := by
    intro primitive
    simpa [SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c0SectionEquiv,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        compatibility.d0_face_to primitive
  d0_face_from := by
    intro primitive
    simpa [SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c0SectionEquiv,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        compatibility.d0_face_from primitive
  d1_face_to := by
    intro cochain
    simpa [SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        compatibility.d1_face_to cochain
  d1_face_from := by
    intro cochain
    simpa [SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        compatibility.d1_face_from cochain

/--
Carrier-only model data plus actual selected face-restriction compatibility
constructs the selected Cech face-law source required by the Cycle 25
carrier-specific provenance path.
-/
theorem selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility_constructs_selectedCechFaceLawSource
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K)
    (compatibility :
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        additive
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    Nonempty
      (SemanticRepairSelectedCechFaceLawSource
        additive
        (SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
          model)) :=
  ⟨of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
      model compatibility⟩

/--
Construct the selected Cech face-law source from direct selected differential
laws.

The direct laws speak in terms of the selected cover-relative Cech differential
`K.d`.  The construction normalizes them to the selected presheaf
face-restriction presentation using `K.d_eq_alternatingFaceCombination` through
`SemanticRepairCoverRelativeDirectDifferentialCompatibility.toFaceRestrictionCompatibility`,
then uses the Cycle 27 constructor.  This keeps the remaining lower premise at
the level of selected differential compatibility, not an already supplied
face-law source.
-/
def of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K)
    (direct :
      SemanticRepairCoverRelativeDirectDifferentialCompatibility
        additive
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    SemanticRepairSelectedCechFaceLawSource
      additive
      (SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
        model) :=
  of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
    model direct.toFaceRestrictionCompatibility

/--
Carrier-only model data plus direct selected differential laws construct the
selected Cech face-law source for the model-built carrier geometry.

The selected face laws are therefore no longer an independent material premise
once direct selected differential compatibility has been supplied or proved.
-/
theorem selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility_constructs_selectedCechFaceLawSource
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K)
    (direct :
      SemanticRepairCoverRelativeDirectDifferentialCompatibility
        additive
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    Nonempty
      (SemanticRepairSelectedCechFaceLawSource
        additive
        (SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
          model)) :=
  ⟨of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
      model direct⟩

/--
Boundary audit for the selected Cech face-law source: supplying this source is
exactly supplying the four selected face-restriction equations for the fixed
selected carrier geometry.

This theorem does not generate the equations from presheaf restriction,
sheaf condition, descent, or cover membership.  It exposes the material
premise contained in the source so it cannot be counted as an opaque
certificate.
-/
theorem requires_explicit_selected_face_restriction_equations
    {geometry :
      SemanticRepairSelectedCarrierGeometry additive coverBridge K}
    (faceLaws :
      SemanticRepairSelectedCechFaceLawSource additive geometry) :
    (letI := additive.c0AddCommGroup
     letI := additive.c1AddCommGroup
     letI := K.cochainAddCommGroup 0
     letI := K.cochainAddCommGroup 1
     forall primitive : E.coefficient.C0,
      K.alternatingFaceCombination 0
          (fun σ i =>
            K.faceRestrictionTerm 0 i
              (geometry.c0Carrier.toCarrier primitive) σ) =
        geometry.c1Carrier.toCarrier (E.coefficient.delta0 primitive)) /\
      (letI := additive.c0AddCommGroup
       letI := additive.c1AddCommGroup
       letI := K.cochainAddCommGroup 0
       letI := K.cochainAddCommGroup 1
       forall primitive : K.Cn 0,
        E.coefficient.delta0 (geometry.c0Carrier.fromCarrier primitive) =
          geometry.c1Carrier.fromCarrier
            (K.alternatingFaceCombination 0
              (fun σ i => K.faceRestrictionTerm 0 i primitive σ))) /\
      (letI := additive.c1AddCommGroup
       letI := K.cochainAddCommGroup 1
       forall cochain : E.coefficient.C1,
        K.alternatingFaceCombination 1
            (fun σ i =>
              K.faceRestrictionTerm 1 i
                (geometry.c1Carrier.toCarrier cochain) σ) =
          geometry.c2Equiv (E.coefficient.delta1 cochain)) /\
      (letI := additive.c1AddCommGroup
       letI := K.cochainAddCommGroup 1
       forall cochain : K.Cn 1,
        E.coefficient.delta1 (geometry.c1Carrier.fromCarrier cochain) =
          geometry.c2Equiv.symm
            (K.alternatingFaceCombination 1
              (fun σ i => K.faceRestrictionTerm 1 i cochain σ))) := by
  exact
    ⟨faceLaws.d0_face_to,
      faceLaws.d0_face_from,
      faceLaws.d1_face_to,
      faceLaws.d1_face_from⟩

end SemanticRepairSelectedCechFaceLawSource

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
Extract the lower selected carrier geometry contained in carrier-specific
provenance.
-/
def toSelectedCarrierGeometry
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    SemanticRepairSelectedCarrierGeometry additive coverBridge K where
  c0Carrier := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact
      { toCarrier := provenance.toSection0
        fromCarrier := provenance.fromSection0
        from_to := provenance.from_to_section0
        to_from := provenance.to_from_section0
        toCarrier_add := provenance.toSection0_add }
  c1Carrier := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact
      { toCarrier := provenance.toSection1
        fromCarrier := provenance.fromSection1
        from_to := provenance.from_to_section1
        to_from := provenance.to_from_section1
        toCarrier_add := provenance.toSection1_add }
  c2Equiv :=
    { toFun := provenance.toSection2
      invFun := provenance.fromSection2
      left_inv := provenance.from_to_section2
      right_inv := provenance.to_from_section2 }
  c2Equiv_zero := provenance.toSection2_zero
  c2Equiv_symm_zero := provenance.fromSection2_zero

/--
Extract the selected Cech face laws contained in carrier-specific provenance,
relative to the extracted carrier geometry.
-/
def toSelectedCechFaceLawSource
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    SemanticRepairSelectedCechFaceLawSource
      additive provenance.toSelectedCarrierGeometry where
  d0_face_to := by
    intro primitive
    simpa [toSelectedCarrierGeometry] using provenance.d0_face_to primitive
  d0_face_from := by
    intro primitive
    simpa [toSelectedCarrierGeometry] using provenance.d0_face_from primitive
  d1_face_to := by
    intro cochain
    simpa [toSelectedCarrierGeometry] using provenance.d1_face_to cochain
  d1_face_from := by
    intro cochain
    simpa [toSelectedCarrierGeometry] using provenance.d1_face_from cochain

/--
Lower selected carrier geometry plus selected Cech face laws construct
carrier-specific comparison provenance.

This is the Cycle 25 lower-construction theorem.  It separates the carrier
geometry source from the actual face-restriction laws and then reconstructs the
previous monolithic provenance object.  The lower inputs still contain material
carrier and differential data, so this theorem does not reclassify them as
ambient boundary and does not store any target conclusion.
-/
def of_selectedCarrierGeometry_and_faceLaws
    (geometry :
      SemanticRepairSelectedCarrierGeometry additive coverBridge K)
    (faceLaws :
      SemanticRepairSelectedCechFaceLawSource additive geometry) :
    SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K where
  toSection0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact geometry.c0Carrier.toCarrier
  fromSection0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact geometry.c0Carrier.fromCarrier
  from_to_section0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact geometry.c0Carrier.from_to
  to_from_section0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact geometry.c0Carrier.to_from
  toSection0_add := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact geometry.c0Carrier.toCarrier_add
  toSection1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact geometry.c1Carrier.toCarrier
  fromSection1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact geometry.c1Carrier.fromCarrier
  from_to_section1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact geometry.c1Carrier.from_to
  to_from_section1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact geometry.c1Carrier.to_from
  toSection1_add := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact geometry.c1Carrier.toCarrier_add
  toSection2 := geometry.c2Equiv
  fromSection2 := geometry.c2Equiv.symm
  from_to_section2 := geometry.c2Equiv.left_inv
  to_from_section2 := geometry.c2Equiv.right_inv
  toSection2_zero := geometry.c2Equiv_zero
  fromSection2_zero := geometry.c2Equiv_symm_zero
  d0_face_to := faceLaws.d0_face_to
  d0_face_from := faceLaws.d0_face_from
  d1_face_to := faceLaws.d1_face_to
  d1_face_from := faceLaws.d1_face_from

/--
Lower selected carrier geometry and selected Cech face laws are a concrete
source for carrier-specific comparison provenance.
-/
theorem selectedCarrierGeometry_and_faceLaws_constructs_carrierSpecificComparisonProvenance
    (geometry :
      SemanticRepairSelectedCarrierGeometry additive coverBridge K)
    (faceLaws :
      SemanticRepairSelectedCechFaceLawSource additive geometry) :
    Nonempty
      (SemanticRepairCarrierSpecificComparisonProvenance
        additive coverBridge K) :=
  ⟨of_selectedCarrierGeometry_and_faceLaws geometry faceLaws⟩

/--
Carrier-specific provenance is equivalent to supplying lower selected carrier
geometry plus selected Cech face laws.

The forward direction exposes the exact lower material sources; the backward
direction constructs provenance from those sources.  This prevents G-06 from
treating `SemanticRepairCarrierSpecificComparisonProvenance` as an opaque
certificate while keeping the remaining lower obligations explicit.
-/
theorem carrierSpecificComparisonProvenance_iff_selectedCarrierGeometry_and_faceLaws :
    Nonempty
        (SemanticRepairCarrierSpecificComparisonProvenance
          additive coverBridge K) <->
      Exists fun geometry :
        SemanticRepairSelectedCarrierGeometry additive coverBridge K =>
          SemanticRepairSelectedCechFaceLawSource additive geometry := by
  constructor
  · intro hprovenance
    rcases hprovenance with ⟨provenance⟩
    exact
      ⟨provenance.toSelectedCarrierGeometry,
        provenance.toSelectedCechFaceLawSource⟩
  · intro hlower
    rcases hlower with ⟨geometry, faceLaws⟩
    exact ⟨of_selectedCarrierGeometry_and_faceLaws geometry faceLaws⟩

/--
Construct carrier-specific provenance from explicit finite carrier witness data
and the four selected face-restriction equations.

This is the constructive converse to the Cycle 40 extraction path: the
provenance node is not an opaque premise once the lower carrier comparisons,
degree-`2` zero laws, and selected face equations are supplied.  The lower data
itself remains material input; this construction does not generate carrier
maps or face laws from bare cover membership, sheaf condition, descent, or full
sheaf cohomology.
-/
def of_degreewiseCarrierData_and_explicitFaceRestrictionEquations
    (c0Carrier :
      letI := additive.c0AddCommGroup
      letI := K.cochainAddCommGroup 0
      CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0))
    (c1Carrier :
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1))
    (c2Equiv : E.coefficient.C2 ≃ K.Cn 2)
    (c2Equiv_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv E.coefficient.zero2 = 0)
    (c2Equiv_symm_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv.symm 0 = E.coefficient.zero2)
    (d0_face_to :
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := additive) (coverBridge := coverBridge) (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := additive.c0AddCommGroup
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      forall primitive : E.coefficient.C0,
        K.alternatingFaceCombination 0
            (fun σ i =>
              K.faceRestrictionTerm 0 i
                (sectionWitness.c0SectionEquiv primitive) σ) =
          sectionWitness.c1SectionEquiv (E.coefficient.delta0 primitive))
    (d0_face_from :
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := additive) (coverBridge := coverBridge) (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := additive.c0AddCommGroup
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      forall primitive : K.Cn 0,
        E.coefficient.delta0 (sectionWitness.c0SectionEquiv.symm primitive) =
          sectionWitness.c1SectionEquiv.symm
            (K.alternatingFaceCombination 0
              (fun σ i => K.faceRestrictionTerm 0 i primitive σ)))
    (d1_face_to :
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := additive) (coverBridge := coverBridge) (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      forall cochain : E.coefficient.C1,
        K.alternatingFaceCombination 1
            (fun σ i =>
              K.faceRestrictionTerm 1 i
                (sectionWitness.c1SectionEquiv cochain) σ) =
          sectionWitness.c2SectionEquiv (E.coefficient.delta1 cochain))
    (d1_face_from :
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := additive) (coverBridge := coverBridge) (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      forall cochain : K.Cn 1,
        E.coefficient.delta1 (sectionWitness.c1SectionEquiv.symm cochain) =
          sectionWitness.c2SectionEquiv.symm
            (K.alternatingFaceCombination 1
              (fun σ i => K.faceRestrictionTerm 1 i cochain σ))) :
    SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K where
  toSection0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact c0Carrier.toCarrier
  fromSection0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact c0Carrier.fromCarrier
  from_to_section0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact c0Carrier.from_to
  to_from_section0 := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact c0Carrier.to_from
  toSection0_add := by
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    exact c0Carrier.toCarrier_add
  toSection1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact c1Carrier.toCarrier
  fromSection1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact c1Carrier.fromCarrier
  from_to_section1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact c1Carrier.from_to
  to_from_section1 := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact c1Carrier.to_from
  toSection1_add := by
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    exact c1Carrier.toCarrier_add
  toSection2 := c2Equiv
  fromSection2 := c2Equiv.symm
  from_to_section2 := c2Equiv.left_inv
  to_from_section2 := c2Equiv.right_inv
  toSection2_zero := c2Equiv_zero
  fromSection2_zero := c2Equiv_symm_zero
  d0_face_to := by
    dsimp only at d0_face_to
    intro primitive
    simpa [
      SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c0SectionEquiv,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        d0_face_to primitive
  d0_face_from := by
    dsimp only at d0_face_from
    intro primitive
    simpa [
      SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c0SectionEquiv,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        d0_face_from primitive
  d1_face_to := by
    dsimp only at d1_face_to
    intro cochain
    simpa [
      SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        d1_face_to cochain
  d1_face_from := by
    dsimp only at d1_face_from
    intro cochain
    simpa [
      SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        d1_face_from cochain

/--
Explicit finite carrier data and selected face-restriction equations construct
the carrier-specific provenance node required by the downstream G-06 proof DAG.
-/
theorem degreewiseCarrierData_and_explicitFaceRestrictionEquations_constructs_carrierSpecificComparisonProvenance
    (c0Carrier :
      letI := additive.c0AddCommGroup
      letI := K.cochainAddCommGroup 0
      CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0))
    (c1Carrier :
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1))
    (c2Equiv : E.coefficient.C2 ≃ K.Cn 2)
    (c2Equiv_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv E.coefficient.zero2 = 0)
    (c2Equiv_symm_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv.symm 0 = E.coefficient.zero2)
    (d0_face_to :
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := additive) (coverBridge := coverBridge) (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := additive.c0AddCommGroup
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      forall primitive : E.coefficient.C0,
        K.alternatingFaceCombination 0
            (fun σ i =>
              K.faceRestrictionTerm 0 i
                (sectionWitness.c0SectionEquiv primitive) σ) =
          sectionWitness.c1SectionEquiv (E.coefficient.delta0 primitive))
    (d0_face_from :
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := additive) (coverBridge := coverBridge) (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := additive.c0AddCommGroup
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      forall primitive : K.Cn 0,
        E.coefficient.delta0 (sectionWitness.c0SectionEquiv.symm primitive) =
          sectionWitness.c1SectionEquiv.symm
            (K.alternatingFaceCombination 0
              (fun σ i => K.faceRestrictionTerm 0 i primitive σ)))
    (d1_face_to :
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := additive) (coverBridge := coverBridge) (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      forall cochain : E.coefficient.C1,
        K.alternatingFaceCombination 1
            (fun σ i =>
              K.faceRestrictionTerm 1 i
                (sectionWitness.c1SectionEquiv cochain) σ) =
          sectionWitness.c2SectionEquiv (E.coefficient.delta1 cochain))
    (d1_face_from :
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := additive) (coverBridge := coverBridge) (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := additive.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      forall cochain : K.Cn 1,
        E.coefficient.delta1 (sectionWitness.c1SectionEquiv.symm cochain) =
          sectionWitness.c2SectionEquiv.symm
            (K.alternatingFaceCombination 1
              (fun σ i => K.faceRestrictionTerm 1 i cochain σ))) :
    Nonempty
      (SemanticRepairCarrierSpecificComparisonProvenance
        additive coverBridge K) :=
  ⟨of_degreewiseCarrierData_and_explicitFaceRestrictionEquations
    c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
    d0_face_to d0_face_from d1_face_to d1_face_from⟩

/--
The carrier-specific provenance node is equivalent to explicit finite carrier
witness data plus the four selected face-restriction equations.

This is a provenance audit theorem.  It prevents G-06 from treating
`SemanticRepairCarrierSpecificComparisonProvenance` as an independent opaque
premise while keeping the actual lower data visible as the remaining
discharge-required source.
-/
theorem carrierSpecificComparisonProvenance_iff_degreewiseCarrierData_and_explicitFaceRestrictionEquations :
    Nonempty
        (SemanticRepairCarrierSpecificComparisonProvenance
          additive coverBridge K) <->
      Exists fun c0Carrier :
        letI := additive.c0AddCommGroup
        letI := K.cochainAddCommGroup 0
        CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0) =>
      Exists fun c1Carrier :
        letI := additive.c1AddCommGroup
        letI := K.cochainAddCommGroup 1
        CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1) =>
      Exists fun c2Equiv : E.coefficient.C2 ≃ K.Cn 2 =>
      Exists fun c2Equiv_zero :
        letI := K.cochainAddCommGroup 2
        c2Equiv E.coefficient.zero2 = 0 =>
      Exists fun c2Equiv_symm_zero :
        letI := K.cochainAddCommGroup 2
        c2Equiv.symm 0 = E.coefficient.zero2 =>
        (let model :=
          SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
            (additive := additive) (coverBridge := coverBridge) (K := K)
            c0Carrier c1Carrier c2Equiv
            c2Equiv_zero c2Equiv_symm_zero
         let sectionWitness :=
          SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model
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
                  (fun σ i => K.faceRestrictionTerm 1 i cochain σ)))) := by
  constructor
  · intro hprovenance
    rcases hprovenance with ⟨provenance⟩
    let c0Carrier :
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
    let c1Carrier :
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
    let c2Equiv : E.coefficient.C2 ≃ K.Cn 2 :=
      { toFun := provenance.toSection2
        invFun := provenance.fromSection2
        left_inv := provenance.from_to_section2
        right_inv := provenance.to_from_section2 }
    refine
      ⟨c0Carrier,
        c1Carrier,
        c2Equiv,
        provenance.toSection2_zero,
        provenance.fromSection2_zero,
        ?_, ?_, ?_, ?_⟩
    · dsimp only
      intro primitive
      simpa [
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
        SelectedSectionFamilyCarrierModel.c0SectionEquiv,
        SelectedSectionFamilyCarrierModel.c1SectionEquiv,
        CarrierSpecificAdditiveComparisonData.toAddEquiv,
        c0Carrier, c1Carrier, c2Equiv] using
          provenance.d0_face_to primitive
    · dsimp only
      intro primitive
      simpa [
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
        SelectedSectionFamilyCarrierModel.c0SectionEquiv,
        SelectedSectionFamilyCarrierModel.c1SectionEquiv,
        CarrierSpecificAdditiveComparisonData.toAddEquiv,
        c0Carrier, c1Carrier, c2Equiv] using
          provenance.d0_face_from primitive
    · dsimp only
      intro cochain
      simpa [
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
        SelectedSectionFamilyCarrierModel.c1SectionEquiv,
        CarrierSpecificAdditiveComparisonData.toAddEquiv,
        c0Carrier, c1Carrier, c2Equiv] using
          provenance.d1_face_to cochain
    · dsimp only
      intro cochain
      simpa [
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
        SelectedSectionFamilyCarrierModel.c1SectionEquiv,
        CarrierSpecificAdditiveComparisonData.toAddEquiv,
        c0Carrier, c1Carrier, c2Equiv] using
          provenance.d1_face_from cochain
  · intro hlower
    rcases hlower with
      ⟨c0Carrier, c1Carrier, c2Equiv, c2Equiv_zero,
        c2Equiv_symm_zero, d0_face_to, d0_face_from,
        d1_face_to, d1_face_from⟩
    exact
      ⟨of_degreewiseCarrierData_and_explicitFaceRestrictionEquations
        c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
        d0_face_to d0_face_from d1_face_to d1_face_from⟩

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
Cycle 30 blocker theorem: the current site/sheaf/presheaf surface reaches only
the general presheaf restriction laws and the selected Cech differential
formula.

These facts are real mathematical structure: restrictions preserve zero and
addition, and `K.d` is the alternating combination of selected face
restrictions.  They still stop before the selected semantic-delta comparison
needed for
`SemanticRepairCoverRelativeDirectDifferentialCompatibility`: they do not
identify arbitrary semantic coefficient carriers with the selected Cech
section families, and hence cannot by themselves construct the four direct
`K.d` equations exposed in Cycle 29.
-/
theorem current_g06_presheaf_laws_stop_before_selected_differential_source
    (surface :
      CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob)) :
    (∀ {source target : S.category} (f : source ⟶ target),
      letI := Ob.addCommGroup target
      letI := Ob.addCommGroup source
      Ob.carrier.toPresheaf.map f.op 0 = 0) /\
      (∀ {source target : S.category} (f : source ⟶ target)
          (x y : Ob.carrier.toPresheaf.obj (op target)),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op (x + y) =
          Ob.carrier.toPresheaf.map f.op x +
            Ob.carrier.toPresheaf.map f.op y) /\
      (∀ (n : Nat) (c : surface.K.Cn n),
        surface.K.d n c =
          surface.K.alternatingFaceCombination n
            (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          CarrierSpecificAdditiveComparisonData C D) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          C ≃+ D) := by
  exact
    ⟨(by
        intro source target f
        exact Ob.map_zero f),
      (by
        intro source target f x y
        exact Ob.map_add f x y),
      (by
        intro n c
        exact surface.K.d_eq_alternatingFaceCombination n c),
      no_uniform_carrier_specific_additive_comparison_from_bare_groups,
      SemanticRepairCoverRelativeFaceRestrictionRealization.no_uniform_additive_carrier_equivalence_from_bare_lower_data⟩

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

namespace SelectedSectionFamilyCarrierModel

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
Richer carrier-specific provenance constructs the carrier-only model introduced
in Cycle 20.  This bridge reuses only the carrier maps, inverse/additivity laws,
and degree-`2` zero laws; it deliberately discards the face-restriction
equations carried by the richer provenance.
-/
def of_carrierSpecificComparisonProvenance
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    SelectedSectionFamilyCarrierModel additive coverBridge K where
  c0Carrier := provenance.degreeZeroAdditiveComparisonData
  c1Carrier := provenance.degreeOneAdditiveComparisonData
  c2Equiv := provenance.c2SectionEquiv
  c2Equiv_zero := provenance.toSection2_zero
  c2Equiv_symm_zero := provenance.fromSection2_zero

/--
Carrier-specific provenance is a concrete source for the Cycle 20 carrier-only
model.  This is not a discharge from bare site/sheaf/descent input; it connects
the previously audited richer provenance layer to the separated lower carrier
model now used by the G-06 proof DAG.
-/
theorem carrierSpecificComparisonProvenance_constructs_selectedSectionFamilyCarrierModel
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    Nonempty (SelectedSectionFamilyCarrierModel additive coverBridge K) :=
  ⟨of_carrierSpecificComparisonProvenance provenance⟩

end SelectedSectionFamilyCarrierModel

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

/--
Extract the finite section-family witness contained in a richer selected
section-realization bridge.

This projection exposes only carrier equivalences and degree-`2` zero laws. It
does not expose the direct differential laws, `H1` conclusions, descent,
global coherence, refinement naturality, or full sheaf cohomology comparison.
-/
def toSectionFamilyWitness
    (bridge : SemanticRepairCoverRelativeSectionRealizationBridge additive coverBridge K) :
    SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K where
  c0SectionEquiv := bridge.c0SectionEquiv
  c1SectionEquiv := bridge.c1SectionEquiv
  c2SectionEquiv := bridge.c2SectionEquiv
  c2SectionEquiv_zero := bridge.c2SectionEquiv_zero
  c2SectionEquiv_symm_zero := bridge.c2SectionEquiv_symm_zero

/--
Extract the carrier-only selected section-family model from a richer selected
section-realization bridge.
-/
def toSelectedSectionFamilyCarrierModel
    (bridge : SemanticRepairCoverRelativeSectionRealizationBridge additive coverBridge K) :
    SelectedSectionFamilyCarrierModel additive coverBridge K :=
  bridge.toSectionFamilyWitness.toSelectedSectionFamilyCarrierModel

/--
Extract the direct differential laws relative to the bridge's own
section-family witness.
-/
def toDirectDifferentialCompatibility
    (bridge : SemanticRepairCoverRelativeSectionRealizationBridge additive coverBridge K) :
    SemanticRepairCoverRelativeDirectDifferentialCompatibility
      additive bridge.toSectionFamilyWitness where
  d0_direct_to := by
    intro primitive
    exact bridge.d0_section_to primitive
  d0_direct_from := by
    intro primitive
    exact bridge.d0_section_from primitive
  d1_direct_to := by
    intro cochain
    exact bridge.d1_section_to cochain
  d1_direct_from := by
    intro cochain
    exact bridge.d1_section_from cochain

/--
Extract direct differential laws relative to the section witness reconstructed
from the extracted carrier-only model.

This connects the older richer bridge to the Cycle 20/22 lower DAG:
`SelectedSectionFamilyCarrierModel` constructs the section witness, and the
bridge supplies the direct selected differential laws for that witness.
-/
def toDirectDifferentialCompatibilityForSelectedCarrierModel
    (bridge : SemanticRepairCoverRelativeSectionRealizationBridge additive coverBridge K) :
    SemanticRepairCoverRelativeDirectDifferentialCompatibility
      additive
        (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          bridge.toSelectedSectionFamilyCarrierModel) where
  d0_direct_to := by
    intro primitive
    simpa [toSelectedSectionFamilyCarrierModel, toSectionFamilyWitness,
      SemanticRepairCoverRelativeSectionFamilyWitness.toSelectedSectionFamilyCarrierModel,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c0SectionEquiv,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        bridge.d0_section_to primitive
  d0_direct_from := by
    intro primitive
    simpa [toSelectedSectionFamilyCarrierModel, toSectionFamilyWitness,
      SemanticRepairCoverRelativeSectionFamilyWitness.toSelectedSectionFamilyCarrierModel,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c0SectionEquiv,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        bridge.d0_section_from primitive
  d1_direct_to := by
    intro cochain
    simpa [toSelectedSectionFamilyCarrierModel, toSectionFamilyWitness,
      SemanticRepairCoverRelativeSectionFamilyWitness.toSelectedSectionFamilyCarrierModel,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        bridge.d1_section_to cochain
  d1_direct_from := by
    intro cochain
    simpa [toSelectedSectionFamilyCarrierModel, toSectionFamilyWitness,
      SemanticRepairCoverRelativeSectionFamilyWitness.toSelectedSectionFamilyCarrierModel,
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
      SelectedSectionFamilyCarrierModel.c1SectionEquiv,
      CarrierSpecificAdditiveComparisonData.toAddEquiv] using
        bridge.d1_section_from cochain

/--
Construct the richer section-realization bridge from the separated lower
section-family witness and direct selected differential laws.
-/
def of_sectionFamilyWitness_and_directDifferentialCompatibility
    (sectionWitness :
      SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K)
    (direct :
      SemanticRepairCoverRelativeDirectDifferentialCompatibility
        additive sectionWitness) :
    SemanticRepairCoverRelativeSectionRealizationBridge additive coverBridge K where
  c0SectionEquiv := sectionWitness.c0SectionEquiv
  c1SectionEquiv := sectionWitness.c1SectionEquiv
  c2SectionEquiv := sectionWitness.c2SectionEquiv
  c2SectionEquiv_zero := sectionWitness.c2SectionEquiv_zero
  c2SectionEquiv_symm_zero := sectionWitness.c2SectionEquiv_symm_zero
  d0_section_to := direct.d0_direct_to
  d0_section_from := direct.d0_direct_from
  d1_section_to := direct.d1_direct_to
  d1_section_from := direct.d1_direct_from

/--
The richer section-realization bridge is exactly the separated finite
section-family witness plus direct selected differential laws.

This theorem exposes the older bridge as a source for the current lower proof
DAG without treating it as a completed target premise.
-/
theorem sectionRealizationBridge_iff_sectionFamilyWitness_and_directDifferentialCompatibility :
    Nonempty
        (SemanticRepairCoverRelativeSectionRealizationBridge
          additive coverBridge K) <->
      Exists fun sectionWitness :
        SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K =>
          SemanticRepairCoverRelativeDirectDifferentialCompatibility
            additive sectionWitness := by
  constructor
  · intro hbridge
    rcases hbridge with ⟨bridge⟩
    exact ⟨bridge.toSectionFamilyWitness, bridge.toDirectDifferentialCompatibility⟩
  · intro hwitness
    rcases hwitness with ⟨sectionWitness, direct⟩
    exact
      ⟨of_sectionFamilyWitness_and_directDifferentialCompatibility
        sectionWitness direct⟩

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

/--
Lower selected carrier geometry plus selected Cech face laws reach the selected
cover-relative grounding package by first constructing carrier-specific
provenance and then using the existing proof-use path.

This theorem is still relative to the lower carrier geometry and face-law
sources; it does not claim those sources are generated by bare
site/sheaf/descent input.
-/
theorem grounded_package_of_selectedCarrierGeometry_and_faceLaws
    (geometry :
      SemanticRepairSelectedCarrierGeometry additive coverBridge K)
    (faceLaws :
      SemanticRepairSelectedCechFaceLawSource additive geometry) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        (of_selectedCarrierGeometry_and_faceLaws
          geometry faceLaws).toCochainRealization.toH1Comparison) :=
  (of_selectedCarrierGeometry_and_faceLaws
    geometry faceLaws).grounded_package_of_carrier_specific_comparison_provenance

/--
Concrete carrier-only model data reaches the selected cover-relative grounding
package once the separate selected Cech face-law source is supplied for the
constructed carrier geometry.

This is the proof-use theorem for Cycle 26.  The model is consumed to construct
`SemanticRepairSelectedCarrierGeometry`; the face laws are then consumed by the
Cycle 25 carrier-specific provenance constructor.  The result remains relative
to the selected face-law premise and does not claim bare cover/sheaf/descent
data generates those laws.
-/
theorem grounded_package_of_selectedSectionFamilyCarrierModel_and_selectedCechFaceLaws
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K)
    (faceLaws :
      SemanticRepairSelectedCechFaceLawSource
        additive
        (SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
          model)) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        (of_selectedCarrierGeometry_and_faceLaws
          (SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
            model)
          faceLaws).toCochainRealization.toH1Comparison) :=
  grounded_package_of_selectedCarrierGeometry_and_faceLaws
    (SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
      model)
    faceLaws

/--
Carrier-only model data plus actual face-restriction compatibility reach the
selected cover-relative grounding package through the Cycle 25 selected
carrier-geometry / selected face-law-source path.

This is the Cycle 27 proof-use theorem.  The carrier model constructs the
selected carrier geometry; the compatibility witness constructs the selected
Cech face-law source for that geometry; those two lower sources are consumed by
`of_selectedCarrierGeometry_and_faceLaws`.  The theorem remains relative to the
explicit face-restriction compatibility witness and does not claim that bare
cover membership, sheaf condition, descent, or full sheaf cohomology produces
the selected laws.
-/
theorem grounded_package_of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility_via_selectedCechFaceLaws
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K)
    (compatibility :
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        additive
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        (of_selectedCarrierGeometry_and_faceLaws
          (SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
            model)
          (SemanticRepairSelectedCechFaceLawSource.of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
            model compatibility)).toCochainRealization.toH1Comparison) :=
  grounded_package_of_selectedSectionFamilyCarrierModel_and_selectedCechFaceLaws
    model
    (SemanticRepairSelectedCechFaceLawSource.of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
      model compatibility)

/--
Carrier-only model data plus direct selected differential laws reach the
selected cover-relative grounding package through the selected carrier-geometry
/ selected Cech face-law-source path.

This is the Cycle 28 proof-use theorem.  The direct laws are first normalized
to the selected presheaf face-restriction presentation, producing the selected
Cech face-law source for the model-built carrier geometry; that source is then
consumed by `of_selectedCarrierGeometry_and_faceLaws`.  The theorem remains
relative to direct selected differential compatibility and does not claim that
bare cover membership, sheaf condition, descent, or full sheaf cohomology
produces those direct laws.
-/
theorem grounded_package_of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility_via_selectedCechFaceLaws
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K)
    (direct :
      SemanticRepairCoverRelativeDirectDifferentialCompatibility
        additive
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        (of_selectedCarrierGeometry_and_faceLaws
          (SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
            model)
          (SemanticRepairSelectedCechFaceLawSource.of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
            model direct)).toCochainRealization.toH1Comparison) :=
  grounded_package_of_selectedSectionFamilyCarrierModel_and_selectedCechFaceLaws
    model
    (SemanticRepairSelectedCechFaceLawSource.of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
      model direct)

/--
Carrier-specific provenance constructs the richer section-realization bridge by
first forming the face-restriction realization and then deriving direct `K.d`
compatibility from the general Cech face formula.

This is still lower selected comparison provenance: it contains carrier maps,
inverse/additivity laws, degree-`2` zero laws, and selected differential laws,
but no `H1` zero, boundary membership, global coherence, effective descent,
refinement naturality, or full sheaf cohomology comparison.
-/
def toSectionRealizationBridge
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    SemanticRepairCoverRelativeSectionRealizationBridge additive coverBridge K :=
  provenance.toFaceRestrictionRealization.toSectionRealizationBridge

/--
Carrier-specific provenance is a concrete source for the richer
section-realization bridge used in Cycle 23.
-/
theorem carrierSpecificComparisonProvenance_constructs_sectionRealizationBridge
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    Nonempty
      (SemanticRepairCoverRelativeSectionRealizationBridge
        additive coverBridge K) :=
  ⟨provenance.toSectionRealizationBridge⟩

/--
The richer section-realization bridge and the lower carrier-specific
provenance determine each other as selected comparison sources.

The forward direction extracts carrier-specific provenance through the
cochain-realization layer.  The backward direction constructs the bridge from
carrier maps and selected face-restriction laws.  This theorem moves the
remaining bridge source down to explicit lower selected carrier / differential
provenance; it does not classify that provenance as ambient boundary.
-/
theorem sectionRealizationBridge_iff_carrierSpecificComparisonProvenance :
    Nonempty
        (SemanticRepairCoverRelativeSectionRealizationBridge
          additive coverBridge K) <->
      Nonempty
        (SemanticRepairCarrierSpecificComparisonProvenance
          additive coverBridge K) := by
  constructor
  · intro hbridge
    rcases hbridge with ⟨bridge⟩
    exact ⟨bridge.toCochainRealization.toCarrierSpecificComparisonProvenance⟩
  · intro hprovenance
    rcases hprovenance with ⟨provenance⟩
    exact provenance.carrierSpecificComparisonProvenance_constructs_sectionRealizationBridge

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

/--
Cycle 19 lower-construction theorem: separated finite section-family witness
data plus selected face-restriction differential equations construct the
cochain-realization premise required by the G-06 cover-relative `H1`
grounding path.

This theorem does not construct the section-family witness from bare cover
membership or sheaf descent.  It fixes the exact lower witness shape that must
be supplied or proved next, and then derives direct `K.d` compatibility through
the existing face-restriction realization bridge.
-/
def of_sectionFamilyWitness_and_faceRestrictionCompatibility
    (sectionWitness :
      SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K)
    (compatibility :
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        additive sectionWitness) :
    SemanticRepairCoverRelativeCochainRealization additive K :=
  (SemanticRepairCoverRelativeFaceRestrictionRealization.of_sectionFamilyWitness
      sectionWitness compatibility).toCochainRealization

/--
The remaining cochain-realization premise is equivalent to supplying the lower
finite section-family witness together with the four selected face-restriction
equations.

The forward direction exposes the lower witness through the constructed
carrier-specific provenance path; the backward direction builds the
cochain-realization layer by theorem.  No `H1` equivalence, zero-class result,
global coherence, effective descent, refinement naturality, or full sheaf
cohomology comparison is stored in the lower witness.
-/
theorem cochainRealization_iff_sectionFamilyWitness_and_faceRestrictionCompatibility :
    Nonempty (SemanticRepairCoverRelativeCochainRealization additive K) <->
      Exists fun sectionWitness :
        SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K =>
          SemanticRepairCoverRelativeFaceRestrictionCompatibility
            additive sectionWitness := by
  constructor
  · intro hrealization
    rcases hrealization with ⟨realization⟩
    exact
      realization.toCarrierSpecificComparisonProvenance
        |>.constructs_sectionFamilyWitness_and_faceRestrictionCompatibility
  · intro hwitness
    rcases hwitness with ⟨sectionWitness, compatibility⟩
    exact
      ⟨of_sectionFamilyWitness_and_faceRestrictionCompatibility
        sectionWitness compatibility⟩

/--
Lower finite witness data reaches the selected cover-relative grounding package
by first constructing `SemanticRepairCoverRelativeCochainRealization` and then
using the existing quotient-level comparison theorem.

This keeps the proof-use path explicit:
section-family witness and face equations are consumed to build cochain
realization; cochain realization is consumed to build the `H1` comparison
package.
-/
theorem grounded_package_of_sectionFamilyWitness_and_faceRestrictionCompatibility
    (sectionWitness :
      SemanticRepairCoverRelativeSectionFamilyWitness additive coverBridge K)
    (compatibility :
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        additive sectionWitness) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        (of_sectionFamilyWitness_and_faceRestrictionCompatibility
          sectionWitness compatibility).toH1Comparison) :=
  (of_sectionFamilyWitness_and_faceRestrictionCompatibility
    sectionWitness compatibility).grounded_package_of_cochain_realization

/--
Cycle 32 lower-construction theorem: carrier-only selected section-family data
plus direct selected differential compatibility construct the cochain
realization source required by the G-06 cover-relative `H1` grounding path.

This theorem lowers the Cycle 31 source one step: it does not take an existing
`SemanticRepairCoverRelativeCochainRealization` as input.  The carrier model
builds the selected section-family witness, and the direct `K.d` compatibility
is normalized to face-restriction compatibility through the existing
`K.d_eq_alternatingFaceCombination` path.  It still remains relative to the two
lower material sources and does not claim that bare site/sheaf/descent data
constructs them.
-/
def of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K)
    (direct :
      SemanticRepairCoverRelativeDirectDifferentialCompatibility
        additive
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    SemanticRepairCoverRelativeCochainRealization additive K :=
  of_sectionFamilyWitness_and_faceRestrictionCompatibility
    (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
      model)
    direct.toFaceRestrictionCompatibility

/--
The cochain-realization premise is supplied by exactly the separated lower
carrier model plus direct selected differential compatibility.

The forward direction exposes those lower sources through existing provenance
projections; the backward direction constructs the cochain realization by the
Cycle 32 constructor.  No `H1` zero, boundary membership, global coherence,
effective descent, refinement naturality, or full sheaf cohomology comparison is
introduced as a field or hidden certificate.
-/
theorem cochainRealization_iff_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility :
    Nonempty (SemanticRepairCoverRelativeCochainRealization additive K) <->
      Exists fun model : SelectedSectionFamilyCarrierModel additive coverBridge K =>
        SemanticRepairCoverRelativeDirectDifferentialCompatibility
          additive
            (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
              model) := by
  constructor
  · intro hrealization
    rcases hrealization with ⟨realization⟩
    let provenance := realization.toCarrierSpecificComparisonProvenance
    let bridge := provenance.toSectionRealizationBridge
    exact
      ⟨bridge.toSelectedSectionFamilyCarrierModel,
        bridge.toDirectDifferentialCompatibilityForSelectedCarrierModel⟩
  · intro hsource
    rcases hsource with ⟨model, direct⟩
    exact
      ⟨of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
        model direct⟩

/--
Transparent lower-data predicate for Cycle 42.

This is only an abbreviation for the explicit finite carrier witness data,
degree-`2` zero laws, and the four selected face-restriction equations.  It is
not a certificate structure and it stores no `H1` zero, boundary membership,
global coherence, effective descent, refinement naturality, or full sheaf
cohomology comparison.
-/
abbrev DegreewiseCarrierDataAndExplicitFaceRestrictionEquations : Prop :=
      Exists fun c0Carrier :
        letI := additive.c0AddCommGroup
        letI := K.cochainAddCommGroup 0
        CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0) =>
      Exists fun c1Carrier :
        letI := additive.c1AddCommGroup
        letI := K.cochainAddCommGroup 1
        CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1) =>
      Exists fun c2Equiv : E.coefficient.C2 ≃ K.Cn 2 =>
      Exists fun c2Equiv_zero :
        letI := K.cochainAddCommGroup 2
        c2Equiv E.coefficient.zero2 = 0 =>
      Exists fun c2Equiv_symm_zero :
        letI := K.cochainAddCommGroup 2
        c2Equiv.symm 0 = E.coefficient.zero2 =>
        (let model :=
          SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
            (additive := additive) (coverBridge := coverBridge) (K := K)
            c0Carrier c1Carrier c2Equiv
            c2Equiv_zero c2Equiv_symm_zero
         let sectionWitness :=
          SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model
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
                  (fun σ i => K.faceRestrictionTerm 1 i cochain σ))))

/--
The cochain-realization source is equivalent to the explicit lower data exposed
in Cycle 41.

Forward, a cochain realization is first converted to carrier-specific
provenance and then unfolded to finite carrier data plus the four selected
face-restriction equations.  Backward, the explicit lower data constructs
carrier-specific provenance, which constructs a cochain realization.  This
theorem does not generate the lower data from bare cover membership, sheaf
condition, descent, or full sheaf cohomology.
-/
theorem cochainRealization_iff_degreewiseCarrierData_and_explicitFaceRestrictionEquations :
    Nonempty (SemanticRepairCoverRelativeCochainRealization additive K) <->
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
        (additive := additive) (coverBridge := coverBridge) (K := K) := by
  constructor
  · intro hrealization
    rcases hrealization with ⟨realization⟩
    exact
      (SemanticRepairCarrierSpecificComparisonProvenance.carrierSpecificComparisonProvenance_iff_degreewiseCarrierData_and_explicitFaceRestrictionEquations
        (additive := additive) (coverBridge := coverBridge) (K := K)).1
        ⟨realization.toCarrierSpecificComparisonProvenance⟩
  · intro hlower
    rcases
      (SemanticRepairCarrierSpecificComparisonProvenance.carrierSpecificComparisonProvenance_iff_degreewiseCarrierData_and_explicitFaceRestrictionEquations
        (additive := additive) (coverBridge := coverBridge) (K := K)).2
        hlower with
      ⟨provenance⟩
    exact ⟨provenance.toCochainRealization⟩

/--
A cochain realization constructs carrier-specific provenance through the
explicit lower data exposed in Cycle 41.

The result keeps both pieces visible: the extracted lower data and the
provenance reconstructed from it.  The lower data remains the material source;
this theorem is not a bare site/sheaf/descent discharge.
-/
theorem constructs_carrierSpecificComparisonProvenance_via_explicitLowerData
    (realization : SemanticRepairCoverRelativeCochainRealization additive K) :
    DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
        (additive := additive) (coverBridge := coverBridge) (K := K) /\
      Nonempty
        (SemanticRepairCarrierSpecificComparisonProvenance
          additive coverBridge K) := by
  have hlower :
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
        (additive := additive) (coverBridge := coverBridge) (K := K) :=
    (cochainRealization_iff_degreewiseCarrierData_and_explicitFaceRestrictionEquations
      (additive := additive) (coverBridge := coverBridge) (K := K)).1
      ⟨realization⟩
  exact
    ⟨hlower,
      (SemanticRepairCarrierSpecificComparisonProvenance.carrierSpecificComparisonProvenance_iff_degreewiseCarrierData_and_explicitFaceRestrictionEquations
        (additive := additive) (coverBridge := coverBridge) (K := K)).2
        hlower⟩

/--
Cycle 43 checkpoint theorem: the current G-06 site/sheaf/presheaf surface
reaches the general restriction and selected Cech differential laws, and the
remaining selected cochain-realization premise is exactly the explicit lower
carrier data plus four face-restriction equations exposed in Cycle 42.

This theorem intentionally does not construct that lower data from
`CurrentG06InputSurface`.  It proof-uses the available current-surface laws and
then records the precise remaining equivalence, while keeping the no-uniform
carrier/equivalence blockers visible.
-/
theorem currentG06InputSurface_reduces_cochainRealization_to_explicitLowerData
    (surface :
      SemanticRepairCarrierSpecificComparisonProvenance.CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob)) :
    (∀ {source target : S.category} (f : source ⟶ target),
      letI := Ob.addCommGroup target
      letI := Ob.addCommGroup source
      Ob.carrier.toPresheaf.map f.op 0 = 0) /\
      (∀ {source target : S.category} (f : source ⟶ target)
          (x y : Ob.carrier.toPresheaf.obj (op target)),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op (x + y) =
          Ob.carrier.toPresheaf.map f.op x +
            Ob.carrier.toPresheaf.map f.op y) /\
      (∀ (n : Nat) (c : surface.K.Cn n),
        surface.K.d n c =
          surface.K.alternatingFaceCombination n
            (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
      (Nonempty (SemanticRepairCoverRelativeCochainRealization additive surface.K) <->
        DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
          (additive := additive) (coverBridge := surface.coverBridge)
          (K := surface.K)) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          CarrierSpecificAdditiveComparisonData C D) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          C ≃+ D) := by
  have hsurface :
      (∀ {source target : S.category} (f : source ⟶ target),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op 0 = 0) /\
        (∀ {source target : S.category} (f : source ⟶ target)
            (x y : Ob.carrier.toPresheaf.obj (op target)),
          letI := Ob.addCommGroup target
          letI := Ob.addCommGroup source
          Ob.carrier.toPresheaf.map f.op (x + y) =
            Ob.carrier.toPresheaf.map f.op x +
              Ob.carrier.toPresheaf.map f.op y) /\
        (∀ (n : Nat) (c : surface.K.Cn n),
          surface.K.d n c =
            surface.K.alternatingFaceCombination n
              (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            CarrierSpecificAdditiveComparisonData C D) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            C ≃+ D) :=
    SemanticRepairCarrierSpecificComparisonProvenance.current_g06_presheaf_laws_stop_before_selected_differential_source
      (surface := surface)
  exact
    ⟨hsurface.1,
      hsurface.2.1,
      hsurface.2.2.1,
      cochainRealization_iff_degreewiseCarrierData_and_explicitFaceRestrictionEquations
        (additive := additive) (coverBridge := surface.coverBridge)
        (K := surface.K),
      hsurface.2.2.2.1,
      hsurface.2.2.2.2⟩

/--
Cycle 44 checkpoint theorem: for the current G-06 input surface, the selected
cochain-realization source is equivalent to the existing separated lower
source of selected carrier geometry plus selected Cech face laws.

This theorem does not construct either lower source from
`CurrentG06InputSurface`.  It specializes the provenance equivalence to
`surface.coverBridge` and `surface.K`, and keeps the no-uniform
carrier/equivalence blockers visible so the lower source remains
`discharge-required`.
-/
theorem currentG06InputSurface_cochainRealization_iff_selectedCarrierGeometry_and_faceLawSource
    (surface :
      SemanticRepairCarrierSpecificComparisonProvenance.CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob)) :
    (Nonempty (SemanticRepairCoverRelativeCochainRealization additive surface.K) <->
      Exists fun geometry :
        SemanticRepairSelectedCarrierGeometry additive surface.coverBridge surface.K =>
          SemanticRepairSelectedCechFaceLawSource additive geometry) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          CarrierSpecificAdditiveComparisonData C D) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          C ≃+ D) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hrealization
      rcases hrealization with ⟨realization⟩
      exact
        (SemanticRepairCarrierSpecificComparisonProvenance.carrierSpecificComparisonProvenance_iff_selectedCarrierGeometry_and_faceLaws
          (additive := additive) (coverBridge := surface.coverBridge)
          (K := surface.K)).1
          ⟨realization.toCarrierSpecificComparisonProvenance⟩
    · intro hlower
      rcases
        (SemanticRepairCarrierSpecificComparisonProvenance.carrierSpecificComparisonProvenance_iff_selectedCarrierGeometry_and_faceLaws
          (additive := additive) (coverBridge := surface.coverBridge)
          (K := surface.K)).2
          hlower with
        ⟨provenance⟩
      exact ⟨provenance.toCochainRealization⟩
  · exact no_uniform_carrier_specific_additive_comparison_from_bare_groups
  · exact
      SemanticRepairCoverRelativeFaceRestrictionRealization.no_uniform_additive_carrier_equivalence_from_bare_lower_data

/--
Cycle 45 boundary theorem: the Cycle 44 lower pair for the current G-06
surface necessarily exposes the explicit carrier-comparison source and the
four selected face-restriction equations.

The current surface is proof-used only for the general presheaf restriction
laws and the selected Cech differential formula.  The selected carrier
geometry and selected Cech face-law source are separate material inputs whose
contents are projected here; this theorem does not construct them from cover
membership, `AATSheafCondition`, `AATDescent`, or presheaf zero/add laws.
-/
theorem currentG06InputSurface_selectedCarrierGeometry_and_faceLawSource_requires_explicit_lower_sources
    (surface :
      SemanticRepairCarrierSpecificComparisonProvenance.CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob))
    (geometry :
      SemanticRepairSelectedCarrierGeometry additive surface.coverBridge surface.K)
    (faceLaws :
      SemanticRepairSelectedCechFaceLawSource additive geometry) :
    (∀ {source target : S.category} (f : source ⟶ target),
      letI := Ob.addCommGroup target
      letI := Ob.addCommGroup source
      Ob.carrier.toPresheaf.map f.op 0 = 0) /\
      (∀ {source target : S.category} (f : source ⟶ target)
          (x y : Ob.carrier.toPresheaf.obj (op target)),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op (x + y) =
          Ob.carrier.toPresheaf.map f.op x +
            Ob.carrier.toPresheaf.map f.op y) /\
      (∀ (n : Nat) (c : surface.K.Cn n),
        surface.K.d n c =
          surface.K.alternatingFaceCombination n
            (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
      ((Nonempty
          (letI := additive.c0AddCommGroup
           letI := surface.K.cochainAddCommGroup 0
           CarrierSpecificAdditiveComparisonData
            E.coefficient.C0 (surface.K.Cn 0)) /\
        Nonempty
          (letI := additive.c1AddCommGroup
           letI := surface.K.cochainAddCommGroup 1
           CarrierSpecificAdditiveComparisonData
            E.coefficient.C1 (surface.K.Cn 1)) /\
        Exists fun c2Equiv : E.coefficient.C2 ≃ surface.K.Cn 2 =>
          (letI := surface.K.cochainAddCommGroup 2
           c2Equiv E.coefficient.zero2 = 0) /\
            (letI := surface.K.cochainAddCommGroup 2
             c2Equiv.symm 0 = E.coefficient.zero2)) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            CarrierSpecificAdditiveComparisonData C D)) /\
      ((letI := additive.c0AddCommGroup
        letI := additive.c1AddCommGroup
        letI := surface.K.cochainAddCommGroup 0
        letI := surface.K.cochainAddCommGroup 1
        forall primitive : E.coefficient.C0,
          surface.K.alternatingFaceCombination 0
              (fun σ i =>
                surface.K.faceRestrictionTerm 0 i
                  (geometry.c0Carrier.toCarrier primitive) σ) =
            geometry.c1Carrier.toCarrier (E.coefficient.delta0 primitive)) /\
        (letI := additive.c0AddCommGroup
         letI := additive.c1AddCommGroup
         letI := surface.K.cochainAddCommGroup 0
         letI := surface.K.cochainAddCommGroup 1
         forall primitive : surface.K.Cn 0,
          E.coefficient.delta0 (geometry.c0Carrier.fromCarrier primitive) =
            geometry.c1Carrier.fromCarrier
              (surface.K.alternatingFaceCombination 0
                (fun σ i => surface.K.faceRestrictionTerm 0 i primitive σ))) /\
        (letI := additive.c1AddCommGroup
         letI := surface.K.cochainAddCommGroup 1
         forall cochain : E.coefficient.C1,
          surface.K.alternatingFaceCombination 1
              (fun σ i =>
                surface.K.faceRestrictionTerm 1 i
                  (geometry.c1Carrier.toCarrier cochain) σ) =
            geometry.c2Equiv (E.coefficient.delta1 cochain)) /\
        (letI := additive.c1AddCommGroup
         letI := surface.K.cochainAddCommGroup 1
         forall cochain : surface.K.Cn 1,
          E.coefficient.delta1 (geometry.c1Carrier.fromCarrier cochain) =
            geometry.c2Equiv.symm
              (surface.K.alternatingFaceCombination 1
                (fun σ i => surface.K.faceRestrictionTerm 1 i cochain σ)))) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          C ≃+ D) := by
  have hsurface :
      (∀ {source target : S.category} (f : source ⟶ target),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op 0 = 0) /\
        (∀ {source target : S.category} (f : source ⟶ target)
            (x y : Ob.carrier.toPresheaf.obj (op target)),
          letI := Ob.addCommGroup target
          letI := Ob.addCommGroup source
          Ob.carrier.toPresheaf.map f.op (x + y) =
            Ob.carrier.toPresheaf.map f.op x +
              Ob.carrier.toPresheaf.map f.op y) /\
        (∀ (n : Nat) (c : surface.K.Cn n),
          surface.K.d n c =
            surface.K.alternatingFaceCombination n
              (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            CarrierSpecificAdditiveComparisonData C D) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            C ≃+ D) :=
    SemanticRepairCarrierSpecificComparisonProvenance.current_g06_presheaf_laws_stop_before_selected_differential_source
      (surface := surface)
  have hcarrier :
      (Nonempty
          (letI := additive.c0AddCommGroup
           letI := surface.K.cochainAddCommGroup 0
           CarrierSpecificAdditiveComparisonData
            E.coefficient.C0 (surface.K.Cn 0)) /\
        Nonempty
          (letI := additive.c1AddCommGroup
           letI := surface.K.cochainAddCommGroup 1
           CarrierSpecificAdditiveComparisonData
            E.coefficient.C1 (surface.K.Cn 1)) /\
        Exists fun c2Equiv : E.coefficient.C2 ≃ surface.K.Cn 2 =>
          (letI := surface.K.cochainAddCommGroup 2
           c2Equiv E.coefficient.zero2 = 0) /\
            (letI := surface.K.cochainAddCommGroup 2
             c2Equiv.symm 0 = E.coefficient.zero2)) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            CarrierSpecificAdditiveComparisonData C D) :=
    SemanticRepairSelectedCarrierGeometry.requires_explicit_selected_carrier_source
      (geometry := geometry)
  have hface :
      (letI := additive.c0AddCommGroup
       letI := additive.c1AddCommGroup
       letI := surface.K.cochainAddCommGroup 0
       letI := surface.K.cochainAddCommGroup 1
       forall primitive : E.coefficient.C0,
        surface.K.alternatingFaceCombination 0
            (fun σ i =>
              surface.K.faceRestrictionTerm 0 i
                (geometry.c0Carrier.toCarrier primitive) σ) =
          geometry.c1Carrier.toCarrier (E.coefficient.delta0 primitive)) /\
        (letI := additive.c0AddCommGroup
         letI := additive.c1AddCommGroup
         letI := surface.K.cochainAddCommGroup 0
         letI := surface.K.cochainAddCommGroup 1
         forall primitive : surface.K.Cn 0,
          E.coefficient.delta0 (geometry.c0Carrier.fromCarrier primitive) =
            geometry.c1Carrier.fromCarrier
              (surface.K.alternatingFaceCombination 0
                (fun σ i => surface.K.faceRestrictionTerm 0 i primitive σ))) /\
        (letI := additive.c1AddCommGroup
         letI := surface.K.cochainAddCommGroup 1
         forall cochain : E.coefficient.C1,
          surface.K.alternatingFaceCombination 1
              (fun σ i =>
                surface.K.faceRestrictionTerm 1 i
                  (geometry.c1Carrier.toCarrier cochain) σ) =
            geometry.c2Equiv (E.coefficient.delta1 cochain)) /\
        (letI := additive.c1AddCommGroup
         letI := surface.K.cochainAddCommGroup 1
         forall cochain : surface.K.Cn 1,
          E.coefficient.delta1 (geometry.c1Carrier.fromCarrier cochain) =
            geometry.c2Equiv.symm
              (surface.K.alternatingFaceCombination 1
                (fun σ i => surface.K.faceRestrictionTerm 1 i cochain σ))) :=
    SemanticRepairSelectedCechFaceLawSource.requires_explicit_selected_face_restriction_equations
      (faceLaws := faceLaws)
  exact
    ⟨hsurface.1,
      hsurface.2.1,
      hsurface.2.2.1,
      hcarrier,
      hface,
      hsurface.2.2.2.2⟩

/--
Cycle 46 finite-witness construction theorem: for the current G-06 input
surface, an explicit finite lower witness constructs the selected carrier
geometry and selected Cech face-law source required by Cycle 44/45.

The current surface is proof-used for the presheaf zero/add laws and selected
Cech differential formula.  The explicit finite witness is proof-used by
decomposing it into the degree-wise carrier data, degree-`2` zero laws, and
four face-restriction equations, then constructing the carrier model,
face-restriction compatibility, selected carrier geometry, and selected Cech
face-law source in sequence.  This theorem does not claim that
`CurrentG06InputSurface` alone produces that finite witness.
-/
theorem currentG06InputSurface_explicitFiniteWitness_constructs_selectedCarrierGeometry_and_faceLawSource
    (surface :
      SemanticRepairCarrierSpecificComparisonProvenance.CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob))
    (lower :
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
        (additive := additive) (coverBridge := surface.coverBridge)
        (K := surface.K)) :
    (∀ {source target : S.category} (f : source ⟶ target),
      letI := Ob.addCommGroup target
      letI := Ob.addCommGroup source
      Ob.carrier.toPresheaf.map f.op 0 = 0) /\
      (∀ {source target : S.category} (f : source ⟶ target)
          (x y : Ob.carrier.toPresheaf.obj (op target)),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op (x + y) =
          Ob.carrier.toPresheaf.map f.op x +
            Ob.carrier.toPresheaf.map f.op y) /\
      (∀ (n : Nat) (c : surface.K.Cn n),
        surface.K.d n c =
          surface.K.alternatingFaceCombination n
            (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
      Exists fun geometry :
        SemanticRepairSelectedCarrierGeometry additive surface.coverBridge surface.K =>
          SemanticRepairSelectedCechFaceLawSource additive geometry := by
  have hsurface :
      (∀ {source target : S.category} (f : source ⟶ target),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op 0 = 0) /\
        (∀ {source target : S.category} (f : source ⟶ target)
            (x y : Ob.carrier.toPresheaf.obj (op target)),
          letI := Ob.addCommGroup target
          letI := Ob.addCommGroup source
          Ob.carrier.toPresheaf.map f.op (x + y) =
            Ob.carrier.toPresheaf.map f.op x +
              Ob.carrier.toPresheaf.map f.op y) /\
        (∀ (n : Nat) (c : surface.K.Cn n),
          surface.K.d n c =
            surface.K.alternatingFaceCombination n
              (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            CarrierSpecificAdditiveComparisonData C D) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            C ≃+ D) :=
    SemanticRepairCarrierSpecificComparisonProvenance.current_g06_presheaf_laws_stop_before_selected_differential_source
      (surface := surface)
  rcases lower with
    ⟨c0Carrier, c1Carrier, c2Equiv,
      c2Equiv_zero, c2Equiv_symm_zero,
      d0_face_to, d0_face_from, d1_face_to, d1_face_from⟩
  let model :
      SelectedSectionFamilyCarrierModel additive surface.coverBridge surface.K :=
    SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
      (additive := additive) (coverBridge := surface.coverBridge)
      (K := surface.K)
      c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
  let sectionWitness :
      SemanticRepairCoverRelativeSectionFamilyWitness
        additive surface.coverBridge surface.K :=
    SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
      model
  let compatibility :
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        additive sectionWitness :=
    SemanticRepairCoverRelativeFaceRestrictionCompatibility.of_explicit_face_restriction_equations
      (additive := additive) (sectionWitness := sectionWitness)
      d0_face_to d0_face_from d1_face_to d1_face_from
  let geometry :
      SemanticRepairSelectedCarrierGeometry
        additive surface.coverBridge surface.K :=
    SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
      model
  let faceLaws :
      SemanticRepairSelectedCechFaceLawSource additive geometry :=
    SemanticRepairSelectedCechFaceLawSource.of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
      model compatibility
  exact
    ⟨hsurface.1,
      hsurface.2.1,
      hsurface.2.2.1,
      ⟨geometry, faceLaws⟩⟩

/--
Cycle 47 blocker theorem: the explicit finite witness required after Cycle 46
is not a surface-only product.

Given the current G-06 input surface and an explicit finite lower witness, the
theorem proof-uses both sides and returns the concrete lower sources that the
witness contains: degree-wise carrier data, degree-`2` zero laws, and the four
selected face-restriction equations.  The current surface contributes only the
presheaf restriction laws and selected Cech differential formula, together with
the existing no-uniform constructor boundaries.  This theorem deliberately does
not construct the finite witness from `CurrentG06InputSurface`, and it does not
identify cover-relative `H1` with full sheaf cohomology.
-/
theorem currentG06InputSurface_explicitFiniteWitness_requires_concrete_lower_sources
    (surface :
      SemanticRepairCarrierSpecificComparisonProvenance.CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob))
    (lower :
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
        (additive := additive) (coverBridge := surface.coverBridge)
        (K := surface.K)) :
    (∀ {source target : S.category} (f : source ⟶ target),
      letI := Ob.addCommGroup target
      letI := Ob.addCommGroup source
      Ob.carrier.toPresheaf.map f.op 0 = 0) /\
      (∀ {source target : S.category} (f : source ⟶ target)
          (x y : Ob.carrier.toPresheaf.obj (op target)),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op (x + y) =
          Ob.carrier.toPresheaf.map f.op x +
            Ob.carrier.toPresheaf.map f.op y) /\
      (∀ (n : Nat) (c : surface.K.Cn n),
        surface.K.d n c =
          surface.K.alternatingFaceCombination n
            (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
      (Exists fun c0Carrier :
        letI := additive.c0AddCommGroup
        letI := surface.K.cochainAddCommGroup 0
        CarrierSpecificAdditiveComparisonData E.coefficient.C0 (surface.K.Cn 0) =>
      Exists fun c1Carrier :
        letI := additive.c1AddCommGroup
        letI := surface.K.cochainAddCommGroup 1
        CarrierSpecificAdditiveComparisonData E.coefficient.C1 (surface.K.Cn 1) =>
      Exists fun c2Equiv : E.coefficient.C2 ≃ surface.K.Cn 2 =>
      Exists fun c2Equiv_zero :
        letI := surface.K.cochainAddCommGroup 2
        c2Equiv E.coefficient.zero2 = 0 =>
      Exists fun c2Equiv_symm_zero :
        letI := surface.K.cochainAddCommGroup 2
        c2Equiv.symm 0 = E.coefficient.zero2 =>
        let model :=
          SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
            (additive := additive) (coverBridge := surface.coverBridge)
            (K := surface.K)
            c0Carrier c1Carrier c2Equiv
            c2Equiv_zero c2Equiv_symm_zero
        let sectionWitness :=
          SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model
        (letI := additive.c0AddCommGroup
         letI := additive.c1AddCommGroup
         letI := surface.K.cochainAddCommGroup 0
         letI := surface.K.cochainAddCommGroup 1
         forall primitive : E.coefficient.C0,
           surface.K.alternatingFaceCombination 0
               (fun σ i =>
                 surface.K.faceRestrictionTerm 0 i
                   (sectionWitness.c0SectionEquiv primitive) σ) =
             sectionWitness.c1SectionEquiv (E.coefficient.delta0 primitive)) /\
        (letI := additive.c0AddCommGroup
         letI := additive.c1AddCommGroup
         letI := surface.K.cochainAddCommGroup 0
         letI := surface.K.cochainAddCommGroup 1
         forall primitive : surface.K.Cn 0,
           E.coefficient.delta0 (sectionWitness.c0SectionEquiv.symm primitive) =
             sectionWitness.c1SectionEquiv.symm
               (surface.K.alternatingFaceCombination 0
                 (fun σ i => surface.K.faceRestrictionTerm 0 i primitive σ))) /\
        (letI := additive.c1AddCommGroup
         letI := surface.K.cochainAddCommGroup 1
         forall cochain : E.coefficient.C1,
           surface.K.alternatingFaceCombination 1
               (fun σ i =>
                 surface.K.faceRestrictionTerm 1 i
                   (sectionWitness.c1SectionEquiv cochain) σ) =
             sectionWitness.c2SectionEquiv (E.coefficient.delta1 cochain)) /\
        (letI := additive.c1AddCommGroup
         letI := surface.K.cochainAddCommGroup 1
         forall cochain : surface.K.Cn 1,
           E.coefficient.delta1 (sectionWitness.c1SectionEquiv.symm cochain) =
             sectionWitness.c2SectionEquiv.symm
               (surface.K.alternatingFaceCombination 1
                 (fun σ i => surface.K.faceRestrictionTerm 1 i cochain σ)))) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          CarrierSpecificAdditiveComparisonData C D) /\
      IsEmpty
        ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
          C ≃+ D) := by
  have hsurface :
      (∀ {source target : S.category} (f : source ⟶ target),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op 0 = 0) /\
        (∀ {source target : S.category} (f : source ⟶ target)
            (x y : Ob.carrier.toPresheaf.obj (op target)),
          letI := Ob.addCommGroup target
          letI := Ob.addCommGroup source
          Ob.carrier.toPresheaf.map f.op (x + y) =
            Ob.carrier.toPresheaf.map f.op x +
              Ob.carrier.toPresheaf.map f.op y) /\
        (∀ (n : Nat) (c : surface.K.Cn n),
          surface.K.d n c =
            surface.K.alternatingFaceCombination n
              (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            CarrierSpecificAdditiveComparisonData C D) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            C ≃+ D) :=
    SemanticRepairCarrierSpecificComparisonProvenance.current_g06_presheaf_laws_stop_before_selected_differential_source
      (surface := surface)
  rcases lower with
    ⟨c0Carrier, c1Carrier, c2Equiv,
      c2Equiv_zero, c2Equiv_symm_zero,
      d0_face_to, d0_face_from, d1_face_to, d1_face_from⟩
  exact
    ⟨hsurface.1,
      hsurface.2.1,
      hsurface.2.2.1,
      ⟨c0Carrier, c1Carrier, c2Equiv,
        c2Equiv_zero, c2Equiv_symm_zero,
        d0_face_to, d0_face_from, d1_face_to, d1_face_from⟩,
      hsurface.2.2.2.1,
      hsurface.2.2.2.2⟩

/--
Cycle 48 blocker theorem: a surface-only constructor for the whole explicit
finite witness cannot be unconditional over the current G-06 input surface.

The explicit finite witness contains degree-`0` carrier-specific comparison
data.  Therefore, on any test surface whose semantic degree-`0` carrier is
additively equivalent to `PUnit` while the selected cover-relative degree-`0`
carrier is additively equivalent to `ZMod 2`, such a constructor would produce
an additive equivalence `PUnit ≃+ ZMod 2`, forcing `0 = 1`.

This is a blocker for the current-surface-only route to
`DegreewiseCarrierDataAndExplicitFaceRestrictionEquations`; it does not
construct the finite witness, and it does not reclassify the witness as
ambient boundary.
-/
theorem no_constructor_from_currentG06InputSurface_without_degreewiseCarrierData_and_explicitFaceRestrictionEquations
    (surface :
      SemanticRepairCarrierSpecificComparisonProvenance.CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob))
    (c0SourceEquiv :
      letI := additive.c0AddCommGroup
      E.coefficient.C0 ≃+ PUnit)
    (c0TargetEquiv :
      letI := surface.K.cochainAddCommGroup 0
      surface.K.Cn 0 ≃+ ZMod 2)
    (currentInputFiniteWitnessConstructor :
      (surface :
        SemanticRepairCarrierSpecificComparisonProvenance.CurrentG06InputSurface
          (semanticCover := semanticCover) (S := S) (Ob := Ob)) ->
        DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
          (additive := additive) (coverBridge := surface.coverBridge)
          (K := surface.K)) :
    False := by
  letI := additive.c0AddCommGroup
  letI := surface.K.cochainAddCommGroup 0
  rcases currentInputFiniteWitnessConstructor surface with
    ⟨c0Carrier, _c1Carrier, _c2Equiv,
      _c2Equiv_zero, _c2Equiv_symm_zero,
      _d0_face_to, _d0_face_from, _d1_face_to, _d1_face_from⟩
  let eSemanticToCech : E.coefficient.C0 ≃+ surface.K.Cn 0 :=
    c0Carrier.toAddEquiv
  let e : PUnit ≃+ ZMod 2 :=
    c0SourceEquiv.symm.trans (eSemanticToCech.trans c0TargetEquiv)
  rcases e.surjective (0 : ZMod 2) with ⟨x0, hx0⟩
  rcases e.surjective (1 : ZMod 2) with ⟨x1, hx1⟩
  have hzero_one : (0 : ZMod 2) = 1 := by
    rw [← hx0, ← hx1]
  exact (by norm_num : (0 : ZMod 2) ≠ 1) hzero_one

/--
Cycle 49 source-relative constructor: an allowed selected cochain-realization
source is sufficient to expose the explicit finite witness and route it through
the Cycle 46 selected lower-pair constructor.

This theorem deliberately remains source-relative.  The
`SemanticRepairCoverRelativeCochainRealization` argument is the selected
carrier / semantic-delta compatibility source; it is decomposed through
`cochainRealization_iff_degreewiseCarrierData_and_explicitFaceRestrictionEquations`
and then proof-used by Cycles 47 and 46.  The theorem does not claim that
`CurrentG06InputSurface` alone constructs the finite witness.
-/
theorem currentG06InputSurface_selectedCochainRealization_constructs_degreewiseCarrierData_and_selectedCarrierGeometry_and_faceLawSource
    (surface :
      SemanticRepairCarrierSpecificComparisonProvenance.CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob))
    (realization : SemanticRepairCoverRelativeCochainRealization additive surface.K) :
    (∀ {source target : S.category} (f : source ⟶ target),
      letI := Ob.addCommGroup target
      letI := Ob.addCommGroup source
      Ob.carrier.toPresheaf.map f.op 0 = 0) /\
      (∀ {source target : S.category} (f : source ⟶ target)
          (x y : Ob.carrier.toPresheaf.obj (op target)),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op (x + y) =
          Ob.carrier.toPresheaf.map f.op x +
            Ob.carrier.toPresheaf.map f.op y) /\
      (∀ (n : Nat) (c : surface.K.Cn n),
        surface.K.d n c =
          surface.K.alternatingFaceCombination n
            (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
        (additive := additive) (coverBridge := surface.coverBridge)
        (K := surface.K) /\
      (Exists fun geometry :
        SemanticRepairSelectedCarrierGeometry additive surface.coverBridge surface.K =>
          SemanticRepairSelectedCechFaceLawSource additive geometry) := by
  have lower :
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
        (additive := additive) (coverBridge := surface.coverBridge)
        (K := surface.K) :=
    (cochainRealization_iff_degreewiseCarrierData_and_explicitFaceRestrictionEquations
      (additive := additive) (coverBridge := surface.coverBridge)
      (K := surface.K)).1
      ⟨realization⟩
  have hsource :
      (∀ {source target : S.category} (f : source ⟶ target),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op 0 = 0) /\
        (∀ {source target : S.category} (f : source ⟶ target)
            (x y : Ob.carrier.toPresheaf.obj (op target)),
          letI := Ob.addCommGroup target
          letI := Ob.addCommGroup source
          Ob.carrier.toPresheaf.map f.op (x + y) =
            Ob.carrier.toPresheaf.map f.op x +
              Ob.carrier.toPresheaf.map f.op y) /\
        (∀ (n : Nat) (c : surface.K.Cn n),
          surface.K.d n c =
            surface.K.alternatingFaceCombination n
              (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
        (Exists fun c0Carrier :
          letI := additive.c0AddCommGroup
          letI := surface.K.cochainAddCommGroup 0
          CarrierSpecificAdditiveComparisonData E.coefficient.C0 (surface.K.Cn 0) =>
        Exists fun c1Carrier :
          letI := additive.c1AddCommGroup
          letI := surface.K.cochainAddCommGroup 1
          CarrierSpecificAdditiveComparisonData E.coefficient.C1 (surface.K.Cn 1) =>
        Exists fun c2Equiv : E.coefficient.C2 ≃ surface.K.Cn 2 =>
        Exists fun c2Equiv_zero :
          letI := surface.K.cochainAddCommGroup 2
          c2Equiv E.coefficient.zero2 = 0 =>
        Exists fun c2Equiv_symm_zero :
          letI := surface.K.cochainAddCommGroup 2
          c2Equiv.symm 0 = E.coefficient.zero2 =>
          let model :=
            SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
              (additive := additive) (coverBridge := surface.coverBridge)
              (K := surface.K)
              c0Carrier c1Carrier c2Equiv
              c2Equiv_zero c2Equiv_symm_zero
          let sectionWitness :=
            SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
              model
          (letI := additive.c0AddCommGroup
           letI := additive.c1AddCommGroup
           letI := surface.K.cochainAddCommGroup 0
           letI := surface.K.cochainAddCommGroup 1
           forall primitive : E.coefficient.C0,
             surface.K.alternatingFaceCombination 0
                 (fun σ i =>
                   surface.K.faceRestrictionTerm 0 i
                     (sectionWitness.c0SectionEquiv primitive) σ) =
               sectionWitness.c1SectionEquiv (E.coefficient.delta0 primitive)) /\
          (letI := additive.c0AddCommGroup
           letI := additive.c1AddCommGroup
           letI := surface.K.cochainAddCommGroup 0
           letI := surface.K.cochainAddCommGroup 1
           forall primitive : surface.K.Cn 0,
             E.coefficient.delta0 (sectionWitness.c0SectionEquiv.symm primitive) =
               sectionWitness.c1SectionEquiv.symm
                 (surface.K.alternatingFaceCombination 0
                   (fun σ i => surface.K.faceRestrictionTerm 0 i primitive σ))) /\
          (letI := additive.c1AddCommGroup
           letI := surface.K.cochainAddCommGroup 1
           forall cochain : E.coefficient.C1,
             surface.K.alternatingFaceCombination 1
                 (fun σ i =>
                   surface.K.faceRestrictionTerm 1 i
                     (sectionWitness.c1SectionEquiv cochain) σ) =
               sectionWitness.c2SectionEquiv (E.coefficient.delta1 cochain)) /\
          (letI := additive.c1AddCommGroup
           letI := surface.K.cochainAddCommGroup 1
           forall cochain : surface.K.Cn 1,
             E.coefficient.delta1 (sectionWitness.c1SectionEquiv.symm cochain) =
               sectionWitness.c2SectionEquiv.symm
                 (surface.K.alternatingFaceCombination 1
                   (fun σ i => surface.K.faceRestrictionTerm 1 i cochain σ)))) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            CarrierSpecificAdditiveComparisonData C D) /\
        IsEmpty
          ((C D : Type) -> [AddCommGroup C] -> [AddCommGroup D] ->
            C ≃+ D) :=
    currentG06InputSurface_explicitFiniteWitness_requires_concrete_lower_sources
      (surface := surface) lower
  have hselected :
      (∀ {source target : S.category} (f : source ⟶ target),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op 0 = 0) /\
        (∀ {source target : S.category} (f : source ⟶ target)
            (x y : Ob.carrier.toPresheaf.obj (op target)),
          letI := Ob.addCommGroup target
          letI := Ob.addCommGroup source
          Ob.carrier.toPresheaf.map f.op (x + y) =
            Ob.carrier.toPresheaf.map f.op x +
              Ob.carrier.toPresheaf.map f.op y) /\
        (∀ (n : Nat) (c : surface.K.Cn n),
          surface.K.d n c =
            surface.K.alternatingFaceCombination n
              (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
        Exists fun geometry :
          SemanticRepairSelectedCarrierGeometry additive surface.coverBridge surface.K =>
            SemanticRepairSelectedCechFaceLawSource additive geometry :=
    currentG06InputSurface_explicitFiniteWitness_constructs_selectedCarrierGeometry_and_faceLawSource
      (surface := surface) lower
  exact
    ⟨hsource.1,
      hsource.2.1,
      hsource.2.2.1,
      lower,
      hselected.2.2.2⟩

/--
Carrier-only section-family model data reaches the selected cover-relative
grounding package once the separate face-restriction compatibility premise is
proved for the constructed section-family witness.

This wires the Cycle 20 lower carrier model into the Cycle 19 path:
carrier model -> section-family witness -> cochain realization -> selected
cover-relative `H1` grounding package.  Face-restriction compatibility remains
visible as its own discharge-required premise.
-/
theorem grounded_package_of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K)
    (compatibility :
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        additive
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        (of_sectionFamilyWitness_and_faceRestrictionCompatibility
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)
          compatibility).toH1Comparison) :=
  grounded_package_of_sectionFamilyWitness_and_faceRestrictionCompatibility
    (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
      model)
    compatibility

/--
Carrier-only model data reaches the selected cover-relative grounding package
from direct selected differential laws by first normalizing those laws to the
selected presheaf face-restriction presentation.

The proof-use path is explicit:
carrier model constructs the section-family witness; direct `K.d` compatibility
is converted to face-restriction compatibility using
`K.d_eq_alternatingFaceCombination`; those two lower witnesses construct the
cochain realization and hence the selected cover-relative `H1` grounding
package.
-/
theorem grounded_package_of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
    (model : SelectedSectionFamilyCarrierModel additive coverBridge K)
    (direct :
      SemanticRepairCoverRelativeDirectDifferentialCompatibility
        additive
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        (of_sectionFamilyWitness_and_faceRestrictionCompatibility
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)
          direct.toFaceRestrictionCompatibility).toH1Comparison) :=
  grounded_package_of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
    model direct.toFaceRestrictionCompatibility

/--
Cycle 31 bridge theorem: selected cochain realization discharges the direct
selected differential-compatibility node for the carrier model extracted from
the same realization.

The source is the existing cochain-realization layer: degree-wise selected
carrier equivalences plus semantic `delta0` / `delta1` compatibility with the
chosen cover-relative Cech differential.  The theorem constructs the
carrier-only model, the direct `K.d` compatibility for the model-built section
witness, and then proof-uses both witnesses in the existing selected
cover-relative grounding package path.  It introduces no new certificate
structure and stores no `H1` zero, boundary membership, global coherence,
effective descent, refinement naturality, or full sheaf cohomology comparison.
-/
theorem selectedSemanticDeltaPresheafRestriction_constructs_directDifferentialCompatibility
    (realization :
      SemanticRepairCoverRelativeCochainRealization additive K) :
    Exists fun model : SelectedSectionFamilyCarrierModel additive coverBridge K =>
      Exists fun direct :
        SemanticRepairCoverRelativeDirectDifferentialCompatibility
          additive
            (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
              model) =>
          Nonempty
            (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
              (of_sectionFamilyWitness_and_faceRestrictionCompatibility
                (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
                  model)
                direct.toFaceRestrictionCompatibility).toH1Comparison) := by
  let provenance := realization.toCarrierSpecificComparisonProvenance
  let bridge := provenance.toSectionRealizationBridge
  let model := bridge.toSelectedSectionFamilyCarrierModel
  let direct := bridge.toDirectDifferentialCompatibilityForSelectedCarrierModel
  exact
    ⟨model, direct,
      grounded_package_of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
        model direct⟩

/--
Cycle 50 lower-source constructor: selected carrier model data plus direct
selected semantic-delta / Cech-differential compatibility constructs the
selected cochain-realization source itself.

This is the source-discharge path left open by Cycle 49.  The theorem does not
take `SemanticRepairCoverRelativeCochainRealization` as an argument.  Instead,
the carrier model supplies the selected degree-wise section-family carriers,
and the direct differential source supplies the semantic `delta0` / `delta1`
compatibility with the chosen cover-relative Cech differential.  The constructed
realization is then proof-used by the Cycle 49 finite-witness path and by the
existing direct-differential grounding theorem.
-/
theorem currentG06InputSurface_selectedCarrierModel_and_directDifferentialCompatibility_constructs_selectedCochainRealization_and_groundingSources
    (surface :
      SemanticRepairCarrierSpecificComparisonProvenance.CurrentG06InputSurface
        (semanticCover := semanticCover) (S := S) (Ob := Ob))
    (model : SelectedSectionFamilyCarrierModel
      additive surface.coverBridge surface.K)
    (direct :
      SemanticRepairCoverRelativeDirectDifferentialCompatibility
        additive
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    Nonempty (SemanticRepairCoverRelativeCochainRealization additive surface.K) /\
      (∀ {source target : S.category} (f : source ⟶ target),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op 0 = 0) /\
      (∀ {source target : S.category} (f : source ⟶ target)
          (x y : Ob.carrier.toPresheaf.obj (op target)),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op (x + y) =
          Ob.carrier.toPresheaf.map f.op x +
            Ob.carrier.toPresheaf.map f.op y) /\
      (∀ (n : Nat) (c : surface.K.Cn n),
        surface.K.d n c =
          surface.K.alternatingFaceCombination n
            (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
        (additive := additive) (coverBridge := surface.coverBridge)
        (K := surface.K) /\
      (Exists fun geometry :
        SemanticRepairSelectedCarrierGeometry additive surface.coverBridge surface.K =>
          SemanticRepairSelectedCechFaceLawSource additive geometry) /\
      (Exists fun realizedModel :
        SelectedSectionFamilyCarrierModel additive surface.coverBridge surface.K =>
          Exists fun realizedDirect :
            SemanticRepairCoverRelativeDirectDifferentialCompatibility
              additive
                (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
                  realizedModel) =>
            Nonempty
              (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
                (of_sectionFamilyWitness_and_faceRestrictionCompatibility
                  (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
                    realizedModel)
                  realizedDirect.toFaceRestrictionCompatibility).toH1Comparison)) := by
  let realization :=
    of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
      (additive := additive) (coverBridge := surface.coverBridge)
      (K := surface.K) model direct
  have hcycle49 :
      (∀ {source target : S.category} (f : source ⟶ target),
        letI := Ob.addCommGroup target
        letI := Ob.addCommGroup source
        Ob.carrier.toPresheaf.map f.op 0 = 0) /\
        (∀ {source target : S.category} (f : source ⟶ target)
            (x y : Ob.carrier.toPresheaf.obj (op target)),
          letI := Ob.addCommGroup target
          letI := Ob.addCommGroup source
          Ob.carrier.toPresheaf.map f.op (x + y) =
            Ob.carrier.toPresheaf.map f.op x +
              Ob.carrier.toPresheaf.map f.op y) /\
        (∀ (n : Nat) (c : surface.K.Cn n),
          surface.K.d n c =
            surface.K.alternatingFaceCombination n
              (fun σ i => surface.K.faceRestrictionTerm n i c σ)) /\
        DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
          (additive := additive) (coverBridge := surface.coverBridge)
          (K := surface.K) /\
        (Exists fun geometry :
          SemanticRepairSelectedCarrierGeometry additive surface.coverBridge surface.K =>
            SemanticRepairSelectedCechFaceLawSource additive geometry) :=
    currentG06InputSurface_selectedCochainRealization_constructs_degreewiseCarrierData_and_selectedCarrierGeometry_and_faceLawSource
      (surface := surface) realization
  have hdirect :
      Exists fun realizedModel :
        SelectedSectionFamilyCarrierModel additive surface.coverBridge surface.K =>
          Exists fun realizedDirect :
            SemanticRepairCoverRelativeDirectDifferentialCompatibility
              additive
                (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
                  realizedModel) =>
            Nonempty
              (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
                (of_sectionFamilyWitness_and_faceRestrictionCompatibility
                  (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
                    realizedModel)
                  realizedDirect.toFaceRestrictionCompatibility).toH1Comparison) :=
    selectedSemanticDeltaPresheafRestriction_constructs_directDifferentialCompatibility
      (additive := additive) (coverBridge := surface.coverBridge)
      (K := surface.K) realization
  exact
    ⟨⟨realization⟩,
      hcycle49.1,
      hcycle49.2.1,
      hcycle49.2.2.1,
      hcycle49.2.2.2.1,
      hcycle49.2.2.2.2,
      hdirect⟩

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
The richer section-realization bridge reaches the selected cover-relative
grounding package through the current lower DAG:

`SectionRealizationBridge -> SelectedSectionFamilyCarrierModel`
and
`SectionRealizationBridge -> DirectDifferentialCompatibility`, followed by the
Cycle 22 theorem that consumes carrier model plus direct differential laws.
-/
theorem grounded_package_of_section_realization_bridge_via_selectedCarrierModel_and_directDifferentialCompatibility
    (bridge : SemanticRepairCoverRelativeSectionRealizationBridge
      additive coverBridge K) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        (SemanticRepairCoverRelativeCochainRealization.of_sectionFamilyWitness_and_faceRestrictionCompatibility
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            bridge.toSelectedSectionFamilyCarrierModel)
          bridge.toDirectDifferentialCompatibilityForSelectedCarrierModel.toFaceRestrictionCompatibility).toH1Comparison) :=
  SemanticRepairCoverRelativeCochainRealization.grounded_package_of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
    bridge.toSelectedSectionFamilyCarrierModel
    bridge.toDirectDifferentialCompatibilityForSelectedCarrierModel

end SemanticRepairCoverRelativeSectionRealizationBridge

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
Carrier-specific provenance reaches the selected cover-relative grounding
package through the richer bridge and the Cycle 23 lower-DAG proof-use theorem.

This is a proof-use theorem: the constructed bridge is consumed by the existing
`SectionRealizationBridge -> SelectedSectionFamilyCarrierModel +
DirectDifferentialCompatibility -> H1 package` path.  The result is still
relative to the lower carrier-specific provenance source.
-/
theorem grounded_package_of_carrier_specific_comparison_provenance_via_sectionRealizationBridge
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance additive coverBridge K) :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        (SemanticRepairCoverRelativeCochainRealization.of_sectionFamilyWitness_and_faceRestrictionCompatibility
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            provenance.toSectionRealizationBridge.toSelectedSectionFamilyCarrierModel)
          provenance.toSectionRealizationBridge.toDirectDifferentialCompatibilityForSelectedCarrierModel.toFaceRestrictionCompatibility).toH1Comparison) :=
  provenance.toSectionRealizationBridge
    |>.grounded_package_of_section_realization_bridge_via_selectedCarrierModel_and_directDifferentialCompatibility

end SemanticRepairCarrierSpecificComparisonProvenance

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
Boundary-relation additive true-sheaf gluing reaches the selected
cover-relative Cech `H1` zero predicate once the explicit cochain comparison is
available.

This is a proof-use theorem, not a new certificate.  The selected AAT sheaf
condition and cover membership are consumed by
`aatSheafCondition_coverMembership_descent_effectiveGluing` to produce descent
and an effective global gluing section for the supplied local data.  The
G-05 true-sheaf additive package is then composed with the G-06
cover-relative zero equivalence.  The cover-relative comparison remains an
explicit premise; no full sheaf cohomology comparison or refinement naturality
claim is introduced.
-/
theorem trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package
    {Atom : Type u}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
        data.boundaryRelation S F cover)
    (gluingData : AAT.AG.Site.AATGluingData S F cover)
    {coverRel : AAT.AG.Cohomology.CoverRelativeCechCover S}
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    {K : AAT.AG.Cohomology.CoverRelativeCechComplex coverRel Ob}
    (comparison :
      SemanticRepairCoverRelativeH1Comparison
        data.toAdditiveCechH1Data K) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      (∃! globalSection : F.obj (op base),
        AAT.AG.Site.AATGlobalSectionRealizes
          gluingData globalSection) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          comparison) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope
                data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
          comparison.CoverRelativeResidualH1Zero) /\
      (comparison.CoverRelativeResidualH1Zero ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData))) /\
      (GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) ->
        comparison.CoverRelativeResidualH1Zero) /\
      (SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data <->
        comparison.CoverRelativeResidualH1Zero) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) := by
  rcases
    aatSheafCondition_coverMembership_descent_effectiveGluing
      certificate.sheafCondition cover certificate.cover_mem gluingData with
    ⟨hSheafFor, hDescent, hEffectiveGluing⟩
  rcases
    trueSheafH1SemanticRepairGluing_trueSheafBoundaryRelationAdditive_package
      data S F cover certificate with
    ⟨_, _, _, _, hGlobalAdditive, _, _, _, hTorsor, hHigher, hStack⟩
  have hAdditiveCover :
      SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data <->
        comparison.CoverRelativeResidualH1Zero :=
    comparison.semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero
  have hGlobalCover :
      GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
        comparison.CoverRelativeResidualH1Zero :=
    hGlobalAdditive.trans hAdditiveCover
  exact
    ⟨hSheafFor,
      hDescent,
      hEffectiveGluing,
      comparison.semanticRepairAdditiveH1_coverRelativeH1_comparison_package,
      hGlobalCover,
      hGlobalCover.2,
      hGlobalCover.1,
      hAdditiveCover,
      hTorsor,
      hHigher,
      hStack⟩

/--
Cycle 34 lower-source version of
`trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package`.

The top-level `SemanticRepairCoverRelativeH1Comparison` premise is constructed
from the existing lower selected data:
`SelectedSectionFamilyCarrierModel` plus direct selected differential
compatibility.  The construction passes through
`SemanticRepairCoverRelativeCochainRealization.of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility`
and then uses `toH1Comparison`.

This still does not discharge the carrier model or direct differential-law
sources.  It only removes the already constructed comparison object from the
true-sheaf / cover-relative gluing theorem's argument list.
-/
theorem trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
        data.boundaryRelation S F cover)
    (gluingData : AAT.AG.Site.AATGluingData S F cover)
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob)
    (model :
      SelectedSectionFamilyCarrierModel
        data.toAdditiveCechH1Data coverBridge K)
    (direct :
      SemanticRepairCoverRelativeDirectDifferentialCompatibility
        data.toAdditiveCechH1Data
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      (∃! globalSection : F.obj (op base),
        AAT.AG.Site.AATGlobalSectionRealizes
          gluingData globalSection) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          (SemanticRepairCoverRelativeCochainRealization.of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
            model direct).toH1Comparison) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope
                data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
          (SemanticRepairCoverRelativeCochainRealization.of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
            model direct).toH1Comparison.CoverRelativeResidualH1Zero) /\
      ((SemanticRepairCoverRelativeCochainRealization.of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
            model direct).toH1Comparison.CoverRelativeResidualH1Zero ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData))) /\
      (GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) ->
        (SemanticRepairCoverRelativeCochainRealization.of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
          model direct).toH1Comparison.CoverRelativeResidualH1Zero) /\
      (SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data <->
        (SemanticRepairCoverRelativeCochainRealization.of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
          model direct).toH1Comparison.CoverRelativeResidualH1Zero) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) :=
  trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package
    data S F cover certificate gluingData
    (SemanticRepairCoverRelativeCochainRealization.of_selectedSectionFamilyCarrierModel_and_directDifferentialCompatibility
      model direct).toH1Comparison

/--
Cycle 35 lower-source version using carrier-specific comparison provenance.

This lowers the Cycle 34 `SelectedSectionFamilyCarrierModel + direct
differential compatibility` pair to the already separated
`SemanticRepairCarrierSpecificComparisonProvenance` source.  The provenance is
consumed through `provenance.toCochainRealization.toH1Comparison` and then fed
into the Cycle 33 true-sheaf / cover-relative `H1` zero effective-gluing
package.

The theorem still does not construct carrier-specific provenance from current
site/sheaf/descent input.  That provenance remains a material source containing
selected carrier maps, inverse/additivity laws, degree-`2` zero laws, and
selected face-restriction differential equations.
-/
theorem trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_carrierSpecificComparisonProvenance
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
        data.boundaryRelation S F cover)
    (gluingData : AAT.AG.Site.AATGluingData S F cover)
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob)
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance
        data.toAdditiveCechH1Data coverBridge K) :
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      (∃! globalSection : F.obj (op base),
        AAT.AG.Site.AATGlobalSectionRealizes
          gluingData globalSection) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          provenance.toCochainRealization.toH1Comparison) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope
                data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
          provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData))) /\
      (GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) ->
        provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data <->
        provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) :=
  trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package
    data S F cover certificate gluingData
    provenance.toCochainRealization.toH1Comparison

/--
Cycle 36 lower-source version using separated selected carrier geometry and
selected Cech face laws.

This theorem consumes the already separated lower sources through
`SemanticRepairCarrierSpecificComparisonProvenance.of_selectedCarrierGeometry_and_faceLaws`
and then applies the Cycle 35 carrier-specific provenance theorem.  It keeps
both material inputs visible: carrier geometry alone is not counted as
differential compatibility, and selected Cech face laws are still an explicit
premise.  No refinement naturality or full sheaf cohomology comparison is
introduced.
-/
theorem trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_selectedCarrierGeometry_and_faceLaws
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
        data.boundaryRelation S F cover)
    (gluingData : AAT.AG.Site.AATGluingData S F cover)
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob)
    (geometry :
      SemanticRepairSelectedCarrierGeometry
        data.toAdditiveCechH1Data coverBridge K)
    (faceLaws :
      SemanticRepairSelectedCechFaceLawSource
        data.toAdditiveCechH1Data geometry) :
    let provenance :=
      SemanticRepairCarrierSpecificComparisonProvenance.of_selectedCarrierGeometry_and_faceLaws
        geometry faceLaws
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      (∃! globalSection : F.obj (op base),
        AAT.AG.Site.AATGlobalSectionRealizes
          gluingData globalSection) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          provenance.toCochainRealization.toH1Comparison) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope
                data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
          provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData))) /\
      (GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) ->
        provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data <->
        provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) := by
  dsimp only
  exact
    trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_carrierSpecificComparisonProvenance
      data S F cover certificate gluingData coverBridge K
      (SemanticRepairCarrierSpecificComparisonProvenance.of_selectedCarrierGeometry_and_faceLaws
        geometry faceLaws)

/--
Cycle 37 lower-source version using the concrete carrier-only model and actual
selected face-restriction compatibility.

This theorem removes the top-level selected carrier-geometry and selected
face-law arguments from the effective-gluing bridge.  The carrier geometry is
constructed from `SelectedSectionFamilyCarrierModel`, and the selected Cech face
laws are constructed from
`SemanticRepairCoverRelativeFaceRestrictionCompatibility` for the section-family
witness generated by the same model.  The result remains relative to those two
lower material sources; no bare cover/sheaf/descent input is claimed to produce
them.
-/
theorem trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
        data.boundaryRelation S F cover)
    (gluingData : AAT.AG.Site.AATGluingData S F cover)
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob)
    (model :
      SelectedSectionFamilyCarrierModel
        data.toAdditiveCechH1Data coverBridge K)
    (compatibility :
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        data.toAdditiveCechH1Data
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    let geometry :=
      SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
        model
    let faceLaws :=
      SemanticRepairSelectedCechFaceLawSource.of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
        model compatibility
    let provenance :=
      SemanticRepairCarrierSpecificComparisonProvenance.of_selectedCarrierGeometry_and_faceLaws
        geometry faceLaws
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      (∃! globalSection : F.obj (op base),
        AAT.AG.Site.AATGlobalSectionRealizes
          gluingData globalSection) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          provenance.toCochainRealization.toH1Comparison) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope
                data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
          provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData))) /\
      (GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) ->
        provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data <->
        provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) := by
  dsimp only
  exact
    trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_selectedCarrierGeometry_and_faceLaws
      data S F cover certificate gluingData coverBridge K
      (SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
        model)
      (SemanticRepairSelectedCechFaceLawSource.of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
        model compatibility)

/--
Cycle 38 lower-source version using explicit finite carrier witness data plus
actual selected face-restriction compatibility.

This theorem removes `SelectedSectionFamilyCarrierModel` as a top-level
argument of the effective-gluing bridge.  The model is constructed from the
degree-`0` and degree-`1` additive carrier comparisons together with the
degree-`2` zero-preserving equivalence, and that constructed model is then
proof-used in the Cycle 37 theorem.  Face-restriction compatibility remains an
explicit lower material premise, now relative to the section-family witness
constructed from the finite carrier witness.
-/
theorem trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_degreewiseCarrierData_and_faceRestrictionCompatibility
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
        data.boundaryRelation S F cover)
    (gluingData : AAT.AG.Site.AATGluingData S F cover)
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob)
    (c0Carrier :
      let E :=
        toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData
      letI := data.toAdditiveCechH1Data.c0AddCommGroup
      letI := K.cochainAddCommGroup 0
      CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0))
    (c1Carrier :
      let E :=
        toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData
      letI := data.toAdditiveCechH1Data.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1))
    (c2Equiv :
      (toSheafH1Envelope
        data.boundaryRelation.toAbelianDescentData.toEnvelopeData).coefficient.C2 ≃
        K.Cn 2)
    (c2Equiv_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData).coefficient.zero2 =
        0)
    (c2Equiv_symm_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv.symm 0 =
        (toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData).coefficient.zero2)
    (compatibility :
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := data.toAdditiveCechH1Data)
          (coverBridge := coverBridge)
          (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      SemanticRepairCoverRelativeFaceRestrictionCompatibility
        data.toAdditiveCechH1Data
          (SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            model)) :
    let model :=
      SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
        (additive := data.toAdditiveCechH1Data)
        (coverBridge := coverBridge)
        (K := K)
        c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
    let geometry :=
      SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
        model
    let faceLaws :=
      SemanticRepairSelectedCechFaceLawSource.of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
        model compatibility
    let provenance :=
      SemanticRepairCarrierSpecificComparisonProvenance.of_selectedCarrierGeometry_and_faceLaws
        geometry faceLaws
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      (∃! globalSection : F.obj (op base),
        AAT.AG.Site.AATGlobalSectionRealizes
          gluingData globalSection) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          provenance.toCochainRealization.toH1Comparison) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope
                data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
          provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData))) /\
      (GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) ->
        provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data <->
        provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) := by
  dsimp only
  exact
    trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
      data S F cover certificate gluingData coverBridge K
      (SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
        (additive := data.toAdditiveCechH1Data)
        (coverBridge := coverBridge)
        (K := K)
        c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero)
      compatibility

/--
Cycle 39 lower-source version using finite carrier witness data plus the four
explicit selected face-restriction equations.

This removes `SemanticRepairCoverRelativeFaceRestrictionCompatibility` as a
top-level opaque premise of the effective-gluing bridge.  The compatibility
object is constructed from the four displayed equations and then proof-used by
the Cycle 38 theorem.  The equations themselves remain the unresolved lower
semantic-delta / presheaf-restriction source; they are not generated from bare
cover membership, sheaf condition, descent, or full sheaf cohomology.
-/
theorem trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_degreewiseCarrierData_and_explicitFaceRestrictionEquations
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
        data.boundaryRelation S F cover)
    (gluingData : AAT.AG.Site.AATGluingData S F cover)
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob)
    (c0Carrier :
      let E :=
        toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData
      letI := data.toAdditiveCechH1Data.c0AddCommGroup
      letI := K.cochainAddCommGroup 0
      CarrierSpecificAdditiveComparisonData E.coefficient.C0 (K.Cn 0))
    (c1Carrier :
      let E :=
        toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData
      letI := data.toAdditiveCechH1Data.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      CarrierSpecificAdditiveComparisonData E.coefficient.C1 (K.Cn 1))
    (c2Equiv :
      (toSheafH1Envelope
        data.boundaryRelation.toAbelianDescentData.toEnvelopeData).coefficient.C2 ≃
        K.Cn 2)
    (c2Equiv_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData).coefficient.zero2 =
        0)
    (c2Equiv_symm_zero :
      letI := K.cochainAddCommGroup 2
      c2Equiv.symm 0 =
        (toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData).coefficient.zero2)
    (d0_face_to :
      let E :=
        toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := data.toAdditiveCechH1Data)
          (coverBridge := coverBridge)
          (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := data.toAdditiveCechH1Data.c0AddCommGroup
      letI := data.toAdditiveCechH1Data.c1AddCommGroup
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      forall primitive : E.coefficient.C0,
        K.alternatingFaceCombination 0
            (fun σ i =>
              K.faceRestrictionTerm 0 i
                (sectionWitness.c0SectionEquiv primitive) σ) =
          sectionWitness.c1SectionEquiv (E.coefficient.delta0 primitive))
    (d0_face_from :
      let E :=
        toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := data.toAdditiveCechH1Data)
          (coverBridge := coverBridge)
          (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := data.toAdditiveCechH1Data.c0AddCommGroup
      letI := data.toAdditiveCechH1Data.c1AddCommGroup
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      forall primitive : K.Cn 0,
        E.coefficient.delta0 (sectionWitness.c0SectionEquiv.symm primitive) =
          sectionWitness.c1SectionEquiv.symm
            (K.alternatingFaceCombination 0
              (fun σ i => K.faceRestrictionTerm 0 i primitive σ)))
    (d1_face_to :
      let E :=
        toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := data.toAdditiveCechH1Data)
          (coverBridge := coverBridge)
          (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := data.toAdditiveCechH1Data.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      forall cochain : E.coefficient.C1,
        K.alternatingFaceCombination 1
            (fun σ i =>
              K.faceRestrictionTerm 1 i
                (sectionWitness.c1SectionEquiv cochain) σ) =
          sectionWitness.c2SectionEquiv (E.coefficient.delta1 cochain))
    (d1_face_from :
      let E :=
        toSheafH1Envelope
          data.boundaryRelation.toAbelianDescentData.toEnvelopeData
      let model :=
        SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
          (additive := data.toAdditiveCechH1Data)
          (coverBridge := coverBridge)
          (K := K)
          c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      let sectionWitness :=
        SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
          model
      letI := data.toAdditiveCechH1Data.c1AddCommGroup
      letI := K.cochainAddCommGroup 1
      forall cochain : K.Cn 1,
        E.coefficient.delta1 (sectionWitness.c1SectionEquiv.symm cochain) =
          sectionWitness.c2SectionEquiv.symm
            (K.alternatingFaceCombination 1
              (fun σ i => K.faceRestrictionTerm 1 i cochain σ))) :
    let model :=
      SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
        (additive := data.toAdditiveCechH1Data)
        (coverBridge := coverBridge)
        (K := K)
        c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
    let sectionWitness :=
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
        model
    let compatibility :=
      SemanticRepairCoverRelativeFaceRestrictionCompatibility.of_explicit_face_restriction_equations
        (additive := data.toAdditiveCechH1Data)
        (sectionWitness := sectionWitness)
        d0_face_to d0_face_from d1_face_to d1_face_from
    let geometry :=
      SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
        model
    let faceLaws :=
      SemanticRepairSelectedCechFaceLawSource.of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
        model compatibility
    let provenance :=
      SemanticRepairCarrierSpecificComparisonProvenance.of_selectedCarrierGeometry_and_faceLaws
        geometry faceLaws
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      (∃! globalSection : F.obj (op base),
        AAT.AG.Site.AATGlobalSectionRealizes
          gluingData globalSection) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          provenance.toCochainRealization.toH1Comparison) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope
                data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
          provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData))) /\
      (GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) ->
        provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data <->
        provenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) := by
  dsimp only
  exact
    trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_degreewiseCarrierData_and_faceRestrictionCompatibility
      data S F cover certificate gluingData coverBridge K
      c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero
      (SemanticRepairCoverRelativeFaceRestrictionCompatibility.of_explicit_face_restriction_equations
        (additive := data.toAdditiveCechH1Data)
        (sectionWitness :=
          SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
            (SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
              (additive := data.toAdditiveCechH1Data)
              (coverBridge := coverBridge)
              (K := K)
              c0Carrier c1Carrier c2Equiv c2Equiv_zero c2Equiv_symm_zero))
        d0_face_to d0_face_from d1_face_to d1_face_from)

/--
Cycle 40 lower-source version using the concrete carrier-specific provenance
source, but routing through the Cycle 39 explicit finite carrier and selected
face-restriction equations path.

This theorem consumes a `SemanticRepairCarrierSpecificComparisonProvenance`
inhabitant by extracting its degree-wise carrier data, degree-`2` zero laws, and
four selected face-restriction equations, then feeds those extracted components
into the Cycle 39 theorem.  Thus the finite carrier witness data and the four
explicit face equations are no longer separate top-level premises of this
bridge.  The carrier-specific provenance itself remains the visible material
source; it is not constructed from bare cover membership, sheaf condition,
descent, or full sheaf cohomology.
-/
theorem trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_carrierSpecificComparisonProvenance_via_explicitFaceRestrictionEquations
    {Atom : Type u}
    {site : SemanticRepairSite.{u, v} Atom}
    {semanticCover : SemanticRepairCover.{u, v, w} site}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} Atom)
    {U : AAT.AG.AtomCarrier.{r}}
    {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A)
    (F : AAT.AG.Site.AATPresheaf S)
    {base : S.category}
    (cover : Sieve base)
    (certificate :
      SemanticRepairCoverH1BoundaryRelationTrueSheafConditionCertificate
        data.boundaryRelation S F cover)
    (gluingData : AAT.AG.Site.AATGluingData S F cover)
    (coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    {Ob : AAT.AG.Cohomology.ObstructionSheaf S}
    (K : AAT.AG.Cohomology.CoverRelativeCechComplex
      (SemanticRepairCover.toCoverRelativeCechCover coverBridge) Ob)
    (provenance :
      SemanticRepairCarrierSpecificComparisonProvenance
        data.toAdditiveCechH1Data coverBridge K) :
    let c0Carrier :=
      SemanticRepairCarrierSpecificComparisonProvenance.degreeZeroAdditiveComparisonData
        provenance
    let c1Carrier :=
      SemanticRepairCarrierSpecificComparisonProvenance.degreeOneAdditiveComparisonData
        provenance
    let c2Equiv :=
      SemanticRepairCarrierSpecificComparisonProvenance.c2SectionEquiv
        provenance
    let model :=
      SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence
        (additive := data.toAdditiveCechH1Data)
        (coverBridge := coverBridge)
        (K := K)
        c0Carrier c1Carrier c2Equiv
        provenance.toSection2_zero provenance.fromSection2_zero
    let sectionWitness :=
      SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel
        model
    let compatibility :=
      SemanticRepairCoverRelativeFaceRestrictionCompatibility.of_explicit_face_restriction_equations
        (additive := data.toAdditiveCechH1Data)
        (sectionWitness := sectionWitness)
        (by
          intro primitive
          simpa [c0Carrier, c1Carrier, c2Equiv, model, sectionWitness,
            SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
            SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
            SelectedSectionFamilyCarrierModel.c0SectionEquiv,
            SelectedSectionFamilyCarrierModel.c1SectionEquiv,
            CarrierSpecificAdditiveComparisonData.toAddEquiv,
            SemanticRepairCarrierSpecificComparisonProvenance.degreeZeroAdditiveComparisonData,
            SemanticRepairCarrierSpecificComparisonProvenance.degreeOneAdditiveComparisonData,
            SemanticRepairCarrierSpecificComparisonProvenance.c2SectionEquiv] using
              provenance.d0_face_to primitive)
        (by
          intro primitive
          simpa [c0Carrier, c1Carrier, c2Equiv, model, sectionWitness,
            SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
            SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
            SelectedSectionFamilyCarrierModel.c0SectionEquiv,
            SelectedSectionFamilyCarrierModel.c1SectionEquiv,
            CarrierSpecificAdditiveComparisonData.toAddEquiv,
            SemanticRepairCarrierSpecificComparisonProvenance.degreeZeroAdditiveComparisonData,
            SemanticRepairCarrierSpecificComparisonProvenance.degreeOneAdditiveComparisonData,
            SemanticRepairCarrierSpecificComparisonProvenance.c2SectionEquiv] using
              provenance.d0_face_from primitive)
        (by
          intro cochain
          simpa [c0Carrier, c1Carrier, c2Equiv, model, sectionWitness,
            SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
            SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
            SelectedSectionFamilyCarrierModel.c1SectionEquiv,
            CarrierSpecificAdditiveComparisonData.toAddEquiv,
            SemanticRepairCarrierSpecificComparisonProvenance.degreeZeroAdditiveComparisonData,
            SemanticRepairCarrierSpecificComparisonProvenance.degreeOneAdditiveComparisonData,
            SemanticRepairCarrierSpecificComparisonProvenance.c2SectionEquiv] using
              provenance.d1_face_to cochain)
        (by
          intro cochain
          simpa [c0Carrier, c1Carrier, c2Equiv, model, sectionWitness,
            SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
            SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
            SelectedSectionFamilyCarrierModel.c1SectionEquiv,
            CarrierSpecificAdditiveComparisonData.toAddEquiv,
            SemanticRepairCarrierSpecificComparisonProvenance.degreeZeroAdditiveComparisonData,
            SemanticRepairCarrierSpecificComparisonProvenance.degreeOneAdditiveComparisonData,
            SemanticRepairCarrierSpecificComparisonProvenance.c2SectionEquiv] using
              provenance.d1_face_from cochain)
    let geometry :=
      SemanticRepairSelectedCarrierGeometry.of_selectedSectionFamilyCarrierModel
        model
    let faceLaws :=
      SemanticRepairSelectedCechFaceLawSource.of_selectedSectionFamilyCarrierModel_and_faceRestrictionCompatibility
        model compatibility
    let reconstructedProvenance :=
      SemanticRepairCarrierSpecificComparisonProvenance.of_selectedCarrierGeometry_and_faceLaws
        geometry faceLaws
    AAT.AG.Site.AATSheafConditionFor S F cover /\
      AAT.AG.Site.AATDescent S F cover /\
      (∃! globalSection : F.obj (op base),
        AAT.AG.Site.AATGlobalSectionRealizes
          gluingData globalSection) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          reconstructedProvenance.toCochainRealization.toH1Comparison) /\
      (GlobalSemanticRepairCoherent
            (toFiniteTower
              (toSheafH1Envelope
                data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) <->
          reconstructedProvenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (reconstructedProvenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero ->
        GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData))) /\
      (GlobalSemanticRepairCoherent
          (toFiniteTower
            (toSheafH1Envelope
              data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) ->
        reconstructedProvenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      (SemanticRepairAdditiveH1Zero data.toAdditiveCechH1Data <->
        reconstructedProvenance.toCochainRealization.toH1Comparison.CoverRelativeResidualH1Zero) /\
      NonabelianTorsorTrivial
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      HigherCoherenceVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) /\
      StackEffectivelyVanishes
        (toFiniteTower
          (toSheafH1Envelope
            data.boundaryRelation.toAbelianDescentData.toEnvelopeData)) := by
  dsimp only
  exact
    trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package_of_degreewiseCarrierData_and_explicitFaceRestrictionEquations
      data S F cover certificate gluingData coverBridge K
      (SemanticRepairCarrierSpecificComparisonProvenance.degreeZeroAdditiveComparisonData
        provenance)
      (SemanticRepairCarrierSpecificComparisonProvenance.degreeOneAdditiveComparisonData
        provenance)
      (SemanticRepairCarrierSpecificComparisonProvenance.c2SectionEquiv
        provenance)
      provenance.toSection2_zero
      provenance.fromSection2_zero
      (by
        dsimp only
        intro primitive
        simpa [
          SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
          SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
          SelectedSectionFamilyCarrierModel.c0SectionEquiv,
          SelectedSectionFamilyCarrierModel.c1SectionEquiv,
          CarrierSpecificAdditiveComparisonData.toAddEquiv,
          SemanticRepairCarrierSpecificComparisonProvenance.degreeZeroAdditiveComparisonData,
          SemanticRepairCarrierSpecificComparisonProvenance.degreeOneAdditiveComparisonData,
          SemanticRepairCarrierSpecificComparisonProvenance.c2SectionEquiv] using
            provenance.d0_face_to primitive)
      (by
        dsimp only
        intro primitive
        simpa [
          SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
          SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
          SelectedSectionFamilyCarrierModel.c0SectionEquiv,
          SelectedSectionFamilyCarrierModel.c1SectionEquiv,
          CarrierSpecificAdditiveComparisonData.toAddEquiv,
          SemanticRepairCarrierSpecificComparisonProvenance.degreeZeroAdditiveComparisonData,
          SemanticRepairCarrierSpecificComparisonProvenance.degreeOneAdditiveComparisonData,
          SemanticRepairCarrierSpecificComparisonProvenance.c2SectionEquiv] using
            provenance.d0_face_from primitive)
      (by
        dsimp only
        intro cochain
        simpa [
          SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
          SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
          SelectedSectionFamilyCarrierModel.c1SectionEquiv,
          CarrierSpecificAdditiveComparisonData.toAddEquiv,
          SemanticRepairCarrierSpecificComparisonProvenance.degreeZeroAdditiveComparisonData,
          SemanticRepairCarrierSpecificComparisonProvenance.degreeOneAdditiveComparisonData,
          SemanticRepairCarrierSpecificComparisonProvenance.c2SectionEquiv] using
            provenance.d1_face_to cochain)
      (by
        dsimp only
        intro cochain
        simpa [
          SelectedSectionFamilyCarrierModel.of_degreewise_carrier_data_and_c2_zero_equivalence,
          SemanticRepairCoverRelativeSectionFamilyWitness.of_selectedSectionFamilyCarrierModel,
          SelectedSectionFamilyCarrierModel.c1SectionEquiv,
          CarrierSpecificAdditiveComparisonData.toAddEquiv,
          SemanticRepairCarrierSpecificComparisonProvenance.degreeZeroAdditiveComparisonData,
          SemanticRepairCarrierSpecificComparisonProvenance.degreeOneAdditiveComparisonData,
          SemanticRepairCarrierSpecificComparisonProvenance.c2SectionEquiv] using
            provenance.d1_face_from cochain)

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
