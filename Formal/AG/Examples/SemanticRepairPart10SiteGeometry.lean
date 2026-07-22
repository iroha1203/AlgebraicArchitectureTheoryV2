import Formal.AG.Examples.SemanticRepairPart10

noncomputable section

namespace AAT.AG
namespace Examples
namespace SemanticRepairPart10

open CategoryTheory
open Opposite
open SemanticRepair

/-!
# #3719: site-geometry nonzero `H^1` witness (kite instance)

X.意味8.3 states that nontrivial `H^1` content comes from the geometry of the
cover.  The fixed circle witness of X.例9.2 discloses that its nerve is
supplied simplicial data over a single-object site with identity inclusions,
`C^2 = Empty`, and a vacuous `Z^1` condition.  This file adds the
complementary witness demanded by #3719: a cover-relative Cech complex over a
multi-chart AAT site whose overlap objects are definitionally the
chart-intersection meets and whose nerve incidence is certified against the
atom-level intersection geometry.

The selected *kite* cover has four charts `v0 v1 v2 v3`, five pairwise
overlaps `e01 e02 e12 e03 e23`, and one triple overlap `f012`.  Its geometric
content is two triangles sharing the edge `e02`: the triangle `v0 v1 v2` is
filled by the triple overlap, while the triangle `v0 v2 v3` is hollow, so the
loop `e02, e03, e23` carries a nonzero degree-one class over the law-equation
quotient coefficient `Q = ZZ/(2)`.

Site geometry, not supplied identities:

* charts are pairwise distinct contexts of `FiniteModel.object`, each strictly
  below the base context, so every `inclusion` is a morphism between distinct
  objects of the thin context category (hence not an identity morphism);
* overlap objects of the nerve are the finite-meet (`productContext`) of their
  endpoint charts inside the canonical restriction-morphism preorder, and each
  `faceRestriction` is the corresponding projection, again between distinct
  objects;
* the nerve incidence agrees with the actual atom-level overlap geometry: the
  five selected edges have nonempty chart intersections, the non-selected pair
  `v1, v3` has empty intersection, the selected triple `v0 v1 v2` has a common
  atom, and every other triple intersection is empty;
* `C^2` is nonempty, the degree-one differential fires on a non-cocycle, and
  the residual cocycle condition has a genuine computational proof, so
  `Z^1 = ker d^1` is non-vacuous.

Boundaries (disclosed, mirroring the X.例9.2 discipline):

* the witness-topology trick is kept.  The selected coverage requirements
  leave no admissible cover, so every covering sieve of the selected topology
  is top and the constant-observable law-equation quotient is a sheaf.  The
  site geometry behind the nerve lives in the context category and its finite
  meets; the Grothendieck topology side stays the degenerate witness
  topology, exactly as in the circle witness;
* the simplex sets are *selected* by the nonempty-intersection nerve rule and
  then certified against the atom-level intersection geometry by the decide
  theorems below.  The generated coefficient `Q` does not vanish on
  empty-overlap meet contexts (the obstruction ideal is `(2)` at every
  context), so dropping the empty intersections from the nerve is part of the
  selected nerve rule, not a consequence forced by the coefficient; on a
  full-tuple nerve that includes the empty overlaps, the residual would fail
  the cocycle condition at the `(v0, v1, v3)` triple;
* the four chart read-sets do not jointly cover the base read-set
  (`contractImpl` and `substitutesImplBase` are read only by the base
  context): the kite family is a chart family strictly below the base, not a
  covering family of it in either the atom-level or the topological sense,
  and the degree-one computation depends only on the pairwise and triple
  overlaps.
-/

/-! ## Kite nerve carriers -/

/-- #3719: the four chart indices / vertices of the kite cover. -/
inductive KiteVertex where
  | v0
  | v1
  | v2
  | v3
  deriving DecidableEq

/-- #3719: the five selected pairwise overlaps / edges of the kite cover. -/
inductive KiteEdge where
  | e01
  | e02
  | e12
  | e03
  | e23
  deriving DecidableEq

/-- #3719: the unique selected triple overlap / face of the kite cover. -/
inductive KiteFace where
  | f012
  deriving DecidableEq

instance : Fintype KiteVertex where
  elems := {KiteVertex.v0, KiteVertex.v1, KiteVertex.v2, KiteVertex.v3}
  complete := by intro v; cases v <;> decide

instance : Fintype KiteEdge where
  elems :=
    {KiteEdge.e01, KiteEdge.e02, KiteEdge.e12, KiteEdge.e03, KiteEdge.e23}
  complete := by intro e; cases e <;> decide

instance : Fintype KiteFace where
  elems := {KiteFace.f012}
  complete := by intro f; cases f; decide

/-- #3719: the two endpoint vertices of a selected kite edge. -/
def kiteEdgeVertices : KiteEdge -> KiteVertex × KiteVertex
  | .e01 => (.v0, .v1)
  | .e02 => (.v0, .v2)
  | .e12 => (.v1, .v2)
  | .e03 => (.v0, .v3)
  | .e23 => (.v2, .v3)

/-! ## Chart read-sets over the finite Atom universe -/

/--
#3719: decidable chart read-sets.  Chart `v` reads exactly the atoms of its
selected region:

* `v0` reads `componentA componentB dependsAB dependsCA`;
* `v1` reads `componentA componentB dependsBC`;
* `v2` reads `componentA dependsAB dependsBC contractBase`;
* `v3` reads `dependsCA contractBase`.

The pairwise intersections realize exactly the five selected edges, the
triple intersection `v0 v1 v2` is `{componentA}`, and every other triple as
well as the pair `v1, v3` is empty.  `componentC` is read by no chart, so all
read-sets stay inside the extracted object family.
-/
def kiteReadsB : KiteVertex -> FiniteModel.FiniteAtom -> Bool
  | .v0, .componentA => true
  | .v0, .componentB => true
  | .v0, .dependsAB => true
  | .v0, .dependsCA => true
  | .v1, .componentA => true
  | .v1, .componentB => true
  | .v1, .dependsBC => true
  | .v2, .componentA => true
  | .v2, .dependsAB => true
  | .v2, .dependsBC => true
  | .v2, .contractBase => true
  | .v3, .dependsCA => true
  | .v3, .contractBase => true
  | _, _ => false

/-- #3719: chart read-sets avoid the non-extracted atom `componentC`. -/
theorem kiteReadsB_ne_componentC {v : KiteVertex}
    {atom : FiniteModel.FiniteAtom} (h : kiteReadsB v atom = true) :
    atom ≠ FiniteModel.FiniteAtom.componentC := by
  intro hc
  subst hc
  cases v <;> exact absurd h (by decide)

/-- #3719: every atom read by a chart belongs to the extracted object family. -/
theorem kiteReadsB_mem_family {v : KiteVertex}
    {atom : FiniteModel.FiniteAtom} (h : kiteReadsB v atom = true) :
    FiniteModel.allFamily.mem atom :=
  FiniteModel.allFamily_mem atom (kiteReadsB_ne_componentC h)

/-! ## Chart contexts and the canonical restriction preorder -/

/-- #3719: the chart context of a kite vertex, reading its selected region. -/
def kiteChartCtx (v : KiteVertex) : Site.ArchCtx FiniteModel.object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ atom => kiteReadsB v atom = true
    supportReads_objectFamily := fun h => kiteReadsB_mem_family h
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/--
#3719: the kite site preorder is the canonical restriction-morphism preorder
on contexts of the finite object, not an equality preorder: distinct contexts
are related exactly when a restriction context morphism exists.
-/
noncomputable def kitePreorder : Site.ContextPreorderCategory FiniteModel.object :=
  Site.contextMorphismPreorderCategory FiniteModel.object

/-- #3719: finite meets for the kite preorder are the product contexts. -/
noncomputable def kiteMeet : Site.ContextFiniteMeet kitePreorder :=
  Site.productContextFiniteMeet

/-- #3719: the pairwise overlap context of an edge is the meet of its charts. -/
def kiteEdgeCtx (e : KiteEdge) : Site.ArchCtx FiniteModel.object :=
  Site.productContext (kiteChartCtx (kiteEdgeVertices e).1)
    (kiteChartCtx (kiteEdgeVertices e).2)

/-- #3719: the triple overlap context is the iterated meet of `v0 v1 v2`. -/
def kiteFaceCtx : Site.ArchCtx FiniteModel.object :=
  Site.productContext
    (Site.productContext (kiteChartCtx KiteVertex.v0) (kiteChartCtx KiteVertex.v1))
    (kiteChartCtx KiteVertex.v2)

/-- #3719: the trivial context morphism from a chart into the full base context. -/
def kiteChartToBaseMorphism (v : KiteVertex) :
    Site.ContextMorphism (kiteChartCtx v) FiniteModel.siteContext where
  supportMap _ := PUnit.unit
  axisMap _ := PUnit.unit
  observableRestrict _ := PUnit.unit

/-- #3719: the chart-to-base morphism is a restriction morphism. -/
theorem kiteChartToBaseMorphism_isRestriction (v : KiteVertex) :
    (kiteChartToBaseMorphism v).IsRestriction :=
  ⟨fun h => kiteReadsB_ne_componentC h,
    fun _ => trivial,
    fun _ => trivial,
    fun h => FiniteModel.allFamily_mem _ h⟩

/-- #3719: every chart context reads into the base context. -/
theorem kiteChartCtx_le_base (v : KiteVertex) :
    kitePreorder.le (kiteChartCtx v) FiniteModel.siteContext :=
  ⟨kiteChartToBaseMorphism v, kiteChartToBaseMorphism_isRestriction v⟩

/-- #3719: an edge overlap context reads into its first endpoint chart. -/
theorem kiteEdgeCtx_le_fst (e : KiteEdge) :
    kitePreorder.le (kiteEdgeCtx e) (kiteChartCtx (kiteEdgeVertices e).1) :=
  kiteMeet.meet_le_left _ _

/-- #3719: an edge overlap context reads into its second endpoint chart. -/
theorem kiteEdgeCtx_le_snd (e : KiteEdge) :
    kitePreorder.le (kiteEdgeCtx e) (kiteChartCtx (kiteEdgeVertices e).2) :=
  kiteMeet.meet_le_right _ _

/-- #3719: the triple overlap context reads into chart `v0`. -/
theorem kiteFaceCtx_le_v0 :
    kitePreorder.le kiteFaceCtx (kiteChartCtx KiteVertex.v0) :=
  kitePreorder.trans (kiteMeet.meet_le_left _ _) (kiteMeet.meet_le_left _ _)

/-- #3719: the triple overlap context reads into chart `v1`. -/
theorem kiteFaceCtx_le_v1 :
    kitePreorder.le kiteFaceCtx (kiteChartCtx KiteVertex.v1) :=
  kitePreorder.trans (kiteMeet.meet_le_left _ _) (kiteMeet.meet_le_right _ _)

/-- #3719: the triple overlap context reads into chart `v2`. -/
theorem kiteFaceCtx_le_v2 :
    kitePreorder.le kiteFaceCtx (kiteChartCtx KiteVertex.v2) :=
  kiteMeet.meet_le_right _ _

/-- #3719: the triple overlap context reads into the overlap of `v1 v2`. -/
theorem kiteFaceCtx_le_e12 :
    kitePreorder.le kiteFaceCtx (kiteEdgeCtx KiteEdge.e12) :=
  kiteMeet.le_meet kiteFaceCtx_le_v1 kiteFaceCtx_le_v2

/-- #3719: the triple overlap context reads into the overlap of `v0 v2`. -/
theorem kiteFaceCtx_le_e02 :
    kitePreorder.le kiteFaceCtx (kiteEdgeCtx KiteEdge.e02) :=
  kiteMeet.le_meet kiteFaceCtx_le_v0 kiteFaceCtx_le_v2

/-- #3719: the triple overlap context reads into the overlap of `v0 v1`. -/
theorem kiteFaceCtx_le_e01 :
    kitePreorder.le kiteFaceCtx (kiteEdgeCtx KiteEdge.e01) :=
  kiteMeet.le_meet kiteFaceCtx_le_v0 kiteFaceCtx_le_v1

/-! ## Distinctness of the selected contexts -/

/--
#3719: two contexts differ whenever some atom is readable in the first and
unreadable in the second.  This is the lever for all non-identity statements
below: in the thin context category, a morphism between distinct objects is
never an identity morphism.
-/
theorem kiteCtx_ne_of_reads {W V : Site.ArchCtx FiniteModel.object}
    (atom : FiniteModel.FiniteAtom)
    (hW : ∃ s : W.Support, W.minimal.supportReads s atom)
    (hV : ¬ ∃ s : V.Support, V.minimal.supportReads s atom) :
    W ≠ V := by
  intro h
  exact hV (Eq.mp (congrArg (fun X : Site.ArchCtx FiniteModel.object =>
    ∃ s : X.Support, X.minimal.supportReads s atom) h) hW)

/-- #3719: no chart context reads `contractImpl`, but the base context does. -/
theorem kiteChartCtx_ne_base (v : KiteVertex) :
    kiteChartCtx v ≠ FiniteModel.siteContext := by
  refine Ne.symm (kiteCtx_ne_of_reads FiniteModel.FiniteAtom.contractImpl
    ⟨PUnit.unit, ?_⟩ ?_)
  · show FiniteModel.FiniteAtom.contractImpl ≠ FiniteModel.FiniteAtom.componentC
    decide
  · rintro ⟨_, hs⟩
    have hs' : kiteReadsB v FiniteModel.FiniteAtom.contractImpl = true := hs
    cases v <;> exact absurd hs' (by decide)

/-- #3719: distinct kite vertices select distinct chart contexts. -/
theorem kiteChartCtx_injective : Function.Injective kiteChartCtx := by
  have ne : ∀ (v w : KiteVertex) (atom : FiniteModel.FiniteAtom),
      kiteReadsB v atom = true -> kiteReadsB w atom = false ->
      kiteChartCtx v ≠ kiteChartCtx w := by
    intro v w atom hv hw
    refine kiteCtx_ne_of_reads atom ⟨PUnit.unit, hv⟩ ?_
    rintro ⟨_, hs⟩
    have hs' : kiteReadsB w atom = true := hs
    rw [hw] at hs'
    exact Bool.noConfusion hs'
  intro v w h
  cases v <;> cases w <;>
    first
      | rfl
      | exact absurd h
          (ne _ _ FiniteModel.FiniteAtom.componentA (by decide) (by decide))
      | exact absurd h
          (ne _ _ FiniteModel.FiniteAtom.componentB (by decide) (by decide))
      | exact absurd h
          (ne _ _ FiniteModel.FiniteAtom.dependsAB (by decide) (by decide))
      | exact absurd h
          (ne _ _ FiniteModel.FiniteAtom.dependsBC (by decide) (by decide))
      | exact absurd h
          (ne _ _ FiniteModel.FiniteAtom.dependsCA (by decide) (by decide))
      | exact absurd h
          (ne _ _ FiniteModel.FiniteAtom.contractBase (by decide) (by decide))

/-- #3719: an atom read by the first endpoint chart but not by the second. -/
def kiteEdgeFstOnlyAtom : KiteEdge -> FiniteModel.FiniteAtom
  | .e01 => FiniteModel.FiniteAtom.dependsAB
  | .e02 => FiniteModel.FiniteAtom.componentB
  | .e12 => FiniteModel.FiniteAtom.componentB
  | .e03 => FiniteModel.FiniteAtom.componentB
  | .e23 => FiniteModel.FiniteAtom.dependsAB

/-- #3719: an atom read by the second endpoint chart but not by the first. -/
def kiteEdgeSndOnlyAtom : KiteEdge -> FiniteModel.FiniteAtom
  | .e01 => FiniteModel.FiniteAtom.dependsBC
  | .e02 => FiniteModel.FiniteAtom.dependsBC
  | .e12 => FiniteModel.FiniteAtom.contractBase
  | .e03 => FiniteModel.FiniteAtom.contractBase
  | .e23 => FiniteModel.FiniteAtom.dependsCA

/-- #3719: an edge overlap context differs from its first endpoint chart. -/
theorem kiteEdgeCtx_ne_fst (e : KiteEdge) :
    kiteEdgeCtx e ≠ kiteChartCtx (kiteEdgeVertices e).1 := by
  refine Ne.symm (kiteCtx_ne_of_reads (kiteEdgeFstOnlyAtom e)
    ⟨PUnit.unit, ?_⟩ ?_)
  · show kiteReadsB (kiteEdgeVertices e).1 (kiteEdgeFstOnlyAtom e) = true
    cases e <;> decide
  · rintro ⟨_, _hfst, hsnd⟩
    have hs' : kiteReadsB (kiteEdgeVertices e).2 (kiteEdgeFstOnlyAtom e) = true :=
      hsnd
    cases e <;> exact absurd hs' (by decide)

/-- #3719: an edge overlap context differs from its second endpoint chart. -/
theorem kiteEdgeCtx_ne_snd (e : KiteEdge) :
    kiteEdgeCtx e ≠ kiteChartCtx (kiteEdgeVertices e).2 := by
  refine Ne.symm (kiteCtx_ne_of_reads (kiteEdgeSndOnlyAtom e)
    ⟨PUnit.unit, ?_⟩ ?_)
  · show kiteReadsB (kiteEdgeVertices e).2 (kiteEdgeSndOnlyAtom e) = true
    cases e <;> decide
  · rintro ⟨_, hfst, _hsnd⟩
    have hs' : kiteReadsB (kiteEdgeVertices e).1 (kiteEdgeSndOnlyAtom e) = true :=
      hfst
    cases e <;> exact absurd hs' (by decide)

/-- #3719: the triple overlap context differs from each of its three edges. -/
theorem kiteFaceCtx_ne_edges :
    kiteFaceCtx ≠ kiteEdgeCtx KiteEdge.e12 ∧
      kiteFaceCtx ≠ kiteEdgeCtx KiteEdge.e02 ∧
        kiteFaceCtx ≠ kiteEdgeCtx KiteEdge.e01 := by
  refine ⟨?_, ?_, ?_⟩
  · refine Ne.symm (kiteCtx_ne_of_reads FiniteModel.FiniteAtom.dependsBC
      ⟨⟨PUnit.unit, PUnit.unit⟩, ?_, ?_⟩ ?_)
    · show kiteReadsB KiteVertex.v1 FiniteModel.FiniteAtom.dependsBC = true
      decide
    · show kiteReadsB KiteVertex.v2 FiniteModel.FiniteAtom.dependsBC = true
      decide
    · rintro ⟨_, ⟨h0, _h1⟩, _h2⟩
      have h0' : kiteReadsB KiteVertex.v0 FiniteModel.FiniteAtom.dependsBC = true :=
        h0
      exact absurd h0' (by decide)
  · refine Ne.symm (kiteCtx_ne_of_reads FiniteModel.FiniteAtom.dependsAB
      ⟨⟨PUnit.unit, PUnit.unit⟩, ?_, ?_⟩ ?_)
    · show kiteReadsB KiteVertex.v0 FiniteModel.FiniteAtom.dependsAB = true
      decide
    · show kiteReadsB KiteVertex.v2 FiniteModel.FiniteAtom.dependsAB = true
      decide
    · rintro ⟨_, ⟨_h0, h1⟩, _h2⟩
      have h1' : kiteReadsB KiteVertex.v1 FiniteModel.FiniteAtom.dependsAB = true :=
        h1
      exact absurd h1' (by decide)
  · refine Ne.symm (kiteCtx_ne_of_reads FiniteModel.FiniteAtom.componentB
      ⟨⟨PUnit.unit, PUnit.unit⟩, ?_, ?_⟩ ?_)
    · show kiteReadsB KiteVertex.v0 FiniteModel.FiniteAtom.componentB = true
      decide
    · show kiteReadsB KiteVertex.v1 FiniteModel.FiniteAtom.componentB = true
      decide
    · rintro ⟨_, _h01, h2⟩
      have h2' : kiteReadsB KiteVertex.v2 FiniteModel.FiniteAtom.componentB = true :=
        h2
      exact absurd h2' (by decide)

/-! ## Nerve incidence agrees with the atom-level overlap geometry -/

/-- #3719: every selected edge has a genuinely overlapping pair of charts. -/
theorem kiteEdges_overlap_nonempty (e : KiteEdge) :
    ∃ atom : FiniteModel.FiniteAtom,
      kiteReadsB (kiteEdgeVertices e).1 atom = true ∧
        kiteReadsB (kiteEdgeVertices e).2 atom = true := by
  cases e
  · exact ⟨FiniteModel.FiniteAtom.componentB, by decide, by decide⟩
  · exact ⟨FiniteModel.FiniteAtom.dependsAB, by decide, by decide⟩
  · exact ⟨FiniteModel.FiniteAtom.dependsBC, by decide, by decide⟩
  · exact ⟨FiniteModel.FiniteAtom.dependsCA, by decide, by decide⟩
  · exact ⟨FiniteModel.FiniteAtom.contractBase, by decide, by decide⟩

/-- #3719: the unselected chart pair `v1, v3` genuinely does not overlap. -/
theorem kiteNonEdge_v1_v3_empty (atom : FiniteModel.FiniteAtom) :
    ¬ (kiteReadsB KiteVertex.v1 atom = true ∧
        kiteReadsB KiteVertex.v3 atom = true) := by
  cases atom <;> decide

/-- #3719: the selected triple overlap `v0 v1 v2` has a common atom. -/
theorem kiteTriple_overlap_nonempty :
    kiteReadsB KiteVertex.v0 FiniteModel.FiniteAtom.componentA = true ∧
      kiteReadsB KiteVertex.v1 FiniteModel.FiniteAtom.componentA = true ∧
        kiteReadsB KiteVertex.v2 FiniteModel.FiniteAtom.componentA = true := by
  decide

/-- #3719: every unselected triple of charts has empty intersection. -/
theorem kiteOtherTriples_empty (atom : FiniteModel.FiniteAtom) :
    ¬ (kiteReadsB KiteVertex.v0 atom = true ∧
        kiteReadsB KiteVertex.v1 atom = true ∧
          kiteReadsB KiteVertex.v3 atom = true) ∧
      ¬ (kiteReadsB KiteVertex.v0 atom = true ∧
          kiteReadsB KiteVertex.v2 atom = true ∧
            kiteReadsB KiteVertex.v3 atom = true) ∧
        ¬ (kiteReadsB KiteVertex.v1 atom = true ∧
            kiteReadsB KiteVertex.v2 atom = true ∧
              kiteReadsB KiteVertex.v3 atom = true) := by
  cases atom <;> decide

/-! ## Kite witness site -/

/-- #3719: generated finite core specialized to the kite context preorder. -/
noncomputable def kiteCorePackage : AATCorePackage FiniteModel.carrier :=
  FiniteModel.corePackageFor kitePreorder

/--
#3719: degenerate witness-site coverage requirements for the kite site.

Exactly as in X.例9.2, these requirements deliberately leave no admissible
cover, so the generated topology is the top-only witness topology and the
constant-observable law-equation quotient below is a sheaf.  The multi-chart
geometry of the kite cover lives in the context category and its meets, not
in this topology selection.
-/
def kiteCoverageRequirements :
    Site.CoverageRequirements FiniteModel.object
      kiteCorePackage.equationSystem FiniteModel.signature where
  requiredSupport := fun _ => True
  requiredEquationCoordinate := fun _ => False
  selectedViolationWitness := fun _ => False
  requiredAxis := fun _ => False
  supportVisibleOn := fun _ _ => False
  equationCoordinateVisibleOn := fun _ _ => False
  violationWitnessVisibleOn := fun _ _ => False
  axisReadableOn := fun _ _ => False
  boundaryVisibleOn := fun _ _ => False

/-- #3719: meet-based overlap pullback data on the kite preorder. -/
noncomputable def kiteSiteOverlap : Site.ContextOverlapPullback kitePreorder :=
  Site.meetOverlapPullback kitePreorder kiteMeet

/-- #3719: generated-core geometry reading for the kite witness site. -/
noncomputable def kiteGeometryReading :
    Site.SelectedGeometryReading kiteCorePackage where
  requirements := kiteCoverageRequirements
  overlap := kiteSiteOverlap

/-- #3719: the kite witness site over the generated finite core object. -/
noncomputable def kiteSite : Site.AATSite kiteCorePackage.object :=
  kiteGeometryReading.toAATSite

/-- #3719: the kite topology is generated from its selected coverage. -/
theorem kiteSite_topology_eq_generated :
    kiteSite.topology =
      Site.AATGrothendieckTopology kiteCoverageRequirements kiteSiteOverlap :=
  Site.SelectedGeometryReading.topology_eq_generated kiteGeometryReading

/-- #3719: the base object of the kite site is the full base context. -/
def kiteSiteBase : kiteSite.category :=
  Site.ContextCategoryObject.of kitePreorder FiniteModel.siteContext

/-- #3719: chart objects of the kite site. -/
def kiteChartObj (v : KiteVertex) : kiteSite.category :=
  Site.ContextCategoryObject.of kitePreorder (kiteChartCtx v)

/-- #3719: no admissible cover exists for the kite witness topology. -/
theorem kiteCoverageFamily_impossible {base : kiteSite.category}
    (F : Site.AATCoverageFamily kiteCoverageRequirements
      kiteSiteOverlap base) :
    False := by
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentA trivial with ⟨i, hi⟩
  exact hi

/-- #3719: every covering sieve in the kite witness topology is top. -/
theorem kiteSiteTopology_cover_eq_top {base : kiteSite.category}
    {cover : Sieve base} (hcover : cover ∈ kiteSite.topology base) :
    cover = ⊤ := by
  rw [kiteSite_topology_eq_generated] at hcover
  change
    (Site.admissiblePrecoverage kiteCoverageRequirements
      kiteSiteOverlap).Saturate base cover at hcover
  induction hcover with
  | of _X _S hS =>
      rcases hS with ⟨F, rfl⟩
      exact False.elim (kiteCoverageFamily_impossible F)
  | top _X =>
      rfl
  | pullback _X _S _hS _Y _f ih =>
      rw [ih, Sieve.pullback_top]
  | transitive X S R _hS hR ihS ihR =>
      rw [← Sieve.id_mem_iff_eq_top]
      have hSid : S (𝟙 X) := by
        rw [Sieve.id_mem_iff_eq_top, ihS]
      have hlocal : R = ⊤ := by
        simpa using ihR hSid
      rw [hlocal]
      trivial

/-! ## Law-equation quotient coefficient on the kite site -/

/--
#3719: production law-equation core with observable ring `ZZ` and constant
violation witness `2` on the kite site, mirroring the X.例9.1/9.2 integer
core so the coefficient is generated, not supplied.
-/
def kiteLawCore :
    LawAlgebra.SemanticLawEquationWitnessIdealCore kiteSite where
  Observable _ := ℤ
  observableCommRing _ := inferInstance
  restrict _ := RingHom.id ℤ
  restrict_id := by
    intro _W x
    rfl
  restrict_comp := by
    intro _W₀ _W₁ _W₂ _f _g x
    rfl
  violationWitness _ _ _ := (2 : ℤ)
  violationWitness_restrict := by
    intro _source _target _f _lawIndex _atom
    rfl
  supportAtom := FiniteModel.FiniteAtom.componentA
  supportLawIndex := PUnit.unit
  supportLawIndex_required := rfl

/-- #3719: generated quotient presheaf `ZZ / I_Ob` on the kite site. -/
abbrev kiteLawQuotientPresheaf : Site.AATPresheaf kiteSite :=
  kiteLawCore.obstructionQuotientPresheaf

/-- #3719: the law-equation quotient is a sheaf on the kite witness topology. -/
theorem kiteLawQuotientIsSheaf :
    Site.AATSheafCondition kiteSite kiteLawQuotientPresheaf := by
  intro _base cover hcover
  rw [Site.AATSheafConditionFor, kiteSiteTopology_cover_eq_top hcover]
  exact Presieve.isSheafFor_top kiteLawQuotientPresheaf

/-- #3719: every kite witness ideal is contained in `span {2}`. -/
theorem kiteLaw_lawWitnessIdeal_le (W : kiteSite.category)
    (lawIndex : kiteSite.equationSystem.toLegacyLawUniverse.Index) :
    kiteLawCore.lawWitnessIdeal W lawIndex ≤
      Ideal.span ({(2 : ℤ)} : Set ℤ) := by
  refine Ideal.span_le.mpr ?_
  rintro _x ⟨atom, rfl⟩
  exact Ideal.subset_span rfl

/-- #3719: the kite obstruction ideal is exactly `span {2}`. -/
theorem kiteLaw_obstructionIdeal_eq_span_two (W : kiteSite.category) :
    kiteLawCore.obstructionIdeal W =
      Ideal.span ({(2 : ℤ)} : Set ℤ) := by
  have hwitness :
      kiteLawCore.lawWitnessIdeal W PUnit.unit =
        Ideal.span ({(2 : ℤ)} : Set ℤ) := by
    dsimp [LawAlgebra.SemanticLawEquationWitnessIdealCore.lawWitnessIdeal,
      kiteLawCore]
    congr
    ext x
    constructor
    · rintro ⟨_atom, rfl⟩
      simp
    · intro hx
      exact ⟨FiniteModel.FiniteAtom.componentA, by simpa using hx.symm⟩
  apply le_antisymm
  · change
      (kiteLawCore.selectedLawWitnessIdealFamily W).localObstructionIdeal ≤
        Ideal.span ({(2 : ℤ)} : Set ℤ)
    rw [LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.localObstructionIdeal_le_iff]
    intro lawIndex _hselected
    cases lawIndex
    change kiteLawCore.lawWitnessIdeal W PUnit.unit ≤
      Ideal.span ({(2 : ℤ)} : Set ℤ)
    rw [hwitness]
  · rw [← hwitness]
    exact kiteLawCore.lawWitnessIdeal_le_obstructionIdeal W rfl

/-- #3719: the defect `1` is not killed by the kite obstruction ideal. -/
theorem kiteLaw_one_notMem_obstructionIdeal (W : kiteSite.category) :
    (1 : ℤ) ∉ kiteLawCore.obstructionIdeal W := by
  intro hmem
  rw [kiteLaw_obstructionIdeal_eq_span_two W, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  omega

/-- #3719: selected coefficient `Q = ZZ / I_Ob` at the kite base. -/
abbrev KiteLawQuotient := kiteLawCore.ObstructionQuotient kiteSiteBase

/-- #3719: the residual value is the quotient class `[1] ∈ Q`. -/
def kiteLawQuotientOne : KiteLawQuotient :=
  Ideal.Quotient.mk (kiteLawCore.obstructionIdeal kiteSiteBase) (1 : ℤ)

/-- #3719: `[1]` survives in the kite law-equation quotient. -/
theorem kiteLawQuotientOne_ne_zero : kiteLawQuotientOne ≠ 0 := by
  intro hzero
  exact kiteLaw_one_notMem_obstructionIdeal kiteSiteBase
    (Ideal.Quotient.eq_zero_iff_mem.mp hzero)

/-- #3719: the concrete kite law quotient is `ZZ/(2) ≅ F₂`. -/
noncomputable def kiteLawQuotientEquivF2 : KiteLawQuotient ≃+* ZMod 2 :=
  (Ideal.quotEquivOfEq (kiteLaw_obstructionIdeal_eq_span_two kiteSiteBase)).trans
    (Int.quotientSpanNatEquivZMod 2)

/-- #3719: under `Q ≅ F₂`, the selected residual value `[1]` maps to `1`. -/
theorem kiteLawQuotientOne_toF2 :
    kiteLawQuotientEquivF2 kiteLawQuotientOne = (1 : ZMod 2) := by
  change (Int.quotientSpanNatEquivZMod 2)
    (Ideal.quotEquivOfEq (kiteLaw_obstructionIdeal_eq_span_two kiteSiteBase)
      (Ideal.Quotient.mk (kiteLawCore.obstructionIdeal kiteSiteBase) (1 : ℤ))) = 1
  rw [Ideal.quotEquivOfEq_mk]
  rfl

/-- #3719: obstruction coefficient sheaf from the kite law-equation quotient. -/
def kiteObstructionSheaf : Cohomology.ObstructionSheaf kiteSite :=
  Cohomology.ObstructionSheaf.ofAddCommGrpValued
    kiteLawCore.obstructionQuotientCoefficient kiteLawQuotientIsSheaf

/-- #3719: the generated quotient restriction acts as the identity on `Q`. -/
theorem kiteQuotientRestrict_apply {source target : kiteSite.category}
    (f : source ⟶ target) (x : KiteLawQuotient) :
    kiteLawCore.obstructionQuotientRestrict f x = x := by
  refine Quotient.inductionOn' x ?_
  intro r
  show kiteLawCore.obstructionQuotientRestrict f
      (Ideal.Quotient.mk (kiteLawCore.obstructionIdeal target) r) =
    Ideal.Quotient.mk (kiteLawCore.obstructionIdeal target) r
  rw [kiteLawCore.obstructionQuotientRestrict_mk]
  rfl

/-- #3719: the obstruction sheaf restriction maps act as the identity on `Q`. -/
theorem kiteSheafMap_apply {source target : kiteSite.category}
    (f : source ⟶ target) (x : KiteLawQuotient) :
    kiteObstructionSheaf.carrier.toPresheaf.map f.op x = x :=
  kiteQuotientRestrict_apply f x

/-! ## Kite nerve and cover -/

/-- #3719: kite nerve simplices: four vertices, five edges, one face. -/
def kiteSimplex : Nat -> Type
  | 0 => KiteVertex
  | 1 => KiteEdge
  | 2 => KiteFace
  | _ + 3 => Empty

/--
#3719: nerve face maps.  Degree-zero faces select the edge endpoints (face `0`
drops the first vertex); degree-one faces are the three boundary edges of
`f012` in the standard order `e12, e02, e01`.
-/
def kiteFaceMap : ∀ n : Nat, Fin (n + 2) -> kiteSimplex (n + 1) -> kiteSimplex n
  | 0, i, e => if i.val = 0 then (kiteEdgeVertices e).2 else (kiteEdgeVertices e).1
  | 1, i, _f =>
      if i.val = 0 then KiteEdge.e12
      else if i.val = 1 then KiteEdge.e02
      else KiteEdge.e01
  | _ + 2, _i, σ => Empty.elim σ

/-- #3719: nerve overlap contexts are the selected chart meets. -/
def kiteOverlapCtx : ∀ n : Nat, kiteSimplex n -> Site.ArchCtx FiniteModel.object
  | 0, v => kiteChartCtx v
  | 1, e => kiteEdgeCtx e
  | 2, _f => kiteFaceCtx
  | _ + 3, σ => Empty.elim σ

/-- #3719: every nerve overlap reads into the overlap of each of its faces. -/
theorem kiteOverlap_le :
    ∀ (n : Nat) (i : Fin (n + 2)) (σ : kiteSimplex (n + 1)),
      kitePreorder.le (kiteOverlapCtx (n + 1) σ)
        (kiteOverlapCtx n (kiteFaceMap n i σ))
  | 0, ⟨0, _⟩, e => kiteEdgeCtx_le_snd e
  | 0, ⟨1, _⟩, e => kiteEdgeCtx_le_fst e
  | 0, ⟨n + 2, h⟩, _e => absurd h (by omega)
  | 1, ⟨0, _⟩, _f => kiteFaceCtx_le_e12
  | 1, ⟨1, _⟩, _f => kiteFaceCtx_le_e02
  | 1, ⟨2, _⟩, _f => kiteFaceCtx_le_e01
  | 1, ⟨n + 3, h⟩, _f => absurd h (by omega)
  | _ + 2, _i, σ => Empty.elim σ

/--
#3719: the kite cover.  Four charts on the multi-chart witness site; the
nerve is generated from the chart-intersection meets, every inclusion and
face restriction is a morphism between distinct objects of the thin context
category (see the non-identity theorems below).
-/
noncomputable def kiteCoverRelativeCover :
    Cohomology.CoverRelativeCechCover kiteSite where
  base := kiteSiteBase
  Index := KiteVertex
  chart := kiteChartObj
  inclusion v := homOfLE (kiteChartCtx_le_base v)
  simplex := kiteSimplex
  overlap n σ := Site.ContextCategoryObject.of kitePreorder (kiteOverlapCtx n σ)
  face := kiteFaceMap
  faceRestriction n i σ := homOfLE (kiteOverlap_le n i σ)

/-- #3719: degree-one nerve overlaps are definitionally the chart meets. -/
theorem kiteCover_overlap_eq_meet (e : KiteEdge) :
    (kiteCoverRelativeCover.overlap 1 e).ctx =
      kiteMeet.meet (kiteChartCtx (kiteEdgeVertices e).1)
        (kiteChartCtx (kiteEdgeVertices e).2) :=
  rfl

/-- #3719: the triple nerve overlap is definitionally the iterated chart meet. -/
theorem kiteCover_tripleOverlap_eq_meet (f : KiteFace) :
    (kiteCoverRelativeCover.overlap 2 f).ctx =
      kiteMeet.meet
        (kiteMeet.meet (kiteChartCtx KiteVertex.v0) (kiteChartCtx KiteVertex.v1))
        (kiteChartCtx KiteVertex.v2) :=
  rfl

/-! ## Kite cover-relative Cech complex -/

/-- #3719: kite C0 cochains over `Q = ZZ/(2)`. -/
abbrev kiteC0 : Type := KiteVertex -> KiteLawQuotient

/-- #3719: kite C1 cochains. -/
abbrev kiteC1 : Type := KiteEdge -> KiteLawQuotient

/-- #3719: kite C2 cochains over the nonempty face carrier. -/
abbrev kiteC2 : Type := KiteFace -> KiteLawQuotient

/-- #3719: kite Cech coboundary `d0`. -/
def kiteD0 (cochain : kiteC0) : kiteC1 :=
  fun e => cochain (kiteEdgeVertices e).2 - cochain (kiteEdgeVertices e).1

/-- #3719: kite Cech coboundary `d1`, alternating over the faces of `f012`. -/
def kiteD1 (cochain : kiteC1) : kiteC2 :=
  fun _f =>
    cochain KiteEdge.e12 - cochain KiteEdge.e02 + cochain KiteEdge.e01

/-- #3719: uniform component groups of the kite cochain surfaces. -/
def kiteCochainComponentGroup :
    ∀ (n : Nat) (σ : kiteSimplex n),
      AddCommGroup
        (kiteObstructionSheaf.carrier.toPresheaf.obj
          (op (kiteCoverRelativeCover.overlap n σ)))
  | 0, _v => inferInstanceAs (AddCommGroup KiteLawQuotient)
  | 1, _e => inferInstanceAs (AddCommGroup KiteLawQuotient)
  | 2, _f => inferInstanceAs (AddCommGroup KiteLawQuotient)
  | _ + 3, σ => Empty.elim σ

/-- #3719: the kite cover-relative Cech complex over `Q = ZZ/(2)`. -/
noncomputable def kiteCoverRelativeComplex :
    Cohomology.CoverRelativeCechComplex
      kiteCoverRelativeCover kiteObstructionSheaf where
  cochainAddCommGroup n := by
    letI := kiteCochainComponentGroup n
    exact Pi.addCommGroup
  alternatingFaceCombination
    | 0, terms => fun e =>
        (terms e 0 : KiteLawQuotient) - (terms e 1 : KiteLawQuotient)
    | 1, terms => fun f =>
        (terms f 0 : KiteLawQuotient) - (terms f 1 : KiteLawQuotient) +
          (terms f 2 : KiteLawQuotient)
    | _ + 2, _terms => fun σ => Empty.elim σ
  differential
    | 0 => by
        change kiteC0 →+ kiteC1
        exact {
          toFun := kiteD0
          map_zero' := by
            funext e
            simp [kiteD0]
          map_add' := by
            intro left right
            funext e
            simp [kiteD0]
            abel
        }
    | 1 => by
        change kiteC1 →+ kiteC2
        exact {
          toFun := kiteD1
          map_zero' := by
            funext f
            simp [kiteD1]
          map_add' := by
            intro left right
            funext f
            simp [kiteD1]
            abel
        }
    | n + 2 => by
        letI := kiteCochainComponentGroup (n + 2)
        letI := kiteCochainComponentGroup (n + 3)
        change ((σ : kiteSimplex (n + 2)) ->
            kiteObstructionSheaf.carrier.toPresheaf.obj
              (op (kiteCoverRelativeCover.overlap (n + 2) σ))) →+
          ((σ : kiteSimplex (n + 3)) ->
            kiteObstructionSheaf.carrier.toPresheaf.obj
              (op (kiteCoverRelativeCover.overlap (n + 3) σ)))
        refine {
          toFun := fun _ => fun σ => Empty.elim σ
          map_zero' := ?_
          map_add' := ?_ }
        · funext σ
          exact Empty.elim σ
        · intro _left _right
          funext σ
          exact Empty.elim σ
  differential_eq_alternatingFaceCombination := by
    intro n c
    match n with
    | 0 =>
        funext e
        show kiteD0 c e =
          (kiteObstructionSheaf.carrier.toPresheaf.map
              (kiteCoverRelativeCover.faceRestriction 0 0 e).op
              (c (kiteCoverRelativeCover.face 0 0 e)) : KiteLawQuotient) -
            (kiteObstructionSheaf.carrier.toPresheaf.map
              (kiteCoverRelativeCover.faceRestriction 0 1 e).op
              (c (kiteCoverRelativeCover.face 0 1 e)) : KiteLawQuotient)
        rw [kiteSheafMap_apply, kiteSheafMap_apply]
        rfl
    | 1 =>
        funext f
        show kiteD1 c f =
          (kiteObstructionSheaf.carrier.toPresheaf.map
              (kiteCoverRelativeCover.faceRestriction 1 0 f).op
              (c (kiteCoverRelativeCover.face 1 0 f)) : KiteLawQuotient) -
            (kiteObstructionSheaf.carrier.toPresheaf.map
              (kiteCoverRelativeCover.faceRestriction 1 1 f).op
              (c (kiteCoverRelativeCover.face 1 1 f)) : KiteLawQuotient) +
            (kiteObstructionSheaf.carrier.toPresheaf.map
              (kiteCoverRelativeCover.faceRestriction 1 2 f).op
              (c (kiteCoverRelativeCover.face 1 2 f)) : KiteLawQuotient)
        rw [kiteSheafMap_apply, kiteSheafMap_apply, kiteSheafMap_apply]
        rfl
    | n + 2 =>
        funext σ
        exact Empty.elim σ
  differential_comp := by
    intro n c
    match n with
    | 0 =>
        funext f
        cases f
        show kiteD1 (kiteD0 c) KiteFace.f012 = 0
        show kiteD0 c KiteEdge.e12 - kiteD0 c KiteEdge.e02 +
            kiteD0 c KiteEdge.e01 = 0
        simp [kiteD0, kiteEdgeVertices]
    | n + 1 =>
        funext σ
        exact Empty.elim σ

/-! ## Nonzero `H^1` class and non-vacuous `Z^1` -/

/-- #3719: residual one-cochain `[1]` supported on the hollow-loop edge `e03`. -/
def kiteResidual : kiteC1 :=
  fun e => if e = KiteEdge.e03 then kiteLawQuotientOne else 0

/-- #3719: the zero one-cochain. -/
def kiteZero1 : kiteC1 :=
  fun _ => 0

/--
#3719 (Z^1 positive): the residual satisfies the cocycle condition by a real
computation over the nonempty `C^2`, not by `Empty.elim`.
-/
theorem kiteResidual_cocycle : kiteD1 kiteResidual = 0 := by
  funext f
  cases f
  show kiteResidual KiteEdge.e12 - kiteResidual KiteEdge.e02 +
      kiteResidual KiteEdge.e01 = 0
  simp [kiteResidual]

/-- #3719: indicator one-cochain `[1]` on the filled-triangle edge `e01`. -/
def kiteIndicatorE01 : kiteC1 :=
  fun e => if e = KiteEdge.e01 then kiteLawQuotientOne else 0

/--
#3719 (Z^1 negative): the indicator of `e01` violates the cocycle condition,
so `Z^1 = ker d^1` genuinely constrains one-cochains on the kite nerve.
-/
theorem kiteIndicatorE01_not_cocycle : kiteD1 kiteIndicatorE01 ≠ 0 := by
  intro h
  have hf : kiteIndicatorE01 KiteEdge.e12 - kiteIndicatorE01 KiteEdge.e02 +
      kiteIndicatorE01 KiteEdge.e01 = 0 :=
    congrFun h KiteFace.f012
  apply kiteLawQuotientOne_ne_zero
  simpa [kiteIndicatorE01] using hf

/-- #3719: the degree-one differential is not the constant zero map. -/
theorem kiteDelta1_not_constant_zero : ∃ cochain : kiteC1, kiteD1 cochain ≠ 0 :=
  ⟨kiteIndicatorE01, kiteIndicatorE01_not_cocycle⟩

/-- #3719: the residual `([1] on e03)` is not a kite coboundary. -/
theorem kiteResidual_not_coboundary :
    ¬ ∃ primitive : kiteC0, kiteResidual - kiteZero1 = kiteD0 primitive := by
  rintro ⟨primitive, hprimitive⟩
  have h01 := congrFun hprimitive KiteEdge.e01
  have h12 := congrFun hprimitive KiteEdge.e12
  have h23 := congrFun hprimitive KiteEdge.e23
  have h03 := congrFun hprimitive KiteEdge.e03
  simp [kiteResidual, kiteZero1, kiteD0, kiteEdgeVertices] at h01 h12 h23 h03
  have heq1 : primitive KiteVertex.v1 = primitive KiteVertex.v0 :=
    sub_eq_zero.mp h01.symm
  have heq2 : primitive KiteVertex.v2 = primitive KiteVertex.v1 :=
    sub_eq_zero.mp h12.symm
  have heq3 : primitive KiteVertex.v3 = primitive KiteVertex.v2 :=
    sub_eq_zero.mp h23.symm
  apply kiteLawQuotientOne_ne_zero
  calc
    kiteLawQuotientOne = primitive KiteVertex.v3 - primitive KiteVertex.v0 := h03
    _ = 0 := by rw [heq3, heq2, heq1]; exact sub_self _

/-- #3719: selected cover-relative residual cocycle. -/
def kiteCoverRelativeResidualCocycle :
    kiteCoverRelativeComplex.CechCocycle 1 where
  val := kiteResidual
  property := kiteResidual_cocycle

/-- #3719: selected cover-relative zero cocycle. -/
def kiteCoverRelativeZeroCocycle :
    kiteCoverRelativeComplex.CechCocycle 1 where
  val := kiteZero1
  property := by
    funext f
    cases f
    show kiteZero1 KiteEdge.e12 - kiteZero1 KiteEdge.e02 +
        kiteZero1 KiteEdge.e01 = 0
    simp [kiteZero1]

/-- #3719: selected cover-relative residual class. -/
def kiteCoverRelativeResidualClass :
    kiteCoverRelativeComplex.CechCohomologySucc 0 :=
  kiteCoverRelativeComplex.cohomologyClassSucc 0 kiteCoverRelativeResidualCocycle

/-- #3719: selected cover-relative zero class. -/
def kiteCoverRelativeZeroClass :
    kiteCoverRelativeComplex.CechCohomologySucc 0 :=
  kiteCoverRelativeComplex.cohomologyClassSucc 0 kiteCoverRelativeZeroCocycle

/-- #3719: the kite residual cocycle is not a cover-relative coboundary. -/
theorem kiteCoverRelative_residual_not_coboundary :
    ¬ (kiteCoverRelativeComplex.CechCoboundarySetoidSucc 0).r
      kiteCoverRelativeResidualCocycle kiteCoverRelativeZeroCocycle := by
  rintro ⟨primitive, hprimitive⟩
  have hzero : kiteResidual - kiteZero1 = kiteD0 primitive := hprimitive
  exact kiteResidual_not_coboundary ⟨primitive, hzero⟩

/--
#3719: the residual class generated by the hollow-loop geometry of the kite
cover is nonzero in cover-relative `H^1`.
-/
theorem kiteCoverRelativeH1_nonzero :
    kiteCoverRelativeResidualClass ≠ kiteCoverRelativeZeroClass := by
  intro hzero
  exact kiteCoverRelative_residual_not_coboundary (Quotient.exact hzero)

/-! ## Shape and non-identity audit surface -/

instance kiteNerve_vertex_fintype : Fintype (kiteSimplex 0) := by
  change Fintype KiteVertex
  infer_instance

instance kiteNerve_edge_fintype : Fintype (kiteSimplex 1) := by
  change Fintype KiteEdge
  infer_instance

instance kiteNerve_face_fintype : Fintype (kiteSimplex 2) := by
  change Fintype KiteFace
  infer_instance

/-- #3719: the kite nerve has four charts, five edges, and one face. -/
theorem kiteNerve_shape :
    Fintype.card (kiteSimplex 0) = 4 ∧ Fintype.card (kiteSimplex 1) = 5 ∧
      Fintype.card (kiteSimplex 2) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- #3719: `C^2` is generated over a nonempty face carrier. -/
theorem kiteNerve_face_nonempty : Nonempty (kiteSimplex 2) :=
  ⟨KiteFace.f012⟩

/-- #3719: the four charts of the kite cover are pairwise distinct objects. -/
theorem kiteCover_charts_injective :
    Function.Injective kiteCoverRelativeCover.chart := by
  intro v w h
  exact kiteChartCtx_injective (congrArg Site.ContextCategoryObject.ctx h)

/--
#3719: every chart inclusion of the kite cover has source distinct from its
target base object; in the thin context category a morphism between distinct
objects is never an identity morphism.
-/
theorem kiteCover_chart_ne_base (v : KiteVertex) :
    kiteCoverRelativeCover.chart v ≠ kiteCoverRelativeCover.base := by
  intro h
  exact kiteChartCtx_ne_base v (congrArg Site.ContextCategoryObject.ctx h)

/-- #3719: each degree-zero face restriction relates distinct objects. -/
theorem kiteCover_edgeOverlap_ne_chartOverlap (i : Fin 2) (e : KiteEdge) :
    kiteCoverRelativeCover.overlap 1 e ≠
      kiteCoverRelativeCover.overlap 0 (kiteCoverRelativeCover.face 0 i e) := by
  intro h
  have hctx := congrArg Site.ContextCategoryObject.ctx h
  rcases i with ⟨iv, hiv⟩
  rcases iv with _ | _ | iv
  · exact kiteEdgeCtx_ne_snd e hctx
  · exact kiteEdgeCtx_ne_fst e hctx
  · omega

/-- #3719: each degree-one face restriction relates distinct objects. -/
theorem kiteCover_faceOverlap_ne_edgeOverlap (i : Fin 3) (f : KiteFace) :
    kiteCoverRelativeCover.overlap 2 f ≠
      kiteCoverRelativeCover.overlap 1 (kiteCoverRelativeCover.face 1 i f) := by
  intro h
  have hctx := congrArg Site.ContextCategoryObject.ctx h
  rcases i with ⟨iv, hiv⟩
  rcases iv with _ | _ | _ | iv
  · exact kiteFaceCtx_ne_edges.1 hctx
  · exact kiteFaceCtx_ne_edges.2.1 hctx
  · exact kiteFaceCtx_ne_edges.2.2 hctx
  · omega

/--
#3719 summary packet: the kite instance has at least two charts, a nonempty
`C^2`, a firing (non-constant-zero) degree-one differential, a genuinely
cocyclic residual, and a nonzero cover-relative `H^1` class.
-/
theorem kiteSiteGeometry_witness_packet :
    (2 ≤ Fintype.card KiteVertex) ∧
      Nonempty (kiteSimplex 2) ∧
        (∃ cochain : kiteC1, kiteD1 cochain ≠ 0) ∧
          kiteD1 kiteResidual = 0 ∧
            kiteCoverRelativeResidualClass ≠ kiteCoverRelativeZeroClass :=
  ⟨by decide, kiteNerve_face_nonempty, kiteDelta1_not_constant_zero,
    kiteResidual_cocycle, kiteCoverRelativeH1_nonzero⟩

end SemanticRepairPart10
end Examples
end AAT.AG
