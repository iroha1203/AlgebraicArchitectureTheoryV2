import Formal.AG.SemanticRepair.Projection

noncomputable section

namespace AAT.AG
namespace SemanticRepair

universe u v w x y

/--
X.定義3.1: finite semantic repair-gluing complex.

The projection and finite cover datum are inherited from §2.  `C0` is the
supplied type of local repair primitives, `C1` is the supplied type of residual
gluing cochains, and `delta0` is the supplied restriction-difference map.  The
generated theorem layer below reads the selected residual cochain through the
boundary predicate `B1`; this structure does not assert arbitrary sheaf
cohomology or a global repair certificate by itself.
-/
structure FiniteSemanticRepairGluingComplex where
  projection : SemanticAtomProjection.{u, v}
  cover : FiniteSemanticRepairCoverDatum.{v, w, x} projection.Component
  C0 : Type y
  C1 : Type x
  primitiveFinite : Fintype C0
  cochainFinite : Fintype C1
  supportOf : C0 -> projection.Support
  delta0 : C0 -> C1
  residual : C1

namespace FiniteSemanticRepairGluingComplex

attribute [instance] primitiveFinite cochainFinite

end FiniteSemanticRepairGluingComplex

/--
X.定義3.1: full finite semantic repair-gluing complex.

This is the data-level presentation of the finite complex from the text: the
chart enumeration, every chart-pair overlap, both primitive restrictions, and
the cochain evaluator are explicit.  `restriction_difference` is supplied
finite-complex data, while the descent theorem is read through the existing
minimal complex after `toFiniteSemanticRepairGluingComplex` forgets this
presentation data.

Implementation notes: the minimal complex remains the target of the existing
boundary and semantic-coherence API, so this structure records the additional
Definition 3.1 data instead of changing that API.  Encoding the restrictions
as a separate certificate over the minimal complex would hide `resL`, `resR`,
and `ev` from the object whose differential they describe.

Boundary: `resL`, `resR`, `ev`, and `restriction_difference` are
Definition-3.1 presentation data.  Beyond the field projection
`delta0_ev_iff_restriction_xor` and fixture example theorems that exercise
these fields on concrete data, no general theorem consumes them; the §3
descent theorems are proved on the forgotten minimal complex and depend only
on the abstract `delta0` boundary structure, not on this presentation.
-/
structure FullFiniteSemanticRepairGluingComplex where
  /-- The semantic atom vocabulary and its component projection. -/
  projection : SemanticAtomProjection.{u, v}
  /-- The separately supplied cover datum used to read residual semantic atoms. -/
  cover : FiniteSemanticRepairCoverDatum.{v, w, x} projection.Component
  /-- The charts belonging to this finite gluing complex, independently of `cover.Chart`. -/
  Chart : Type w
  /-- Finiteness of the complex chart family. -/
  chartFinite : Fintype Chart
  /-- A complete finite enumeration of the complex charts. -/
  chartEnumeration : List Chart
  /-- Every complex chart occurs in `chartEnumeration`. -/
  chart_enumeration_complete : forall chart, chart ∈ chartEnumeration
  /-- The finite overlap components for each ordered pair of complex charts. -/
  Overlap : Chart -> Chart -> Type x
  /-- Finiteness of every chart-pair overlap family. -/
  overlapFinite : forall left right, Fintype (Overlap left right)
  /-- A complete finite enumeration of all chart-pair overlap components. -/
  overlapEnumeration : List (Sigma fun left : Chart =>
    Sigma fun right : Chart => Overlap left right)
  /-- Every chart-pair overlap component occurs in `overlapEnumeration`. -/
  overlap_enumeration_complete : forall overlap, overlap ∈ overlapEnumeration
  /-- The finite type of local repair primitives. -/
  C0 : Type y
  /-- The finite type of residual repair-gluing cochains. -/
  C1 : Type x
  /-- Finiteness of local repair primitives. -/
  primitiveFinite : Fintype C0
  /-- Finiteness of residual repair-gluing cochains. -/
  cochainFinite : Fintype C1
  /-- A complete finite enumeration of local repair primitives. -/
  c0Enumeration : List C0
  /-- Every local repair primitive occurs in `c0Enumeration`. -/
  c0_enumeration_complete : forall primitive, primitive ∈ c0Enumeration
  /-- A complete finite enumeration of residual repair-gluing cochains. -/
  c1Enumeration : List C1
  /-- Every residual repair-gluing cochain occurs in `c1Enumeration`. -/
  c1_enumeration_complete : forall cochain, cochain ∈ c1Enumeration
  /-- The semantic support assigned to each local repair primitive. -/
  supportOf : C0 -> projection.Support
  /-- The left restriction of a primitive at a selected overlap component. -/
  resL : C0 ->
    (Sigma fun left : Chart => Sigma fun right : Chart => Overlap left right) ->
      projection.Support
  /-- The right restriction of a primitive at a selected overlap component. -/
  resR : C0 ->
    (Sigma fun left : Chart => Sigma fun right : Chart => Overlap left right) ->
      projection.Support
  /-- The predicate that a residual cochain charges an atom at an overlap component. -/
  ev : C1 ->
    (Sigma fun left : Chart => Sigma fun right : Chart => Overlap left right) ->
      projection.SemanticAtom -> Prop
  /-- The supplied restriction-difference differential from local primitives to cochains. -/
  delta0 : C0 -> C1
  /-- The supplied residual cochain selected for the finite complex. -/
  residual : C1
  /-- Evaluation of `delta0` charges exactly the exclusive difference of the two restrictions. -/
  restriction_difference : forall primitive overlap atom,
    ev (delta0 primitive) overlap atom <->
      (resL primitive overlap atom /\ ¬ resR primitive overlap atom) \/
        (resR primitive overlap atom /\ ¬ resL primitive overlap atom)

namespace FullFiniteSemanticRepairGluingComplex

attribute [instance] chartFinite primitiveFinite cochainFinite overlapFinite

/--
Forget the Definition 3.1 presentation data while preserving the finite
boundary, support, and selected residual consumed by the existing theorem 3.4
API.
-/
def toFiniteSemanticRepairGluingComplex
    (K : FullFiniteSemanticRepairGluingComplex.{u, v, w, x, y}) :
    FiniteSemanticRepairGluingComplex.{u, v, w, x, y} where
  projection := K.projection
  cover := K.cover
  C0 := K.C0
  C1 := K.C1
  primitiveFinite := K.primitiveFinite
  cochainFinite := K.cochainFinite
  supportOf := K.supportOf
  delta0 := K.delta0
  residual := K.residual

end FullFiniteSemanticRepairGluingComplex

/--
X.定義3.2: boundary membership `B¹`.

`B1 K cochain` means the cochain is generated by a local primitive through the
finite restriction-difference map `delta0`.
-/
def B1 (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (cochain : K.C1) : Prop :=
  exists primitive, K.delta0 primitive = cochain

/-- X.定義3.2: the selected finite obstruction class vanishes exactly when it lies in `B¹`. -/
def ObstructionClassVanishes
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}) : Prop :=
  B1 K K.residual

/-- X.定義3.2: nonzero obstruction is failure of selected boundary membership. -/
def ObstructionClassNonzero
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}) : Prop :=
  Not (ObstructionClassVanishes K)

/--
X.定義3.2: a primitive is semantically closed when its support closes every
§2 residual atom of the selected finite cover.
-/
def PrimitiveSemanticallyClosed
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (primitive : K.C0) : Prop :=
  SemanticRepairClosed K.projection K.cover (K.supportOf primitive)

/--
X.定義3.2: global semantic repair coherence.

The generated certificate is a primitive whose `delta0` equals the selected
residual and whose semantic support is closed.
-/
def GlobalSemanticRepairCoherent
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}) : Prop :=
  exists primitive,
    K.delta0 primitive = K.residual /\
      PrimitiveSemanticallyClosed K primitive

/--
X.定義3.3: semantic faithfulness hypotheses.

These are the supplied semantic conditions required only for the sufficiency
direction: a boundary primitive must have residual-component coverage and
faithfulness back to the actual residual atom.  By X.補題2.5 these two facts
generate semantic closure.
-/
structure SemanticFaithfulnessHypotheses
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}) where
  component_covered_of_boundary :
    forall primitive,
      K.delta0 primitive = K.residual ->
        ResidualComponentCoveredSupport
          K.projection K.cover (K.supportOf primitive)
  component_faithful_of_boundary :
    forall primitive,
      K.delta0 primitive = K.residual ->
        ResidualComponentFaithfulSupport
          K.projection K.cover (K.supportOf primitive)

/--
X.定理3.4 support lemma: semantic faithfulness turns a boundary primitive into
a closed semantic repair primitive.
-/
theorem primitive_semanticRepairClosed_of_faithful_delta0
    {K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}}
    (hfaithful : SemanticFaithfulnessHypotheses K)
    {primitive : K.C0}
    (hboundary : K.delta0 primitive = K.residual) :
    PrimitiveSemanticallyClosed K primitive := by
  exact
    (semanticRepairClosed_iff_residualComponentCovered_and_faithful).mpr
      ⟨hfaithful.component_covered_of_boundary primitive hboundary,
        hfaithful.component_faithful_of_boundary primitive hboundary⟩

/-- X.定理3.4(i): global semantic coherence forces obstruction vanishing. -/
theorem globalRepairCoherent_forces_obstructionVanishes
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}) :
    GlobalSemanticRepairCoherent K -> ObstructionClassVanishes K := by
  intro hglobal
  rcases hglobal with ⟨primitive, hboundary, _hclosed⟩
  exact ⟨primitive, hboundary⟩

/-- X.定理3.4(i), contrapositive: nonzero obstruction rules out global coherence. -/
theorem no_globalRepairCoherent_of_nonzero_obstruction
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}) :
    ObstructionClassNonzero K -> Not (GlobalSemanticRepairCoherent K) := by
  intro hnonzero hglobal
  exact hnonzero (globalRepairCoherent_forces_obstructionVanishes K hglobal)

/-- X.定理3.4(ii): under semantic faithfulness, vanishing generates global coherence. -/
theorem globalRepairCoherent_of_obstructionVanishes
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (hfaithful : SemanticFaithfulnessHypotheses K) :
    ObstructionClassVanishes K -> GlobalSemanticRepairCoherent K := by
  intro hvanishes
  rcases hvanishes with ⟨primitive, hboundary⟩
  exact
    ⟨primitive, hboundary,
      primitive_semanticRepairClosed_of_faithful_delta0 hfaithful hboundary⟩

/--
X.定理3.4(iii): finite semantic repair-gluing descent equivalence under
semantic faithfulness hypotheses.
-/
theorem finiteSemanticRepairGluingDescent_iff
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (hfaithful : SemanticFaithfulnessHypotheses K) :
    GlobalSemanticRepairCoherent K <-> ObstructionClassVanishes K :=
  ⟨globalRepairCoherent_forces_obstructionVanishes K,
    globalRepairCoherent_of_obstructionVanishes K hfaithful⟩

/--
X.定理3.4 package: necessity and nonzero-obstruction exclusion are
unconditional; sufficiency and iff carry exactly the semantic faithfulness
hypotheses.
-/
theorem finiteSemanticRepairGluingDescent_package
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (hfaithful : SemanticFaithfulnessHypotheses K) :
    (GlobalSemanticRepairCoherent K -> ObstructionClassVanishes K) /\
      (ObstructionClassNonzero K -> Not (GlobalSemanticRepairCoherent K)) /\
      (ObstructionClassVanishes K -> GlobalSemanticRepairCoherent K) /\
      (GlobalSemanticRepairCoherent K <-> ObstructionClassVanishes K) := by
  exact
    ⟨globalRepairCoherent_forces_obstructionVanishes K,
      no_globalRepairCoherent_of_nonzero_obstruction K,
      globalRepairCoherent_of_obstructionVanishes K hfaithful,
      finiteSemanticRepairGluingDescent_iff K hfaithful⟩

/--
X.定理3.5: complete-support boundary class.

Every primitive in the class uses the same complete support, and that complete
support is already semantically closed for the selected cover.  Therefore the
semantic faithfulness hypotheses are generated from X.補題2.5 rather than left
as material premises.
-/
structure CompleteSupportBoundaryComplex where
  K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}
  completeSupport : K.projection.Support
  support_eq : forall primitive, K.supportOf primitive = completeSupport
  complete_closed : SemanticRepairClosed K.projection K.cover completeSupport

/--
X.定理3.5: the full support is semantically closed for every cover.

The law-equation route states the same fact for its complete repair support
as `lawEquationCompleteRepairSupport_semanticRepairClosed`; that file sits
above this one in the import graph, so the general form is stated here.
-/
theorem semanticRepairClosed_top
    (P : SemanticAtomProjection.{u, v})
    (cover : FiniteSemanticRepairCoverDatum.{v, w, x} P.Component) :
    SemanticRepairClosed P cover (fun _ => True) :=
  fun _ _ => trivial

/--
X.定理3.5 positive class: a complex whose primitives all carry the full
Λ-support generates the complete-support boundary class.  Closure is
generated by `semanticRepairClosed_top` rather than re-assumed, so this is
the constructor that fires the spec's "Λ-support automates closure" reading.
-/
def CompleteSupportBoundaryComplex.ofFullSupport
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (hsupport : forall primitive, K.supportOf primitive = fun _ => True) :
    CompleteSupportBoundaryComplex.{u, v, w, x, y} where
  K := K
  completeSupport := fun _ => True
  support_eq := hsupport
  complete_closed := semanticRepairClosed_top K.projection K.cover

/--
X.定理3.5: a complete-support boundary class discharges
`SemanticFaithfulnessHypotheses`.
-/
theorem completeSupportBoundary_semanticFaithfulnessHypotheses
    (L : CompleteSupportBoundaryComplex.{u, v, w, x, y}) :
    SemanticFaithfulnessHypotheses L.K := by
  have hdecomp :
      ResidualComponentCoveredSupport L.K.projection L.K.cover L.completeSupport /\
        ResidualComponentFaithfulSupport L.K.projection L.K.cover L.completeSupport :=
    (semanticRepairClosed_iff_residualComponentCovered_and_faithful).mp
      L.complete_closed
  constructor
  · intro primitive _hboundary
    simpa [L.support_eq primitive] using hdecomp.1
  · intro primitive _hboundary
    simpa [L.support_eq primitive] using hdecomp.2

/--
X.定理3.5: finite descent equivalence for a complete-support class, with
semantic faithfulness discharged by the class certificate.
-/
theorem finiteSemanticRepairGluingDescent_iff_of_completeSupportBoundary
    (L : CompleteSupportBoundaryComplex.{u, v, w, x, y}) :
    GlobalSemanticRepairCoherent L.K <-> ObstructionClassVanishes L.K :=
  finiteSemanticRepairGluingDescent_iff L.K
    (completeSupportBoundary_semanticFaithfulnessHypotheses L)

/-- X.定理3.5 package for complete-support families. -/
theorem completeSupportBoundary_descent_package
    (L : CompleteSupportBoundaryComplex.{u, v, w, x, y}) :
    SemanticFaithfulnessHypotheses L.K /\
      (GlobalSemanticRepairCoherent L.K -> ObstructionClassVanishes L.K) /\
      (ObstructionClassNonzero L.K -> Not (GlobalSemanticRepairCoherent L.K)) /\
      (ObstructionClassVanishes L.K -> GlobalSemanticRepairCoherent L.K) /\
      (GlobalSemanticRepairCoherent L.K <-> ObstructionClassVanishes L.K) := by
  let hfaithful := completeSupportBoundary_semanticFaithfulnessHypotheses L
  exact
    ⟨hfaithful,
      globalRepairCoherent_forces_obstructionVanishes L.K,
      no_globalRepairCoherent_of_nonzero_obstruction L.K,
      globalRepairCoherent_of_obstructionVanishes L.K hfaithful,
      finiteSemanticRepairGluingDescent_iff_of_completeSupportBoundary L⟩

namespace FullFiniteSemanticRepairGluingComplex

/--
X.定義3.1 restriction-difference API: evaluating `delta0 primitive` at an
overlap charges exactly the atom on which the two supplied restrictions differ.
-/
theorem delta0_ev_iff_restriction_xor
    (K : FullFiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (primitive : K.C0)
    (overlap : Sigma fun left : K.Chart =>
      Sigma fun right : K.Chart => K.Overlap left right)
    (atom : K.projection.SemanticAtom) :
    K.ev (K.delta0 primitive) overlap atom <->
      (K.resL primitive overlap atom /\ ¬ K.resR primitive overlap atom) \/
        (K.resR primitive overlap atom /\ ¬ K.resL primitive overlap atom) :=
  K.restriction_difference primitive overlap atom

/-- X.定義3.2, read on the full Definition 3.1 presentation. -/
def ObstructionClassVanishes
    (K : FullFiniteSemanticRepairGluingComplex.{u, v, w, x, y}) : Prop :=
  _root_.AAT.AG.SemanticRepair.ObstructionClassVanishes
    K.toFiniteSemanticRepairGluingComplex

/-- X.定義3.2, read on the full Definition 3.1 presentation. -/
def ObstructionClassNonzero
    (K : FullFiniteSemanticRepairGluingComplex.{u, v, w, x, y}) : Prop :=
  _root_.AAT.AG.SemanticRepair.ObstructionClassNonzero
    K.toFiniteSemanticRepairGluingComplex

/-- X.定義3.2, read on the full Definition 3.1 presentation. -/
def GlobalSemanticRepairCoherent
    (K : FullFiniteSemanticRepairGluingComplex.{u, v, w, x, y}) : Prop :=
  _root_.AAT.AG.SemanticRepair.GlobalSemanticRepairCoherent
    K.toFiniteSemanticRepairGluingComplex

/-- X.定理3.4(i), transported from the minimal finite complex by forgetting. -/
theorem globalRepairCoherent_forces_obstructionVanishes
    (K : FullFiniteSemanticRepairGluingComplex.{u, v, w, x, y}) :
    GlobalSemanticRepairCoherent K -> ObstructionClassVanishes K :=
  _root_.AAT.AG.SemanticRepair.globalRepairCoherent_forces_obstructionVanishes
    K.toFiniteSemanticRepairGluingComplex

/-- X.定理3.4(i), transported from the minimal finite complex by forgetting. -/
theorem no_globalRepairCoherent_of_nonzero_obstruction
    (K : FullFiniteSemanticRepairGluingComplex.{u, v, w, x, y}) :
    ObstructionClassNonzero K -> Not (GlobalSemanticRepairCoherent K) :=
  _root_.AAT.AG.SemanticRepair.no_globalRepairCoherent_of_nonzero_obstruction
    K.toFiniteSemanticRepairGluingComplex

/--
X.定理3.4(ii): under the same semantic faithfulness hypotheses as the minimal
complex, the full Definition 3.1 presentation has global semantic repair
coherence whenever its selected residual is a boundary.
-/
theorem globalRepairCoherent_of_obstructionVanishes
    (K : FullFiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (hfaithful : SemanticFaithfulnessHypotheses K.toFiniteSemanticRepairGluingComplex) :
    ObstructionClassVanishes K -> GlobalSemanticRepairCoherent K :=
  _root_.AAT.AG.SemanticRepair.globalRepairCoherent_of_obstructionVanishes
    K.toFiniteSemanticRepairGluingComplex hfaithful

/-- X.定理3.4(iii), transported to the full Definition 3.1 presentation. -/
theorem finiteSemanticRepairGluingDescent_iff
    (K : FullFiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (hfaithful : SemanticFaithfulnessHypotheses K.toFiniteSemanticRepairGluingComplex) :
    GlobalSemanticRepairCoherent K <-> ObstructionClassVanishes K :=
  _root_.AAT.AG.SemanticRepair.finiteSemanticRepairGluingDescent_iff
    K.toFiniteSemanticRepairGluingComplex hfaithful

/-- X.定理3.4 package, transported to the full Definition 3.1 presentation. -/
theorem finiteSemanticRepairGluingDescent_package
    (K : FullFiniteSemanticRepairGluingComplex.{u, v, w, x, y})
    (hfaithful : SemanticFaithfulnessHypotheses K.toFiniteSemanticRepairGluingComplex) :
    (GlobalSemanticRepairCoherent K -> ObstructionClassVanishes K) /\
      (ObstructionClassNonzero K -> Not (GlobalSemanticRepairCoherent K)) /\
      (ObstructionClassVanishes K -> GlobalSemanticRepairCoherent K) /\
      (GlobalSemanticRepairCoherent K <-> ObstructionClassVanishes K) :=
  _root_.AAT.AG.SemanticRepair.finiteSemanticRepairGluingDescent_package
    K.toFiniteSemanticRepairGluingComplex hfaithful

end FullFiniteSemanticRepairGluingComplex

end SemanticRepair
end AAT.AG
