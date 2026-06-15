import Formal.AG.Evolution.Profile
import Formal.AG.Cohomology.FinitePosetComparison

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
PRD-9 R2 / AC4 temporal product-site surface.

The temporal site is a selected finite trace regime together with a selected
finite AAT context regime.  It is not a general product-site construction over
all traces or all architecture contexts.
-/

/--
IX.§3 / AC4: selected finite temporal incidence site.

Objects are read as pairs of selected trace objects and selected architecture
contexts.  The finite data are inherited from the selected trace regime and
the selected finite-poset AAT site regime.
-/
structure TemporalSite {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (E : EvolutionProfile.{u, v, w, x, y, z}) where
  traceRegime : E.trace.FiniteRegime
  siteRegime : Site.FinitePosetAATSiteRegime S

namespace TemporalSite

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}

/-- IX.§3 / AC4: temporal incidence objects are selected trace/context pairs. -/
abbrev Point (T : TemporalSite S E) : Type (max u y) :=
  E.trace.Obj × T.siteRegime.ContextIndex

/--
IX.§3 / AC4: a selected incidence leg in `Tr_E × X`.

The leg combines a selected trace arrow and a selected architecture-context
order witness.  This is the finite product/incidence relation used by the
temporal cover and coefficient restriction surfaces.
-/
structure IncidenceLeg (T : TemporalSite S E) (p q : T.Point) where
  trace : E.trace.Hom p.1 q.1
  trace_selected : T.traceRegime.selectedArrow trace
  context : T.siteRegime.contextLe p.2 q.2

/-- IX.§3 / AC4: identity incidence leg on a selected temporal point. -/
def idLeg (T : TemporalSite S E) (p : T.Point) : T.IncidenceLeg p p where
  trace := E.trace.id p.1
  trace_selected := T.traceRegime.id_selected p.1
  context := T.siteRegime.contextLe_refl p.2

/-- IX.§3 / AC4: composition of selected temporal incidence legs. -/
def compLeg (T : TemporalSite S E) {p q r : T.Point}
    (f : T.IncidenceLeg p q) (g : T.IncidenceLeg q r) :
    T.IncidenceLeg p r where
  trace := E.trace.comp f.trace g.trace
  trace_selected := T.traceRegime.comp_selected f.trace_selected g.trace_selected
  context := T.siteRegime.contextLe_trans f.context g.context

/-- IX.§3 / AC4: the selected trace component is finite. -/
theorem trace_object_finite (T : TemporalSite S E) : Finite E.trace.Obj :=
  T.traceRegime.object_finite

/-- IX.§3 / AC4: the selected architecture-context component is finite. -/
theorem context_index_finite (T : TemporalSite S E) :
    Finite T.siteRegime.ContextIndex :=
  T.siteRegime.context_index_finite

/-- IX.§3 / AC4: identity incidence legs are selected product-site legs. -/
theorem idLeg_trace_selected (T : TemporalSite S E) (p : T.Point) :
    T.traceRegime.selectedArrow (T.idLeg p).trace :=
  (T.idLeg p).trace_selected

/-- IX.§3 / AC4: composed incidence legs remain selected product-site legs. -/
theorem compLeg_trace_selected (T : TemporalSite S E) {p q r : T.Point}
    (f : T.IncidenceLeg p q) (g : T.IncidenceLeg q r) :
    T.traceRegime.selectedArrow (T.compLeg f g).trace :=
  (T.compLeg f g).trace_selected

/-- IX.§3 / AC4: incidence context legs are sound in the underlying AAT site. -/
theorem incidence_context_sound (T : TemporalSite S E) {p q : T.Point}
    (f : T.IncidenceLeg p q) :
    S.contextPreorder.le (T.siteRegime.context p.2) (T.siteRegime.context q.2) :=
  T.siteRegime.contextLe_sound f.context

end TemporalSite

/--
IX.§3 / AC4: selected temporal cover.

Each chart carries both a selected trace arrow into the base trace object and
a selected architecture-context order witness into the base context.  This is
the trace/context cover data used by the Part IX Čech bridge.
-/
structure TemporalCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    (T : TemporalSite S E) where
  baseTrace : E.trace.Obj
  baseContext : T.siteRegime.ContextIndex
  Index : Type (max u y)
  finiteIndex : Finite Index
  chartTrace : Index -> E.trace.Obj
  chartContext : Index -> T.siteRegime.ContextIndex
  traceToBase : ∀ i : Index, E.trace.Hom (chartTrace i) baseTrace
  traceToBase_selected : ∀ i : Index, T.traceRegime.selectedArrow (traceToBase i)
  contextToBase : ∀ i : Index, T.siteRegime.contextLe (chartContext i) baseContext

namespace TemporalCover

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}

/-- IX.§3 / AC4: the selected temporal cover index is finite. -/
theorem index_finite (𝒯 : TemporalCover T) : Finite 𝒯.Index :=
  𝒯.finiteIndex

/-- IX.§3 / AC4: every temporal trace leg lies in the selected trace regime. -/
theorem trace_leg_selected (𝒯 : TemporalCover T) (i : 𝒯.Index) :
    T.traceRegime.selectedArrow (𝒯.traceToBase i) :=
  𝒯.traceToBase_selected i

/-- IX.§3 / AC4: architecture-context cover legs are sound in the AAT site. -/
theorem context_leg_sound (𝒯 : TemporalCover T) (i : 𝒯.Index) :
    S.contextPreorder.le (T.siteRegime.context (𝒯.chartContext i))
      (T.siteRegime.context 𝒯.baseContext) :=
  T.siteRegime.contextLe_sound (𝒯.contextToBase i)

/-- IX.§3 / AC4: the chart-to-base cover leg as a temporal incidence leg. -/
def incidenceLeg (𝒯 : TemporalCover T) (i : 𝒯.Index) :
    T.IncidenceLeg (𝒯.chartTrace i, 𝒯.chartContext i) (𝒯.baseTrace, 𝒯.baseContext) where
  trace := 𝒯.traceToBase i
  trace_selected := 𝒯.traceToBase_selected i
  context := 𝒯.contextToBase i

/-- IX.§3 / AC4: cover incidence legs are selected in the trace regime. -/
theorem incidence_leg_selected (𝒯 : TemporalCover T) (i : 𝒯.Index) :
    T.traceRegime.selectedArrow (𝒯.incidenceLeg i).trace :=
  (𝒯.incidenceLeg i).trace_selected

end TemporalCover

/--
IX.§3 / AC4: typed comparison from a temporal cover to a PRD-4 site cover.

This records how temporal chart indices are represented by the AAT
cover-relative Čech cover and how temporal trace/context legs are retained
when the PRD-4 complex is reused.
-/
structure TemporalCoverToSiteCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} (𝒯 : TemporalCover T)
    (𝒰 : Cohomology.CoverRelativeCechCover S) where
  siteIndexOf : 𝒯.Index -> 𝒰.Index
  chart_eq :
    ∀ i : 𝒯.Index,
      𝒰.chart (siteIndexOf i) =
        Site.ContextCategoryObject.of S.contextPreorder
          (T.siteRegime.context (𝒯.chartContext i))
  base_eq :
    𝒰.base =
      Site.ContextCategoryObject.of S.contextPreorder
        (T.siteRegime.context 𝒯.baseContext)
  preservesTraceLeg : ∀ i : 𝒯.Index, T.traceRegime.selectedArrow (𝒯.traceToBase i)
  preservesContextLeg :
    ∀ i : 𝒯.Index,
      S.contextPreorder.le (T.siteRegime.context (𝒯.chartContext i))
        (T.siteRegime.context 𝒯.baseContext)

namespace TemporalCoverToSiteCover

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {𝒯 : TemporalCover T}
variable {𝒰 : Cohomology.CoverRelativeCechCover S}

/-- IX.§3 / AC4: temporal trace legs survive the site-cover comparison. -/
theorem trace_leg_selected (M : TemporalCoverToSiteCover 𝒯 𝒰)
    (i : 𝒯.Index) : T.traceRegime.selectedArrow (𝒯.traceToBase i) :=
  M.preservesTraceLeg i

/-- IX.§3 / AC4: temporal context legs survive as AAT site preorder legs. -/
theorem context_leg_sound (M : TemporalCoverToSiteCover 𝒯 𝒰)
    (i : 𝒯.Index) :
    S.contextPreorder.le (T.siteRegime.context (𝒯.chartContext i))
      (T.siteRegime.context 𝒯.baseContext) :=
  M.preservesContextLeg i

end TemporalCoverToSiteCover

/--
IX.§3 / AC4: bridge from selected temporal cover data to the PRD-4
cover-relative Čech complex surface.

The temporal cover is kept explicit, while the additive Čech complex is the
existing PRD-4 package over the selected AAT site.
-/
structure TemporalCechBridge {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    (T : TemporalSite S E) (Ob : Cohomology.ObstructionSheaf S) where
  temporalCover : TemporalCover T
  siteCover : Cohomology.CoverRelativeCechCover S
  coverComparison : TemporalCoverToSiteCover temporalCover siteCover
  siteComplex : Cohomology.CoverRelativeCechComplex siteCover Ob

namespace TemporalCechBridge

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {Ob : Cohomology.ObstructionSheaf S}

/-- IX.§3 / AC4: read the selected PRD-4 cover-relative complex. -/
def complex (B : TemporalCechBridge T Ob) :
    Cohomology.CoverRelativeCechComplex B.siteCover Ob :=
  B.siteComplex

/-- IX.§3 / AC4: read the typed temporal-cover to site-cover comparison. -/
def comparison (B : TemporalCechBridge T Ob) :
    TemporalCoverToSiteCover B.temporalCover B.siteCover :=
  B.coverComparison

/-- IX.§3 / AC4: the selected temporal Čech differential squares to zero. -/
theorem differential_comp_zero (B : TemporalCechBridge T Ob)
    (n : Nat) (c : B.siteComplex.Cn n) :
    letI := B.siteComplex.cochainAddCommGroup (n + 2)
    B.siteComplex.d (n + 1) (B.siteComplex.d n c) = 0 :=
  B.siteComplex.d_comp_d_eq_zero n c

end TemporalCechBridge

/--
IX.§3 / AC4: finite-poset temporal Čech bridge.

This specializes the temporal bridge to a PRD-2 finite-poset Čech complex and
the PRD-4 finite-poset comparison package.
-/
structure FinitePosetTemporalCechBridge {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    (T : TemporalSite S E) (Ob : Cohomology.ObstructionSheaf S) where
  temporalCover : TemporalCover T
  finitePosetComplex : Site.FinitePosetCechComplex T.siteRegime
  coverComparison :
    TemporalCoverToSiteCover temporalCover
      (Cohomology.finitePosetCoverRelativeCover finitePosetComplex)
  comparison :
    Cohomology.FinitePosetCechComparisonData finitePosetComplex Ob

namespace FinitePosetTemporalCechBridge

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {Ob : Cohomology.ObstructionSheaf S}

/-- IX.§3 / AC4: the induced PRD-4 cover-relative temporal bridge. -/
def toTemporalCechBridge (B : FinitePosetTemporalCechBridge T Ob) :
    TemporalCechBridge T Ob where
  temporalCover := B.temporalCover
  siteCover := Cohomology.finitePosetCoverRelativeCover B.finitePosetComplex
  coverComparison := B.coverComparison
  siteComplex := B.comparison.generalComplex

/-- IX.§3 / AC4: finite-poset cochains compare to the induced PRD-4 cochains. -/
theorem cochain_to_from (B : FinitePosetTemporalCechBridge T Ob)
    (n : Nat) (c : Site.FinitePosetCechCochain T.siteRegime n) :
    B.comparison.comparisonTarget.toFinitePosetCochain n
      (B.comparison.comparisonTarget.fromFinitePosetCochain n c) = c :=
  B.comparison.cochain_to_from n c

/-- IX.§3 / AC4: the finite-poset comparison respects selected differentials. -/
theorem differential_compatible (B : FinitePosetTemporalCechBridge T Ob)
    (n : Nat) (c : B.comparison.generalComplex.Cn n) :
    B.comparison.comparisonTarget.toFinitePosetCochain (n + 1)
        (B.comparison.generalComplex.d n c) =
      B.finitePosetComplex.differential n
        (B.comparison.comparisonTarget.toFinitePosetCochain n c) :=
  B.comparison.differential_compatible n c

end FinitePosetTemporalCechBridge

end Evolution
end AAT.AG
