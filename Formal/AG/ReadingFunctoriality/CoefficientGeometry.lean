import Formal.AG.ReadingFunctoriality.StandardSchemeCoefficient
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Closed-equational geometry under coefficient change

This module implements the fixed declarations of PRD SD7 / AC31, the per-law chart comparison of
AC32, and the aggregate ideal and lawful closed-geometry transport of AC33.  Its input is a source
raw system `raw`, a source standard scheme `X`, a semantic equation
core `G` with its source presentation bridge `B`, and a flat coefficient change `f`.  Source and
target `HasSheafify` instances type the two standard schemes; the explicit site-dependent
`HasSheafCompose` instance supplies the coefficient-change compatibility already required by the
canonical scheme pullback.

The equation-system route starts from an `EquationObservableRealization` of
`S.equationSystem`.  Coefficient change transports every context-owned
observable and residual section through the canonical sheafified-section map,
transports section-dependent architecture readings through the actual
standard-scheme projection, and then carries the symbolic-residual equalizer,
generated witness and obstruction ideals, their ideal sheaves, and the
realization and lawful closed subschemes.

The fixed definition sends each source global equation through the actual
`StandardArchitectureScheme.baseChangeMap.appTop`.  The target geometric predicate and its
closed-equational witness are then reconstructed from that same transported family by
`ClosedEquationalLawWitness.ofGlobalSections`.  The characterization theorem compares target
vanishing with source vanishing after the actual projection, while the validity theorem derives
restriction compatibility from the global-section constructor.

No target raw bridge, caller-supplied target reading, comparison map, or witness certificate is
accepted.  The six AC31 declarations omit the source bridge validity premise `hB`; the AC32 chart
comparison first uses it through the source chart-ideal realization and then compares the two
pullbacks through the actual changed-chart square.  AC33 independently transports the global
equations, commutes ideal-sheaf pullback with their fixed-index supremum, and constructs the
required and all-law closed-subscheme maps from those aggregate equalities.
-/

namespace AAT.AG

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped TensorProduct

universe u v

noncomputable section

namespace LawAlgebra

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k k' : Type v}
variable [CommRing k] [CommRing k']
variable (raw : RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (AATCommAlgCat k)]
variable [HasSheafify S.topology (AATCommAlgCat k')]
variable (X : StandardArchitectureScheme raw)

/-- The AC31 fixed definition that sends one source semantic-core equation through the actual
coefficient-change projection.  The source bridge `B` creates the source global section; no
target bridge or caller-supplied comparison morphism is accepted. -/
noncomputable def baseChangedSemanticCoreGlobalEquation
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : G.Index) (a : U.Atom) :
    Γ((X.baseChange raw f).underlying, ⊤) :=
  (X.baseChangeMap raw f).appTop
    (semanticCoreGlobalEquation raw X G B i a)

/-- The AC31 target reading generated from the transported global equations.  Its geometric
predicate and witness use the same section family, and `ofGlobalSections` supplies canonical
coordinates instead of accepting a target reading or witness certificate from the caller. -/
noncomputable def ClosedEquationalLawReading.baseChangeOfSemanticCore
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    ClosedEquationalLawReading
      (raw.baseChange f.hom) (X.baseChange raw f) G where
  geometric := {
    HoldsOn := fun s i =>
      GlobalEquationsVanishAlong
        (raw.baseChange f.hom) (X.baseChange raw f)
        (baseChangedSemanticCoreGlobalEquation raw X G B f i) s
  }
  closed := Set.univ
  selected := fun _ => Set.univ
  witness := fun i _ =>
    ClosedEquationalLawWitness.ofGlobalSections
      (raw.baseChange f.hom) (X.baseChange raw f) i
      (baseChangedSemanticCoreGlobalEquation raw X G B f i)

/-- The AC31 characterization API: transported vanishing is exactly source vanishing after the
actual coefficient-change projection.  This records the defining `appTop` composition and does
not introduce an auxiliary comparison map. -/
theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_geometric_iff
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ (X.baseChange raw f).underlying)
    (i : G.Index) :
    (ClosedEquationalLawReading.baseChangeOfSemanticCore
      raw X G B f).geometric.HoldsOn s i ↔
      (ClosedEquationalLawReading.ofSemanticCore
        raw X G B).geometric.HoldsOn
          (s ≫ X.baseChangeMap raw f) i := by
  rfl

/-- The AC31 principal validity theorem.  Geometric stability follows from composition of Scheme
global-section maps, while witness compatibility is derived from
`ClosedEquationalLawWitness.ofGlobalSections_valid`; neither conclusion is supplied as a
premise. -/
theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    IsClosedEquationalLawReading
      (raw.baseChange f.hom) (X.baseChange raw f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f) where
  geometric_stable := by
    intro T T' s g i hs a
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hs a, map_zero]
  witness_compatible := by
    intro i hi
    exact ClosedEquationalLawWitness.ofGlobalSections_valid
      (raw.baseChange f.hom) (X.baseChange raw f) i _
  selected_closed := fun _ i _ => Set.mem_univ i
  selected_basicOpen := fun _ _ i =>
    iff_of_true (Set.mem_univ i) (Set.mem_univ i)

/-- The required-law selection consequence of the AC31 fixed reading.  It reads the constructed
`Set.univ` closed and selected fields and makes no semantic-truth claim. -/
theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    RequiredClosed
      (raw.baseChange f.hom) (X.baseChange raw f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f) where
  closed := fun i _ => Set.mem_univ i
  selected := fun _ i _ => Set.mem_univ i

/-- The all-law selection consequence of the AC31 fixed reading.  It reads the constructed
`Set.univ` fields; source chart realization remains the separate R7 / AC32 obligation using
`hB`. -/
theorem ClosedEquationalLawReading.baseChangeOfSemanticCore_allLawsSelected
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    AllLawsSelected
      (raw.baseChange f.hom) (X.baseChange raw f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore
        raw X G B f) where
  closed := fun i => Set.mem_univ i
  selected := fun _ i => Set.mem_univ i

/-! ## Equation-system realization under coefficient change -/

namespace EquationObservableRealization

variable {raw : RawAmbientRestrictionSystem S k}
variable {X : StandardArchitectureScheme raw}
variable {E : ArchitecturalEquationSystem S.contextPreorder}

/--
The canonical map on sheafified sections commutes with context
restriction.
-/
private theorem sectionBaseChangeMap_natural
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    {W V : S.category} (g : W ⟶ V) :
    RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap raw f V ≫
        sheafifiedRestriction (raw.baseChange f.hom) g =
      sheafifiedRestriction raw g ≫
        RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap raw f W := by
  let comparison :
      raw.toRingedSite.structureSheaf.val ⋙ f.coefficientExtension ≅
        (raw.baseChange f.hom).toRingedSite.structureSheaf.val :=
    (sheafifyComposeIso S.topology f.coefficientExtension raw.toPresheaf).symm ≪≫
      ((CategoryTheory.sheafification S.topology
        (AATCommAlgCat.{u, v} k')).mapIso
          (RawAmbientRestrictionSystem.baseChangePresheafIso raw f)).symm
  have hnat := congrArg (fun q => q.right)
    (comparison.hom.naturality g.op)
  change ((f.coefficientExtension.map
      (raw.toRingedSite.structureSheaf.val.map g.op)).right ≫
        (comparison.app (Opposite.op W)).hom.right) =
    (comparison.app (Opposite.op V)).hom.right ≫
      ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.map g.op).right at hnat
  change pushout.inl _ _ ≫ (comparison.app (Opposite.op V)).hom.right ≫
      ((raw.baseChange f.hom).toRingedSite.structureSheaf.val.map g.op).right =
    (raw.toRingedSite.structureSheaf.val.map g.op).right ≫
      pushout.inl _ _ ≫ (comparison.app (Opposite.op W)).hom.right
  rw [← hnat]
  simp only [← Category.assoc]
  rw [cancel_mono (comparison.app (Opposite.op W)).hom.right]
  simp [FlatCoefficientChange.coefficientExtension]

/--
Coefficient change transports every observable component through the actual
canonical map of the corresponding sheafified section ring.
-/
noncomputable def baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    EquationObservableRealization
      (raw.baseChange f.hom) (X.baseChange raw f) E where
  sectionMap := fun W =>
    (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
      raw f W).hom.comp (R.sectionMap W)
  architectureAt := fun s =>
    R.architectureAt (s ≫ X.baseChangeMap raw f)
  residualSection := fun W i a =>
    RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
      raw f W (R.residualSection W i a)

/-- The changed base-context section map is the source map followed by the
actual standard-scheme projection on global sections. -/
theorem baseSectionMap_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (R.baseChange f).baseSectionMap =
      (X.baseChangeMap raw f).appTop.hom.comp R.baseSectionMap := by
  ext x
  change
    (X.baseChange raw f).decoration.interpretation
        (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f X.decoration.context (R.sectionMap X.decoration.context x)) =
      (X.baseChangeMap raw f).appTop
        (X.decoration.interpretation
          (R.sectionMap X.decoration.context x))
  simpa only [CommRingCat.comp_apply] using congrArg
    (fun q => q (R.sectionMap X.decoration.context x))
    (StandardArchitectureScheme.baseChangedDecoration_interpretation
      raw X f)

/-- The map from a changed test-chart pullback to the corresponding source
test-chart pullback. -/
noncomputable def chartPullbackBaseChangeMap
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ (X.baseChange raw f).underlying)
    (j : X.atlas.Index) :
    (R.baseChange f).chartPullback s j ⟶
      R.chartPullback (s ≫ X.baseChangeMap raw f) j :=
  pullback.lift
    (pullback.fst s ((X.baseChange raw f).atlas.chart j).map)
    (pullback.snd s ((X.baseChange raw f).atlas.chart j).map ≫
      StandardArchitectureScheme.baseChangedChartMap raw X f j)
    (by
      rw [← Category.assoc, pullback.condition]
      simpa only [Category.assoc] using congrArg
        (fun q =>
          pullback.snd s ((X.baseChange raw f).atlas.chart j).map ≫ q)
        (StandardArchitectureScheme.baseChangedChart_isPullback
          raw X f j).w)

/-- Evaluation on a changed test-chart pullback is the pullback of source
evaluation through the canonical comparison map. -/
theorem chartEvaluation_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ (X.baseChange raw f).underlying)
    (j : X.atlas.Index)
    (x : SheafifiedSectionRing raw (X.atlas.chart j).context) :
    (R.baseChange f).chartEvaluation s j
        (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f (X.atlas.chart j).context x) =
      (R.chartPullbackBaseChangeMap f s j).appTop
        (R.chartEvaluation (s ≫ X.baseChangeMap raw f) j x) := by
  have hChart :
      StandardArchitectureScheme.baseChangedChartMap raw X f j =
        Scheme.Spec.map
          (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
            raw f (X.atlas.chart j).context).op := by
    exact
      RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso_hom_fst
        raw f (X.atlas.chart j).context
  have hLift :
      R.chartPullbackBaseChangeMap f s j ≫
          pullback.snd (s ≫ X.baseChangeMap raw f)
            (X.atlas.chart j).map =
        pullback.snd s ((X.baseChange raw f).atlas.chart j).map ≫
          StandardArchitectureScheme.baseChangedChartMap raw X f j := by
    exact pullback.lift_snd _ _ _
  have hTop := congrArg (fun q => q.appTop) hLift
  simp only [Scheme.Hom.comp_appTop] at hTop
  change
    ((Scheme.ΓSpecIso
        (SheafifiedSectionRing (raw.baseChange f.hom)
          (X.atlas.chart j).context)).inv ≫
      (pullback.snd s ((X.baseChange raw f).atlas.chart j).map).appTop)
        (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f (X.atlas.chart j).context x) =
      ((Scheme.ΓSpecIso
          (SheafifiedSectionRing raw
            (X.atlas.chart j).context)).inv ≫
        (pullback.snd (s ≫ X.baseChangeMap raw f)
          (X.atlas.chart j).map).appTop ≫
        (R.chartPullbackBaseChangeMap f s j).appTop) x
  rw [hTop, hChart]
  apply congrArg
    (fun z =>
      (pullback.snd s
        ((X.baseChange raw f).atlas.chart j).map).appTop z)
  simpa only [Category.assoc, CommRingCat.comp_apply] using congrArg
    (fun q => q x)
      (Scheme.ΓSpecIso_inv_naturality
        (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f (X.atlas.chart j).context))

/-- Coefficient change preserves the representable-regime recognition laws. -/
theorem baseChange_valid
    (R : EquationObservableRealization raw X E)
    (hR : IsEquationObservableRealization R)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    IsEquationObservableRealization (R.baseChange f) where
  sectionMap_natural := by
    intro source target g x
    change RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap raw f source
        (R.sectionMap source (E.restrict g x)) =
      sheafifiedRestriction (raw.baseChange f.hom) g
        (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap raw f target
          (R.sectionMap target x))
    rw [hR.sectionMap_natural g x]
    simpa only [CommRingCat.comp_apply] using congrArg
      (fun q => q (R.sectionMap target x))
      (sectionBaseChangeMap_natural (raw := raw) f g).symm
  residualSection_natural := by
    intro source target g i a
    change RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap raw f source
        (R.residualSection source i a) =
      sheafifiedRestriction (raw.baseChange f.hom) g
        (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap raw f target
          (R.residualSection target i a))
    rw [hR.residualSection_natural g i a]
    simpa only [CommRingCat.comp_apply] using congrArg
      (fun q => q (R.residualSection target i a))
      (sectionBaseChangeMap_natural (raw := raw) f g).symm
  architectureAt_comp := by
    intro T T' s g
    simpa only [baseChange, Category.assoc] using
      hR.architectureAt_comp (s ≫ X.baseChangeMap raw f) g
  residualSection_evaluates := by
    intro T s i a
    change s.appTop
        ((R.baseChange f).ambientResidualSection i a) =
      s.appTop
        ((R.baseChange f).baseSectionMap
          (E.equationResidual X.decoration.context
            (R.architectureAt (s ≫ X.baseChangeMap raw f)) i a))
    rw [R.baseSectionMap_baseChange f]
    change s.appTop
        ((X.baseChange raw f).decoration.interpretation
          (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
            raw f X.decoration.context
            (R.residualSection X.decoration.context i a))) =
      s.appTop
        ((X.baseChangeMap raw f).appTop
          (R.baseSectionMap
            (E.equationResidual X.decoration.context
              (R.architectureAt (s ≫ X.baseChangeMap raw f)) i a)))
    rw [show
      (X.baseChange raw f).decoration.interpretation
          (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
            raw f X.decoration.context
            (R.residualSection X.decoration.context i a)) =
        (X.baseChangeMap raw f).appTop
          (X.decoration.interpretation
            (R.residualSection X.decoration.context i a)) by
      simpa only [CommRingCat.comp_apply] using congrArg
        (fun q => q (R.residualSection X.decoration.context i a))
        (StandardArchitectureScheme.baseChangedDecoration_interpretation
          raw X f)]
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      hR.residualSection_evaluates
        (s ≫ X.baseChangeMap raw f) i a
  residualSection_evaluates_on_chart := by
    intro T s j i a
    change
      (R.baseChange f).chartEvaluation s j
          (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
            raw f (X.atlas.chart j).context
            (R.residualSection (X.atlas.chart j).context i a)) =
        (R.baseChange f).chartEvaluation s j
          (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
            raw f (X.atlas.chart j).context
            (R.sectionMap (X.atlas.chart j).context
              (E.equationResidual (X.atlas.chart j).context
                (R.architectureAt (s ≫ X.baseChangeMap raw f)) i a)))
    rw [R.chartEvaluation_baseChange f s j,
      R.chartEvaluation_baseChange f s j]
    exact congrArg
      (fun z => (R.chartPullbackBaseChangeMap f s j).appTop z)
      (hR.residualSection_evaluates_on_chart
        (s ≫ X.baseChangeMap raw f) j i a)

@[simp] theorem baseChange_sectionMap
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) (x : E.Observable W) :
    (R.baseChange f).sectionMap W x =
      RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
        raw f W (R.sectionMap W x) :=
  rfl

@[simp] theorem violationSection_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : E.Index) (a : U.Atom) :
    (R.baseChange f).violationSection i a =
      (X.baseChangeMap raw f).appTop (R.violationSection i a) :=
  by
    change
      (R.baseChange f).baseSectionMap
          (E.violationCoordinate X.decoration.context i a) =
        (X.baseChangeMap raw f).appTop
          (R.baseSectionMap
            (E.violationCoordinate X.decoration.context i a))
    rw [R.baseSectionMap_baseChange f]
    rfl

@[simp] theorem residualSection_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) (i : E.Index) (a : U.Atom) :
    (R.baseChange f).residualSection W i a =
      RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
        raw f W (R.residualSection W i a) :=
  rfl

@[simp] theorem ambientResidualSection_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : E.Index) (a : U.Atom) :
    (R.baseChange f).ambientResidualSection i a =
      (X.baseChangeMap raw f).appTop
        (R.ambientResidualSection i a) := by
  change
    (X.baseChange raw f).decoration.interpretation
        (RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
          raw f X.decoration.context
          (R.residualSection X.decoration.context i a)) =
      (X.baseChangeMap raw f).appTop
        (X.decoration.interpretation
          (R.residualSection X.decoration.context i a))
  simpa only [CommRingCat.comp_apply] using congrArg
    (fun q => q (R.residualSection X.decoration.context i a))
    (StandardArchitectureScheme.baseChangedDecoration_interpretation
      raw X f)

@[simp] theorem realizationRelation_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (g : EquationObservableRealization.GeneratorIndex E) :
    (R.baseChange f).realizationRelation g =
      (X.baseChangeMap raw f).appTop (R.realizationRelation g) := by
  simp only [realizationRelation, violationSection_baseChange,
    ambientResidualSection_baseChange, map_sub]

/-- The equalizer ideal is extended by the actual coefficient map. -/
theorem realizationIdeal_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (R.baseChange f).realizationIdeal =
      Ideal.map (X.baseChangeMap raw f).appTop.hom
        R.realizationIdeal := by
  rw [realizationIdeal, realizationIdeal, Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨R.realizationRelation g, ⟨g, rfl⟩,
      (R.realizationRelation_baseChange f g).symm⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, R.realizationRelation_baseChange f g⟩

/-- Every global witness ideal is extended by the actual coefficient map. -/
theorem globalWitnessIdeal_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : E.Index) :
    (R.baseChange f).globalWitnessIdeal i =
      Ideal.map (X.baseChangeMap raw f).appTop.hom
        (R.globalWitnessIdeal i) := by
  rw [globalWitnessIdeal, globalWitnessIdeal,
    R.baseSectionMap_baseChange f, Ideal.map_map]
  rfl

/-- The global obstruction ideal is extended by the actual coefficient map. -/
theorem globalObstructionIdeal_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (R.baseChange f).globalObstructionIdeal =
      Ideal.map (X.baseChangeMap raw f).appTop.hom
        R.globalObstructionIdeal := by
  rw [globalObstructionIdeal, globalObstructionIdeal,
    R.baseSectionMap_baseChange f, Ideal.map_map]
  rfl

end EquationObservableRealization

/-- Proof-internal AC32 algebra API: the kernel of scalar extension to a quotient is the
extended quotient ideal.  It is derived from Mathlib's canonical quotient-tensor equivalence and
introduces no flatness or comparison premise. -/
private theorem ker_tensor_quotient_algebraMap
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (I : Ideal R) :
    RingHom.ker (algebraMap T (T ⊗[R] (R ⧸ I))) =
      Ideal.map (algebraMap R T) I := by
  let J := Ideal.map (algebraMap R T) I
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I
  change RingHom.ker (algebraMap T (T ⊗[R] (R ⧸ I))) = J
  rw [show algebraMap T (T ⊗[R] (R ⧸ I)) =
      e.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk J) by
    ext t
    exact e.commutes t]
  rw [RingHom.ker_equiv_comp, Ideal.mk_ker]

/-- Proof-internal AC32 algebra API reducing a surjective scalar map to its quotient by the kernel.
This supplies the tensor-product kernel calculation used by the affine ideal-sheaf pullback. -/
private theorem ker_tensor_algebraMap_of_surjective
    {R T Q : Type*} [CommRing R] [CommRing T] [CommRing Q]
    [Algebra R T] [Algebra R Q]
    (hq : Function.Surjective (algebraMap R Q)) :
    RingHom.ker (algebraMap T (T ⊗[R] Q)) =
      Ideal.map (algebraMap R T) (RingHom.ker (algebraMap R Q)) := by
  let q : (R ⧸ RingHom.ker (algebraMap R Q)) ≃ₐ[R] Q :=
    Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId R Q) hq
  let e : T ⊗[R] Q ≃ₐ[T]
      T ⊗[R] (R ⧸ RingHom.ker (algebraMap R Q)) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) q.symm
  rw [← RingHom.ker_equiv_comp
    (algebraMap T (T ⊗[R] Q)) e.toRingEquiv]
  rw [show e.toRingEquiv.toRingHom.comp (algebraMap T (T ⊗[R] Q)) =
      algebraMap T (T ⊗[R] (R ⧸ RingHom.ker (algebraMap R Q))) by
    ext t
    exact e.commutes t]
  exact ker_tensor_quotient_algebraMap (RingHom.ker (algebraMap R Q))

/-- Proof-internal AC32 categorical API transporting the surjective tensor-product kernel formula
to Mathlib's `CommRingCat` pushout presentation. -/
private theorem ker_pushout_inl_of_surjective
    {R T Q : CommRingCat} (f : R ⟶ T) (q : R ⟶ Q)
    (hq : Function.Surjective q.hom) :
    RingHom.ker (pushout.inl f q).hom =
      Ideal.map f.hom (RingHom.ker q.hom) := by
  letI := f.hom.toAlgebra
  letI := q.hom.toAlgebra
  rw [← show _ = pushout.inl f q from
    colimit.isoColimitCocone_ι_inv
      ⟨_, CommRingCat.pushoutCoconeIsColimit R T Q⟩ WalkingSpan.left]
  rw [CommRingCat.hom_comp]
  rw [RingHom.ker_comp_of_injective _
    (ConcreteCategory.injective_of_mono_of_preservesPullback _)]
  dsimp only [CommRingCat.pushoutCocone_inl, PushoutCocone.ι_app_left]
  exact ker_tensor_algebraMap_of_surjective hq

/-- Proof-internal AC32 ideal-sheaf API: between affine schemes, comap of a global-section ideal
is induced by the actual `appTop` ring map.  The result is derived through Mathlib's closed
subscheme pullback and pushout APIs. -/
private theorem ofIdealTop_comap_of_isAffine
    {Y Z : Scheme} [IsAffine Y] [IsAffine Z]
    (I : Ideal Γ(Z, ⊤)) (g : Y ⟶ Z) :
    (Scheme.IdealSheafData.ofIdealTop I).comap g =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map g.appTop.hom I) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.comap, Scheme.ker_of_isAffine]
  simp
  letI : IsAffine (Scheme.IdealSheafData.ofIdealTop I).subscheme :=
    isAffine_of_isAffineHom
      (Scheme.IdealSheafData.ofIdealTop I).subschemeι
  erw [← PreservesPullback.iso_inv_fst AffineScheme.forgetToScheme
    (AffineScheme.ofHom g)
    (AffineScheme.ofHom (Scheme.IdealSheafData.ofIdealTop I).subschemeι)]
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  let ePullback := PreservesPullback.iso AffineScheme.forgetToScheme
    (AffineScheme.ofHom g)
    (AffineScheme.ofHom (Scheme.IdealSheafData.ofIdealTop I).subschemeι)
  let eRing := (asIso ePullback.inv.appTop).commRingCatIsoToRingEquiv
  change RingHom.ker
      (eRing.toRingHom.comp
        (AffineScheme.forgetToScheme.map
          (pullback.fst (AffineScheme.ofHom g)
            (AffineScheme.ofHom
              (Scheme.IdealSheafData.ofIdealTop I).subschemeι))).appTop.hom) = _
  rw [RingHom.ker_equiv_comp]
  rw [AffineScheme.forgetToScheme_map]
  have hΓ := congr_arg Quiver.Hom.unop
      (PreservesPullback.iso_hom_fst AffineScheme.Γ.rightOp
        (AffineScheme.ofHom g)
        (AffineScheme.ofHom
          (Scheme.IdealSheafData.ofIdealTop I).subschemeι))
  simp only [AffineScheme.Γ, Functor.rightOp_obj, Functor.comp_obj,
    Functor.op_obj, unop_comp, AffineScheme.forgetToScheme_obj,
    Scheme.Γ_obj, Functor.rightOp_map, Functor.comp_map, Functor.op_map,
    Quiver.Hom.unop_op, AffineScheme.forgetToScheme_map, Scheme.Γ_map] at hΓ
  rw [← hΓ]
  rw [CommRingCat.hom_comp]
  rw [RingHom.ker_comp_of_injective _
    (ConcreteCategory.injective_of_mono_of_preservesPullback _)]
  rw [← pushoutIsoUnopPullback_inl_hom]
  rw [CommRingCat.hom_comp]
  rw [RingHom.ker_comp_of_injective _
    (ConcreteCategory.injective_of_mono_of_preservesPullback _)]
  have hq : Function.Surjective
      (Scheme.Hom.appTop
        (AffineScheme.ofHom
          (Scheme.IdealSheafData.ofIdealTop I).subschemeι).hom).hom := by
    change Function.Surjective
      (Scheme.IdealSheafData.ofIdealTop I).subschemeι.appTop.hom
    exact (Scheme.IdealSheafData.ofIdealTop I).subschemeι_app_surjective
      ⟨⊤, isAffineOpen_top Z⟩
  rw [ker_pushout_inl_of_surjective _ _ hq]
  change Ideal.map g.appTop.hom
    (RingHom.ker
      (Scheme.IdealSheafData.ofIdealTop I).subschemeι.appTop.hom) = _
  have hk := (Scheme.IdealSheafData.ofIdealTop I).ker_subschemeι_app
    ⟨⊤, isAffineOpen_top Z⟩
  have hk' : RingHom.ker
      (Scheme.IdealSheafData.ofIdealTop I).subschemeι.appTop.hom = I := by
    simpa using hk
  rw [hk']

/-- Proof-internal AC32 restriction API: along an open immersion with affine source, comap of a
global-section ideal is induced by the actual `appTop` restriction map. -/
private theorem ofIdealTop_comap_of_isOpenImmersion
    {Y Z : Scheme} [IsAffine Y]
    (I : Ideal Γ(Z, ⊤)) (g : Y ⟶ Z) [IsOpenImmersion g] :
    (Scheme.IdealSheafData.ofIdealTop I).comap g =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map g.appTop.hom I) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
  let e := g.appIso ⊤
  have comap_inv (J : Ideal Γ(Z,
      g ''ᵁ (⊤ : Y.Opens))) :
      Ideal.comap e.inv.hom J = Ideal.map e.hom.hom J := by
    ext x
    constructor
    · intro hx
      change e.inv x ∈ J at hx
      simpa using Ideal.mem_map_of_mem e.hom.hom hx
    · intro hx
      rw [Ideal.mem_map_iff_of_surjective e.hom.hom
        e.commRingCatIsoToRingEquiv.surjective] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      change e.inv x ∈ J
      rw [← hxy]
      simpa using hy
  rw [comap_inv, Ideal.map_map]
  have appTop_eq :
      e.hom.hom.comp
          (Z.presheaf.map (homOfLE le_top).op).hom =
        g.appTop.hom := by
    apply RingHom.ext
    intro z
    change
      ((Z.presheaf.map (homOfLE le_top).op) ≫ e.hom) z =
        g.appTop z
    simp only [e, Scheme.Hom.appIso_hom]
    rw [← Category.assoc]
    rw [g.naturality]
    rw [Category.assoc, ← Functor.map_comp]
    simp
  rw [appTop_eq]
  have top_res :
      (Y.presheaf.map (homOfLE le_top).op).hom =
        RingHom.id Γ(Y, ⊤) := by
    apply RingHom.ext
    intro z
    have h := Y.presheaf.map_id (Opposite.op (⊤ : Y.Opens))
    exact congrArg (fun q => q z) h
  rw [top_res, Ideal.map_id]

/-- Proof-internal AC33 descent API: two ideal sheaves are equal when their comaps to every
chart of a valid architecture affine atlas agree. -/
private theorem idealSheafData_eq_of_architectureAtlas_comap
    {Y : AlgebraicGeometry.Scheme}
    {D : AATReadingDecoration raw Y}
    (atlas : ArchitectureAffineAtlas raw Y D)
    (hatlas : IsArchitectureAffineAtlas raw atlas)
    (I J : Y.IdealSheafData)
    (h : ∀ j : atlas.Index,
      I.comap (atlas.chart j).map =
        J.comap (atlas.chart j).map) :
    I = J := by
  let U (j : atlas.Index) : Y.affineOpens :=
    by
      letI : IsOpenImmersion (atlas.chart j).map :=
        (hatlas.chart_valid j).isOpenImmersion
      letI : IsAffine (atlas.chart j).domain :=
        (atlas.chart j).domain_isAffine
      exact ⟨(atlas.chart j).map ''ᵁ
          (⊤ : (atlas.chart j).domain.Opens),
        (isAffineOpen_top _).image_of_isOpenImmersion (atlas.chart j).map⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · simpa only [U, Scheme.Hom.image_top_eq_opensRange] using
      atlas.jointlyCovers raw hatlas
  intro j
  letI : IsOpenImmersion (atlas.chart j).map :=
    (hatlas.chart_valid j).isOpenImmersion
  letI : IsAffine (atlas.chart j).domain :=
    (atlas.chart j).domain_isAffine
  let e := (atlas.chart j).map.appIso ⊤
  have hj := congrArg
    (fun K : (atlas.chart j).domain.IdealSheafData =>
      K.ideal ⟨⊤, isAffineOpen_top _⟩) (h j)
  change
    (I.comap (atlas.chart j).map).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (J.comap (atlas.chart j).map).ideal ⟨⊤, isAffineOpen_top _⟩ at hj
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hj
  apply Ideal.comap_injective_of_surjective e.inv.hom
    e.symm.commRingCatIsoToRingEquiv.surjective
  simpa only [U, e, Scheme.Hom.image_top_eq_opensRange] using hj

/-- Proof-internal AC33 global-section API: formation of the ideal sheaf generated on the top
open commutes with the canonical coefficient-change projection. -/
private theorem ofIdealTop_comap_baseChangeMap
    (I : Ideal Γ(X.underlying, ⊤))
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (Scheme.IdealSheafData.ofIdealTop (X := X.underlying) I).comap
        (X.baseChangeMap raw f) =
      Scheme.IdealSheafData.ofIdealTop
        (X := (X.baseChange raw f).underlying)
        (Ideal.map (X.baseChangeMap raw f).appTop.hom I) := by
  apply idealSheafData_eq_of_architectureAtlas_comap
    (raw := raw.baseChange f.hom) (X.baseChangedAtlas raw f)
    (X.baseChange raw f).atlasValid
  intro j'
  let j := cast (X.baseChangedAtlas_Index raw f) j'
  have hj' : cast (X.baseChangedAtlas_Index raw f).symm j = j' := by
    simp only [j, cast_eq]
  rw [← hj']
  rw [← Scheme.IdealSheafData.comap_comp]
  rw [(X.baseChangedChart_isPullback raw f j).w]
  rw [Scheme.IdealSheafData.comap_comp]
  letI : IsOpenImmersion (X.atlas.chart j).map :=
    (X.atlasValid.chart_valid j).isOpenImmersion
  letI : IsAffine (X.atlas.chart j).domain :=
    (X.atlas.chart j).domain_isAffine
  let j' := cast (X.baseChangedAtlas_Index raw f).symm j
  letI : IsOpenImmersion ((X.baseChangedAtlas raw f).chart j').map :=
    ((X.baseChange raw f).atlasValid.chart_valid j').isOpenImmersion
  letI : IsAffine ((X.baseChangedAtlas raw f).chart j').domain :=
    ((X.baseChangedAtlas raw f).chart j').domain_isAffine
  rw [ofIdealTop_comap_of_isOpenImmersion]
  rw [ofIdealTop_comap_of_isAffine]
  rw [ofIdealTop_comap_of_isOpenImmersion]
  congr 1
  rw [Ideal.map_map, Ideal.map_map]
  have hTop := congrArg (fun q => q.appTop)
    (X.baseChangedChart_isPullback raw f j).w
  simp only [Scheme.Hom.comp_appTop] at hTop
  exact congrArg (fun q : Γ(X.underlying, ⊤) →+*
      Γ(((X.baseChangedAtlas raw f).chart j').domain, ⊤) => Ideal.map q I)
    (congrArg CommRingCat.Hom.hom hTop.symm)

namespace EquationObservableRealization

variable {raw : RawAmbientRestrictionSystem S k}
variable {X : StandardArchitectureScheme raw}
variable {E : ArchitecturalEquationSystem S.contextPreorder}

/-- The realization ideal sheaf pulls back to the coefficient-changed realization. -/
theorem realizationIdealSheaf_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.realizationIdealSheaf.comap
        (X.baseChangeMap raw f) =
      (R.baseChange f).realizationIdealSheaf := by
  rw [realizationIdealSheaf, realizationIdealSheaf,
    ofIdealTop_comap_baseChangeMap raw X,
    ← R.realizationIdeal_baseChange f]

/-- Every global witness ideal sheaf pulls back to its transported realization. -/
theorem globalWitnessIdealSheaf_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : E.Index) :
    (R.globalWitnessIdealSheaf i).comap
        (X.baseChangeMap raw f) =
      (R.baseChange f).globalWitnessIdealSheaf i := by
  rw [globalWitnessIdealSheaf, globalWitnessIdealSheaf,
    ofIdealTop_comap_baseChangeMap raw X,
    ← R.globalWitnessIdeal_baseChange f i]

/-- The global obstruction ideal sheaf pulls back to its transported realization. -/
theorem globalObstructionIdealSheaf_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.globalObstructionIdealSheaf.comap
        (X.baseChangeMap raw f) =
      (R.baseChange f).globalObstructionIdealSheaf := by
  rw [globalObstructionIdealSheaf, globalObstructionIdealSheaf,
    ofIdealTop_comap_baseChangeMap raw X,
    ← R.globalObstructionIdeal_baseChange f]

/-- The canonical map from the transported equalizer to the source equalizer. -/
noncomputable def realizationBaseChangeMap
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (R.baseChange f).realizationScheme ⟶
      R.realizationScheme :=
  Scheme.IdealSheafData.subschemeMap
    (R.baseChange f).realizationIdealSheaf
    R.realizationIdealSheaf
    (X.baseChangeMap raw f)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_of_eq (R.realizationIdealSheaf_baseChange f)))

/-- The equalizer map lies over the standard coefficient-change projection. -/
@[reassoc] theorem realizationBaseChangeMap_immersion
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.realizationBaseChangeMap f ≫
        R.realizationImmersion =
      (R.baseChange f).realizationImmersion ≫
        X.baseChangeMap raw f := by
  exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- Witness ideal sheaves commute with the generated equalizer map. -/
theorem witnessIdealSheaf_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : E.Index) :
    (R.witnessIdealSheaf i).comap
        (R.realizationBaseChangeMap f) =
      (R.baseChange f).witnessIdealSheaf i := by
  rw [witnessIdealSheaf, witnessIdealSheaf,
    ← Scheme.IdealSheafData.comap_comp,
    R.realizationBaseChangeMap_immersion f,
    Scheme.IdealSheafData.comap_comp,
    R.globalWitnessIdealSheaf_baseChange f i]

/-- The required generated ideal sheaf commutes with coefficient change. -/
theorem generatedIdealSheaf_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.generatedIdealSheaf.comap
        (R.realizationBaseChangeMap f) =
      (R.baseChange f).generatedIdealSheaf := by
  rw [generatedIdealSheaf, generatedIdealSheaf,
    (Scheme.IdealSheafData.map_gc
      (R.realizationBaseChangeMap f)).l_iSup]
  congr 1
  funext i
  exact R.witnessIdealSheaf_baseChange f i.1

/-- The canonical map between the transported and source lawful subschemes. -/
noncomputable def lawfulClosedSubschemeBaseChangeMap
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (R.baseChange f).lawfulClosedSubscheme ⟶
      R.lawfulClosedSubscheme :=
  Scheme.IdealSheafData.subschemeMap
    (R.baseChange f).generatedIdealSheaf
    R.generatedIdealSheaf
    (R.realizationBaseChangeMap f)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_of_eq (R.generatedIdealSheaf_baseChange f)))

/-- The lawful-subscheme map lies over the generated equalizer map. -/
@[reassoc] theorem lawfulClosedSubschemeBaseChangeMap_immersion
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.lawfulClosedSubschemeBaseChangeMap f ≫
        R.lawfulClosedImmersion =
      (R.baseChange f).lawfulClosedImmersion ≫
        R.realizationBaseChangeMap f := by
  exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

end EquationObservableRealization

/-- Proof-internal AC33 per-law API: the source law-witness ideal sheaf pulls back to the
canonically reconstructed target law-witness ideal sheaf, directly from their global equations. -/
private theorem lawWitnessIdealSheaf_baseChange_ofSemanticCore
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : G.Index) :
    let R := ClosedEquationalLawReading.ofSemanticCore raw X G B
    let hR :=
      (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B).witness_compatible
    let R' := ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f
    let hR' :=
      (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
        raw X G B f).witness_compatible
    (lawWitnessIdealSheaf raw X R hR i (Set.mem_univ i)).comap
        (X.baseChangeMap raw f) =
      lawWitnessIdealSheaf
        (raw.baseChange f.hom) (X.baseChange raw f)
        R' hR' i (Set.mem_univ i) := by
  dsimp only
  rw [lawWitnessIdealSheaf_ofGlobalSections raw X _ _ i (Set.mem_univ i)
    (semanticCoreGlobalEquation raw X G B i) rfl]
  rw [lawWitnessIdealSheaf_ofGlobalSections
    (raw.baseChange f.hom) (X.baseChange raw f) _ _ i (Set.mem_univ i)
    (baseChangedSemanticCoreGlobalEquation raw X G B f i) rfl]
  rw [ofIdealTop_comap_baseChangeMap raw X]
  congr 1
  simp only [Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨semanticCoreGlobalEquation raw X G B i a, ⟨a, rfl⟩, rfl⟩


/-- The AC32 per-law chart comparison.  The source side uses the Part 3 semantic-core
realization supplied by `hB`; the target side uses the R6f global-section witness.  The two
chartwise pullbacks are compared through the actual changed-chart square and functoriality of
ideal-sheaf comap. -/
theorem semanticCoreLawWitnessIdeal_baseChangedChart
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (j : X.atlas.Index)
    (i : G.Index) :
    let R' := ClosedEquationalLawReading.baseChangeOfSemanticCore
      raw X G B f
    let hR' :=
      (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
        raw X G B f).witness_compatible
    let j' := cast (X.baseChangedAtlas_Index raw f).symm j
    Scheme.IdealSheafData.comap
        (Scheme.IdealSheafData.ofIdealTop
          (X := (X.atlas.chart j).domain)
          (Ideal.map
            (AlgebraicGeometry.Scheme.ΓSpecIso
              (SheafifiedSectionRing raw
                (X.atlas.chart j).context)).inv.hom
            (Ideal.map
              (B.toSheafifiedSection (X.atlas.chart j).context)
              (G.witnessIdeal (X.atlas.chart j).context i))))
        (X.baseChangedChartMap raw f j) =
      Scheme.IdealSheafData.comap
        (lawWitnessIdealSheaf
          (raw.baseChange f.hom) (X.baseChange raw f)
          R' hR' i (Set.mem_univ i))
        ((X.baseChangedAtlas raw f).chart j').map := by
  dsimp only
  let R := ClosedEquationalLawReading.ofSemanticCore raw X G B
  let hR := ClosedEquationalLawReading.ofSemanticCore_witnessCompatible raw X G B
  let R' := ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f
  let hR' :=
    (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
      raw X G B f).witness_compatible
  have hsource := (semanticCoreIdealSheaf_realized raw X G B hB).2 j i
  change
    (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map
        (Scheme.ΓSpecIso
          (SheafifiedSectionRing raw (X.atlas.chart j).context)).inv.hom
        (Ideal.map
          (B.toSheafifiedSection (X.atlas.chart j).context)
          (G.witnessIdeal (X.atlas.chart j).context i)))).comap
        (X.baseChangedChartMap raw f j) =
      (lawWitnessIdealSheaf
        (raw.baseChange f.hom) (X.baseChange raw f)
        R' hR' i (Set.mem_univ i)).comap
        ((X.baseChangedAtlas raw f).chart
          (cast (X.baseChangedAtlas_Index raw f).symm j)).map
  dsimp only at hsource
  rw [← hsource]
  rw [← Scheme.IdealSheafData.comap_comp]
  rw [← (X.baseChangedChart_isPullback raw f j).w]
  rw [Scheme.IdealSheafData.comap_comp]
  rw [lawWitnessIdealSheaf_ofGlobalSections
    (raw.baseChange f.hom) (X.baseChange raw f) R' hR' i (Set.mem_univ i)
    (baseChangedSemanticCoreGlobalEquation raw X G B f i) rfl]
  rw [lawWitnessIdealSheaf_ofGlobalSections raw X R hR i (Set.mem_univ i)
    (semanticCoreGlobalEquation raw X G B i) rfl]
  rw [← Scheme.IdealSheafData.comap_comp]
  rw [(X.baseChangedChart_isPullback raw f j).w]
  rw [Scheme.IdealSheafData.comap_comp]
  letI : IsOpenImmersion (X.atlas.chart j).map :=
    (X.atlasValid.chart_valid j).isOpenImmersion
  letI : IsAffine (X.atlas.chart j).domain :=
    (X.atlas.chart j).domain_isAffine
  let j' := cast (X.baseChangedAtlas_Index raw f).symm j
  letI : IsOpenImmersion ((X.baseChangedAtlas raw f).chart j').map :=
    ((X.baseChange raw f).atlasValid.chart_valid j').isOpenImmersion
  letI : IsAffine ((X.baseChangedAtlas raw f).chart j').domain :=
    ((X.baseChangedAtlas raw f).chart j').domain_isAffine
  rw [ofIdealTop_comap_of_isOpenImmersion]
  rw [ofIdealTop_comap_of_isAffine]
  rw [ofIdealTop_comap_of_isOpenImmersion]
  congr 1
  rw [Ideal.map_map]
  simp only [Ideal.map_span]
  congr 1
  have hTop := congrArg (fun q => q.appTop)
    (X.baseChangedChart_isPullback raw f j).w
  simp only [Scheme.Hom.comp_appTop] at hTop
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨baseChangedSemanticCoreGlobalEquation raw X G B f i a,
      ⟨a, rfl⟩, ?_⟩
    simpa only [baseChangedSemanticCoreGlobalEquation,
      CommRingCat.comp_apply, RingHom.comp_apply] using congrArg
        (fun q => q (semanticCoreGlobalEquation raw X G B i a)) hTop
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨semanticCoreGlobalEquation raw X G B i a, ⟨a, rfl⟩, ?_⟩
    simpa only [baseChangedSemanticCoreGlobalEquation,
      CommRingCat.comp_apply, RingHom.comp_apply] using congrArg
        (fun q => q (semanticCoreGlobalEquation raw X G B i a)) hTop.symm

/-- The AC33 required-law aggregate equality.  Both generated ideal sheaves are normalized to a
fixed supremum of required per-law witnesses, and pullback commutes with that supremum by the
Mathlib ideal-sheaf Galois connection. -/
theorem lawGeneratedIdealSheaf_baseChange_ofSemanticCore
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    Scheme.IdealSheafData.comap
        (lawGeneratedIdealSheaf raw X
          (ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B))
        (X.baseChangeMap raw f) =
      lawGeneratedIdealSheaf
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed raw X G B f) := by
  rw [lawGeneratedIdealSheaf_eq_iSup_required raw X
    (ClosedEquationalLawReading.ofSemanticCore raw X G B)
    (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B)
    (ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B)]
  rw [lawGeneratedIdealSheaf_eq_iSup_required
    (raw.baseChange f.hom) (X.baseChange raw f)
    (ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
    (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f)
    (ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed raw X G B f)]
  rw [(Scheme.IdealSheafData.map_gc (X.baseChangeMap raw f)).l_iSup]
  congr 1
  funext i
  exact lawWitnessIdealSheaf_baseChange_ofSemanticCore raw X G B f i.1

/-- The AC33 all-selected aggregate equality, obtained from the same per-law global-equation
transport after normalizing both sides to the fixed law-index supremum. -/
theorem allSelectedLawGeneratedIdealSheaf_baseChange_ofSemanticCore
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    Scheme.IdealSheafData.comap
        (allLawGeneratedIdealSheaf raw X
          (ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B))
        (X.baseChangeMap raw f) =
      allLawGeneratedIdealSheaf
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f) := by
  rw [allLawGeneratedIdealSheaf_eq_iSup raw X
    (ClosedEquationalLawReading.ofSemanticCore raw X G B)
    (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B)
    (ClosedEquationalLawReading.ofSemanticCore_allLawsSelected raw X G B)]
  rw [allLawGeneratedIdealSheaf_eq_iSup
    (raw.baseChange f.hom) (X.baseChange raw f)
    (ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
    (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f)
    (ClosedEquationalLawReading.baseChangeOfSemanticCore_allLawsSelected raw X G B f)]
  rw [(Scheme.IdealSheafData.map_gc (X.baseChangeMap raw f)).l_iSup]
  congr 1
  funext i
  exact lawWitnessIdealSheaf_baseChange_ofSemanticCore raw X G B f i

/-- The AC33 canonical map from the target required-law closed subscheme to the source one. -/
noncomputable def lawfulClosedSubschemeBaseChangeMap
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    lawfulClosedSubscheme
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed raw X G B f) ⟶
      lawfulClosedSubscheme raw X
        (ClosedEquationalLawReading.ofSemanticCore raw X G B)
        (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B)
        (ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B) :=
  Scheme.IdealSheafData.subschemeMap
    (lawGeneratedIdealSheaf
      (raw.baseChange f.hom) (X.baseChange raw f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed raw X G B f))
    (lawGeneratedIdealSheaf raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B))
    (X.baseChangeMap raw f)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_of_eq (lawGeneratedIdealSheaf_baseChange_ofSemanticCore raw X G B f)))

/-- The required-law base-change map lies over the canonical coefficient-change projection. -/
@[reassoc] theorem lawfulClosedSubschemeBaseChangeMap_immersion
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    lawfulClosedSubschemeBaseChangeMap raw X G B f ≫
        lawfulClosedImmersion raw X
          (ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B) =
      lawfulClosedImmersion
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed raw X G B f) ≫
          X.baseChangeMap raw f := by
  exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The AC33 canonical map from the target all-law closed subscheme to the source one. -/
noncomputable def allLawfulClosedSubschemeBaseChangeMap
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    allLawfulClosedSubscheme
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f) ⟶
      allLawfulClosedSubscheme raw X
        (ClosedEquationalLawReading.ofSemanticCore raw X G B)
        (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B) :=
  Scheme.IdealSheafData.subschemeMap
    (allLawGeneratedIdealSheaf
      (raw.baseChange f.hom) (X.baseChange raw f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
      (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f))
    (allLawGeneratedIdealSheaf raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B))
    (X.baseChangeMap raw f)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_of_eq (allSelectedLawGeneratedIdealSheaf_baseChange_ofSemanticCore raw X G B f)))

/-- The all-law base-change map lies over the canonical coefficient-change projection. -/
@[reassoc] theorem allLawfulClosedSubschemeBaseChangeMap_immersion
    (G : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    allLawfulClosedSubschemeBaseChangeMap raw X G B f ≫
        allLawfulClosedImmersion raw X
          (ClosedEquationalLawReading.ofSemanticCore raw X G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B) =
      allLawfulClosedImmersion
        (raw.baseChange f.hom) (X.baseChange raw f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore raw X G B f)
        (ClosedEquationalLawReading.baseChangeOfSemanticCore_valid raw X G B f) ≫
        X.baseChangeMap raw f := by
  exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

end LawAlgebra

end

end AAT.AG
