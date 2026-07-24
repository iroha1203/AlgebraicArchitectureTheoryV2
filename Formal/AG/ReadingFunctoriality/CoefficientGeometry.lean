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

The equation-system route starts from the represented point source of
`S.equationSystem`.  For every flat coefficient map, the actual base-changed
scheme carries the canonical pullback of the source universal point.
Its observable evaluation, section-dependent architecture reading, regular
residuals, symbolic-residual equalizer, locally glued witness ideals, ideal
sheaves, and lawful closed subscheme are constructed directly from the
coefficient projection, without a second evaluation family or a target
representation premise.  Re-representation of the unchanged absolute point
functor is retained only as an optional isomorphic case; a theorem shows that
such a package forces the coefficient-change projection to be an
isomorphism.

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
Actual re-representation data for the equation-point functor after coefficient
change.  Every component is fixed as pullback of the source universal point
along the concrete coefficient-change morphism; the universal-point equation
and naturality are derived below.
-/
structure BaseChangeRepresentation
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] where
  /-- The coefficient-changed scheme represents the same generated point functor. -/
  representingEquiv :
    ∀ T : AlgebraicGeometry.Scheme.{max u v},
      (T ⟶ (X.baseChange raw f).underlying) ≃
        EquationArchitecturePoint R.reading T
  /--
  Each represented point is generated by pullback of the source universal
  point through the actual coefficient-change map.
  -/
  representingEquiv_eq_pullback :
    ∀ {T : AlgebraicGeometry.Scheme.{max u v}}
      (s : T ⟶ (X.baseChange raw f).underlying),
      representingEquiv T s =
        EquationArchitecturePoint.pullback s
          (EquationArchitecturePoint.pullback (X.baseChangeMap raw f)
            (R.pointAt (𝟙 X.underlying)))

namespace BaseChangeRepresentation

/--
Producer from the actual coefficient-change construction when its projection
is an isomorphism.  No universal-point equality is supplied by the caller.
-/
noncomputable def ofIsIso
    (R : EquationObservableRealization raw X E)
    (hR : IsEquationObservableRealization R)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    [IsIso (X.baseChangeMap raw f)] :
    BaseChangeRepresentation R f where
  representingEquiv T := {
    toFun := fun s =>
      R.representingEquiv T (s ≫ X.baseChangeMap raw f)
    invFun := fun p =>
      (R.representingEquiv T).symm p ≫ inv (X.baseChangeMap raw f)
    left_inv := by
      intro s
      simp
    right_inv := by
      intro p
      simp
  }
  representingEquiv_eq_pullback := by
    intro T s
    change R.pointAt (s ≫ X.baseChangeMap raw f) = _
    rw [hR.representingEquiv_natural (X.baseChangeMap raw f) s]
    congr 1
    simpa only [Category.comp_id] using
      hR.representingEquiv_natural
        (𝟙 X.underlying) (X.baseChangeMap raw f)

/--
Producer for every bijective flat coefficient map.  Bijectivity makes the
coefficient affine map an isomorphism, hence the actual pullback projection
`baseChangeMap` is an isomorphism.
-/
noncomputable def ofBijectiveCoefficient
    (R : EquationObservableRealization raw X E)
    (hR : IsEquationObservableRealization R)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (hf : Function.Bijective f.hom) :
    BaseChangeRepresentation R f := by
  have hlifted : Function.Bijective f.liftedHom :=
    ULift.ringEquiv.symm.bijective.comp
      (hf.comp ULift.ringEquiv.bijective)
  letI : IsIso (CommRingCat.ofHom f.liftedHom) :=
    (ConcreteCategory.isIso_iff_bijective
      (CommRingCat.ofHom f.liftedHom)).mpr hlifted
  letI : IsIso
      (AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom f.liftedHom).op) := inferInstance
  letI : IsIso (X.baseChangeMap raw f) := by
    rw [StandardArchitectureScheme.baseChangeMap_eq_pullback_fst]
    infer_instance
  exact ofIsIso R hR f

/-- Naturality is generated from the componentwise pullback formula. -/
theorem representingEquiv_natural
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f)
    {T T' : AlgebraicGeometry.Scheme.{max u v}}
    (s : T ⟶ (X.baseChange raw f).underlying) (g : T' ⟶ T) :
    P.representingEquiv T' (g ≫ s) =
      EquationArchitecturePoint.pullback g (P.representingEquiv T s) := by
  rw [P.representingEquiv_eq_pullback,
    P.representingEquiv_eq_pullback]
  exact EquationArchitecturePoint.pullback_comp s g
    (EquationArchitecturePoint.pullback (X.baseChangeMap raw f)
      (R.pointAt (𝟙 X.underlying)))

/--
The represented universal point is derived from the component formula.
-/
theorem universalPoint
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    P.representingEquiv (X.baseChange raw f).underlying
        (𝟙 (X.baseChange raw f).underlying) =
      EquationArchitecturePoint.pullback (X.baseChangeMap raw f)
        (R.pointAt (𝟙 X.underlying)) := by
  rw [P.representingEquiv_eq_pullback]
  exact EquationArchitecturePoint.pullback_id _

/--
Re-representing the unchanged absolute point functor forces the actual
coefficient-change projection to be an isomorphism.  Thus
`BaseChangeRepresentation` is an optional re-representation package, while
the general flat geometry below does not depend on it.
-/
theorem baseChangeMap_isIso
    (R : EquationObservableRealization raw X E)
    (hR : IsEquationObservableRealization R)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    IsIso (X.baseChangeMap raw f) := by
  let b := X.baseChangeMap raw f
  have hP :
      ∀ {T : AlgebraicGeometry.Scheme.{max u v}}
        (s : T ⟶ (X.baseChange raw f).underlying),
        P.representingEquiv T s = R.pointAt (s ≫ b) := by
    intro T s
    calc
      P.representingEquiv T s =
          EquationArchitecturePoint.pullback s
            (EquationArchitecturePoint.pullback b
              (R.pointAt (𝟙 X.underlying))) :=
        P.representingEquiv_eq_pullback s
      _ = EquationArchitecturePoint.pullback s (R.pointAt b) := by
        congr 1
        simpa only [b, Category.comp_id] using
          (hR.representingEquiv_natural
            (𝟙 X.underlying) b).symm
      _ = R.pointAt (s ≫ b) :=
        (hR.representingEquiv_natural b s).symm
  let g : X.underlying ⟶ (X.baseChange raw f).underlying :=
    (P.representingEquiv X.underlying).symm
      (R.pointAt (𝟙 X.underlying))
  have hgb : g ≫ b = 𝟙 X.underlying := by
    apply (R.representingEquiv X.underlying).injective
    have hg :=
      (P.representingEquiv X.underlying).apply_symm_apply
        (R.pointAt (𝟙 X.underlying))
    exact (hP g).symm.trans (by simpa only [g] using hg)
  have hbg : b ≫ g = 𝟙 (X.baseChange raw f).underlying := by
    apply (P.representingEquiv
      (X.baseChange raw f).underlying).injective
    rw [hP, hP, Category.assoc, hgb,
      Category.comp_id, Category.id_comp]
  exact ⟨⟨g, hbg, hgb⟩⟩

/-- A concrete flat, bijective coefficient change exchanging two factors. -/
def coefficientSwap
    (K : Type v) [CommRing K] :
    FlatCoefficientChange (K × K) (K × K) where
  hom := (RingEquiv.prodComm (R := K) (S := K)).toRingHom
  flat := RingHom.Flat.of_bijective
    (RingEquiv.prodComm (R := K) (S := K)).bijective

/-- The factor exchange is a genuinely nonidentity coefficient map. -/
theorem coefficientSwap_ne_refl
    (K : Type v) [CommRing K] [Nontrivial K] :
    (coefficientSwap K).hom ≠
      (FlatCoefficientChange.refl (K × K)).hom := by
  intro h
  have hpair := RingHom.congr_fun h ((0 : K), (1 : K))
  have hfirst := congrArg Prod.fst hpair
  exact (one_ne_zero : (1 : K) ≠ 0) (by simpa [coefficientSwap,
    FlatCoefficientChange.refl] using hfirst)

/--
The nonidentity factor exchange fires the actual base-change representation
producer for every selected equation realization.
-/
noncomputable def ofCoefficientSwap
    {K : Type v} [CommRing K]
    {raw₀ : RawAmbientRestrictionSystem S (K × K)}
    [HasSheafify S.topology (AATCommAlgCat (K × K))]
    {X₀ : StandardArchitectureScheme raw₀}
    {E₀ : ArchitecturalEquationSystem S.contextPreorder}
    (R₀ : EquationObservableRealization raw₀ X₀ E₀)
    (hR₀ : IsEquationObservableRealization R₀)
    [S.topology.HasSheafCompose
      ((coefficientSwap K).coefficientExtension :
        AATCommAlgCat.{u, v} (K × K) ⥤
          AATCommAlgCat.{u, v} (K × K))] :
    BaseChangeRepresentation R₀ (coefficientSwap K) :=
  ofBijectiveCoefficient R₀ hR₀ (coefficientSwap K)
    (RingEquiv.prodComm (R := K) (S := K)).bijective

end BaseChangeRepresentation

/--
Coefficient change uses the supplied natural representation on the actual
base-changed standard scheme.
-/
noncomputable def baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    EquationObservableRealization
      (raw.baseChange f.hom) (X.baseChange raw f) E :=
  EquationObservableRealization.ofRepresentingEquiv
    R.reading P.representingEquiv

/-- The supplied natural representation validates the coefficient-changed realization. -/
theorem baseChange_valid
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    IsEquationObservableRealization (R.baseChange f P) :=
  EquationObservableRealization.ofRepresentingEquiv_valid
    R.reading P.representingEquiv
      (BaseChangeRepresentation.representingEquiv_natural
        R f P)

/--
The concrete nonidentity factor exchange fires the actual coefficient-change
realization producer and its derived naturality theorem.
-/
theorem coefficientSwap_baseChange_valid
    {K : Type v} [CommRing K]
    {raw₀ : RawAmbientRestrictionSystem S (K × K)}
    [HasSheafify S.topology (AATCommAlgCat (K × K))]
    {X₀ : StandardArchitectureScheme raw₀}
    {E₀ : ArchitecturalEquationSystem S.contextPreorder}
    (R₀ : EquationObservableRealization raw₀ X₀ E₀)
    (hR₀ : IsEquationObservableRealization R₀)
    [S.topology.HasSheafCompose
      ((BaseChangeRepresentation.coefficientSwap K).coefficientExtension :
        AATCommAlgCat.{u, v} (K × K) ⥤
          AATCommAlgCat.{u, v} (K × K))] :
    IsEquationObservableRealization
      (R₀.baseChange
        (BaseChangeRepresentation.coefficientSwap K)
        (BaseChangeRepresentation.ofCoefficientSwap R₀ hR₀)) :=
  R₀.baseChange_valid
    (BaseChangeRepresentation.coefficientSwap K)
    (BaseChangeRepresentation.ofCoefficientSwap R₀ hR₀)

/-- The transported universal map is the source map followed by `baseChangeMap`. -/
theorem baseChange_sectionMap_eq
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f)
    (W : S.category) :
    (R.baseChange f P).sectionMap W =
      (X.baseChangeMap raw f).appTop.hom.comp
        (R.sectionMap W) := by
  ext x
  have h := congrArg
    (fun p : EquationArchitecturePoint R.reading
        (X.baseChange raw f).underlying => p.evaluation W x)
    (BaseChangeRepresentation.universalPoint R f P)
  simpa [EquationObservableRealization.sectionMap,
    EquationObservableRealization.evaluation,
    EquationObservableRealization.pointAt,
    EquationArchitecturePoint.pullback, baseChange] using h

/-- Application form of `baseChange_sectionMap_eq`. -/
@[simp] theorem baseChange_sectionMap
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f)
    (W : S.category) (x : E.Observable W) :
    (R.baseChange f P).sectionMap W x =
      (X.baseChangeMap raw f).appTop (R.sectionMap W x) := by
  rw [R.baseChange_sectionMap_eq f P]
  rfl

/-- Decoration-context specialization of the transported universal map. -/
theorem baseSectionMap_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    ∀ P : BaseChangeRepresentation R f,
    (R.baseChange f P).sectionMap X.decoration.context =
      (X.baseChangeMap raw f).appTop.hom.comp
        (R.sectionMap X.decoration.context) :=
  fun P => R.baseChange_sectionMap_eq f P X.decoration.context

/-- The transported universal reading is the actual pullback of the source reading. -/
theorem baseChange_universalReading
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    ((R.baseChange f P).pointAt
        (𝟙 (X.baseChange raw f).underlying)).reading =
      R.reading.pullback (X.baseChangeMap raw f)
        (R.pointAt (𝟙 X.underlying)).reading := by
  have h := congrArg
    (fun p : EquationArchitecturePoint R.reading
        (X.baseChange raw f).underlying => p.reading)
    (BaseChangeRepresentation.universalPoint R f P)
  simpa [EquationObservableRealization.pointAt,
    EquationArchitecturePoint.pullback, baseChange] using h

@[simp] theorem violationSection_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    (R.baseChange f P).violationSection W i a =
      (X.baseChangeMap raw f).appTop
        (R.violationSection W i a) := by
  rw [violationSection, violationSection,
    R.baseChange_sectionMap f P]

@[simp] theorem residualSection_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    (R.baseChange f P).residualSection W i a =
      (X.baseChangeMap raw f).appTop
        (R.residualSection W i a) := by
  rw [EquationObservableRealization.residualSection,
    EquationObservableRealization.residualSection]
  rw [R.baseChange_sectionMap f P]
  change
    (X.baseChangeMap raw f).appTop
        (R.sectionMap W
          (E.equationResidual W
            (R.reading.object
              ((R.baseChange f P).pointAt
                (𝟙 (X.baseChange raw f).underlying)).reading)
            i a)) =
      (X.baseChangeMap raw f).appTop
        (R.sectionMap W
          (E.equationResidual W
            (R.reading.object
              (R.pointAt (𝟙 X.underlying)).reading)
            i a))
  rw [R.baseChange_universalReading f P]
  exact R.reading.residual_pullback
    (X.baseChangeMap raw f)
    (R.pointAt (𝟙 X.underlying)).reading W i a
    (R.sectionMap W)

@[simp] theorem ambientResidualSection_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    (R.baseChange f P).ambientResidualSection W i a =
      (X.baseChangeMap raw f).appTop
        (R.ambientResidualSection W i a) :=
  R.residualSection_baseChange f P W i a

@[simp] theorem realizationRelation_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f)
    (g : EquationObservableRealization.GeneratorIndex E) :
    (R.baseChange f P).realizationRelation g =
      (X.baseChangeMap raw f).appTop (R.realizationRelation g) := by
  simp only [realizationRelation, violationSection_baseChange R f P,
    ambientResidualSection_baseChange R f P, map_sub]

/-- The equalizer ideal is extended by the actual coefficient map. -/
theorem realizationIdeal_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    (R.baseChange f P).realizationIdeal =
      Ideal.map (X.baseChangeMap raw f).appTop.hom
        R.realizationIdeal := by
  rw [realizationIdeal, realizationIdeal, Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨R.realizationRelation g, ⟨g, rfl⟩,
      (R.realizationRelation_baseChange f P g).symm⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, R.realizationRelation_baseChange f P g⟩

/-- Every global witness ideal is extended by the actual coefficient map. -/
theorem globalWitnessIdeal_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f)
    (i : E.Index) :
    (R.baseChange f P).globalWitnessIdeal i =
      Ideal.map (X.baseChangeMap raw f).appTop.hom
        (R.globalWitnessIdeal i) := by
  rw [globalWitnessIdeal, globalWitnessIdeal, Ideal.map_iSup]
  congr 1
  funext W
  rw [contextWitnessIdeal, contextWitnessIdeal,
    R.baseChange_sectionMap_eq f P W, Ideal.map_map]

/-- The global obstruction ideal is extended by the actual coefficient map. -/
theorem globalObstructionIdeal_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    (R.baseChange f P).globalObstructionIdeal =
      Ideal.map (X.baseChangeMap raw f).appTop.hom
        R.globalObstructionIdeal := by
  rw [globalObstructionIdeal, globalObstructionIdeal, Ideal.map_iSup]
  congr 1
  funext W
  rw [R.baseChange_sectionMap_eq f P W, Ideal.map_map]

/-! ### Canonical geometry for every flat coefficient change -/

/--
The canonical coefficient-changed universal point.  It exists for every flat
coefficient change and is the pullback of the source universal point along
the actual standard-scheme projection; no target representation is required.
-/
noncomputable def flatBaseChangePoint
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    EquationArchitecturePoint R.reading
      (X.baseChange raw f).underlying :=
  EquationArchitecturePoint.pullback (X.baseChangeMap raw f)
    (R.pointAt (𝟙 X.underlying))

/-- Observable sections transported by the actual coefficient-change map. -/
noncomputable def flatBaseChangeSectionMap
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    E.Observable W →+* Γ((X.baseChange raw f).underlying, ⊤) :=
  (R.flatBaseChangePoint f).evaluation W

/-- The canonical section map is the source section map followed by projection. -/
theorem flatBaseChangeSectionMap_eq
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    R.flatBaseChangeSectionMap f W =
      (X.baseChangeMap raw f).appTop.hom.comp (R.sectionMap W) :=
  rfl

/-- The architecture read from the canonical coefficient-changed point. -/
noncomputable def flatBaseChangeArchitecture
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    ArchitectureObject U :=
  R.reading.object (R.flatBaseChangePoint f).reading

/-- Canonically transported symbolic violation section. -/
noncomputable def flatBaseChangeViolationSection
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) (i : E.Index) (a : U.Atom) :
    Γ((X.baseChange raw f).underlying, ⊤) :=
  R.flatBaseChangeSectionMap f W (E.violationCoordinate W i a)

/-- Canonically transported object-dependent residual section. -/
noncomputable def flatBaseChangeResidualSection
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) (i : E.Index) (a : U.Atom) :
    Γ((X.baseChange raw f).underlying, ⊤) :=
  R.flatBaseChangeSectionMap f W
    (E.equationResidual W (R.flatBaseChangeArchitecture f) i a)

/-- Residual transport is derived from architecture-reading pullback. -/
theorem flatBaseChangeResidualSection_eq
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) (i : E.Index) (a : U.Atom) :
    R.flatBaseChangeResidualSection f W i a =
      (X.baseChangeMap raw f).appTop (R.residualSection W i a) := by
  exact R.reading.residual_pullback
    (X.baseChangeMap raw f)
    (R.pointAt (𝟙 X.underlying)).reading W i a
    (R.sectionMap W)

/-- One transported equalizer relation. -/
noncomputable def flatBaseChangeRealizationRelation
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (g : GeneratorIndex E) :
    Γ((X.baseChange raw f).underlying, ⊤) :=
  R.flatBaseChangeViolationSection f g.1 g.2.1 g.2.2 -
    R.flatBaseChangeResidualSection f g.1 g.2.1 g.2.2

/-- Every transported relation is the actual image of its source relation. -/
theorem flatBaseChangeRealizationRelation_eq
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (g : GeneratorIndex E) :
    R.flatBaseChangeRealizationRelation f g =
      (X.baseChangeMap raw f).appTop (R.realizationRelation g) := by
  rw [flatBaseChangeRealizationRelation,
    flatBaseChangeViolationSection, flatBaseChangeSectionMap_eq,
    flatBaseChangeResidualSection_eq]
  rw [realizationRelation, violationSection, map_sub]
  rfl

/-- The equalizer ideal generated on the coefficient-changed scheme. -/
noncomputable def flatBaseChangeRealizationIdeal
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    Ideal Γ((X.baseChange raw f).underlying, ⊤) :=
  Ideal.span (Set.range (R.flatBaseChangeRealizationRelation f))

/-- The flat coefficient equalizer ideal is scalar extension of the source. -/
theorem flatBaseChangeRealizationIdeal_eq
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.flatBaseChangeRealizationIdeal f =
      Ideal.map (X.baseChangeMap raw f).appTop.hom
        R.realizationIdeal := by
  rw [flatBaseChangeRealizationIdeal, realizationIdeal, Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨R.realizationRelation g, ⟨g, rfl⟩,
      (R.flatBaseChangeRealizationRelation_eq f g).symm⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, R.flatBaseChangeRealizationRelation_eq f g⟩

/-- The global witness ideal generated by transported equation coordinates. -/
noncomputable def flatBaseChangeGlobalWitnessIdeal
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : E.Index) :
    Ideal Γ((X.baseChange raw f).underlying, ⊤) :=
  ⨆ W : S.category,
    Ideal.map (R.flatBaseChangeSectionMap f W) (E.witnessIdeal W i)

/-- Global witness ideals commute with every flat coefficient change. -/
theorem flatBaseChangeGlobalWitnessIdeal_eq
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : E.Index) :
    R.flatBaseChangeGlobalWitnessIdeal f i =
      Ideal.map (X.baseChangeMap raw f).appTop.hom
        (R.globalWitnessIdeal i) := by
  rw [flatBaseChangeGlobalWitnessIdeal, globalWitnessIdeal, Ideal.map_iSup]
  congr 1
  funext W
  rw [flatBaseChangeSectionMap_eq, contextWitnessIdeal, Ideal.map_map]

/-- The transported global obstruction ideal for every flat coefficient map. -/
noncomputable def flatBaseChangeGlobalObstructionIdeal
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    Ideal Γ((X.baseChange raw f).underlying, ⊤) :=
  ⨆ W : S.category,
    Ideal.map (R.flatBaseChangeSectionMap f W) (E.obstructionIdeal W)

/-- Global obstruction ideals commute with every flat coefficient change. -/
theorem flatBaseChangeGlobalObstructionIdeal_eq
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.flatBaseChangeGlobalObstructionIdeal f =
      Ideal.map (X.baseChangeMap raw f).appTop.hom
        R.globalObstructionIdeal := by
  rw [flatBaseChangeGlobalObstructionIdeal,
    globalObstructionIdeal, Ideal.map_iSup]
  congr 1
  funext W
  rw [flatBaseChangeSectionMap_eq, Ideal.map_map]

/-- A glued local equation section transported through the coefficient map. -/
noncomputable def flatBaseChangeGluedViolationSection
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    (i : E.Index) (a : U.Atom) :
    Γ((X.baseChange raw f).underlying, ⊤) :=
  (X.baseChangeMap raw f).appTop
    (R.gluedViolationSection C P.coordinate i a)

/-- The transported ideal generated from the glued local equation family. -/
noncomputable def flatBaseChangeGluedWitnessIdeal
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    (i : E.Index) :
    Ideal Γ((X.baseChange raw f).underlying, ⊤) :=
  Ideal.span (Set.range
    (R.flatBaseChangeGluedViolationSection f C P i))

/-- Locally glued witness ideals commute with every flat coefficient change. -/
theorem flatBaseChangeGluedWitnessIdeal_eq
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    (i : E.Index) :
    R.flatBaseChangeGluedWitnessIdeal f C P i =
      Ideal.map (X.baseChangeMap raw f).appTop.hom
        (R.gluedWitnessIdeal C P.coordinate i) := by
  rw [flatBaseChangeGluedWitnessIdeal, gluedWitnessIdeal, Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨R.gluedViolationSection C P.coordinate i a,
      ⟨a, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

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

/-- The equalizer ideal sheaf constructed for every flat coefficient change. -/
noncomputable def flatBaseChangeRealizationIdealSheaf
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (X.baseChange raw f).underlying.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (R.flatBaseChangeRealizationIdeal f)

/--
The source equalizer ideal sheaf pulls back to the canonically generated
coefficient-changed equalizer for every flat coefficient map.
-/
theorem realizationIdealSheaf_flatBaseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.realizationIdealSheaf.comap (X.baseChangeMap raw f) =
      R.flatBaseChangeRealizationIdealSheaf f := by
  rw [realizationIdealSheaf, flatBaseChangeRealizationIdealSheaf,
    ofIdealTop_comap_baseChangeMap raw X,
    R.flatBaseChangeRealizationIdeal_eq f]

/-- The coefficient-changed equalizer scheme for an arbitrary flat map. -/
noncomputable def flatBaseChangeRealizationScheme
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    AlgebraicGeometry.Scheme :=
  (R.flatBaseChangeRealizationIdealSheaf f).subscheme

/-- Its canonical closed immersion into the base-changed standard scheme. -/
noncomputable def flatBaseChangeRealizationImmersion
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.flatBaseChangeRealizationScheme f ⟶
      (X.baseChange raw f).underlying :=
  (R.flatBaseChangeRealizationIdealSheaf f).subschemeι

/-- The canonical map from the flatly transported equalizer to the source. -/
noncomputable def flatRealizationBaseChangeMap
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.flatBaseChangeRealizationScheme f ⟶ R.realizationScheme :=
  Scheme.IdealSheafData.subschemeMap
    (R.flatBaseChangeRealizationIdealSheaf f)
    R.realizationIdealSheaf
    (X.baseChangeMap raw f)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_of_eq (R.realizationIdealSheaf_flatBaseChange f)))

/-- The general flat equalizer map lies over the actual coefficient projection. -/
@[reassoc] theorem flatRealizationBaseChangeMap_immersion
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.flatRealizationBaseChangeMap f ≫ R.realizationImmersion =
      R.flatBaseChangeRealizationImmersion f ≫
        X.baseChangeMap raw f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- A transported global witness ideal sheaf on the changed ambient scheme. -/
noncomputable def flatBaseChangeGlobalWitnessIdealSheaf
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : E.Index) :
    (X.baseChange raw f).underlying.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (R.flatBaseChangeGlobalWitnessIdeal f i)

/-- Every source global witness sheaf pulls back along an arbitrary flat map. -/
theorem globalWitnessIdealSheaf_flatBaseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : E.Index) :
    (R.globalWitnessIdealSheaf i).comap (X.baseChangeMap raw f) =
      R.flatBaseChangeGlobalWitnessIdealSheaf f i := by
  rw [globalWitnessIdealSheaf, flatBaseChangeGlobalWitnessIdealSheaf,
    ofIdealTop_comap_baseChangeMap raw X,
    R.flatBaseChangeGlobalWitnessIdeal_eq f i]

/-- A transported global obstruction ideal sheaf on the changed ambient scheme. -/
noncomputable def flatBaseChangeGlobalObstructionIdealSheaf
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (X.baseChange raw f).underlying.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (R.flatBaseChangeGlobalObstructionIdeal f)

/-- The source obstruction sheaf pulls back along every flat coefficient map. -/
theorem globalObstructionIdealSheaf_flatBaseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    R.globalObstructionIdealSheaf.comap (X.baseChangeMap raw f) =
      R.flatBaseChangeGlobalObstructionIdealSheaf f := by
  rw [globalObstructionIdealSheaf,
    flatBaseChangeGlobalObstructionIdealSheaf,
    ofIdealTop_comap_baseChangeMap raw X,
    R.flatBaseChangeGlobalObstructionIdeal_eq f]

/--
The transported sheaf generated from compatible local equation sections on
the changed ambient scheme.
-/
noncomputable def flatBaseChangeGluedWitnessIdealSheaf
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    (i : E.Index) :
    (X.baseChange raw f).underlying.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (R.flatBaseChangeGluedWitnessIdeal f C P i)

/-- Locally glued ambient witness sheaves commute with every flat change. -/
theorem gluedWitnessIdealSheaf_flatBaseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    (i : E.Index) :
    (R.gluedWitnessIdealSheaf C P.coordinate i).comap
        (X.baseChangeMap raw f) =
      R.flatBaseChangeGluedWitnessIdealSheaf f C P i := by
  rw [gluedWitnessIdealSheaf, flatBaseChangeGluedWitnessIdealSheaf,
    ofIdealTop_comap_baseChangeMap raw X,
    R.flatBaseChangeGluedWitnessIdeal_eq f C P i]

/-- One transported global witness sheaf on the changed equalizer. -/
noncomputable def flatBaseChangeWitnessIdealSheaf
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : E.Index) :
    (R.flatBaseChangeRealizationScheme f).IdealSheafData :=
  (R.flatBaseChangeGlobalWitnessIdealSheaf f i).comap
    (R.flatBaseChangeRealizationImmersion f)

/-- Global witness sheaves commute with the general flat equalizer map. -/
theorem witnessIdealSheaf_flatBaseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : E.Index) :
    (R.witnessIdealSheaf i).comap
        (R.flatRealizationBaseChangeMap f) =
      R.flatBaseChangeWitnessIdealSheaf f i := by
  rw [witnessIdealSheaf, flatBaseChangeWitnessIdealSheaf,
    ← Scheme.IdealSheafData.comap_comp,
    R.flatRealizationBaseChangeMap_immersion f,
    Scheme.IdealSheafData.comap_comp,
    R.globalWitnessIdealSheaf_flatBaseChange f i]

/-- One locally generated equation witness sheaf on the changed equalizer. -/
noncomputable def flatBaseChangeEquationWitnessIdealSheaf
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    (i : E.Index) :
    (R.flatBaseChangeRealizationScheme f).IdealSheafData :=
  (R.flatBaseChangeGluedWitnessIdealSheaf f C P i).comap
    (R.flatBaseChangeRealizationImmersion f)

/--
The standard locally generated equation witness sheaf commutes with every
flat coefficient change.
-/
theorem equationWitnessIdealSheaf_flatBaseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    (i : E.Index) :
    (R.equationWitnessIdealSheaf C P i).comap
        (R.flatRealizationBaseChangeMap f) =
      R.flatBaseChangeEquationWitnessIdealSheaf f C P i := by
  rw [equationWitnessIdealSheaf,
    flatBaseChangeEquationWitnessIdealSheaf,
    ← Scheme.IdealSheafData.comap_comp,
    R.flatRealizationBaseChangeMap_immersion f,
    Scheme.IdealSheafData.comap_comp,
    R.gluedWitnessIdealSheaf_flatBaseChange f C P i]

/-- The required locally generated ideal on the changed equalizer. -/
noncomputable def flatBaseChangeEquationGeneratedIdealSheaf
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C) :
    (R.flatBaseChangeRealizationScheme f).IdealSheafData :=
  ⨆ i : E.RequiredIndex,
    R.flatBaseChangeEquationWitnessIdealSheaf f C P i.1

/-- Required locally generated ideals commute with every flat change. -/
theorem equationGeneratedIdealSheaf_flatBaseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C) :
    (R.equationGeneratedIdealSheaf C P).comap
        (R.flatRealizationBaseChangeMap f) =
      R.flatBaseChangeEquationGeneratedIdealSheaf f C P := by
  rw [equationGeneratedIdealSheaf,
    flatBaseChangeEquationGeneratedIdealSheaf,
    (Scheme.IdealSheafData.map_gc
      (R.flatRealizationBaseChangeMap f)).l_iSup]
  congr 1
  funext i
  exact R.equationWitnessIdealSheaf_flatBaseChange f C P i.1

/-- The required lawful closed subscheme after an arbitrary flat change. -/
noncomputable def flatBaseChangeEquationLawfulClosedSubscheme
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C) :
    AlgebraicGeometry.Scheme :=
  (R.flatBaseChangeEquationGeneratedIdealSheaf f C P).subscheme

/-- Its canonical closed immersion into the changed equalizer. -/
noncomputable def flatBaseChangeEquationLawfulClosedImmersion
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C) :
    R.flatBaseChangeEquationLawfulClosedSubscheme f C P ⟶
      R.flatBaseChangeRealizationScheme f :=
  (R.flatBaseChangeEquationGeneratedIdealSheaf f C P).subschemeι

/-- The transported required lawful locus is a closed subscheme. -/
theorem flatBaseChangeEquationLawfulClosedImmersion_isClosedImmersion
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C) :
    IsClosedImmersion
      (R.flatBaseChangeEquationLawfulClosedImmersion f C P) := by
  change IsClosedImmersion
    (R.flatBaseChangeEquationGeneratedIdealSheaf f C P).subschemeι
  infer_instance

/-- The canonical lawful-locus map for every flat coefficient change. -/
noncomputable def flatEquationLawfulClosedSubschemeBaseChangeMap
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C) :
    R.flatBaseChangeEquationLawfulClosedSubscheme f C P ⟶
      R.equationGeneratedLawfulClosedSubscheme C P :=
  Scheme.IdealSheafData.subschemeMap
    (R.flatBaseChangeEquationGeneratedIdealSheaf f C P)
    (R.equationGeneratedIdealSheaf C P)
    (R.flatRealizationBaseChangeMap f)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_of_eq
        (R.equationGeneratedIdealSheaf_flatBaseChange f C P)))

/-- The lawful-locus map lies over the general flat equalizer map. -/
@[reassoc] theorem flatEquationLawfulClosedSubschemeBaseChangeMap_immersion
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C) :
    R.flatEquationLawfulClosedSubschemeBaseChangeMap f C P ≫
        R.equationGeneratedLawfulClosedImmersion C P =
      R.flatBaseChangeEquationLawfulClosedImmersion f C P ≫
        R.flatRealizationBaseChangeMap f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/--
Complete general-flat producer: equalizer, every locally generated equation
ideal, the required aggregate, and the lawful closed-locus map are all
constructed without a target representation premise.
-/
theorem flatBaseChangeEquationGeometry_realized
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C) :
    R.realizationIdealSheaf.comap (X.baseChangeMap raw f) =
        R.flatBaseChangeRealizationIdealSheaf f ∧
      (∀ i : E.Index,
        (R.equationWitnessIdealSheaf C P i).comap
            (R.flatRealizationBaseChangeMap f) =
          R.flatBaseChangeEquationWitnessIdealSheaf f C P i) ∧
      (R.equationGeneratedIdealSheaf C P).comap
          (R.flatRealizationBaseChangeMap f) =
        R.flatBaseChangeEquationGeneratedIdealSheaf f C P := by
  exact
    ⟨R.realizationIdealSheaf_flatBaseChange f,
      fun i => R.equationWitnessIdealSheaf_flatBaseChange f C P i,
      R.equationGeneratedIdealSheaf_flatBaseChange f C P⟩

/-- The realization ideal sheaf pulls back to the coefficient-changed realization. -/
theorem realizationIdealSheaf_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    R.realizationIdealSheaf.comap
        (X.baseChangeMap raw f) =
      (R.baseChange f P).realizationIdealSheaf := by
  rw [realizationIdealSheaf, realizationIdealSheaf,
    ofIdealTop_comap_baseChangeMap raw X,
    ← R.realizationIdeal_baseChange f P]

/-- Every global witness ideal sheaf pulls back to its transported realization. -/
theorem globalWitnessIdealSheaf_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f)
    (i : E.Index) :
    (R.globalWitnessIdealSheaf i).comap
        (X.baseChangeMap raw f) =
      (R.baseChange f P).globalWitnessIdealSheaf i := by
  rw [globalWitnessIdealSheaf, globalWitnessIdealSheaf,
    ofIdealTop_comap_baseChangeMap raw X,
    ← R.globalWitnessIdeal_baseChange f P i]

/-- The global obstruction ideal sheaf pulls back to its transported realization. -/
theorem globalObstructionIdealSheaf_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    R.globalObstructionIdealSheaf.comap
        (X.baseChangeMap raw f) =
      (R.baseChange f P).globalObstructionIdealSheaf := by
  rw [globalObstructionIdealSheaf, globalObstructionIdealSheaf,
    ofIdealTop_comap_baseChangeMap raw X,
    ← R.globalObstructionIdeal_baseChange f P]

/-- The canonical map from the transported equalizer to the source equalizer. -/
noncomputable def realizationBaseChangeMap
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    (R.baseChange f P).realizationScheme ⟶
      R.realizationScheme :=
  Scheme.IdealSheafData.subschemeMap
    (R.baseChange f P).realizationIdealSheaf
    R.realizationIdealSheaf
    (X.baseChangeMap raw f)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_of_eq (R.realizationIdealSheaf_baseChange f P)))

/-- The equalizer map lies over the standard coefficient-change projection. -/
@[reassoc] theorem realizationBaseChangeMap_immersion
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    R.realizationBaseChangeMap f P ≫
        R.realizationImmersion =
      (R.baseChange f P).realizationImmersion ≫
        X.baseChangeMap raw f := by
  exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- Witness ideal sheaves commute with the generated equalizer map. -/
theorem witnessIdealSheaf_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f)
    (i : E.Index) :
    (R.witnessIdealSheaf i).comap
        (R.realizationBaseChangeMap f P) =
      (R.baseChange f P).witnessIdealSheaf i := by
  rw [witnessIdealSheaf, witnessIdealSheaf,
    ← Scheme.IdealSheafData.comap_comp,
    R.realizationBaseChangeMap_immersion f P,
    Scheme.IdealSheafData.comap_comp,
    R.globalWitnessIdealSheaf_baseChange f P i]

/-- The required generated ideal sheaf commutes with coefficient change. -/
theorem generatedIdealSheaf_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    R.generatedIdealSheaf.comap
        (R.realizationBaseChangeMap f P) =
      (R.baseChange f P).generatedIdealSheaf := by
  rw [generatedIdealSheaf, generatedIdealSheaf,
    (Scheme.IdealSheafData.map_gc
      (R.realizationBaseChangeMap f P)).l_iSup]
  congr 1
  funext i
  exact R.witnessIdealSheaf_baseChange f P i.1

/-- The canonical map between the transported and source lawful subschemes. -/
noncomputable def lawfulClosedSubschemeBaseChangeMap
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    (R.baseChange f P).lawfulClosedSubscheme ⟶
      R.lawfulClosedSubscheme :=
  Scheme.IdealSheafData.subschemeMap
    (R.baseChange f P).generatedIdealSheaf
    R.generatedIdealSheaf
    (R.realizationBaseChangeMap f P)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_of_eq (R.generatedIdealSheaf_baseChange f P)))

/-- The lawful-subscheme map lies over the generated equalizer map. -/
@[reassoc] theorem lawfulClosedSubschemeBaseChangeMap_immersion
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (P : BaseChangeRepresentation R f) :
    R.lawfulClosedSubschemeBaseChangeMap f P ≫
        R.lawfulClosedImmersion =
      (R.baseChange f P).lawfulClosedImmersion ≫
        R.realizationBaseChangeMap f P := by
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
