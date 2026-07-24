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
`S.equationSystem`.  Coefficient change uses the actual base-changed scheme as
the new representing point functor; its observable evaluation is generated
from the source universal sections followed by the canonical projection.
Section-dependent architecture readings, regular residuals,
symbolic-residual equalizers, generated witness and obstruction ideals, their
ideal sheaves, and both closed subschemes are therefore transported without a
second evaluation family.

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
Point source represented by the coefficient-changed standard scheme.  Its
architecture reading is the source universal reading, and every observable
evaluation is generated by the transported universal section.
-/
private noncomputable def baseChangePointSource
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    EquationArchitecturePointSource E where
  Point T := T ⟶ (X.baseChange raw f).underlying
  pullback g p := g ≫ p
  architecture := fun _ =>
    R.architectureAt (𝟙 X.underlying)
  evaluation := fun p W =>
    p.appTop.hom.comp
      ((X.baseChangeMap raw f).appTop.hom.comp
        (R.sectionMap W))

/--
Coefficient change re-represents the transported universal equation sections
on the actual base-changed standard scheme.
-/
noncomputable def baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    EquationObservableRealization
      (raw.baseChange f.hom) (X.baseChange raw f) E :=
  EquationObservableRealization.ofRepresentingEquiv
    (R.baseChangePointSource f) (fun _ => Equiv.refl _)

/-- Coefficient change preserves source functoriality and representation. -/
theorem baseChange_valid
    (R : EquationObservableRealization raw X E)
    (hR : IsEquationObservableRealization R)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    IsEquationObservableRealization (R.baseChange f) := by
  apply EquationObservableRealization.ofRepresentingEquiv_valid
  · refine {
      pullback_id := ?_,
      pullback_comp := ?_,
      architecture_pullback := ?_,
      evaluation_pullback := ?_,
      evaluation_natural := ?_ }
    · intro T p
      simp [baseChangePointSource]
    · intro T T' T'' g h p
      simp [baseChangePointSource, Category.assoc]
    · intros
      rfl
    · intro T T' g p W x
      rfl
    · intro T p source target g x
      change p.appTop
        ((X.baseChangeMap raw f).appTop
          (R.sectionMap source (E.restrict g x))) =
        p.appTop
          ((X.baseChangeMap raw f).appTop
            (R.sectionMap target x))
      rw [R.sectionMap_natural hR g x]
  · intros
    rfl

/-- The transported universal map is the source map followed by `baseChangeMap`. -/
theorem baseChange_sectionMap_eq
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) :
    (R.baseChange f).sectionMap W =
      (X.baseChangeMap raw f).appTop.hom.comp
        (R.sectionMap W) := by
  ext x
  simp [EquationObservableRealization.sectionMap,
    EquationObservableRealization.evaluation,
    EquationObservableRealization.pointAt,
    baseChange, baseChangePointSource]

/-- Application form of `baseChange_sectionMap_eq`. -/
@[simp] theorem baseChange_sectionMap
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) (x : E.Observable W) :
    (R.baseChange f).sectionMap W x =
      (X.baseChangeMap raw f).appTop (R.sectionMap W x) := by
  rw [R.baseChange_sectionMap_eq f]
  rfl

/-- Decoration-context specialization of the transported universal map. -/
theorem baseSectionMap_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    (R.baseChange f).sectionMap X.decoration.context =
      (X.baseChangeMap raw f).appTop.hom.comp
        (R.sectionMap X.decoration.context) :=
  R.baseChange_sectionMap_eq f X.decoration.context

@[simp] theorem violationSection_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) (i : E.Index) (a : U.Atom) :
    (R.baseChange f).violationSection W i a =
      (X.baseChangeMap raw f).appTop
        (R.violationSection W i a) := by
  rw [violationSection, violationSection,
    R.baseChange_sectionMap]

@[simp] theorem residualSection_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) (i : E.Index) (a : U.Atom) :
    (R.baseChange f).residualSection W i a =
      (X.baseChangeMap raw f).appTop
        (R.residualSection W i a) := by
  rw [EquationObservableRealization.residualSection,
    EquationObservableRealization.residualSection]
  rw [R.baseChange_sectionMap]
  rfl

@[simp] theorem ambientResidualSection_baseChange
    (R : EquationObservableRealization raw X E)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (W : S.category) (i : E.Index) (a : U.Atom) :
    (R.baseChange f).ambientResidualSection W i a =
      (X.baseChangeMap raw f).appTop
        (R.ambientResidualSection W i a) :=
  R.residualSection_baseChange f W i a

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
  rw [globalWitnessIdeal, globalWitnessIdeal, Ideal.map_iSup]
  congr 1
  funext W
  rw [contextWitnessIdeal, contextWitnessIdeal,
    R.baseChange_sectionMap_eq f W, Ideal.map_map]

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
  rw [globalObstructionIdeal, globalObstructionIdeal, Ideal.map_iSup]
  congr 1
  funext W
  rw [R.baseChange_sectionMap_eq f W, Ideal.map_map]

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
