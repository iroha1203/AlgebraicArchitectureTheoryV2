import Formal.AG.ReadingFunctoriality.StandardSchemeCoefficient
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Closed-equational geometry under coefficient change

This module implements the fixed declarations of PRD SD7 / AC31 and the per-law chart comparison
of AC32.  Its input is a source raw system `raw`, a source standard scheme `X`, a semantic equation
core `G` with its source presentation bridge `B`, and a flat coefficient change `f`.  Source and
target `HasSheafify` instances type the two standard schemes; the explicit site-dependent
`HasSheafCompose` instance supplies the coefficient-change compatibility already required by the
canonical scheme pullback.

The fixed definition sends each source global equation through the actual
`StandardArchitectureScheme.baseChangeMap.appTop`.  The target geometric predicate and its
closed-equational witness are then reconstructed from that same transported family by
`ClosedEquationalLawWitness.ofGlobalSections`.  The characterization theorem compares target
vanishing with source vanishing after the actual projection, while the validity theorem derives
restriction compatibility from the global-section constructor.

No target raw bridge, caller-supplied target reading, comparison map, or witness certificate is
accepted.  The six AC31 declarations omit the source bridge validity premise `hB`; the AC32 chart
comparison first uses it through the source chart-ideal realization and then compares the two
pullbacks through the actual changed-chart square.
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
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (i : S.lawUniverse.Index) (a : U.Atom) :
    Γ((X.baseChange raw f).underlying, ⊤) :=
  (X.baseChangeMap raw f).appTop
    (semanticCoreGlobalEquation raw X G B i a)

/-- The AC31 target reading generated from the transported global equations.  Its geometric
predicate and witness use the same section family, and `ofGlobalSections` supplies canonical
coordinates instead of accepting a target reading or witness certificate from the caller. -/
noncomputable def ClosedEquationalLawReading.baseChangeOfSemanticCore
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')] :
    ClosedEquationalLawReading
      (raw.baseChange f.hom) (X.baseChange raw f) where
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
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ (X.baseChange raw f).underlying)
    (i : S.lawUniverse.Index) :
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
    (G : SemanticLawEquationWitnessIdealCore S)
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
    (G : SemanticLawEquationWitnessIdealCore S)
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
    (G : SemanticLawEquationWitnessIdealCore S)
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

/-- The AC32 per-law chart comparison.  The source side uses the Part 3 semantic-core
realization supplied by `hB`; the target side uses the R6f global-section witness.  The two
chartwise pullbacks are compared through the actual changed-chart square and functoriality of
ideal-sheaf comap. -/
theorem semanticCoreLawWitnessIdeal_baseChangedChart
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    (f : FlatCoefficientChange k k')
    [S.topology.HasSheafCompose
      (f.coefficientExtension :
        AATCommAlgCat.{u, v} k ⥤ AATCommAlgCat.{u, v} k')]
    (j : X.atlas.Index)
    (i : S.lawUniverse.Index) :
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
              (G.lawWitnessIdeal (X.atlas.chart j).context i))))
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
          (G.lawWitnessIdeal (X.atlas.chart j).context i)))).comap
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

end LawAlgebra

end

end AAT.AG
