import Formal.AG.ReadingFunctoriality.Coverage
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Whiskering

/-!
# Leray comparison foundations

This module owns the injective-resolution computation used by the selected
Čech-to-sheaf-cohomology comparison fixed by Part 4 R5c.
-/

noncomputable section

namespace AAT.AG.Cohomology

universe u

open CategoryTheory

private theorem addCommGrpIsGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} AddCommGrpCat.{u + 1} := by
  exact {
    locallySmall := by infer_instance
    hasFilteredColimitsOfSize := by infer_instance
    ab5OfSize := by infer_instance
    hasSeparator := HasSeparator.of_equivalence
      (forget₂ (ModuleCat.{u + 1} ℤ)
        AddCommGrpCat.{u + 1}).asEquivalence }

/--
Additive sheaves on an AAT site have enough injectives under the Part 4
`HasSheafify` premise.

The proof transfers sheafification to a small equivalent site, applies the
Grothendieck-abelian sheaf theorem, and then obtains enough injectives.  Thus
the injective-resolution premise required below is derived rather than added
to the fixed statement.
-/
theorem standardAddCommGrpSheafEnoughInjectives
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    EnoughInjectives (Sheaf S.topology AddCommGrpCat.{u + 1}) := by
  letI : IsGrothendieckAbelian.{u + 1} AddCommGrpCat.{u + 1} :=
    addCommGrpIsGrothendieckAbelian
  letI : Functor.IsDenseSubsite S.topology
      ((equivSmallModel.{u + 1} S.category).inverse.inducedTopology S.topology)
      (equivSmallModel.{u + 1} S.category).symm.inverse := by
    change Functor.IsDenseSubsite S.topology
      ((equivSmallModel.{u + 1} S.category).inverse.inducedTopology S.topology)
      (equivSmallModel.{u + 1} S.category).functor
    infer_instance
  letI : HasSheafify
      ((equivSmallModel.{u + 1} S.category).inverse.inducedTopology S.topology)
      AddCommGrpCat.{u + 1} :=
    Equivalence.hasSheafify
      ((equivSmallModel.{u + 1} S.category).inverse.inducedTopology S.topology)
      S.topology (equivSmallModel.{u + 1} S.category).symm
      AddCommGrpCat.{u + 1}
  letI : IsGrothendieckAbelian.{u + 1}
      (Sheaf S.topology AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  infer_instance

/--
The chosen injective resolution used to compute obstruction sheaf
cohomology.

Implementation notes: this definition constructs Mathlib's actual
`InjectiveResolution`; it does not store a user-supplied resolution or a
cohomology conclusion in a certificate.
-/
noncomputable def obstructionInjectiveResolution
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    InjectiveResolution Ob.toAddCommGrpSheaf := by
  letI := standardAddCommGrpSheafEnoughInjectives (S := S)
  exact InjectiveResolution.of Ob.toAddCommGrpSheaf

/--
Mathlib's Ext model of `H'` is computed by the chosen injective resolution.

Implementation notes: this is the library equivalence attached to the actual
injective resolution above, rather than an independently supplied comparison
isomorphism.
-/
noncomputable def obstructionHPrimeInjectiveEquiv
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (X : S.category) (n : Nat) :
    (Ob.toAddCommGrpSheaf).H' n X ≃+
      CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor
          (Sheaf S.topology AddCommGrpCat.{u + 1}) 0).obj
            ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
              (yoneda.obj X ⋙ AddCommGrpCat.free)))
        (obstructionInjectiveResolution Ob).cochainComplex n :=
  (obstructionInjectiveResolution Ob).extAddEquivCohomologyClass

end AAT.AG.Cohomology

noncomputable section

/-!
## Cover-relative Čech complexes as Mathlib cochain complexes

This section identifies the custom additive Čech quotient with the homology of
the Mathlib `CochainComplex` built from the same differential. The class
formula and naturality theorem fix the identification on representatives and
cochain maps.

Implementation notes: this is the SD5 foundation used before constructing the
Leray comparison. The square-zero premise comes only from the intrinsic
`CoverRelativeCechComplex.differential_comp` law. We retain the existing
custom quotient as the PRD source and compare it with Mathlib homology instead
of defining a second cohomology theory. The comparison passes through explicit
short complexes because the `ℕ` cochain shape represents degree zero by
`C⁰ ⟶ C⁰ ⟶ C¹`, with the incoming morphism equal to zero, while successor
degrees use `Cⁿ ⟶ Cⁿ⁺¹ ⟶ Cⁿ⁺²`. The proof transports the kernel/image quotient
through `ShortComplex.abHomologyIso`, then transports homology along the iso
from the actual short complex to this explicit presentation. We do not accept
an arbitrary additive equivalence or caller-supplied comparison data: the
representative formula and cochain-map naturality below determine the bridge
from the selected differential itself.
-/

namespace AAT.AG.Cohomology.CoverRelativeCechComplex

universe u

open CategoryTheory

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 𝒱 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}

/--
The SD5 actual-complex definition. Its objects and differential are the
selected Čech data, and its complex law is derived from `K.differential_comp`.
The following API lemmas expose both components without unfolding the
definition.
-/
noncomputable def toCochainComplex
    (K : CoverRelativeCechComplex 𝒰 Ob) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of
    (fun n ↦ AddCommGrpCat.of (K.AdditiveCochain n))
    (fun n ↦ AddCommGrpCat.ofHom (K.d n))
    (fun n ↦ by
      ext c
      exact K.differential_comp n c)

/-- No-unfold SD5 API: the degree-`n` object is the selected cochain group. -/
@[simp] theorem toCochainComplex_X
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    (K.toCochainComplex.X n : Type u) = K.AdditiveCochain n :=
  rfl

/-- No-unfold SD5 API: the actual differential is the selected differential. -/
@[simp] theorem toCochainComplex_d
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    letI := K.cochainAddCommGroup n
    letI := K.cochainAddCommGroup (n + 1)
    K.toCochainComplex.d n (n + 1) = AddCommGrpCat.ofHom (K.d n) := by
  letI := K.cochainAddCommGroup n
  letI := K.cochainAddCommGroup (n + 1)
  exact CochainComplex.of_d _ _ _ n

namespace Hom

/--
The SD5 morphism bridge. Its only compatibility premise is the intrinsic
`f.commutes` law; no homology-level map or naturality data is supplied by the
caller.
-/
noncomputable def toCochainMap
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) : K.toCochainComplex ⟶ L.toCochainComplex :=
  CochainComplex.ofHom _ _ _ _ _ _
    (fun n ↦ AddCommGrpCat.ofHom (f.app n))
    (fun n ↦ by
      ext c
      exact (f.commutes n c).symm)

/-- No-unfold API: the actual cochain-map component is `f.app`. -/
@[simp] theorem toCochainMap_f
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) (n : ℕ) :
    (f.toCochainMap.f n).hom = f.app n :=
  rfl

end Hom

private noncomputable def explicitShortComplex
    (K : CoverRelativeCechComplex 𝒰 Ob) : ℕ → ShortComplex AddCommGrpCat.{u}
  | 0 => by
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      exact ShortComplex.mk
        (0 : AddCommGrpCat.of (K.AdditiveCochain 0) ⟶
          AddCommGrpCat.of (K.AdditiveCochain 0))
        (AddCommGrpCat.ofHom (K.d 0))
        (by simp)
  | n + 1 => by
      letI := K.cochainAddCommGroup n
      letI := K.cochainAddCommGroup (n + 1)
      letI := K.cochainAddCommGroup (n + 2)
      exact ShortComplex.mk
        (AddCommGrpCat.ofHom (K.d n))
        (AddCommGrpCat.ofHom (K.d (n + 1)))
        (by
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro c
          exact K.differential_comp n c)

private noncomputable def cocycleEquivExplicitKer
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    K.CechCocycleSubgroup n ≃+
      AddMonoidHom.ker (K.explicitShortComplex n).g.hom := by
  cases n with
  | zero =>
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      exact
        { toFun := fun x => ⟨x.1, by
              change K.d 0 x.1 = 0
              exact x.2⟩
          invFun := fun x => ⟨x.1, by
              change K.d 0 x.1 = 0
              exact x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl }
  | succ n =>
      letI := K.cochainAddCommGroup n
      letI := K.cochainAddCommGroup (n + 1)
      letI := K.cochainAddCommGroup (n + 2)
      exact
        { toFun := fun x => ⟨x.1, by
              change K.d (n + 1) x.1 = 0
              exact x.2⟩
          invFun := fun x => ⟨x.1, by
              change K.d (n + 1) x.1 = 0
              exact x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl }

private theorem explicitBoundaryMap_eq_range
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    AddSubgroup.map
        (K.cocycleEquivExplicitKer (n + 1)).toAddMonoidHom
        (K.CechCoboundarySubgroupSucc n) =
      (K.explicitShortComplex (n + 1)).abToCycles.range := by
  letI := K.cochainAddCommGroup n
  letI := K.cochainAddCommGroup (n + 1)
  letI := K.cochainAddCommGroup (n + 2)
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨b, rfl⟩
    change ∃ b', (K.explicitShortComplex (n + 1)).abToCycles b' = _
    refine ⟨b, ?_⟩
    apply Subtype.ext
    rfl
  · rintro ⟨b, rfl⟩
    refine ⟨K.coboundaryCocycle n b, ⟨b, rfl⟩, ?_⟩
    apply Subtype.ext
    rfl

private theorem explicitZeroRange_eq_bot
    (K : CoverRelativeCechComplex 𝒰 Ob) :
    (K.explicitShortComplex 0).abToCycles.range = ⊥ := by
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  rw [eq_bot_iff]
  rintro x ⟨b, rfl⟩
  ext
  rfl

private noncomputable def quotientAddEquivOfAddEquiv
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (N : AddSubgroup G) (M : AddSubgroup H)
    (h : AddSubgroup.map e.toAddMonoidHom N = M) :
    G ⧸ N ≃+ H ⧸ M := by
  let forward : G ⧸ N →+ H ⧸ M :=
    QuotientAddGroup.map N M e.toAddMonoidHom (by
      intro x hx
      change e x ∈ M
      rw [← h]
      exact ⟨x, hx, rfl⟩)
  let backward : H ⧸ M →+ G ⧸ N :=
    QuotientAddGroup.map M N e.symm.toAddMonoidHom (by
      intro y hy
      change e.symm y ∈ N
      have hy' : y ∈ AddSubgroup.map e.toAddMonoidHom N := by
        rw [h]
        exact hy
      rcases hy' with ⟨x, hx, hxy⟩
      rw [← hxy]
      change e.symm (e x) ∈ N
      rw [e.symm_apply_apply]
      exact hx)
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro q
        induction q using QuotientAddGroup.induction_on with
        | _ x =>
            change QuotientAddGroup.mk (e.symm (e x)) = QuotientAddGroup.mk x
            rw [e.symm_apply_apply]
      right_inv := by
        intro q
        induction q using QuotientAddGroup.induction_on with
        | _ y =>
            change QuotientAddGroup.mk (e (e.symm y)) = QuotientAddGroup.mk y
            rw [e.apply_symm_apply]
      map_add' := forward.map_add }

private noncomputable def additiveCechHnEquivExplicitQuotient
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    K.AdditiveCechHn n ≃+
      (AddMonoidHom.ker (K.explicitShortComplex n).g.hom ⧸
        (K.explicitShortComplex n).abToCycles.range) := by
  cases n with
  | zero =>
      letI := K.cochainAddCommGroup 0
      letI := K.cochainAddCommGroup 1
      exact (K.cocycleEquivExplicitKer 0).trans
        (((QuotientAddGroup.quotientAddEquivOfEq
          (K.explicitZeroRange_eq_bot)).trans
            QuotientAddGroup.quotientBot).symm)
  | succ n =>
      letI := K.cochainAddCommGroup n
      letI := K.cochainAddCommGroup (n + 1)
      letI := K.cochainAddCommGroup (n + 2)
      exact quotientAddEquivOfAddEquiv
        (K.cocycleEquivExplicitKer (n + 1))
        (K.CechCoboundarySubgroupSucc n)
        (K.explicitShortComplex (n + 1)).abToCycles.range
        (K.explicitBoundaryMap_eq_range n)

private noncomputable def scPrimeZeroIsoExplicit
    (K : CoverRelativeCechComplex 𝒰 Ob) :
    K.toCochainComplex.sc' 0 0 1 ≅ K.explicitShortComplex 0 := by
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [toCochainComplex, explicitShortComplex])
    (by simp [explicitShortComplex])

private noncomputable def scPrimeSuccIsoExplicit
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    K.toCochainComplex.sc' n (n + 1) (n + 2) ≅
      K.explicitShortComplex (n + 1) := by
  letI := K.cochainAddCommGroup n
  letI := K.cochainAddCommGroup (n + 1)
  letI := K.cochainAddCommGroup (n + 2)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [toCochainComplex, explicitShortComplex])
    (by simp [explicitShortComplex])

private noncomputable def scIsoExplicit
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    K.toCochainComplex.sc n ≅ K.explicitShortComplex n := by
  cases n with
  | zero =>
      exact K.toCochainComplex.isoSc' 0 0 1
          CochainComplex.prev_nat_zero
          (by simp) ≪≫
        K.scPrimeZeroIsoExplicit
  | succ n =>
      exact K.toCochainComplex.isoSc' n (n + 1) (n + 2)
          (CochainComplex.prev_nat_succ n)
          (by simp [Nat.add_assoc]) ≪≫
        K.scPrimeSuccIsoExplicit n

private noncomputable def additiveCechHnEquivExplicitHomology
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    K.AdditiveCechHn n ≃+ (K.explicitShortComplex n).homology :=
  (K.additiveCechHnEquivExplicitQuotient n).trans
    ((K.explicitShortComplex n).abHomologyIso.addCommGroupIsoToAddEquiv.symm)

/--
The main SD5 equivalence between the fixed custom quotient and actual Mathlib
homology.

Implementation notes: degree zero is transported from the kernel modulo the
range of an incoming zero map; successor degrees transport the selected
kernel/image quotient. `ShortComplex.abHomologyIso` realizes each explicit
quotient as short-complex homology, and the inverse of the homology iso induced
by `scIsoExplicit` then lands in `K.toCochainComplex.homology n`. This route
keeps degree zero actual and avoids an arbitrary or caller-supplied
`AddEquiv`; the representative and naturality theorems below fix its action.
-/
noncomputable def additiveCechHnEquivHomology
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    K.AdditiveCechHn n ≃+ K.toCochainComplex.homology n :=
  (K.additiveCechHnEquivExplicitHomology n).trans
    ((ShortComplex.homologyMapIso (K.scIsoExplicit n)).addCommGroupIsoToAddEquiv.symm)

private noncomputable def cocycleInclusion
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    AddCommGrpCat.of (K.CechCocycleSubgroup n) ⟶
      K.toCochainComplex.X n :=
  AddCommGrpCat.ofHom (K.CechCocycleSubgroup n).subtype

private theorem cocycleInclusion_comp_d
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    K.cocycleInclusion n ≫ K.toCochainComplex.d n (n + 1) = 0 := by
  letI := K.cochainAddCommGroup n
  letI := K.cochainAddCommGroup (n + 1)
  rw [K.toCochainComplex_d n]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  exact z.2

/--
Representative-level SD5 API. The cocycle equation supplies the lift to the
actual cycle object; no cycle witness is accepted separately.
-/
noncomputable def cocycleToCycles
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    AddCommGrpCat.of (K.CechCocycleSubgroup n) ⟶
      K.toCochainComplex.cycles n :=
  K.toCochainComplex.liftCycles (K.cocycleInclusion n) (n + 1)
    (by simp)
    (K.cocycleInclusion_comp_d n)

/-- No-unfold API fixing the underlying cochain of `cocycleToCycles`. -/
@[simp] theorem cocycleToCycles_i
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ)
    (z : K.CechCocycleSubgroup n) :
    (K.toCochainComplex.iCycles n).hom ((K.cocycleToCycles n).hom z) = z.1 := by
  have h := ConcreteCategory.congr_hom
    (K.toCochainComplex.liftCycles_i
      (K.cocycleInclusion n) (n + 1)
      (by simp)
      (K.cocycleInclusion_comp_d n)) z
  rw [ConcreteCategory.comp_apply] at h
  exact h

private def additiveClass
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    K.CechCocycleSubgroup n → K.AdditiveCechHn n := by
  cases n with
  | zero => exact fun z => z
  | succ n => exact fun z => QuotientAddGroup.mk z

private theorem additiveCechHnEquivExplicitQuotient_additiveClass
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ)
    (z : K.CechCocycleSubgroup n) :
    K.additiveCechHnEquivExplicitQuotient n (K.additiveClass n z) =
      QuotientAddGroup.mk (K.cocycleEquivExplicitKer n z) := by
  cases n with
  | zero => rfl
  | succ n => rfl

private theorem additiveCechHnEquivExplicitHomology_additiveClass
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ)
    (z : K.CechCocycleSubgroup n) :
    K.additiveCechHnEquivExplicitHomology n (K.additiveClass n z) =
      (K.explicitShortComplex n).homologyπ.hom
        ((K.explicitShortComplex n).abCyclesIso.inv
          (K.cocycleEquivExplicitKer n z)) := by
  apply (K.explicitShortComplex n).abHomologyIso.addCommGroupIsoToAddEquiv.injective
  simp only [additiveCechHnEquivExplicitHomology, AddEquiv.trans_apply]
  rw [AddEquiv.apply_symm_apply]
  rw [K.additiveCechHnEquivExplicitQuotient_additiveClass n z]
  change QuotientAddGroup.mk (K.cocycleEquivExplicitKer n z) =
    ((K.explicitShortComplex n).homologyπ ≫
      (K.explicitShortComplex n).abHomologyIso.hom).hom
        ((K.explicitShortComplex n).abCyclesIso.inv
          (K.cocycleEquivExplicitKer n z))
  dsimp only [ShortComplex.abHomologyIso]
  rw [(K.explicitShortComplex n).abLeftHomologyData.homologyπ_comp_homologyIso_hom]
  simp only [ConcreteCategory.comp_apply, ShortComplex.abCyclesIso]
  have hi := ConcreteCategory.congr_hom
    (Iso.inv_hom_id (K.explicitShortComplex n).abLeftHomologyData.cyclesIso)
    (K.cocycleEquivExplicitKer n z)
  rw [ConcreteCategory.comp_apply] at hi
  have hπ := congrArg
    (K.explicitShortComplex n).abLeftHomologyData.π.hom hi
  simpa using hπ.symm

private theorem cyclesMap_scIsoExplicit_inv_explicitCycle
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ)
    (z : K.CechCocycleSubgroup n) :
    (ShortComplex.cyclesMap (K.scIsoExplicit n).inv).hom
        ((K.explicitShortComplex n).abCyclesIso.inv
          (K.cocycleEquivExplicitKer n z)) =
      (K.cocycleToCycles n).hom z := by
  cases n with
  | zero =>
      apply (AddCommGrpCat.mono_iff_injective
        (K.toCochainComplex.sc 0).iCycles).1 inferInstance
      have hmap := ConcreteCategory.congr_hom
        (ShortComplex.cyclesMap_i (K.scIsoExplicit 0).inv)
        ((K.explicitShortComplex 0).abCyclesIso.inv
          (K.cocycleEquivExplicitKer 0 z))
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap
      have hsource := (K.explicitShortComplex 0).abCyclesIso_inv_apply_iCycles
        (K.cocycleEquivExplicitKer 0 z)
      have htarget := ConcreteCategory.congr_hom
        (K.toCochainComplex.liftCycles_i
          (K.cocycleInclusion 0) 1
          (by simp)
          (K.cocycleInclusion_comp_d 0)) z
      rw [ConcreteCategory.comp_apply] at htarget
      change (K.toCochainComplex.iCycles 0).hom
          ((K.cocycleToCycles 0).hom z) = z.1 at htarget
      rw [hmap, hsource]
      dsimp [scIsoExplicit, scPrimeZeroIsoExplicit, ShortComplex.isoMk]
      change (K.cocycleEquivExplicitKer 0 z).1 =
        (K.toCochainComplex.iCycles 0).hom ((K.cocycleToCycles 0).hom z)
      exact Eq.trans rfl htarget.symm
  | succ n =>
      apply (AddCommGrpCat.mono_iff_injective
        (K.toCochainComplex.sc (n + 1)).iCycles).1 inferInstance
      have hmap := ConcreteCategory.congr_hom
        (ShortComplex.cyclesMap_i (K.scIsoExplicit (n + 1)).inv)
        ((K.explicitShortComplex (n + 1)).abCyclesIso.inv
          (K.cocycleEquivExplicitKer (n + 1) z))
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap
      have hsource :=
        (K.explicitShortComplex (n + 1)).abCyclesIso_inv_apply_iCycles
          (K.cocycleEquivExplicitKer (n + 1) z)
      have htarget := ConcreteCategory.congr_hom
        (K.toCochainComplex.liftCycles_i
          (K.cocycleInclusion (n + 1)) (n + 2)
          (by simp [Nat.add_assoc])
          (K.cocycleInclusion_comp_d (n + 1))) z
      rw [ConcreteCategory.comp_apply] at htarget
      change (K.toCochainComplex.iCycles (n + 1)).hom
          ((K.cocycleToCycles (n + 1)).hom z) = z.1 at htarget
      rw [hmap, hsource]
      dsimp [scIsoExplicit, scPrimeSuccIsoExplicit, ShortComplex.isoMk]
      change (K.cocycleEquivExplicitKer (n + 1) z).1 =
        (K.toCochainComplex.iCycles (n + 1)).hom
          ((K.cocycleToCycles (n + 1)).hom z)
      exact Eq.trans rfl htarget.symm

private theorem additiveCechHnEquivHomology_additiveClass
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ)
    (z : K.CechCocycleSubgroup n) :
    K.additiveCechHnEquivHomology n (K.additiveClass n z) =
      (K.toCochainComplex.homologyπ n).hom
        ((K.cocycleToCycles n).hom z) := by
  simp only [additiveCechHnEquivHomology, AddEquiv.trans_apply]
  rw [K.additiveCechHnEquivExplicitHomology_additiveClass n z]
  change (ShortComplex.homologyMap (K.scIsoExplicit n).inv).hom
      ((K.explicitShortComplex n).homologyπ.hom
        ((K.explicitShortComplex n).abCyclesIso.inv
          (K.cocycleEquivExplicitKer n z))) = _
  have hnat := ConcreteCategory.congr_hom
    (ShortComplex.homologyπ_naturality (K.scIsoExplicit n).inv)
    ((K.explicitShortComplex n).abCyclesIso.inv
      (K.cocycleEquivExplicitKer n z))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [hnat, K.cyclesMap_scIsoExplicit_inv_explicitCycle n z]
  rfl

/--
The SD5 representative formula. It pins the main equivalence to the actual
`homologyπ` class and therefore rules out replacing it by an unrelated
additive equivalence.
-/
theorem additiveCechHnEquivHomology_additiveCohomologyClass
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ)
    (c : K.CechCocycle n) :
    K.additiveCechHnEquivHomology n (K.additiveCohomologyClass n c) =
      (K.toCochainComplex.homologyπ n).hom
        ((K.cocycleToCycles n).hom ⟨c.1, c.2⟩) := by
  have hclass : K.additiveCohomologyClass n c =
      K.additiveClass n ⟨c.1, c.2⟩ := by
    cases n <;> rfl
  rw [hclass, K.additiveCechHnEquivHomology_additiveClass]

namespace Hom

private def mapCocycleSubgroup
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) (n : ℕ) :
    K.CechCocycleSubgroup n →+ L.CechCocycleSubgroup n where
  toFun z := ⟨f.app n z.1, by
    letI := L.cochainAddCommGroup (n + 1)
    change L.d n (f.app n z.1) = 0
    rw [← f.commutes, z.2]
    exact map_zero (f.app (n + 1))⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (f.app n)
  map_add' := by
    intro x y
    apply Subtype.ext
    exact map_add (f.app n) x.1 y.1

private theorem cocycleToCycles_naturality
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) (n : ℕ) (z : K.CechCocycleSubgroup n) :
    (HomologicalComplex.cyclesMap f.toCochainMap n).hom
        ((K.cocycleToCycles n).hom z) =
      (L.cocycleToCycles n).hom (f.mapCocycleSubgroup n z) := by
  apply (AddCommGrpCat.mono_iff_injective
    (L.toCochainComplex.iCycles n)).1 inferInstance
  have hmap := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i f.toCochainMap n)
    ((K.cocycleToCycles n).hom z)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap
  rw [hmap]
  change f.app n
      ((K.toCochainComplex.iCycles n).hom ((K.cocycleToCycles n).hom z)) =
    (L.toCochainComplex.iCycles n).hom
      ((L.cocycleToCycles n).hom (f.mapCocycleSubgroup n z))
  rw [K.cocycleToCycles_i, L.cocycleToCycles_i]
  rfl

private theorem cocycleHomologyClass_naturality
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) (n : ℕ) (z : K.CechCocycleSubgroup n) :
    (HomologicalComplex.homologyMap f.toCochainMap n).hom
        ((K.toCochainComplex.homologyπ n).hom
          ((K.cocycleToCycles n).hom z)) =
      (L.toCochainComplex.homologyπ n).hom
        ((L.cocycleToCycles n).hom (f.mapCocycleSubgroup n z)) := by
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality f.toCochainMap n)
    ((K.cocycleToCycles n).hom z)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [hnat, f.cocycleToCycles_naturality n z]

/--
The SD5 naturality theorem. For the existing quotient map induced by any
selected cochain map, the main equivalence agrees with Mathlib's actual
homology map; no naturality certificate is an input.
-/
theorem additiveCechHnEquivHomology_naturality
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) (n : ℕ) (x : K.AdditiveCechHn n) :
    (HomologicalComplex.homologyMap f.toCochainMap n).hom
        (K.additiveCechHnEquivHomology n x) =
      L.additiveCechHnEquivHomology n (f.mapAdditiveCechHn n x) := by
  cases n with
  | zero =>
      change (HomologicalComplex.homologyMap f.toCochainMap 0).hom
          (K.additiveCechHnEquivHomology 0 (K.additiveClass 0 x)) =
        L.additiveCechHnEquivHomology 0
          (L.additiveClass 0 (f.mapCocycleSubgroup 0 x))
      rw [K.additiveCechHnEquivHomology_additiveClass,
        L.additiveCechHnEquivHomology_additiveClass]
      exact f.cocycleHomologyClass_naturality 0 x
  | succ n =>
      change K.CechCocycleSubgroup (n + 1) ⧸
        K.CechCoboundarySubgroupSucc n at x
      induction x using QuotientAddGroup.induction_on with
      | _ z =>
          change (HomologicalComplex.homologyMap f.toCochainMap (n + 1)).hom
              (K.additiveCechHnEquivHomology (n + 1)
                (K.additiveClass (n + 1) z)) =
            L.additiveCechHnEquivHomology (n + 1)
              (L.additiveClass (n + 1) (f.mapCocycleSubgroup (n + 1) z))
          rw [K.additiveCechHnEquivHomology_additiveClass,
            L.additiveCechHnEquivHomology_additiveClass]
          exact f.cocycleHomologyClass_naturality (n + 1) z

end Hom

end AAT.AG.Cohomology.CoverRelativeCechComplex

noncomputable section

namespace AAT.AG.Cohomology

universe u

open CategoryTheory

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- The R5c2 small complex after applying the actual sheaf-coefficient universe lift. -/
noncomputable def liftedCanonicalCechComplex
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (canonicalCechComplex 𝒰 Ob).toCochainComplex

/-- Universe lift commutes with the selected dependent product of sections. -/
private noncomputable def liftedCochainIso
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) :
    (liftedCanonicalCechComplex 𝒰 Ob).X n ≅
      ((selectedCechComplexFunctor 𝒰).obj Ob.toAddCommGrpSheaf.val).X n :=
  (show AddCommGrpCat.of
      (ULift.{u + 1, u} ((canonicalCechComplex 𝒰 Ob).AdditiveCochain n)) ≅
    AddCommGrpCat.of
      (SelectedCechCochain 𝒰 Ob.toAddCommGrpSheaf.val n) from
    { hom := AddCommGrpCat.ofHom
        { toFun := fun c σ ↦ ULift.up (c.down σ)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      inv := AddCommGrpCat.ofHom
        { toFun := fun c ↦ ULift.up (fun σ ↦ (c σ).down)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      hom_inv_id := by
        ext c
        cases c
        rfl
      inv_hom_id := by
        ext c σ
        cases c σ
        rfl })

/--
The lifted R5c2 complex is canonically the large selected Čech complex of the
actual additive obstruction sheaf.

Implementation notes: each component is `ULift (∀ σ, F σ) ≃ (∀ σ, ULift (F σ))`.
Differential compatibility is proved from the two fixed alternating-restriction
formulas; no complex equivalence is accepted from the caller.
-/
noncomputable def obstructionSelectedCechComplexIso
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    liftedCanonicalCechComplex 𝒰 Ob ≅
      (selectedCechComplexFunctor 𝒰).obj Ob.toAddCommGrpSheaf.val :=
  HomologicalComplex.Hom.isoOfComponents
    (liftedCochainIso 𝒰 Ob)
    (fun n m hnm ↦ by
      obtain rfl := hnm
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro c
      rcases c with ⟨c⟩
      funext σ
      simp only [ConcreteCategory.comp_apply]
      rw [selectedCechComplexFunctor_obj_d_apply]
      change
        (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.1) •
          ULift.up
            (Ob.mapAddMonoidHom
              ((canonicalCoverRelative 𝒰).faceRestriction n i σ)
              (c ((canonicalCoverRelative 𝒰).face n i σ)))) = _
      dsimp [liftedCanonicalCechComplex, liftedCochainIso]
      rw [CoverRelativeCechComplex.toCochainComplex_d]
      change _ = ULift.up ((canonicalCechComplex 𝒰 Ob).d n c σ)
      rw [canonicalCechComplex_d_apply]
      change _ = AddEquiv.ulift.symm
        (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.1) •
          Ob.mapAddMonoidHom
            ((canonicalCoverRelative 𝒰).faceRestriction n i σ)
            (c ((canonicalCoverRelative 𝒰).face n i σ)))
      rw [map_sum]
      simp only [map_zsmul]
      apply Finset.sum_congr rfl
      intro i _hi
      rfl)

/-- No-unfold API for the degreewise universe-lift component. -/
@[simp] theorem obstructionSelectedCechComplexIso_hom_f_apply
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ)
    (c : (liftedCanonicalCechComplex 𝒰 Ob).X n)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    ((obstructionSelectedCechComplexIso 𝒰 Ob).hom.f n).hom c σ =
      Ob.toAddCommGrpSheafObjAddEquiv _ (c.down σ) :=
  rfl

/-- The R5c2 refinement cochain map after applying the coefficient universe lift. -/
noncomputable def liftedCanonicalCechMap
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) :
    liftedCanonicalCechComplex 𝒰 Ob ⟶ liftedCanonicalCechComplex 𝒱 Ob :=
  (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
    (ComplexShape.up ℕ)).map (r.canonicalCechHom Ob).toCochainMap

/-- The universe-lift bridge commutes with selected-cover refinement. -/
theorem obstructionSelectedCechComplexIso_refinement_naturality
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) :
    liftedCanonicalCechMap r Ob ≫
        (obstructionSelectedCechComplexIso 𝒱 Ob).hom =
      (obstructionSelectedCechComplexIso 𝒰 Ob).hom ≫
        r.selectedCechMap.app Ob.toAddCommGrpSheaf.val := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  rcases c with ⟨c⟩
  funext σ
  rfl

/-- Homology of the lifted R5c2 complex is the lift of its small homology. -/
noncomputable def liftedCanonicalCechHomologyIso
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) :
    (liftedCanonicalCechComplex 𝒰 Ob).homology n ≅
      AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        ((canonicalCechComplex 𝒰 Ob).toCochainComplex.homology n) :=
  ((canonicalCechComplex 𝒰 Ob).toCochainComplex.sc n).mapHomologyIso
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The lifted homology isomorphism is natural for selected-cover refinement. -/
theorem liftedCanonicalCechHomologyIso_inv_refinement_naturality
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) (n : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map
          (HomologicalComplex.homologyMap
            (r.canonicalCechHom Ob).toCochainMap n) ≫
        (liftedCanonicalCechHomologyIso 𝒱 Ob n).inv =
      (liftedCanonicalCechHomologyIso 𝒰 Ob n).inv ≫
        HomologicalComplex.homologyMap (liftedCanonicalCechMap r Ob) n := by
  simpa only [liftedCanonicalCechHomologyIso, liftedCanonicalCechMap,
    HomologicalComplex.homologyMap] using
    (ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor
        AddCommGrpCat.{u} (ComplexShape.up ℕ) n).map
          (r.canonicalCechHom Ob).toCochainMap)
      AddCommGrpCat.uliftFunctor.{u + 1, u})

/--
A custom cocycle, lifted into the actual coefficient universe, determines a
cycle in the actual large selected Čech complex.
-/
noncomputable def obstructionCocycleToSelectedCycles
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        (AddCommGrpCat.of
          ((canonicalCechComplex 𝒰 Ob).CechCocycleSubgroup n)) ⟶
      ((selectedCechComplexFunctor 𝒰).obj
        Ob.toAddCommGrpSheaf.val).cycles n :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.map
      ((canonicalCechComplex 𝒰 Ob).cocycleToCycles n) ≫
    (((canonicalCechComplex 𝒰 Ob).toCochainComplex.sc n).mapCyclesIso
      AddCommGrpCat.uliftFunctor.{u + 1, u}).inv ≫
    HomologicalComplex.cyclesMap
      (obstructionSelectedCechComplexIso 𝒰 Ob).hom n

/-- The selected cycle has the lifted original cocycle as its underlying cochain. -/
@[simp] theorem obstructionCocycleToSelectedCycles_i_apply
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ)
    (z : (canonicalCechComplex 𝒰 Ob).CechCocycleSubgroup n)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    (((selectedCechComplexFunctor 𝒰).obj
        Ob.toAddCommGrpSheaf.val).iCycles n).hom
        ((obstructionCocycleToSelectedCycles 𝒰 Ob n).hom
          (ULift.up z)) σ =
      Ob.toAddCommGrpSheafObjAddEquiv _ (z.1 σ) := by
  let K := (canonicalCechComplex 𝒰 Ob).toCochainComplex
  let F := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let e := (K.sc n).mapCyclesIso F
  have he : e.inv ≫ (liftedCanonicalCechComplex 𝒰 Ob).iCycles n =
      F.map (K.iCycles n) := by
    rw [← cancel_epi e.hom, ← Category.assoc, e.hom_inv_id,
      Category.id_comp]
    exact (ShortComplex.mapCyclesIso_hom_iCycles (K.sc n) F).symm
  have he_assoc :
      e.inv ≫ (liftedCanonicalCechComplex 𝒰 Ob).iCycles n ≫
          (obstructionSelectedCechComplexIso 𝒰 Ob).hom.f n =
        F.map (K.iCycles n) ≫
          (obstructionSelectedCechComplexIso 𝒰 Ob).hom.f n := by
    simpa only [Category.assoc] using congrArg
      (fun q ↦ q ≫ (obstructionSelectedCechComplexIso 𝒰 Ob).hom.f n) he
  have htotal :
      obstructionCocycleToSelectedCycles 𝒰 Ob n ≫
          ((selectedCechComplexFunctor 𝒰).obj
            Ob.toAddCommGrpSheaf.val).iCycles n =
        F.map ((canonicalCechComplex 𝒰 Ob).cocycleToCycles n ≫
            K.iCycles n) ≫
          (obstructionSelectedCechComplexIso 𝒰 Ob).hom.f n := by
    change F.map ((canonicalCechComplex 𝒰 Ob).cocycleToCycles n) ≫
        e.inv ≫ HomologicalComplex.cyclesMap
          (obstructionSelectedCechComplexIso 𝒰 Ob).hom n ≫
        ((selectedCechComplexFunctor 𝒰).obj
          Ob.toAddCommGrpSheaf.val).iCycles n = _
    simp only [HomologicalComplex.cyclesMap_i]
    rw [he_assoc, ← Category.assoc, ← F.map_comp]
  have hz := ConcreteCategory.congr_hom htotal (ULift.up z)
  have hzσ := congrFun hz σ
  calc
    _ = ((obstructionSelectedCechComplexIso 𝒰 Ob).hom.f n).hom
        (ULift.up
          ((K.iCycles n).hom
            (((canonicalCechComplex 𝒰 Ob).cocycleToCycles n).hom z))) σ := by
      simpa only [ConcreteCategory.comp_apply] using hzσ
    _ = Ob.toAddCommGrpSheafObjAddEquiv _
        (((K.iCycles n).hom
          (((canonicalCechComplex 𝒰 Ob).cocycleToCycles n).hom z)) σ) := by
      rw [obstructionSelectedCechComplexIso_hom_f_apply]
    _ = Ob.toAddCommGrpSheafObjAddEquiv _ (z.1 σ) := by
      rw [CoverRelativeCechComplex.cocycleToCycles_i]

/-- The lifted homology isomorphism carries the actual cycle-class map. -/
theorem liftedCanonicalCechHomologyIso_inv_homologyπ
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map
          ((canonicalCechComplex 𝒰 Ob).toCochainComplex.homologyπ n) ≫
        (liftedCanonicalCechHomologyIso 𝒰 Ob n).inv =
      (((canonicalCechComplex 𝒰 Ob).toCochainComplex.sc n).mapCyclesIso
          AddCommGrpCat.uliftFunctor.{u + 1, u}).inv ≫
        (liftedCanonicalCechComplex 𝒰 Ob).homologyπ n := by
  let K := (canonicalCechComplex 𝒰 Ob).toCochainComplex
  let F := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let h := (K.sc n).leftHomologyData
  change F.map (K.homologyπ n) ≫ ((K.sc n).mapHomologyIso F).inv =
    ((K.sc n).mapCyclesIso F).inv ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ n
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  dsimp only [HomologicalComplex.homologyπ, Iso.trans_inv,
    Functor.mapIso, Iso.symm_inv]
  simp only [Category.assoc]
  rw [← Category.assoc, ← F.map_comp,
    h.homologyπ_comp_homologyIso_hom, F.map_comp]
  change F.map h.cyclesIso.hom ≫ (h.map F).π ≫
    (h.map F).homologyIso.inv = _
  rw [(h.map F).π_comp_homologyIso_inv]
  rfl

/--
The custom cover-relative quotient is canonically the homology of the actual
large selected Čech complex.

Implementation notes: this is the composite of the R5c2 quotient-homology
equivalence, Mathlib's homology-preservation isomorphism for `uliftFunctor`,
and homology of `obstructionSelectedCechComplexIso`. No homology-level
comparison is accepted as input.
-/
noncomputable def additiveCechHnEquivSelectedHomology
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) :
    (canonicalCechComplex 𝒰 Ob).AdditiveCechHn n ≃+
      ((selectedCechComplexFunctor 𝒰).obj
        Ob.toAddCommGrpSheaf.val).homology n :=
  ((canonicalCechComplex 𝒰 Ob).additiveCechHnEquivHomology n).trans
    ((AddEquiv.ulift.{u, u + 1}.symm).trans
      ((CategoryTheory.Iso.addCommGroupIsoToAddEquiv
        (liftedCanonicalCechHomologyIso 𝒰 Ob n).symm).trans
        (CategoryTheory.Iso.addCommGroupIsoToAddEquiv
          (HomologicalComplex.homologyMapIso
            (obstructionSelectedCechComplexIso 𝒰 Ob) n))))

/-- The canonical additive map from the custom quotient to actual selected homology. -/
noncomputable def additiveCechHnToSelectedHomology
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) :
    (canonicalCechComplex 𝒰 Ob).AdditiveCechHn n →+
      ((selectedCechComplexFunctor 𝒰).obj
        Ob.toAddCommGrpSheaf.val).homology n :=
  (additiveCechHnEquivSelectedHomology 𝒰 Ob n).toAddMonoidHom

/-- The canonical map to actual selected homology is bijective in every degree. -/
theorem additiveCechHnToSelectedHomology_bijective
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) :
    Function.Bijective (additiveCechHnToSelectedHomology 𝒰 Ob n) :=
  (additiveCechHnEquivSelectedHomology 𝒰 Ob n).bijective

/-- The actual selected-complex equivalence sends a cocycle to its homology class. -/
theorem additiveCechHnEquivSelectedHomology_additiveCohomologyClass
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ)
    (c : (canonicalCechComplex 𝒰 Ob).CechCocycle n) :
    additiveCechHnEquivSelectedHomology 𝒰 Ob n
        ((canonicalCechComplex 𝒰 Ob).additiveCohomologyClass n c) =
      (HomologicalComplex.homologyMapIso
          (obstructionSelectedCechComplexIso 𝒰 Ob) n).hom.hom
        ((liftedCanonicalCechHomologyIso 𝒰 Ob n).inv.hom
          (ULift.up
            (((canonicalCechComplex 𝒰 Ob).toCochainComplex.homologyπ n).hom
              (((canonicalCechComplex 𝒰 Ob).cocycleToCycles n).hom
                ⟨c.1, c.2⟩)))) := by
  change
    (HomologicalComplex.homologyMapIso
        (obstructionSelectedCechComplexIso 𝒰 Ob) n).hom.hom
      ((liftedCanonicalCechHomologyIso 𝒰 Ob n).inv.hom
        (ULift.up
          ((canonicalCechComplex 𝒰 Ob).additiveCechHnEquivHomology n
            ((canonicalCechComplex 𝒰 Ob).additiveCohomologyClass n c)))) = _
  rw [CoverRelativeCechComplex.additiveCechHnEquivHomology_additiveCohomologyClass]

/-- Representative formula for the canonical additive map. -/
theorem additiveCechHnToSelectedHomology_additiveCohomologyClass
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ)
    (c : (canonicalCechComplex 𝒰 Ob).CechCocycle n) :
    additiveCechHnToSelectedHomology 𝒰 Ob n
        ((canonicalCechComplex 𝒰 Ob).additiveCohomologyClass n c) =
      (HomologicalComplex.homologyMapIso
          (obstructionSelectedCechComplexIso 𝒰 Ob) n).hom.hom
        ((liftedCanonicalCechHomologyIso 𝒰 Ob n).inv.hom
          (ULift.up
            (((canonicalCechComplex 𝒰 Ob).toCochainComplex.homologyπ n).hom
              (((canonicalCechComplex 𝒰 Ob).cocycleToCycles n).hom
                ⟨c.1, c.2⟩)))) :=
  additiveCechHnEquivSelectedHomology_additiveCohomologyClass 𝒰 Ob n c

/-- The canonical map is the actual selected complex's `homologyπ` on the lifted cocycle. -/
theorem additiveCechHnToSelectedHomology_additiveCohomologyClass_eq_homologyπ
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ)
    (c : (canonicalCechComplex 𝒰 Ob).CechCocycle n) :
    additiveCechHnToSelectedHomology 𝒰 Ob n
        ((canonicalCechComplex 𝒰 Ob).additiveCohomologyClass n c) =
      (((selectedCechComplexFunctor 𝒰).obj
          Ob.toAddCommGrpSheaf.val).homologyπ n).hom
        ((obstructionCocycleToSelectedCycles 𝒰 Ob n).hom
          (ULift.up ⟨c.1, c.2⟩)) := by
  let K := (canonicalCechComplex 𝒰 Ob).toCochainComplex
  let z := ((canonicalCechComplex 𝒰 Ob).cocycleToCycles n).hom
    ⟨c.1, c.2⟩
  let zLift :=
    (((canonicalCechComplex 𝒰 Ob).toCochainComplex.sc n).mapCyclesIso
      AddCommGrpCat.uliftFunctor.{u + 1, u}).inv.hom (ULift.up z)
  have hLiftApply := ConcreteCategory.congr_hom
    (liftedCanonicalCechHomologyIso_inv_homologyπ 𝒰 Ob n)
    (ULift.up z)
  have hIsoApply := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality
      (obstructionSelectedCechComplexIso 𝒰 Ob).hom n)
    zLift
  rw [additiveCechHnToSelectedHomology_additiveCohomologyClass]
  change
    (HomologicalComplex.homologyMap
        (obstructionSelectedCechComplexIso 𝒰 Ob).hom n).hom
      ((liftedCanonicalCechHomologyIso 𝒰 Ob n).inv.hom
        (ULift.up ((K.homologyπ n).hom z))) =
      (((selectedCechComplexFunctor 𝒰).obj
          Ob.toAddCommGrpSheaf.val).homologyπ n).hom
        ((HomologicalComplex.cyclesMap
          (obstructionSelectedCechComplexIso 𝒰 Ob).hom n).hom zLift)
  exact congrArg
    (fun y ↦
      (HomologicalComplex.homologyMap
        (obstructionSelectedCechComplexIso 𝒰 Ob).hom n).hom y)
    hLiftApply |>.trans hIsoApply

/-- The actual selected-complex equivalence commutes with refinement homology maps. -/
theorem additiveCechHnEquivSelectedHomology_refinement_naturality
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) (n : ℕ)
    (x : (canonicalCechComplex 𝒰 Ob).AdditiveCechHn n) :
    (HomologicalComplex.homologyMap
        (r.selectedCechMap.app Ob.toAddCommGrpSheaf.val) n).hom
        (additiveCechHnEquivSelectedHomology 𝒰 Ob n x) =
      additiveCechHnEquivSelectedHomology 𝒱 Ob n
        ((r.canonicalCechHom Ob).mapAdditiveCechHn n x) := by
  let f := (r.canonicalCechHom Ob).toCochainMap
  let b := (canonicalCechComplex 𝒰 Ob).additiveCechHnEquivHomology n x
  let a := (liftedCanonicalCechHomologyIso 𝒰 Ob n).inv.hom (ULift.up b)
  have hComplex :
      HomologicalComplex.homologyMap (liftedCanonicalCechMap r Ob) n ≫
          (HomologicalComplex.homologyMapIso
            (obstructionSelectedCechComplexIso 𝒱 Ob) n).hom =
        (HomologicalComplex.homologyMapIso
            (obstructionSelectedCechComplexIso 𝒰 Ob) n).hom ≫
          HomologicalComplex.homologyMap
            (r.selectedCechMap.app Ob.toAddCommGrpSheaf.val) n := by
    have h := congrArg (fun g ↦ HomologicalComplex.homologyMap g n)
      (obstructionSelectedCechComplexIso_refinement_naturality r Ob)
    simpa only [HomologicalComplex.homologyMap_comp] using h
  have hComplexApply := ConcreteCategory.congr_hom hComplex a
  have hLiftApply := ConcreteCategory.congr_hom
    (liftedCanonicalCechHomologyIso_inv_refinement_naturality r Ob n)
    (ULift.up b)
  change
    (HomologicalComplex.homologyMap
        (r.selectedCechMap.app Ob.toAddCommGrpSheaf.val) n).hom
      ((HomologicalComplex.homologyMapIso
          (obstructionSelectedCechComplexIso 𝒰 Ob) n).hom.hom a) =
      (HomologicalComplex.homologyMapIso
          (obstructionSelectedCechComplexIso 𝒱 Ob) n).hom.hom
        ((liftedCanonicalCechHomologyIso 𝒱 Ob n).inv.hom
          (ULift.up
            ((canonicalCechComplex 𝒱 Ob).additiveCechHnEquivHomology n
              ((r.canonicalCechHom Ob).mapAdditiveCechHn n x))))
  rw [← CoverRelativeCechComplex.Hom.additiveCechHnEquivHomology_naturality
    (r.canonicalCechHom Ob) n x]
  exact hComplexApply.symm.trans
    (congrArg
      (fun y ↦
        (HomologicalComplex.homologyMapIso
          (obstructionSelectedCechComplexIso 𝒱 Ob) n).hom.hom y)
      hLiftApply.symm)

/-- The canonical additive map commutes with refinement homology maps. -/
theorem additiveCechHnToSelectedHomology_refinement_naturality
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) (n : ℕ)
    (x : (canonicalCechComplex 𝒰 Ob).AdditiveCechHn n) :
    (HomologicalComplex.homologyMap
        (r.selectedCechMap.app Ob.toAddCommGrpSheaf.val) n).hom
        (additiveCechHnToSelectedHomology 𝒰 Ob n x) =
      additiveCechHnToSelectedHomology 𝒱 Ob n
        ((r.canonicalCechHom Ob).mapAdditiveCechHn n x) :=
  additiveCechHnEquivSelectedHomology_refinement_naturality r Ob n x

/-! ## Selected Čech bicomplex of the injective resolution -/

/--
The first-quadrant bicomplex obtained by applying the actual selected Čech
complex functor to every object of the chosen injective resolution.

Implementation notes: the outer complex direction is the resolution degree
and the inner direction is the selected Čech degree. Both differentials and
their commutation law are supplied by `Functor.mapHomologicalComplex`; no
bicomplex or commutation certificate is accepted from the caller.
-/
noncomputable def selectedCechResolutionBicomplex
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    HomologicalComplex₂ AddCommGrpCat.{u + 1}
      (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (((sheafToPresheaf S.topology AddCommGrpCat.{u + 1}) ⋙
      selectedCechComplexFunctor 𝒰).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
    (obstructionInjectiveResolution Ob).cocomplex

/-- The `(q,p)` object is the product of `I^q`-sections on selected `p`-overlaps. -/
@[simp] theorem selectedCechResolutionBicomplex_obj
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p : ℕ) :
    (((selectedCechResolutionBicomplex 𝒰 Ob).X q).X p : Type (u + 1)) =
      SelectedCechCochain 𝒰
        ((obstructionInjectiveResolution Ob).cocomplex.X q).val p :=
  rfl

/-- The selected Čech differential is the alternating sum of face restrictions. -/
theorem selectedCechResolutionBicomplex_cech_d_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p : ℕ)
    (c : SelectedCechCochain 𝒰
      ((obstructionInjectiveResolution Ob).cocomplex.X q).val p)
    (σ : (canonicalCoverRelative 𝒰).simplex (p + 1)) :
    (((selectedCechResolutionBicomplex 𝒰 Ob).X q).d p (p + 1)).hom c σ =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ i.1) •
        ((obstructionInjectiveResolution Ob).cocomplex.X q).val.map
          ((canonicalCoverRelative 𝒰).faceRestriction p i σ).op
          (c ((canonicalCoverRelative 𝒰).face p i σ)) :=
  selectedCechComplexFunctor_obj_d_apply 𝒰 _ p c σ

/-- The resolution differential acts sectionwise in every selected Čech degree. -/
theorem selectedCechResolutionBicomplex_resolution_d_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p : ℕ)
    (c : SelectedCechCochain 𝒰
      ((obstructionInjectiveResolution Ob).cocomplex.X q).val p)
    (σ : (canonicalCoverRelative 𝒰).simplex p) :
    (((selectedCechResolutionBicomplex 𝒰 Ob).d q (q + 1)).f p).hom c σ =
      ((obstructionInjectiveResolution Ob).cocomplex.d q (q + 1)).val.app _
        (c σ) :=
  rfl

/-- The resolution and selected Čech differentials commute. -/
theorem selectedCechResolutionBicomplex_d_comm
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q q' p p' : ℕ) :
    ((selectedCechResolutionBicomplex 𝒰 Ob).d q q').f p ≫
        ((selectedCechResolutionBicomplex 𝒰 Ob).X q').d p p' =
      ((selectedCechResolutionBicomplex 𝒰 Ob).X q).d p p' ≫
        ((selectedCechResolutionBicomplex 𝒰 Ob).d q q').f p' :=
  HomologicalComplex₂.d_comm
    (selectedCechResolutionBicomplex 𝒰 Ob) q q' p p'

/--
The injective-resolution unit induces the canonical map from the actual
selected Čech complex to resolution degree zero.

Implementation notes: this is the selected Čech functor applied to
`InjectiveResolution.ι`; an edge map is not supplied as external data.
-/
noncomputable def selectedCechResolutionAugmentation
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    (selectedCechComplexFunctor 𝒰).obj Ob.toAddCommGrpSheaf.val ⟶
      (selectedCechResolutionBicomplex 𝒰 Ob).X 0 :=
  (selectedCechComplexFunctor 𝒰).map
    ((obstructionInjectiveResolution Ob).ι.f 0).val

/-- The resolution augmentation applies the unit to every selected section. -/
@[simp] theorem selectedCechResolutionAugmentation_f_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (p : ℕ)
    (c : SelectedCechCochain 𝒰 Ob.toAddCommGrpSheaf.val p)
    (σ : (canonicalCoverRelative 𝒰).simplex p) :
    ((selectedCechResolutionAugmentation 𝒰 Ob).f p).hom c σ =
      ((obstructionInjectiveResolution Ob).ι.f 0).val.app _ (c σ) :=
  rfl

/--
Evaluation at the base maps canonically to selected Čech degree zero.

Implementation notes: each component restricts a base section along the
selected chart inclusion. Naturality is the presheaf naturality square.
-/
noncomputable def baseToSelectedCechZero
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    (evaluation S.categoryᵒᵖ AddCommGrpCat.{u + 1}).obj
        (Opposite.op base) ⟶
      selectedCechComplexFunctor 𝒰 ⋙
        HomologicalComplex.eval AddCommGrpCat.{u + 1}
          (ComplexShape.up ℕ) 0 where
  app F := AddCommGrpCat.ofHom
    { toFun := fun x σ ↦
        F.map ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op x
      map_zero' := by
        funext σ
        exact map_zero _
      map_add' := by
        intro x y
        funext σ
        exact map_add _ _ _ }
  naturality F G η := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    funext σ
    change
      G.map ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op
          (η.app _ x) =
        η.app _
          (F.map ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op x)
    exact (ConcreteCategory.congr_hom
      (η.naturality ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op) x).symm

/-- The degree-zero cover augmentation is restriction along the selected chart. -/
@[simp] theorem baseToSelectedCechZero_app_apply
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (x : F.obj (Opposite.op base))
    (σ : (canonicalCoverRelative 𝒰).simplex 0) :
    ((baseToSelectedCechZero 𝒰).app F).hom x σ =
      F.map ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op x :=
  rfl

/--
The chosen injective resolution evaluated on the base object.

Implementation notes: this uses the `ℕ`-indexed `InjectiveResolution.cocomplex`
needed by the first-quadrant construction, rather than the `ℤ`-indexed
`cochainComplex` used by the Ext model. Their later comparison must pass
through the injective resolution's canonical degree isomorphisms.
-/
noncomputable def baseResolutionComplex
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (Ob : ObstructionSheaf S) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (((sheafToPresheaf S.topology AddCommGrpCat.{u + 1}) ⋙
      (evaluation S.categoryᵒᵖ AddCommGrpCat.{u + 1}).obj
        (Opposite.op base)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
    (obstructionInjectiveResolution Ob).cocomplex

/-- The degree `q` base-resolution object is `I^q(base)`. -/
@[simp] theorem baseResolutionComplex_X
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (Ob : ObstructionSheaf S) (q : ℕ) :
    ((baseResolutionComplex (base := base) Ob).X q : Type (u + 1)) =
      ((obstructionInjectiveResolution Ob).cocomplex.X q).val.obj
        (Opposite.op base) :=
  rfl

/-- The base-resolution differential is evaluation of the resolution differential. -/
theorem baseResolutionComplex_d_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (Ob : ObstructionSheaf S) (q : ℕ)
    (x : ((obstructionInjectiveResolution Ob).cocomplex.X q).val.obj
      (Opposite.op base)) :
    ((baseResolutionComplex (base := base) Ob).d q (q + 1)).hom x =
      ((obstructionInjectiveResolution Ob).cocomplex.d q (q + 1)).val.app _ x :=
  rfl

/--
Morphisms from the sheafified free representable are canonically sections.

Implementation notes: this is the composite of the sheafification adjunction,
the free-abelian-group adjunction in the presheaf category, and Yoneda.  The
additive structure is therefore derived from the standard constructions rather
than supplied as comparison data.
-/
noncomputable def sheafifiedFreeYonedaHomAddEquiv
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (X : S.category)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    (((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj X ⋙ AddCommGrpCat.free) ⟶ F) : Type (u + 1)) ≃+
      (F.val.obj (Opposite.op X) : Type (u + 1)) := by
  let e₁ := (sheafificationAdjunction S.topology
    AddCommGrpCat.{u + 1}).homAddEquiv
      (yoneda.obj X ⋙ AddCommGrpCat.free) F
  let e₂ := (AddCommGrpCat.adj.whiskerRight S.categoryᵒᵖ).homEquiv
      (yoneda.obj X) F.val
  let e₃ : (yoneda.obj X ⟶ F.val ⋙ forget AddCommGrpCat) ≃
      (F.val ⋙ forget AddCommGrpCat).obj (Opposite.op X) :=
    yonedaEquiv
  exact
    { toFun := fun f ↦ e₃ (e₂ (e₁ f))
      invFun := fun x ↦ e₁.symm (e₂.symm (e₃.symm x))
      left_inv := by
        intro f
        change e₁.symm (e₂.symm (e₃.symm (e₃ (e₂ (e₁ f))))) = f
        rw [e₃.symm_apply_apply, e₂.symm_apply_apply, e₁.symm_apply_apply]
      right_inv := by
        intro x
        change e₃ (e₂ (e₁ (e₁.symm (e₂.symm (e₃.symm x))))) = x
        rw [e₁.apply_symm_apply, e₂.apply_symm_apply, e₃.apply_symm_apply]
      map_add' := by
        intro f g
        change e₃ (e₂ (e₁ (f + g))) =
          e₃ (e₂ (e₁ f)) + e₃ (e₂ (e₁ g))
        simp only [map_add]
        rfl }

/-- Postcomposition of free-representable morphisms is evaluation on sections. -/
theorem sheafifiedFreeYonedaHomAddEquiv_comp
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (X : S.category)
    {F G : Sheaf S.topology AddCommGrpCat.{u + 1}}
    (f : ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj X ⋙ AddCommGrpCat.free)) ⟶ F)
    (g : F ⟶ G) :
    sheafifiedFreeYonedaHomAddEquiv X G (f ≫ g) =
      g.val.app (Opposite.op X)
        (sheafifiedFreeYonedaHomAddEquiv X F f) := by
  rfl

/--
Precomposition by a map of sheafified free representables is restriction of
sections.  The normal form is the section map `F.val.map a.op`, so downstream
proofs do not unfold the three adjunctions used by
`sheafifiedFreeYonedaHomAddEquiv`.
-/
theorem sheafifiedFreeYonedaHomAddEquiv_precomp
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {X Y : S.category}
    (a : X ⟶ Y)
    (F : Sheaf S.topology AddCommGrpCat.{u + 1})
    (f : ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj Y ⋙ AddCommGrpCat.free)) ⟶ F) :
    sheafifiedFreeYonedaHomAddEquiv X F
        ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
          (Functor.whiskerRight (yoneda.map a) AddCommGrpCat.free) ≫ f) =
      F.val.map a.op (sheafifiedFreeYonedaHomAddEquiv Y F f) := by
  change yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight S.categoryᵒᵖ).homEquiv
        (yoneda.obj X) F.val)
        (((sheafificationAdjunction S.topology AddCommGrpCat.{u + 1}).homEquiv
          (yoneda.obj X ⋙ AddCommGrpCat.free) F)
          ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
            (Functor.whiskerRight (yoneda.map a) AddCommGrpCat.free) ≫ f))) = _
  rw [(sheafificationAdjunction S.topology
    AddCommGrpCat.{u + 1}).homEquiv_naturality_left]
  change yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight S.categoryᵒᵖ).homEquiv
        (yoneda.obj X) F.val)
        (((Functor.whiskeringRight S.categoryᵒᵖ _ _).obj
          AddCommGrpCat.free).map (yoneda.map a) ≫
            ((sheafificationAdjunction S.topology AddCommGrpCat.{u + 1}).homEquiv
              (yoneda.obj Y ⋙ AddCommGrpCat.free) F) f)) = _
  rw [(AddCommGrpCat.adj.whiskerRight
    S.categoryᵒᵖ).homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ a).symm

/--
The base-resolution complex in the universe of Mathlib's `H'` value.

This universe lift is structural: it permits the homology object and the Ext
group to live in the same `AddCommGrpCat` while retaining
`baseResolutionComplex` as the small source complex.
-/
noncomputable def liftedBaseResolutionComplex
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (Ob : ObstructionSheaf S) :
    CochainComplex AddCommGrpCat.{u + 2} ℕ :=
  (AddCommGrpCat.uliftFunctor.{u + 2, u + 1}.mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (baseResolutionComplex (base := base) Ob)

/-- The lifted complex has the universe lift of the actual section group in each degree. -/
@[simp] theorem liftedBaseResolutionComplex_X
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (Ob : ObstructionSheaf S) (q : ℕ) :
    ((liftedBaseResolutionComplex (base := base) Ob).X q : Type (u + 2)) =
      ULift.{u + 2, u + 1}
        (((obstructionInjectiveResolution Ob).cocomplex.X q).val.obj
          (Opposite.op base)) :=
  rfl

/--
The lifted differential is the universe lift of the evaluated injective-resolution
differential.  This is the no-unfold computation rule for the lifted complex.
-/
theorem liftedBaseResolutionComplex_d_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (Ob : ObstructionSheaf S) (q : ℕ)
    (x : ULift.{u + 2, u + 1}
      (((obstructionInjectiveResolution Ob).cocomplex.X q).val.obj
        (Opposite.op base))) :
    ((liftedBaseResolutionComplex (base := base) Ob).d q (q + 1)).hom x =
      ULift.up
        (((obstructionInjectiveResolution Ob).cocomplex.d q (q + 1)).val.app _ x.down) :=
  rfl

/-- A lifted base-resolution cycle determines a morphism from the free representable. -/
noncomputable def baseResolutionLiftedCycleMorphism
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (Ob : ObstructionSheaf S) (n : ℕ)
    (z : (liftedBaseResolutionComplex (base := base) Ob).cycles n) :
    ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj base ⋙ AddCommGrpCat.free)) ⟶
        (obstructionInjectiveResolution Ob).cocomplex.X n :=
  (sheafifiedFreeYonedaHomAddEquiv base
    ((obstructionInjectiveResolution Ob).cocomplex.X n)).symm
      (((liftedBaseResolutionComplex (base := base) Ob).iCycles n).hom z).down

/--
The section represented by `baseResolutionLiftedCycleMorphism` is the original
lifted cycle.  The right-hand side is the normal form used by later proofs.
-/
@[simp] theorem baseResolutionLiftedCycleMorphism_section
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (Ob : ObstructionSheaf S) (n : ℕ)
    (z : (liftedBaseResolutionComplex (base := base) Ob).cycles n) :
    sheafifiedFreeYonedaHomAddEquiv base
        ((obstructionInjectiveResolution Ob).cocomplex.X n)
        (baseResolutionLiftedCycleMorphism (base := base) Ob n z) =
      (((liftedBaseResolutionComplex (base := base) Ob).iCycles n).hom z).down :=
  (sheafifiedFreeYonedaHomAddEquiv base
    ((obstructionInjectiveResolution Ob).cocomplex.X n)).apply_symm_apply _

/-- The morphism represented by a lifted cycle is a cocycle in the injective resolution. -/
theorem baseResolutionLiftedCycleMorphism_comp_d
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (Ob : ObstructionSheaf S) (n : ℕ)
    (z : (liftedBaseResolutionComplex (base := base) Ob).cycles n) :
    baseResolutionLiftedCycleMorphism (base := base) Ob n z ≫
        (obstructionInjectiveResolution Ob).cocomplex.d n (n + 1) = 0 := by
  apply (sheafifiedFreeYonedaHomAddEquiv base
    ((obstructionInjectiveResolution Ob).cocomplex.X (n + 1))).injective
  rw [sheafifiedFreeYonedaHomAddEquiv_comp]
  rw [baseResolutionLiftedCycleMorphism_section]
  rw [map_zero]
  have h := ConcreteCategory.congr_hom
    ((liftedBaseResolutionComplex (base := base) Ob).iCycles_d n (n + 1)) z
  have hd := congrArg ULift.down h
  simpa only [liftedBaseResolutionComplex_d_apply, ConcreteCategory.comp_apply,
    map_zero] using hd

/--
The canonical cycle map from the lifted base resolution to actual `Sheaf.H'`.

The value is Mathlib's `InjectiveResolution.extMk`; neither an Ext class nor a
comparison map is accepted from the caller.
-/
noncomputable def baseResolutionLiftedCyclesToHPrime
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S) (n : ℕ) :
    (liftedBaseResolutionComplex (base := base) Ob).cycles n ⟶
      (Ob.toAddCommGrpSheaf).H' n base :=
  AddCommGrpCat.ofHom
    { toFun := fun z ↦
        (obstructionInjectiveResolution Ob).extMk
          (baseResolutionLiftedCycleMorphism (base := base) Ob n z) (n + 1) rfl
          (baseResolutionLiftedCycleMorphism_comp_d (base := base) Ob n z)
      map_zero' := by
        have hf0 : baseResolutionLiftedCycleMorphism (base := base) Ob n 0 = 0 := by
          apply (sheafifiedFreeYonedaHomAddEquiv base
            ((obstructionInjectiveResolution Ob).cocomplex.X n)).injective
          simp only [baseResolutionLiftedCycleMorphism_section, map_zero]
          rfl
        simpa only [hf0] using
          (obstructionInjectiveResolution Ob).extMk_zero
            (X := (presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
              (yoneda.obj base ⋙ AddCommGrpCat.free)) (n + 1) rfl
      map_add' := by
        intro x y
        have hxy : baseResolutionLiftedCycleMorphism (base := base) Ob n (x + y) =
            baseResolutionLiftedCycleMorphism (base := base) Ob n x +
              baseResolutionLiftedCycleMorphism (base := base) Ob n y := by
          apply (sheafifiedFreeYonedaHomAddEquiv base
            ((obstructionInjectiveResolution Ob).cocomplex.X n)).injective
          simp only [baseResolutionLiftedCycleMorphism_section, map_add]
          rfl
        simpa only [hxy] using ((obstructionInjectiveResolution Ob).add_extMk
          (baseResolutionLiftedCycleMorphism (base := base) Ob n x)
          (baseResolutionLiftedCycleMorphism (base := base) Ob n y)
          (n + 1) rfl (baseResolutionLiftedCycleMorphism_comp_d (base := base) Ob n x)
          (baseResolutionLiftedCycleMorphism_comp_d (base := base) Ob n y)).symm }

/-- No-unfold API: the lifted cycle map is the standard Ext cocycle constructor. -/
@[simp] theorem baseResolutionLiftedCyclesToHPrime_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S) (n : ℕ)
    (z : (liftedBaseResolutionComplex (base := base) Ob).cycles n) :
    (baseResolutionLiftedCyclesToHPrime (base := base) Ob n).hom z =
      (obstructionInjectiveResolution Ob).extMk
        (baseResolutionLiftedCycleMorphism (base := base) Ob n z) (n + 1) rfl
        (baseResolutionLiftedCycleMorphism_comp_d (base := base) Ob n z) :=
  rfl

private theorem liftedBaseResolutionToCycles_comp_cyclesToHPrime
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S) (n : ℕ) :
    (liftedBaseResolutionComplex (base := base) Ob).toCycles
          ((ComplexShape.up ℕ).prev n) n ≫
        baseResolutionLiftedCyclesToHPrime Ob n = 0 := by
  cases n with
  | zero =>
      rw [(liftedBaseResolutionComplex (base := base) Ob).toCycles_eq_zero
        (i := (ComplexShape.up ℕ).prev 0) (j := 0) (by simp)]
      simp
  | succ n =>
      rw [CochainComplex.prev_nat_succ]
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      let z := ((liftedBaseResolutionComplex (base := base) Ob).toCycles
        n (n + 1)).hom x
      let hz := baseResolutionLiftedCycleMorphism_comp_d
        (base := base) Ob (n + 1) z
      change (obstructionInjectiveResolution Ob).extMk
          (baseResolutionLiftedCycleMorphism (base := base) Ob (n + 1) z)
          (n + 2) rfl hz = 0
      rw [(obstructionInjectiveResolution Ob).extMk_eq_zero_iff
        (baseResolutionLiftedCycleMorphism (base := base) Ob (n + 1) z)
        (n + 2) rfl hz n rfl]
      let g := (sheafifiedFreeYonedaHomAddEquiv base
        ((obstructionInjectiveResolution Ob).cocomplex.X n)).symm x.down
      refine ⟨g, ?_⟩
      apply (sheafifiedFreeYonedaHomAddEquiv base
        ((obstructionInjectiveResolution Ob).cocomplex.X (n + 1))).injective
      rw [sheafifiedFreeYonedaHomAddEquiv_comp]
      rw [show sheafifiedFreeYonedaHomAddEquiv base
          ((obstructionInjectiveResolution Ob).cocomplex.X n) g = x.down by
        exact (sheafifiedFreeYonedaHomAddEquiv base
          ((obstructionInjectiveResolution Ob).cocomplex.X n)).apply_symm_apply _]
      rw [baseResolutionLiftedCycleMorphism_section]
      change
        ((obstructionInjectiveResolution Ob).cocomplex.d n (n + 1)).val.app _ x.down =
          (((liftedBaseResolutionComplex (base := base) Ob).iCycles (n + 1)).hom z).down
      have h := ConcreteCategory.congr_hom
        ((liftedBaseResolutionComplex (base := base) Ob).toCycles_i n (n + 1)) x
      have hd := congrArg ULift.down h
      simpa only [z, liftedBaseResolutionComplex_d_apply,
        ConcreteCategory.comp_apply] using hd.symm

private noncomputable def liftedBaseResolutionHomologyToHPrime
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S) (n : ℕ) :
    (liftedBaseResolutionComplex (base := base) Ob).homology n ⟶
      (Ob.toAddCommGrpSheaf).H' n base :=
  ((liftedBaseResolutionComplex (base := base) Ob).sc n).descHomology
    (baseResolutionLiftedCyclesToHPrime Ob n) (by
      change (liftedBaseResolutionComplex (base := base) Ob).toCycles
          ((ComplexShape.up ℕ).prev n) n ≫
        baseResolutionLiftedCyclesToHPrime Ob n = 0
      exact liftedBaseResolutionToCycles_comp_cyclesToHPrime Ob n)

private theorem liftedBaseResolutionHomologyToHPrime_homologyπ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S) (n : ℕ) :
    (liftedBaseResolutionComplex (base := base) Ob).homologyπ n ≫
        liftedBaseResolutionHomologyToHPrime Ob n =
      baseResolutionLiftedCyclesToHPrime Ob n := by
  exact ((liftedBaseResolutionComplex (base := base) Ob).sc n).π_descHomology
    (baseResolutionLiftedCyclesToHPrime Ob n) _

private theorem liftedBaseResolutionHomologyToHPrime_surjective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S) (n : ℕ) :
    Function.Surjective
      (liftedBaseResolutionHomologyToHPrime (base := base) Ob n) := by
  intro α
  obtain ⟨f, hf, hα⟩ :=
    (obstructionInjectiveResolution Ob).extMk_surjective α (n + 1) rfl
  let s := sheafifiedFreeYonedaHomAddEquiv base
    ((obstructionInjectiveResolution Ob).cocomplex.X n) f
  have hs :
      ((obstructionInjectiveResolution Ob).cocomplex.d n (n + 1)).val.app _ s = 0 := by
    have h := congrArg
      (sheafifiedFreeYonedaHomAddEquiv base
        ((obstructionInjectiveResolution Ob).cocomplex.X (n + 1))) hf
    simpa only [sheafifiedFreeYonedaHomAddEquiv_comp, map_zero] using h
  let x : (liftedBaseResolutionComplex (base := base) Ob).X n := ULift.up s
  have hx :
      (((liftedBaseResolutionComplex (base := base) Ob).sc n).g).hom x = 0 := by
    change ((liftedBaseResolutionComplex (base := base) Ob).d n
      ((ComplexShape.up ℕ).next n)).hom x = 0
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp]
    simpa only [x, liftedBaseResolutionComplex_d_apply] using congrArg ULift.up hs
  let z : (liftedBaseResolutionComplex (base := base) Ob).cycles n :=
    (((liftedBaseResolutionComplex (base := base) Ob).sc n).abCyclesIso.inv).hom
      ⟨x, hx⟩
  have hz : baseResolutionLiftedCycleMorphism (base := base) Ob n z = f := by
    apply (sheafifiedFreeYonedaHomAddEquiv base
      ((obstructionInjectiveResolution Ob).cocomplex.X n)).injective
    rw [baseResolutionLiftedCycleMorphism_section]
    change (((liftedBaseResolutionComplex (base := base) Ob).iCycles n).hom z).down = s
    have hi := ((liftedBaseResolutionComplex (base := base) Ob).sc n).abCyclesIso_inv_apply_iCycles
      ⟨x, hx⟩
    have hid := congrArg (fun y ↦ ULift.down y) hi
    simpa only [z, x] using hid
  refine ⟨((liftedBaseResolutionComplex (base := base) Ob).homologyπ n).hom z, ?_⟩
  have hmap := ConcreteCategory.congr_hom
    (liftedBaseResolutionHomologyToHPrime_homologyπ (base := base) Ob n) z
  rw [ConcreteCategory.comp_apply] at hmap
  rw [hmap]
  change (obstructionInjectiveResolution Ob).extMk
      (baseResolutionLiftedCycleMorphism (base := base) Ob n z) (n + 1) rfl
        (baseResolutionLiftedCycleMorphism_comp_d (base := base) Ob n z) = α
  simpa only [hz] using hα

private theorem baseResolutionExtMk_zero_eq_zero_iff
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S)
    (f : ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj base ⋙ AddCommGrpCat.free)) ⟶
        (obstructionInjectiveResolution Ob).cocomplex.X 0)
    (hf : f ≫ (obstructionInjectiveResolution Ob).cocomplex.d 0 1 = 0) :
    (obstructionInjectiveResolution Ob).extMk f 1 rfl hf = 0 ↔ f = 0 := by
  let R := obstructionInjectiveResolution Ob
  change R.extMk f 1 rfl hf = 0 ↔ f = 0
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    R.extEquivCohomologyClass_extMk, R.extEquivCohomologyClass_zero,
    CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff]
  rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff
    _ _ _ _ _ (-1) (by lia)]
  constructor
  · rintro ⟨g, hg⟩
    have hg0 : g = 0 :=
      (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 (-1) (by lia)).eq_of_tgt _ _
    rw [hg0] at hg
    simp only [Limits.zero_comp] at hg
    apply (cancel_mono (R.cochainComplexXIso 0 0 rfl).inv).1
    simpa only [Limits.zero_comp] using hg.symm
  · rintro rfl
    refine ⟨0, ?_⟩
    simp

private theorem liftedBaseResolutionHomologyToHPrime_injective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S) (n : ℕ) :
    Function.Injective
      (liftedBaseResolutionHomologyToHPrime (base := base) Ob n) := by
  intro a b hab
  have hab0 :
      (liftedBaseResolutionHomologyToHPrime (base := base) Ob n).hom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨z, hz⟩ := ((AddCommGrpCat.epi_iff_surjective
    ((liftedBaseResolutionComplex (base := base) Ob).homologyπ n)).mp
      inferInstance) (a - b)
  have hcycle : (baseResolutionLiftedCyclesToHPrime Ob n).hom z = 0 := by
    have hmap := ConcreteCategory.congr_hom
      (liftedBaseResolutionHomologyToHPrime_homologyπ (base := base) Ob n) z
    rw [ConcreteCategory.comp_apply] at hmap
    rw [← hmap, hz, hab0]
  have hzclass :
      ((liftedBaseResolutionComplex (base := base) Ob).homologyπ n).hom z = 0 := by
    cases n with
    | zero =>
        have hf : baseResolutionLiftedCycleMorphism (base := base) Ob 0 z = 0 := by
          apply (baseResolutionExtMk_zero_eq_zero_iff (base := base) Ob
            (baseResolutionLiftedCycleMorphism (base := base) Ob 0 z)
            (baseResolutionLiftedCycleMorphism_comp_d (base := base) Ob 0 z)).mp
          exact hcycle
        have hi0 :
            ((liftedBaseResolutionComplex (base := base) Ob).iCycles 0).hom z = 0 := by
          apply ULift.down_injective
          have h := congrArg
            (sheafifiedFreeYonedaHomAddEquiv base
              ((obstructionInjectiveResolution Ob).cocomplex.X 0)) hf
          simpa only [baseResolutionLiftedCycleMorphism_section, map_zero] using h
        have hz0 : z = 0 :=
          (AddCommGrpCat.mono_iff_injective
            ((liftedBaseResolutionComplex (base := base) Ob).iCycles 0)).1
              inferInstance (by simpa only [map_zero] using hi0)
        rw [hz0]
        exact map_zero _
    | succ p =>
        let f := baseResolutionLiftedCycleMorphism (base := base) Ob (p + 1) z
        let hf := baseResolutionLiftedCycleMorphism_comp_d
          (base := base) Ob (p + 1) z
        have hext : (obstructionInjectiveResolution Ob).extMk f (p + 2) rfl hf = 0 := by
          exact hcycle
        obtain ⟨g, hg⟩ := ((obstructionInjectiveResolution Ob).extMk_eq_zero_iff
          f (p + 2) rfl hf p rfl).mp hext
        let x : (liftedBaseResolutionComplex (base := base) Ob).X p :=
          ULift.up (sheafifiedFreeYonedaHomAddEquiv base
            ((obstructionInjectiveResolution Ob).cocomplex.X p) g)
        let z' := ((liftedBaseResolutionComplex (base := base) Ob).toCycles
          p (p + 1)).hom x
        have hzz' : z = z' := by
          apply (AddCommGrpCat.mono_iff_injective
            ((liftedBaseResolutionComplex (base := base) Ob).iCycles (p + 1))).1
              inferInstance
          apply ULift.down_injective
          have hz_under :
              (((liftedBaseResolutionComplex (base := base) Ob).iCycles (p + 1)).hom z).down =
                sheafifiedFreeYonedaHomAddEquiv base
                  ((obstructionInjectiveResolution Ob).cocomplex.X (p + 1)) f := by
            simpa only [f] using
              (baseResolutionLiftedCycleMorphism_section
                (base := base) Ob (p + 1) z).symm
          have hboundary := ConcreteCategory.congr_hom
            ((liftedBaseResolutionComplex (base := base) Ob).toCycles_i p (p + 1)) x
          have hboundary_down := congrArg ULift.down hboundary
          rw [hz_under]
          rw [← hg, sheafifiedFreeYonedaHomAddEquiv_comp]
          simpa only [z', x, liftedBaseResolutionComplex_d_apply,
            ConcreteCategory.comp_apply] using hboundary_down.symm
        rw [hzz']
        have hzero := ConcreteCategory.congr_hom
          ((liftedBaseResolutionComplex (base := base) Ob).toCycles_comp_homologyπ
            p (p + 1)) x
        simpa only [z', ConcreteCategory.comp_apply, map_zero] using hzero
  have hab_eq : a - b = 0 := by
    rw [← hz]
    exact hzclass
  exact sub_eq_zero.mp hab_eq

private noncomputable def liftedBaseResolutionHomologyEquivHPrime
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S) (n : ℕ) :
    ((liftedBaseResolutionComplex (base := base) Ob).homology n : Type (u + 2)) ≃+
      ((Ob.toAddCommGrpSheaf).H' n base : Type (u + 2)) :=
  AddEquiv.ofBijective
    (liftedBaseResolutionHomologyToHPrime (base := base) Ob n).hom
    ⟨liftedBaseResolutionHomologyToHPrime_injective Ob n,
      liftedBaseResolutionHomologyToHPrime_surjective Ob n⟩

/-- Homology commutes with the structural universe lift of the base resolution. -/
noncomputable def liftedBaseResolutionHomologyIso
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (Ob : ObstructionSheaf S) (n : ℕ) :
    (liftedBaseResolutionComplex (base := base) Ob).homology n ≅
      AddCommGrpCat.uliftFunctor.{u + 2, u + 1}.obj
        ((baseResolutionComplex (base := base) Ob).homology n) :=
  ((baseResolutionComplex (base := base) Ob).sc n).mapHomologyIso
    AddCommGrpCat.uliftFunctor.{u + 2, u + 1}

/--
Canonical identification of base-resolution homology with actual
`Sheaf.H'`.

It is assembled from the universe-lift homology isomorphism and the Ext
cocycle construction above.  No arbitrary complex, equivalence, comparison
map, or bijectivity premise is accepted.
-/
noncomputable def baseResolutionHomologyEquivHPrime
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S) (n : ℕ) :
    ((baseResolutionComplex (base := base) Ob).homology n : Type (u + 1)) ≃+
      ((Ob.toAddCommGrpSheaf).H' n base : Type (u + 2)) :=
  AddEquiv.ulift.{u + 1, u + 2}.symm |>.trans
    ((liftedBaseResolutionHomologyIso (base := base) Ob n).symm.addCommGroupIsoToAddEquiv.trans
      (liftedBaseResolutionHomologyEquivHPrime (base := base) Ob n))

private theorem liftedBaseResolutionHomologyEquivHPrime_homologyπ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S) (n : ℕ)
    (z : (liftedBaseResolutionComplex (base := base) Ob).cycles n) :
    liftedBaseResolutionHomologyEquivHPrime Ob n
        (((liftedBaseResolutionComplex (base := base) Ob).homologyπ n).hom z) =
      (baseResolutionLiftedCyclesToHPrime Ob n).hom z := by
  change (liftedBaseResolutionHomologyToHPrime (base := base) Ob n).hom
      (((liftedBaseResolutionComplex (base := base) Ob).homologyπ n).hom z) = _
  have h := ConcreteCategory.congr_hom
    (liftedBaseResolutionHomologyToHPrime_homologyπ (base := base) Ob n) z
  simpa only [ConcreteCategory.comp_apply] using h

private theorem liftedBaseResolutionHomologyIso_inv_homologyπ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (Ob : ObstructionSheaf S) (n : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 2, u + 1}.map
          ((baseResolutionComplex (base := base) Ob).homologyπ n) ≫
        (liftedBaseResolutionHomologyIso (base := base) Ob n).inv =
      (((baseResolutionComplex (base := base) Ob).sc n).mapCyclesIso
          AddCommGrpCat.uliftFunctor.{u + 2, u + 1}).inv ≫
        (liftedBaseResolutionComplex (base := base) Ob).homologyπ n := by
  let K := baseResolutionComplex (base := base) Ob
  let F := AddCommGrpCat.uliftFunctor.{u + 2, u + 1}
  let h := (K.sc n).leftHomologyData
  change F.map (K.homologyπ n) ≫ ((K.sc n).mapHomologyIso F).inv =
    ((K.sc n).mapCyclesIso F).inv ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ n
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  dsimp only [HomologicalComplex.homologyπ, Iso.trans_inv,
    Functor.mapIso, Iso.symm_inv]
  simp only [Category.assoc]
  rw [← Category.assoc, ← F.map_comp,
    h.homologyπ_comp_homologyIso_hom, F.map_comp]
  change F.map h.cyclesIso.hom ≫ (h.map F).π ≫
    (h.map F).homologyIso.inv = _
  rw [(h.map F).π_comp_homologyIso_inv]
  rfl

/--
Representative formula for the base-resolution comparison.

A small homology class represented by `z` is first transported through the
canonical universe-lift cycle isomorphism and then sent by the actual Ext
cocycle constructor fixed above.
-/
theorem baseResolutionHomologyEquivHPrime_homologyπ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (Ob : ObstructionSheaf S) (n : ℕ)
    (z : (baseResolutionComplex (base := base) Ob).cycles n) :
    baseResolutionHomologyEquivHPrime Ob n
        (((baseResolutionComplex (base := base) Ob).homologyπ n).hom z) =
      (baseResolutionLiftedCyclesToHPrime Ob n).hom
        (((((baseResolutionComplex (base := base) Ob).sc n).mapCyclesIso
          AddCommGrpCat.uliftFunctor.{u + 2, u + 1}).inv).hom (ULift.up z)) := by
  simp only [baseResolutionHomologyEquivHPrime, AddEquiv.trans_apply]
  have h := ConcreteCategory.congr_hom
    (liftedBaseResolutionHomologyIso_inv_homologyπ (base := base) Ob n)
      (ULift.up z)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  have h' :
      (liftedBaseResolutionHomologyIso (base := base) Ob n).inv.hom
          (ULift.up (((baseResolutionComplex (base := base) Ob).homologyπ n).hom z)) =
        ((liftedBaseResolutionComplex (base := base) Ob).homologyπ n).hom
          (((((baseResolutionComplex (base := base) Ob).sc n).mapCyclesIso
            AddCommGrpCat.uliftFunctor.{u + 2, u + 1}).inv).hom (ULift.up z)) := by
    exact h
  change liftedBaseResolutionHomologyEquivHPrime (base := base) Ob n
      ((liftedBaseResolutionHomologyIso (base := base) Ob n).inv.hom
        (ULift.up (((baseResolutionComplex (base := base) Ob).homologyπ n).hom z))) = _
  rw [h']
  exact liftedBaseResolutionHomologyEquivHPrime_homologyπ (base := base) Ob n _

/--
The base-resolution complex maps to the selected degree-zero column.

Implementation notes: this is `baseToSelectedCechZero` mapped across the
chosen injective resolution, so compatibility with the resolution
differential is inherited from naturality.
-/
noncomputable def baseResolutionToSelectedCechZero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    baseResolutionComplex (base := base) Ob ⟶
      (selectedCechResolutionBicomplex 𝒰 Ob).flip.X 0 :=
  (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft
      (sheafToPresheaf S.topology AddCommGrpCat.{u + 1})
      (baseToSelectedCechZero 𝒰))
    (ComplexShape.up ℕ)).app
      (obstructionInjectiveResolution Ob).cocomplex

/-- The vertical edge map restricts each base section to every selected chart. -/
@[simp] theorem baseResolutionToSelectedCechZero_f_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q : ℕ)
    (x : ((obstructionInjectiveResolution Ob).cocomplex.X q).val.obj
      (Opposite.op base))
    (σ : (canonicalCoverRelative 𝒰).simplex 0) :
    ((baseResolutionToSelectedCechZero 𝒰 Ob).f q).hom x σ =
      ((obstructionInjectiveResolution Ob).cocomplex.X q).val.map
        ((canonicalCoverRelative 𝒰).inclusion (σ 0)).op x :=
  rfl

/--
Selected-cover refinement induces a morphism of injective-resolution
bicomplexes.

Implementation notes: the existing selected Čech natural transformation is
mapped across the actual injective resolution. The two differential
compatibilities are therefore constructed, not accepted as premises.
-/
noncomputable def selectedCechResolutionBicomplexMap
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) :
    selectedCechResolutionBicomplex 𝒰 Ob ⟶
      selectedCechResolutionBicomplex 𝒱 Ob :=
  (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft
      (sheafToPresheaf S.topology AddCommGrpCat.{u + 1})
      r.selectedCechMap)
    (ComplexShape.up ℕ)).app
      (obstructionInjectiveResolution Ob).cocomplex

/-- Refinement acts by the canonical overlap map in every bidegree. -/
@[simp] theorem selectedCechResolutionBicomplexMap_f_f_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) (q p : ℕ)
    (c : SelectedCechCochain 𝒰
      ((obstructionInjectiveResolution Ob).cocomplex.X q).val p)
    (σ : (canonicalCoverRelative 𝒱).simplex p) :
    ((((selectedCechResolutionBicomplexMap r Ob).f q).f p).hom c) σ =
      ((obstructionInjectiveResolution Ob).cocomplex.X q).val.map
        (r.overlapMap p σ).op (c (r.simplexMap p σ)) :=
  rfl

/-- Identity refinement induces the identity bicomplex map. -/
@[simp] theorem selectedCechResolutionBicomplexMap_refl
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    selectedCechResolutionBicomplexMap
        (Site.AATCoverageFamily.Refinement.refl 𝒰) Ob =
      𝟙 (selectedCechResolutionBicomplex 𝒰 Ob) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply HomologicalComplex.Hom.ext
  funext p
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  funext σ
  change
    ((obstructionInjectiveResolution Ob).cocomplex.X q).val.map
      ((Site.AATCoverageFamily.Refinement.refl 𝒰).overlapMap p σ).op
      (c σ) = c σ
  have h : (Site.AATCoverageFamily.Refinement.refl 𝒰).overlapMap p σ = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h]
  exact FunctorToTypes.map_id_apply
    (F := ((obstructionInjectiveResolution Ob).cocomplex.X q).val ⋙
      forget AddCommGrpCat.{u + 1}) (c σ)

/-- Composite refinement induces the composite bicomplex map. -/
@[simp] theorem selectedCechResolutionBicomplexMap_comp
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 𝒱 𝒲 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (s : Site.AATCoverageFamily.Refinement 𝒱 𝒲)
    (Ob : ObstructionSheaf S) :
    selectedCechResolutionBicomplexMap (r.comp s) Ob =
      selectedCechResolutionBicomplexMap r Ob ≫
        selectedCechResolutionBicomplexMap s Ob := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply HomologicalComplex.Hom.ext
  funext p
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  funext σ
  change
    (((obstructionInjectiveResolution Ob).cocomplex.X q).val ⋙
      forget AddCommGrpCat.{u + 1}).map
        ((r.comp s).overlapMap p σ).op
        (c (r.simplexMap p (s.simplexMap p σ))) =
      (((obstructionInjectiveResolution Ob).cocomplex.X q).val ⋙
        forget AddCommGrpCat.{u + 1}).map
        (s.overlapMap p σ).op
        ((((obstructionInjectiveResolution Ob).cocomplex.X q).val ⋙
          forget AddCommGrpCat.{u + 1}).map
          (r.overlapMap p (s.simplexMap p σ)).op
          (c (r.simplexMap p (s.simplexMap p σ))))
  rw [← FunctorToTypes.map_comp_apply]
  congr

/-- The resolution augmentation commutes with selected-cover refinement. -/
theorem selectedCechResolutionAugmentation_refinement_naturality
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) :
    selectedCechResolutionAugmentation 𝒰 Ob ≫
        (selectedCechResolutionBicomplexMap r Ob).f 0 =
      r.selectedCechMap.app Ob.toAddCommGrpSheaf.val ≫
        selectedCechResolutionAugmentation 𝒱 Ob := by
  exact r.selectedCechMap_coefficient_naturality
    ((obstructionInjectiveResolution Ob).ι.f 0).val

/-- The base-resolution edge map is unchanged by selected-cover refinement. -/
theorem baseResolutionToSelectedCechZero_refinement_naturality
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) :
    baseResolutionToSelectedCechZero 𝒰 Ob ≫
        ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{u + 1}
          (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map
            (selectedCechResolutionBicomplexMap r Ob)).f 0 =
      baseResolutionToSelectedCechZero 𝒱 Ob := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext σ
  change
    (((obstructionInjectiveResolution Ob).cocomplex.X q).val ⋙
      forget AddCommGrpCat.{u + 1}).map
        (r.overlapMap 0 σ).op
        ((((obstructionInjectiveResolution Ob).cocomplex.X q).val ⋙
          forget AddCommGrpCat.{u + 1}).map
          ((canonicalCoverRelative 𝒰).inclusion
            ((r.simplexMap 0 σ) 0)).op x) =
      (((obstructionInjectiveResolution Ob).cocomplex.X q).val ⋙
        forget AddCommGrpCat.{u + 1}).map
        ((canonicalCoverRelative 𝒱).inclusion (σ 0)).op x
  rw [← FunctorToTypes.map_comp_apply]
  congr

/-! ## Total complex and its two canonical edges -/

/-- The resolution augmentation is killed by the first resolution differential. -/
theorem selectedCechResolutionAugmentation_comp_resolution_d
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (p : ℕ) :
    (selectedCechResolutionAugmentation 𝒰 Ob).f p ≫
        ((selectedCechResolutionBicomplex 𝒰 Ob).d 0 1).f p = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  funext σ
  have h := congrArg
    (fun f => f.val.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap p σ)))
    (obstructionInjectiveResolution Ob).ι_f_zero_comp_complex_d
  have hx := ConcreteCategory.congr_hom h (c σ)
  simpa only [ConcreteCategory.comp_apply,
    selectedCechResolutionAugmentation_f_apply,
    selectedCechResolutionBicomplex_resolution_d_apply, map_zero] using hx

/-- Restricting a base section gives a selected Čech zero-cocycle. -/
theorem baseResolutionToSelectedCechZero_comp_cech_d
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q : ℕ) :
    (baseResolutionToSelectedCechZero 𝒰 Ob).f q ≫
        ((selectedCechResolutionBicomplex 𝒰 Ob).X q).d 0 1 = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext σ
  change (((selectedCechResolutionBicomplex 𝒰 Ob).X q).d 0 1).hom
      (((baseResolutionToSelectedCechZero 𝒰 Ob).f q).hom x) σ = 0
  rw [selectedCechResolutionBicomplex_cech_d_apply]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_smul,
    baseResolutionToSelectedCechZero_f_apply]
  let F := ((obstructionInjectiveResolution Ob).cocomplex.X q).val ⋙
    forget AddCommGrpCat.{u + 1}
  change F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op
        (F.map ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 0 σ) 0)).op x) +
      -F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op
        (F.map ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 1 σ) 0)).op x) = 0
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
  have hmor :
      ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 0 σ) 0)).op ≫
          ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op =
        ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 1 σ) 0)).op ≫
          ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op :=
    Subsingleton.elim _ _
  rw [hmor]
  simp

/--
Implementation notes: the total construction uses the standard cochain sign
convention `ε₁ = 1` and `ε₂(q,p) = (-1)^q`, matching the resolution-first
presentation of the selected Čech bicomplex. A caller-supplied sign witness is
rejected because the sign is part of this canonical presentation, not a
premise of the comparison.
-/
private instance : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by dsimp; omega
  add_rel p q r (hpq : p + 1 = q) := by dsimp; omega
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [pow_succ]
    simp

/--
The actual total complex of the injective-resolution selected Čech
bicomplex.  Its degree `n` is the coproduct of bidegrees `(q,p)` with
`q + p = n`, and its differential is Mathlib's signed total differential.

Implementation notes: this is Mathlib's `HomologicalComplex₂.total`, so the
comparison uses the actual total complex and its coproduct API. A bespoke
complex carrying preselected differential data is rejected because it would
replace, rather than construct, the totalization required here.
-/
noncomputable def selectedCechResolutionTotalComplex
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (selectedCechResolutionBicomplex 𝒰 Ob).total (ComplexShape.up ℕ)

/--
On every total summand, the total differential is the sum of Mathlib's
signed resolution and selected Čech components.
-/
theorem selectedCechResolutionTotalComplex_ι_d
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p n n' : ℕ) (h : q + p = n) :
    (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) q p n h ≫
        (selectedCechResolutionTotalComplex 𝒰 Ob).d n n' =
      (selectedCechResolutionBicomplex 𝒰 Ob).d₁
          (ComplexShape.up ℕ) q p n' +
        (selectedCechResolutionBicomplex 𝒰 Ob).d₂
          (ComplexShape.up ℕ) q p n' := by
  change _ ≫ ((selectedCechResolutionBicomplex 𝒰 Ob).total
    (ComplexShape.up ℕ)).d n n' = _
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]

/--
The selected Čech complex maps to the total complex through resolution
degree zero.  The horizontal term vanishes by the resolution unit law and
the vertical term is the selected Čech differential.

Implementation notes: the map is constructed from the actual augmentation
and the `(0,p)` total-summand inclusion. An arbitrary edge chain map supplied
as input is rejected because its chain-map law would leave the resolution
unit compatibility unproved.
-/
noncomputable def selectedCechToResolutionTotal
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    (selectedCechComplexFunctor 𝒰).obj Ob.toAddCommGrpSheaf.val ⟶
      selectedCechResolutionTotalComplex 𝒰 Ob where
  f p := (selectedCechResolutionAugmentation 𝒰 Ob).f p ≫
    (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
      (ComplexShape.up ℕ) 0 p p (by simp)
  comm' p p' hp := by
    change p + 1 = p' at hp
    have hε1 : ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (0, p) = 1 := rfl
    have hε2 : ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (0, p) = 1 := by
      change (-1 : ℤˣ) ^ (0 : ℕ) = 1
      simp
    rw [Category.assoc, selectedCechResolutionTotalComplex_ι_d]
    rw [HomologicalComplex₂.d₁_eq
      (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
      (i₁ := 0) (i₁' := 1) (by simp) p p' (by
        change 1 + p = p'
        omega)]
    rw [HomologicalComplex₂.d₂_eq
      (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
      0 hp p' (by
        change 0 + p' = p'
        omega)]
    rw [hε1, hε2]
    simp only [one_smul]
    rw [Preadditive.comp_add]
    rw [← Category.assoc]
    rw [selectedCechResolutionAugmentation_comp_resolution_d]
    simp only [Limits.zero_comp, zero_add]
    rw [← Category.assoc]
    rw [(selectedCechResolutionAugmentation 𝒰 Ob).comm p p']
    simp

/-- The selected-edge component is the augmentation followed by its summand inclusion. -/
theorem selectedCechToResolutionTotal_f
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (p : ℕ) :
    (selectedCechToResolutionTotal 𝒰 Ob).f p =
      (selectedCechResolutionAugmentation 𝒰 Ob).f p ≫
        (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) 0 p p (by simp) :=
  rfl

/--
The base-resolution complex maps to the total complex through selected Čech
degree zero.  The resolution term is inherited from naturality and the Čech
term vanishes because restriction from the base is a zero-cocycle.

Implementation notes: the map is constructed from actual restriction to
selected overlaps and the `(q,0)` total-summand inclusion. An externally
chosen edge map is rejected because it would bypass the zero-cocycle proof
from the face maps.
-/
noncomputable def baseResolutionToSelectedCechTotal
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    baseResolutionComplex (base := base) Ob ⟶
      selectedCechResolutionTotalComplex 𝒰 Ob where
  f q := (baseResolutionToSelectedCechZero 𝒰 Ob).f q ≫
    (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
      (ComplexShape.up ℕ) q 0 q (by simp)
  comm' q q' hq := by
    change q + 1 = q' at hq
    have hε1 : ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (q, 0) = 1 := rfl
    have hcomm :
        (baseResolutionToSelectedCechZero 𝒰 Ob).f q ≫
            ((selectedCechResolutionBicomplex 𝒰 Ob).d q q').f 0 =
          (baseResolutionComplex (base := base) Ob).d q q' ≫
            (baseResolutionToSelectedCechZero 𝒰 Ob).f q' := by
      simpa using (baseResolutionToSelectedCechZero 𝒰 Ob).comm q q'
    rw [Category.assoc, selectedCechResolutionTotalComplex_ι_d]
    rw [HomologicalComplex₂.d₁_eq
      (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
      hq 0 q' (by
        change q' + 0 = q'
        omega)]
    rw [HomologicalComplex₂.d₂_eq
      (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
      q (i₂ := 0) (i₂' := 1) (by simp) q' (by
        change q + 1 = q'
        omega)]
    rw [hε1]
    simp only [one_smul]
    rw [Preadditive.comp_add]
    rw [← Category.assoc]
    rw [hcomm]
    rw [Linear.comp_units_smul]
    rw [← Category.assoc]
    rw [baseResolutionToSelectedCechZero_comp_cech_d]
    simp only [Limits.zero_comp, smul_zero, add_zero]
    simp

/-- The base-edge component is restriction followed by its summand inclusion. -/
theorem baseResolutionToSelectedCechTotal_f
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q : ℕ) :
    (baseResolutionToSelectedCechTotal 𝒰 Ob).f q =
      (baseResolutionToSelectedCechZero 𝒰 Ob).f q ≫
        (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) q 0 q (by simp) :=
  rfl

/--
Refinement induces the Mathlib total map of the actual bicomplex map.

Implementation notes: this uses Mathlib's `HomologicalComplex₂.total.map` on
the actual bicomplex refinement map, which exposes its action on every
summand and inherits composition from bicomplex maps. A degreewise hand-built
chain map is rejected because it would duplicate that functorial structure.
-/
noncomputable def selectedCechResolutionTotalMap
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) :
    selectedCechResolutionTotalComplex 𝒰 Ob ⟶
      selectedCechResolutionTotalComplex 𝒱 Ob :=
  HomologicalComplex₂.total.map
    (selectedCechResolutionBicomplexMap r Ob) (ComplexShape.up ℕ)

/-- The total refinement map is the bicomplex refinement map on every summand. -/
theorem selectedCechResolutionTotalMap_ιTotal
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) (q p n : ℕ) (h : q + p = n) :
    (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) q p n h ≫
        (selectedCechResolutionTotalMap r Ob).f n =
      ((selectedCechResolutionBicomplexMap r Ob).f q).f p ≫
        (selectedCechResolutionBicomplex 𝒱 Ob).ιTotal
          (ComplexShape.up ℕ) q p n h := by
  exact HomologicalComplex₂.ιTotal_map
    (selectedCechResolutionBicomplex 𝒰 Ob)
    (selectedCechResolutionBicomplex 𝒱 Ob)
    (selectedCechResolutionBicomplexMap r Ob)
    (ComplexShape.up ℕ) q p n h

/-- Identity refinement induces the identity total map. -/
@[simp] theorem selectedCechResolutionTotalMap_refl
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    selectedCechResolutionTotalMap
        (Site.AATCoverageFamily.Refinement.refl 𝒰) Ob =
      𝟙 (selectedCechResolutionTotalComplex 𝒰 Ob) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro q p h
  rw [selectedCechResolutionTotalMap_ιTotal]
  rw [selectedCechResolutionBicomplexMap_refl]
  simp only [HomologicalComplex.id_f, Category.id_comp]
  exact (Category.comp_id
    ((selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
      (ComplexShape.up ℕ) q p n h)).symm

/-- Composite refinement induces the composite total map. -/
@[simp] theorem selectedCechResolutionTotalMap_comp
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 𝒱 𝒲 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (s : Site.AATCoverageFamily.Refinement 𝒱 𝒲)
    (Ob : ObstructionSheaf S) :
    selectedCechResolutionTotalMap (r.comp s) Ob =
      selectedCechResolutionTotalMap r Ob ≫
        selectedCechResolutionTotalMap s Ob := by
  simp [selectedCechResolutionTotalMap]

/-- The selected Čech edge commutes with refinement on the total complex. -/
theorem selectedCechToResolutionTotal_refinement_naturality
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) :
    selectedCechToResolutionTotal 𝒰 Ob ≫
        selectedCechResolutionTotalMap r Ob =
      r.selectedCechMap.app Ob.toAddCommGrpSheaf.val ≫
        selectedCechToResolutionTotal 𝒱 Ob := by
  apply HomologicalComplex.Hom.ext
  funext p
  have haug :
      (selectedCechResolutionAugmentation 𝒰 Ob).f p ≫
          ((selectedCechResolutionBicomplexMap r Ob).f 0).f p =
        (r.selectedCechMap.app Ob.toAddCommGrpSheaf.val).f p ≫
          (selectedCechResolutionAugmentation 𝒱 Ob).f p := by
    simpa using congrArg (fun f => f.f p)
      (selectedCechResolutionAugmentation_refinement_naturality r Ob)
  change
    (selectedCechResolutionAugmentation 𝒰 Ob).f p ≫
        (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
            (ComplexShape.up ℕ) 0 p p (by simp) ≫
          (selectedCechResolutionTotalMap r Ob).f p =
      (r.selectedCechMap.app Ob.toAddCommGrpSheaf.val).f p ≫
        (selectedCechResolutionAugmentation 𝒱 Ob).f p ≫
          (selectedCechResolutionBicomplex 𝒱 Ob).ιTotal
            (ComplexShape.up ℕ) 0 p p (by simp)
  rw [selectedCechResolutionTotalMap_ιTotal]
  rw [← Category.assoc]
  rw [haug]
  simp

/-- The base-resolution edge commutes with refinement on the total complex. -/
theorem baseResolutionToSelectedCechTotal_refinement_naturality
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) :
    baseResolutionToSelectedCechTotal 𝒰 Ob ≫
        selectedCechResolutionTotalMap r Ob =
      baseResolutionToSelectedCechTotal 𝒱 Ob := by
  apply HomologicalComplex.Hom.ext
  funext q
  have hzero :
      (baseResolutionToSelectedCechZero 𝒰 Ob).f q ≫
          ((selectedCechResolutionBicomplexMap r Ob).f q).f 0 =
        (baseResolutionToSelectedCechZero 𝒱 Ob).f q := by
    simpa using congrArg (fun f => f.f q)
      (baseResolutionToSelectedCechZero_refinement_naturality r Ob)
  change
    (baseResolutionToSelectedCechZero 𝒰 Ob).f q ≫
        (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
            (ComplexShape.up ℕ) q 0 q (by simp) ≫
          (selectedCechResolutionTotalMap r Ob).f q =
      (baseResolutionToSelectedCechZero 𝒱 Ob).f q ≫
        (selectedCechResolutionBicomplex 𝒱 Ob).ιTotal
          (ComplexShape.up ℕ) q 0 q (by simp)
  rw [selectedCechResolutionTotalMap_ιTotal]
  rw [← Category.assoc, hzero]

/-! ## Leray vanishing and actual resolution columns -/

/--
A selected cover is Leray for the obstruction sheaf when actual local
`Sheaf.H'` vanishes in every positive degree on every selected overlap.

Implementation notes: this is only the mathematical vanishing condition. It
does not store a comparison map, exactness proof, homology equivalence, or
collapse conclusion; those are derived below from the actual injective
resolution.
-/
def IsLerayFor
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})] :
    Prop :=
  ∀ q, 0 < q →
    ∀ p, ∀ σ : (canonicalCoverRelative 𝒰).simplex p,
      Subsingleton
        ((Ob.toAddCommGrpSheaf).H' q
          ((canonicalCoverRelative 𝒰).overlap p σ))

/-- Internal constant-zero additive presheaf used to construct the Leray instance pair. -/
private def zeroAddCommGrpPresheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} :
    S.categoryᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const S.categoryᵒᵖ).obj (AddCommGrpCat.of PUnit)

/--
The zero obstruction coefficient used as the satisfying `IsLerayFor` instance.

Implementation notes: this is the actual constant zero additive presheaf,
packaged through `ObstructionSheaf.ofAddCommGrpValued`. It does not attach a
vanishing certificate to the coefficient object.
-/
def zeroObstructionSheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) : ObstructionSheaf S :=
  ObstructionSheaf.ofAddCommGrpValued
    (zeroAddCommGrpPresheaf (S := S)) (by
      intro _base _cover _hcover family _compatible
      refine ⟨0, ?_, ?_⟩
      · intro _Y f hf
        change family f hf = PUnit.unit
        cases family f hf
        rfl
      · intro y _hy
        change y = PUnit.unit
        cases y
        rfl)

/-- The actual additive sheaf underlying `zeroObstructionSheaf` is a zero object. -/
theorem zeroObstructionSheaf_toAddCommGrpSheaf_isZero
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} :
    Limits.IsZero (zeroObstructionSheaf S).toAddCommGrpSheaf := by
  rw [Limits.IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  letI : Subsingleton
      ((zeroObstructionSheaf S).toAddCommGrpSheaf.val.obj X) := by
    change Subsingleton (ULift PUnit)
    infer_instance
  exact Subsingleton.elim _ _

/--
The zero obstruction coefficient satisfies the actual positive-degree local
cohomology condition for every selected cover.
-/
theorem zeroObstructionSheaf_isLerayFor
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {base : S.category}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    IsLerayFor 𝒰 (zeroObstructionSheaf S) := by
  intro q hq p σ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  letI : Injective (zeroObstructionSheaf S).toAddCommGrpSheaf :=
    zeroObstructionSheaf_toAddCommGrpSheaf_isZero.injective
  exact CategoryTheory.Abelian.Ext.subsingleton_of_injective _ _ n

/--
A nontrivial actual local `Sheaf.H'` group makes the selected cover fail the
Leray condition. This is the rejecting half of the `IsLerayFor` instance pair;
the SD9 finite declaration must construct the required nontrivial group rather
than pass a comparison or collapse witness.
-/
theorem not_isLerayFor_of_nontrivialHPrime
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {base : S.category}
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : ObstructionSheaf S}
    {q p : ℕ} (hq : 0 < q)
    (σ : (canonicalCoverRelative 𝒰).simplex p)
    [Nontrivial
      ((Ob.toAddCommGrpSheaf).H' q
        ((canonicalCoverRelative 𝒰).overlap p σ))] :
    ¬ IsLerayFor 𝒰 Ob := by
  intro hLeray
  exact not_subsingleton _ (hLeray q hq p σ)

/--
The actual resolution column at a fixed selected Čech degree.

Implementation notes: the column is obtained by Mathlib's
`HomologicalComplex₂.flipFunctor` from the actual selected Čech-resolution
bicomplex. A separately supplied column complex is rejected because it would
disconnect later exactness from that bicomplex.
-/
noncomputable def selectedCechResolutionColumn
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (p : ℕ) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{u + 1}
    (ComplexShape.up ℕ) (ComplexShape.up ℕ)).obj
      (selectedCechResolutionBicomplex 𝒰 Ob)).X p

/-- The column object is the product of resolution sections on selected overlaps. -/
@[simp] theorem selectedCechResolutionColumn_X
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (p q : ℕ) :
    ((selectedCechResolutionColumn 𝒰 Ob p).X q : Type (u + 1)) =
      SelectedCechCochain 𝒰
        ((obstructionInjectiveResolution Ob).cocomplex.X q).val p :=
  rfl

/-- The column differential applies the injective-resolution differential pointwise. -/
theorem selectedCechResolutionColumn_d_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (p q : ℕ)
    (c : SelectedCechCochain 𝒰
      ((obstructionInjectiveResolution Ob).cocomplex.X q).val p)
    (σ : (canonicalCoverRelative 𝒰).simplex p) :
    ((selectedCechResolutionColumn 𝒰 Ob p).d q (q + 1)).hom c σ =
      ((obstructionInjectiveResolution Ob).cocomplex.d q (q + 1)).val.app _
        (c σ) :=
  rfl

/-- Leray vanishing kills positive-degree resolution homology on each overlap. -/
theorem IsLerayFor.overlapBaseResolutionHomology_subsingleton
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : ObstructionSheaf S}
    (hLeray : IsLerayFor 𝒰 Ob)
    (q : ℕ) (hq : 0 < q) (p : ℕ)
    (σ : (canonicalCoverRelative 𝒰).simplex p) :
    Subsingleton
      ((baseResolutionComplex
        (base := (canonicalCoverRelative 𝒰).overlap p σ) Ob).homology q :
          Type (u + 1)) := by
  let e := baseResolutionHomologyEquivHPrime
    (base := (canonicalCoverRelative 𝒰).overlap p σ) Ob q
  letI := hLeray q hq p σ
  exact e.injective.subsingleton

/-- Leray vanishing makes each overlap-evaluated resolution exact in positive degree. -/
theorem IsLerayFor.overlapBaseResolution_exactAt
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : ObstructionSheaf S}
    (hLeray : IsLerayFor 𝒰 Ob)
    (q : ℕ) (hq : 0 < q) (p : ℕ)
    (σ : (canonicalCoverRelative 𝒰).simplex p) :
    (baseResolutionComplex
      (base := (canonicalCoverRelative 𝒰).overlap p σ) Ob).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact hLeray.overlapBaseResolutionHomology_subsingleton q hq p σ

/--
Every actual resolution column is exact in positive degree under the Leray
condition. Preimages are chosen on each overlap and assembled into the actual
selected-cochain product.
-/
theorem IsLerayFor.selectedCechResolutionColumn_exactAt
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : ObstructionSheaf S}
    (hLeray : IsLerayFor 𝒰 Ob)
    (q : ℕ) (hq : 0 < q) (p : ℕ) :
    (selectedCechResolutionColumn 𝒰 Ob p).ExactAt q := by
  rcases q with _ | q
  · omega
  rw [(selectedCechResolutionColumn 𝒰 Ob p).exactAt_iff'
    q (q + 1) (q + 2) (CochainComplex.prev_nat_succ q) (by simp)]
  rw [ShortComplex.ab_exact_iff_ker_le_range]
  intro x hx
  change ((selectedCechResolutionColumn 𝒰 Ob p).d (q + 1) (q + 2)).hom x = 0 at hx
  change ∃ y, ((selectedCechResolutionColumn 𝒰 Ob p).d q (q + 1)).hom y = x
  have hpreimage : ∀ σ : (canonicalCoverRelative 𝒰).simplex p,
      ∃ y : ((obstructionInjectiveResolution Ob).cocomplex.X q).val.obj
          (Opposite.op ((canonicalCoverRelative 𝒰).overlap p σ)),
        ((obstructionInjectiveResolution Ob).cocomplex.d q (q + 1)).val.app _ y =
          x σ := by
    intro σ
    let K := baseResolutionComplex
      (base := (canonicalCoverRelative 𝒰).overlap p σ) Ob
    have hlocal := hLeray.overlapBaseResolution_exactAt (q + 1) (by omega) p σ
    rw [K.exactAt_iff' q (q + 1) (q + 2)
      (CochainComplex.prev_nat_succ q) (by simp)] at hlocal
    rw [ShortComplex.ab_exact_iff_ker_le_range] at hlocal
    have hxσ :
        ((obstructionInjectiveResolution Ob).cocomplex.d
          (q + 1) (q + 2)).val.app _ (x σ) = 0 := by
      calc
        _ = ((selectedCechResolutionColumn 𝒰 Ob p).d
              (q + 1) (q + 2)).hom x σ := by
            symm
            simpa [Nat.add_assoc] using
              selectedCechResolutionColumn_d_apply 𝒰 Ob p (q + 1) x σ
        _ = 0 := congrFun hx σ
    have hxK : x σ ∈ ((K.d (q + 1) (q + 2)).hom).ker := by
      change (K.d (q + 1) (q + 2)).hom (x σ) = 0
      rw [baseResolutionComplex_d_apply]
      exact hxσ
    rcases hlocal hxK with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [← baseResolutionComplex_d_apply]
    exact hy
  choose y hy using hpreimage
  refine ⟨fun σ => y σ, ?_⟩
  funext σ
  rw [selectedCechResolutionColumn_d_apply]
  exact hy σ

/-- Positive-degree homology of every actual resolution column is trivial. -/
theorem IsLerayFor.selectedCechResolutionColumn_homology_subsingleton
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : ObstructionSheaf S}
    (hLeray : IsLerayFor 𝒰 Ob)
    (q : ℕ) (hq : 0 < q) (p : ℕ) :
    Subsingleton
      ((selectedCechResolutionColumn 𝒰 Ob p).homology q : Type (u + 1)) := by
  rw [← AddCommGrpCat.isZero_iff_subsingleton]
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact hLeray.selectedCechResolutionColumn_exactAt q hq p

/--
The resolution augmentation is exact at degree zero in every selected Čech
degree. Exactness is mapped from the actual injective resolution through each
overlap evaluation and the resulting preimages are assembled pointwise.
-/
theorem selectedCechResolutionAugmentation_exactAtZero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (p : ℕ) :
    Function.Exact
      ((selectedCechResolutionAugmentation 𝒰 Ob).f p).hom
      (((selectedCechResolutionBicomplex 𝒰 Ob).d 0 1).f p).hom := by
  let R := obstructionInjectiveResolution Ob
  intro x
  constructor
  · intro hx
    have hpreimage : ∀ σ : (canonicalCoverRelative 𝒰).simplex p,
        ∃ y : Ob.toAddCommGrpSheaf.val.obj
            (Opposite.op ((canonicalCoverRelative 𝒰).overlap p σ)),
          ((R.ι.f 0).val.app _).hom y = x σ := by
      intro σ
      let F := sheafToPresheaf S.topology AddCommGrpCat.{u + 1} ⋙
        (evaluation S.categoryᵒᵖ AddCommGrpCat.{u + 1}).obj
          (Opposite.op ((canonicalCoverRelative 𝒰).overlap p σ))
      let K := ShortComplex.mk (R.ι.f 0) (R.cocomplex.d 0 1)
        R.ι_f_zero_comp_complex_d
      have hK : K.Exact := R.exact₀
      have hmap : (K.map F).Exact :=
        hK.map_of_mono_of_preservesKernel F (by infer_instance) (by infer_instance)
      have hfun : Function.Exact (F.map (R.ι.f 0))
          (F.map (R.cocomplex.d 0 1)) :=
        (ShortComplex.ab_exact_iff_function_exact (S := K.map F)).mp hmap
      apply (hfun (x σ)).mp
      change ((R.cocomplex.d 0 1).val.app _).hom (x σ) = 0
      calc
        _ = ((((selectedCechResolutionBicomplex 𝒰 Ob).d 0 1).f p).hom x) σ := by
          symm
          exact selectedCechResolutionBicomplex_resolution_d_apply
            𝒰 Ob 0 p x σ
        _ = 0 := congrFun hx σ
    choose y hy using hpreimage
    refine ⟨fun σ => y σ, ?_⟩
    funext σ
    rw [selectedCechResolutionAugmentation_f_apply]
    exact hy σ
  · rintro ⟨c, rfl⟩
    exact ConcreteCategory.congr_hom
      (selectedCechResolutionAugmentation_comp_resolution_d 𝒰 Ob p) c

/--
Restriction maps of an injective additive sheaf on an AAT context site are
surjective. The proof represents a section by a morphism from the sheafified
free Yoneda object and extends that morphism across the mono induced by the
context arrow.
-/
theorem injectiveSheaf_restriction_surjective
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (I : Sheaf S.topology AddCommGrpCat.{u + 1})
    [Injective I]
    {X Y : S.category} (f : X ⟶ Y) :
    Function.Surjective (I.val.map f.op) := by
  let P (Z : S.category) :=
    (presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
      (yoneda.obj Z ⋙ AddCommGrpCat.free)
  let m : P X ⟶ P Y :=
    (presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
      (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free)
  letI : Mono f := by
    constructor
    intro Z g h _
    exact Subsingleton.elim g h
  letI : Mono m := by
    dsimp [m, P]
    infer_instance
  intro x
  let h : P X ⟶ I :=
    (sheafifiedFreeYonedaHomAddEquiv X I).symm x
  let e : P Y ⟶ I := Injective.factorThru h m
  refine ⟨sheafifiedFreeYonedaHomAddEquiv Y I e, ?_⟩
  rw [← sheafifiedFreeYonedaHomAddEquiv_precomp f I e]
  change sheafifiedFreeYonedaHomAddEquiv X I (m ≫ e) = x
  rw [Injective.comp_factorThru]
  exact (sheafifiedFreeYonedaHomAddEquiv X I).apply_symm_apply x

private def selectedCechSingle
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (i : 𝒰.Index) : (canonicalCoverRelative 𝒰).simplex 0 :=
  fun _ => i

private def selectedCechPair
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (i j : 𝒰.Index) : (canonicalCoverRelative 𝒰).simplex 1 :=
  Fin.cases j (fun _ => i)

private theorem selectedCechPair_face_zero
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (i j : 𝒰.Index) :
    (canonicalCoverRelative 𝒰).face 0 0 (selectedCechPair 𝒰 i j) =
      selectedCechSingle 𝒰 i := by
  rfl

private theorem selectedCechPair_face_one
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (i j : 𝒰.Index) :
    (canonicalCoverRelative 𝒰).face 0 1 (selectedCechPair 𝒰 i j) =
      selectedCechSingle 𝒰 j := by
  funext k
  exact Fin.eq_zero k ▸ rfl

private noncomputable def selectedCechPairLift
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (i j : 𝒰.Index) {Z : S.category}
    (gi : Z ⟶ (canonicalCoverRelative 𝒰).chart i)
    (gj : Z ⟶ (canonicalCoverRelative 𝒰).chart j) :
    Z ⟶ (canonicalCoverRelative 𝒰).overlap 1 (selectedCechPair 𝒰 i j) := by
  apply homOfLE
  exact S.overlap.overlap_lift
    (𝒰.inclusion j) (𝒰.inclusion i) (leOfHom gj) (leOfHom gi)

private theorem selectedCechZeroCompatible
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (c : SelectedCechCochain 𝒰 F 0)
    (hc : (((selectedCechComplexFunctor 𝒰).obj F).d 0 1).hom c = 0) :
    Presieve.Arrows.Compatible (F ⋙ forget AddCommGrpCat.{u + 1})
      (fun i => homOfLE (𝒰.inclusion i))
      (fun i => c (selectedCechSingle 𝒰 i)) := by
  intro i j Z gi gj _
  let σ := selectedCechPair 𝒰 i j
  let k := selectedCechPairLift 𝒰 i j gi gj
  let ri : (canonicalCoverRelative 𝒰).overlap 1 σ ⟶
      (canonicalCoverRelative 𝒰).chart i :=
    (canonicalCoverRelative 𝒰).faceRestriction 0 0 σ ≫
      eqToHom (congrArg ((canonicalCoverRelative 𝒰).overlap 0)
        (selectedCechPair_face_zero 𝒰 i j))
  let rj : (canonicalCoverRelative 𝒰).overlap 1 σ ⟶
      (canonicalCoverRelative 𝒰).chart j :=
    (canonicalCoverRelative 𝒰).faceRestriction 0 1 σ ≫
      eqToHom (congrArg ((canonicalCoverRelative 𝒰).overlap 0)
        (selectedCechPair_face_one 𝒰 i j))
  have hdiff := congrFun hc σ
  rw [selectedCechComplexFunctor_obj_d_apply, Fin.sum_univ_two] at hdiff
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_smul] at hdiff
  have hraw :
      F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op
          (c ((canonicalCoverRelative 𝒰).face 0 0 σ)) =
        F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op
          (c ((canonicalCoverRelative 𝒰).face 0 1 σ)) := by
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg, Pi.zero_apply] using hdiff
  have hi :
      F.map ri.op (c (selectedCechSingle 𝒰 i)) =
        F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op
          (c ((canonicalCoverRelative 𝒰).face 0 0 σ)) := by
    simp [ri, σ]
    congr 1
  have hj :
      F.map rj.op (c (selectedCechSingle 𝒰 j)) =
        F.map ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op
          (c ((canonicalCoverRelative 𝒰).face 0 1 σ)) := by
    simp [rj, σ]
    congr 2
    funext x
    exact Fin.eq_zero x ▸ rfl
  have hlocal : F.map ri.op (c (selectedCechSingle 𝒰 i)) =
      F.map rj.op (c (selectedCechSingle 𝒰 j)) :=
    hi.trans (hraw.trans hj.symm)
  change F.map gi.op (c (selectedCechSingle 𝒰 i)) =
    F.map gj.op (c (selectedCechSingle 𝒰 j))
  have hki : ri.op ≫ k.op = gi.op := Subsingleton.elim _ _
  have hkj : rj.op ≫ k.op = gj.op := Subsingleton.elim _ _
  calc
    _ = F.map k.op (F.map ri.op (c (selectedCechSingle 𝒰 i))) := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, hki]
      rfl
    _ = F.map k.op (F.map rj.op (c (selectedCechSingle 𝒰 j))) :=
      congrArg _ hlocal
    _ = _ := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, hkj]
      rfl

private theorem baseToSelectedCechZero_comp_cech_d
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (baseToSelectedCechZero 𝒰).app F ≫
        ((selectedCechComplexFunctor 𝒰).obj F).d 0 1 = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext σ
  change (((selectedCechComplexFunctor 𝒰).obj F).d 0 1).hom
      (((baseToSelectedCechZero 𝒰).app F).hom x) σ = 0
  rw [selectedCechComplexFunctor_obj_d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_smul, baseToSelectedCechZero_app_apply]
  let F' := F ⋙ forget AddCommGrpCat.{u + 1}
  change F'.map ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op
        (F'.map ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 0 σ) 0)).op x) +
      -F'.map ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op
        (F'.map ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 1 σ) 0)).op x) = 0
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
  have hmor :
      ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 0 σ) 0)).op ≫
          ((canonicalCoverRelative 𝒰).faceRestriction 0 0 σ).op =
        ((canonicalCoverRelative 𝒰).inclusion
          (((canonicalCoverRelative 𝒰).face 0 1 σ) 0)).op ≫
          ((canonicalCoverRelative 𝒰).faceRestriction 0 1 σ).op :=
    Subsingleton.elim _ _
  rw [hmor]
  simp

/--
The selected Čech augmentation is exact at degree zero for every actual sheaf.
The proof converts the degree-zero cocycle equation into compatibility for the
selected covering family and applies the sheaf gluing condition on its generated
covering sieve.
-/
theorem sheaf_selectedCechAugmentation_exactAtZero
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (I : Sheaf S.topology AddCommGrpCat.{u + 1}) :
    Function.Exact
      ((baseToSelectedCechZero 𝒰).app I.val).hom
      (((selectedCechComplexFunctor 𝒰).obj I.val).d 0 1).hom := by
  intro c
  constructor
  · intro hc
    have hTypePresheaf : Presheaf.IsSheaf S.topology
        (I.val ⋙ forget AddCommGrpCat.{u + 1}) :=
      (Presheaf.isSheaf_iff_isSheaf_forget
        (J := S.topology) (P' := I.val)
        (forget AddCommGrpCat.{u + 1})).mp I.cond
    have hType : Presieve.IsSheaf S.topology
        (I.val ⋙ forget AddCommGrpCat.{u + 1}) :=
      (isSheaf_iff_isSheaf_of_type S.topology
        (I.val ⋙ forget AddCommGrpCat.{u + 1})).mp hTypePresheaf
    have hgen := hType (Sieve.generate 𝒰.presieve) 𝒰.mem_topology
    have hcover : Presieve.IsSheafFor
        (I.val ⋙ forget AddCommGrpCat.{u + 1}) 𝒰.presieve :=
      (Presieve.isSheafFor_iff_generate 𝒰.presieve).mpr hgen
    have hglue := (Presieve.isSheafFor_arrows_iff
      (I.val ⋙ forget AddCommGrpCat.{u + 1})
      (fun i => homOfLE (𝒰.inclusion i))).mp hcover
      (fun i => c (selectedCechSingle 𝒰 i))
      (selectedCechZeroCompatible 𝒰 I.val c hc)
    obtain ⟨t, ht, _⟩ := hglue
    refine ⟨t, ?_⟩
    funext σ
    have hσ : σ = selectedCechSingle 𝒰 (σ 0) := by
      funext k
      exact Fin.eq_zero k ▸ rfl
    rw [hσ]
    exact ht (σ 0)
  · rintro ⟨t, rfl⟩
    exact ConcreteCategory.congr_hom
      (baseToSelectedCechZero_comp_cech_d 𝒰 I.val) t

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

abbrev SelectedCechFreeGenerator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (X : S.category) :=
  Σ σ : (canonicalCoverRelative 𝒰).simplex n,
    X ⟶ (canonicalCoverRelative 𝒰).overlap n σ

def selectedCechFreeGeneratorMap
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {X Y : S.categoryᵒᵖ} (f : X ⟶ Y) :
    SelectedCechFreeGenerator 𝒰 n X.unop → SelectedCechFreeGenerator 𝒰 n Y.unop :=
  fun g => ⟨g.1, f.unop ≫ g.2⟩

@[simp] theorem selectedCechFreeGeneratorMap_id
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (X : S.categoryᵒᵖ) :
    selectedCechFreeGeneratorMap 𝒰 n (𝟙 X) = id := by
  funext g
  rcases g with ⟨σ, g⟩
  simp [selectedCechFreeGeneratorMap]

theorem selectedCechFreeGeneratorMap_comp
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {X Y Z : S.categoryᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    selectedCechFreeGeneratorMap 𝒰 n (f ≫ g) =
      selectedCechFreeGeneratorMap 𝒰 n g ∘ selectedCechFreeGeneratorMap 𝒰 n f := by
  funext h
  rcases h with ⟨σ, h⟩
  simp [selectedCechFreeGeneratorMap]

noncomputable def selectedCechFreePresheaf
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj X := AddCommGrpCat.of (FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 n X.unop))
  map {X Y} f := AddCommGrpCat.ofHom
    (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n f))
  map_id X := by
    change AddCommGrpCat.ofHom
      (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n (𝟙 X))) = 𝟙 _
    rw [selectedCechFreeGeneratorMap_id, FreeAbelianGroup.map_id]
    rfl
  map_comp f g := by
    change AddCommGrpCat.ofHom
        (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n (f ≫ g))) =
      AddCommGrpCat.ofHom (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n f)) ≫
        AddCommGrpCat.ofHom (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n g))
    rw [selectedCechFreeGeneratorMap_comp, FreeAbelianGroup.map_comp]
    rfl

@[simp] theorem selectedCechFreePresheaf_map_of
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {X Y : S.categoryᵒᵖ} (f : X ⟶ Y)
    (g : SelectedCechFreeGenerator 𝒰 n X.unop) :
    (selectedCechFreePresheaf 𝒰 n).map f (FreeAbelianGroup.of g) =
      FreeAbelianGroup.of ⟨g.1, f.unop ≫ g.2⟩ := by
  change FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n f)
      (FreeAbelianGroup.of g) = _
  exact FreeAbelianGroup.map_of_apply g

def selectedCechFreeFaceGenerator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (i : Fin (n + 2)) {X : S.category}
    (g : SelectedCechFreeGenerator 𝒰 (n + 1) X) : SelectedCechFreeGenerator 𝒰 n X :=
  ⟨(canonicalCoverRelative 𝒰).face n i g.1,
    g.2 ≫ (canonicalCoverRelative 𝒰).faceRestriction n i g.1⟩

def selectedCechFreeBoundaryGenerator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {X : S.category} :
    SelectedCechFreeGenerator 𝒰 (n + 1) X → FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 n X) :=
  fun g => ∑ i : Fin (n + 2),
    ((-1 : ℤ) ^ i.1) • FreeAbelianGroup.of
      (selectedCechFreeFaceGenerator 𝒰 n i g)

noncomputable def selectedCechFreeBoundary
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) : selectedCechFreePresheaf 𝒰 (n + 1) ⟶ selectedCechFreePresheaf 𝒰 n where
  app X := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n))
  naturality X Y f := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro g
    change FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n)
        (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 (n + 1) f)
          (FreeAbelianGroup.of g)) =
      FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n f)
        (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n)
          (FreeAbelianGroup.of g))
    rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
    simp only [selectedCechFreeBoundaryGenerator, map_sum, map_zsmul,
      FreeAbelianGroup.map_of_apply]
    apply Finset.sum_congr rfl
    intro i _
    congr 2

@[simp] theorem selectedCechFreeBoundary_app_of
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (X : S.categoryᵒᵖ)
    (g : SelectedCechFreeGenerator 𝒰 (n + 1) X.unop) :
    (selectedCechFreeBoundary 𝒰 n).app X (FreeAbelianGroup.of g) =
      selectedCechFreeBoundaryGenerator 𝒰 n g := by
  exact FreeAbelianGroup.lift_apply_of (selectedCechFreeBoundaryGenerator 𝒰 n) g

def selectedCechFreeSimplexGeneratorMap
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {x y : SimplexCategory} (f : x ⟶ y) {X : S.category} :
    SelectedCechFreeGenerator 𝒰 y.len X → SelectedCechFreeGenerator 𝒰 x.len X :=
  fun g =>
    ⟨fun i => g.1 (f.toOrderHom i),
      g.2 ≫ canonicalTupleOverlapMap 𝒰 f g.1⟩

noncomputable def selectedCechFreeSimplexMap
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {x y : SimplexCategory} (f : x ⟶ y) :
    selectedCechFreePresheaf 𝒰 y.len ⟶ selectedCechFreePresheaf 𝒰 x.len where
  app X := AddCommGrpCat.ofHom
    (FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 f))
  naturality X Y g := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro h
    change FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 f)
        (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 y.len g)
          (FreeAbelianGroup.of h)) =
      FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 x.len g)
        (FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 f)
          (FreeAbelianGroup.of h))
    simp only [FreeAbelianGroup.map_of_apply]
    congr 2

@[simp] theorem selectedCechFreeSimplexMap_app_of
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {x y : SimplexCategory} (f : x ⟶ y) (X : S.categoryᵒᵖ)
    (g : SelectedCechFreeGenerator 𝒰 y.len X.unop) :
    (selectedCechFreeSimplexMap 𝒰 f).app X (FreeAbelianGroup.of g) =
      FreeAbelianGroup.of (selectedCechFreeSimplexGeneratorMap 𝒰 f g) := by
  exact FreeAbelianGroup.map_of_apply g

@[simp] theorem selectedCechFreeSimplexMap_id
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (x : SimplexCategory) :
    selectedCechFreeSimplexMap 𝒰 (𝟙 x) = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro g
  change FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 (𝟙 x))
      (FreeAbelianGroup.of g) = FreeAbelianGroup.of g
  rw [FreeAbelianGroup.map_of_apply]
  congr 2

theorem selectedCechFreeSimplexMap_comp
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {x y z : SimplexCategory} (f : x ⟶ y) (g : y ⟶ z) :
    selectedCechFreeSimplexMap 𝒰 (f ≫ g) =
      selectedCechFreeSimplexMap 𝒰 g ≫ selectedCechFreeSimplexMap 𝒰 f := by
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro h
  change FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 (f ≫ g))
      (FreeAbelianGroup.of h) =
    FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 f)
      (FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 g)
        (FreeAbelianGroup.of h))
  rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.map_of_apply,
    FreeAbelianGroup.map_of_apply]
  apply congrArg FreeAbelianGroup.of
  apply Sigma.ext
  · funext i
    rfl
  · exact heq_of_eq (Subsingleton.elim _ _)

noncomputable def selectedCechFreeSimplicialObject
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    SimplicialObject (S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) where
  obj x := selectedCechFreePresheaf 𝒰 x.unop.len
  map f := selectedCechFreeSimplexMap 𝒰 f.unop
  map_id x := by
    exact selectedCechFreeSimplexMap_id 𝒰 x.unop
  map_comp f g := by
    exact selectedCechFreeSimplexMap_comp 𝒰 g.unop f.unop

noncomputable def selectedCechFreeChain
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ChainComplex (S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ :=
  AlgebraicTopology.alternatingFaceMapComplex
    (S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) |>.obj
      (selectedCechFreeSimplicialObject 𝒰)

theorem selectedCechFreeSimplicial_delta_app_of
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) (i : Fin (n + 2)) (X : S.categoryᵒᵖ)
    (g : SelectedCechFreeGenerator 𝒰 (n + 1) X.unop) :
    (((-1 : ℤ) ^ (i : ℕ) •
      (selectedCechFreeSimplicialObject 𝒰).δ i).app X).hom
        (FreeAbelianGroup.of g) =
      ((-1 : ℤ) ^ (i : ℕ)) •
        FreeAbelianGroup.of (selectedCechFreeFaceGenerator 𝒰 n i g) := by
  rw [NatTrans.app_zsmul]
  change (((-1 : ℤ) ^ (i : ℕ)) •
      FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 (SimplexCategory.δ i)))
        (FreeAbelianGroup.of g) = _
  rw [show (((( -1 : ℤ) ^ (i : ℕ)) •
      FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 (SimplexCategory.δ i)))
        (FreeAbelianGroup.of g)) =
      ((-1 : ℤ) ^ (i : ℕ)) •
        FreeAbelianGroup.map (selectedCechFreeSimplexGeneratorMap 𝒰 (SimplexCategory.δ i))
          (FreeAbelianGroup.of g) from rfl,
    FreeAbelianGroup.map_of_apply]
  rfl

theorem selectedCechFreeChain_d_eq_selectedCechFreeBoundary
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) :
    (selectedCechFreeChain 𝒰).d (n + 1) n = selectedCechFreeBoundary 𝒰 n := by
  unfold selectedCechFreeChain
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro g
  change
    ((∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (selectedCechFreeSimplicialObject 𝒰).δ i).app X) (FreeAbelianGroup.of g) = _
  rw [show
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (selectedCechFreeSimplicialObject 𝒰).δ i).app X =
        ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ) •
          (selectedCechFreeSimplicialObject 𝒰).δ i).app X by
      simpa using map_sum
        (NatTrans.appHom (F := selectedCechFreePresheaf 𝒰 (n + 1))
          (G := selectedCechFreePresheaf 𝒰 n) X)
        (fun i : Fin (n + 2) => (-1 : ℤ) ^ (i : ℕ) •
          (selectedCechFreeSimplicialObject 𝒰).δ i) Finset.univ]
  let ev : ((selectedCechFreePresheaf 𝒰 (n + 1)).obj X ⟶
      (selectedCechFreePresheaf 𝒰 n).obj X) →+
      ((selectedCechFreePresheaf 𝒰 n).obj X : Type (u + 1)) :=
    { toFun := fun (f : (selectedCechFreePresheaf 𝒰 (n + 1)).obj X ⟶
        (selectedCechFreePresheaf 𝒰 n).obj X) => f.hom (FreeAbelianGroup.of g)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ) •
    (selectedCechFreeSimplicialObject 𝒰).δ i).app X) = _
  rw [show ev (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ) •
      (selectedCechFreeSimplicialObject 𝒰).δ i).app X) =
        ∑ i : Fin (n + 2), ev
          (((-1 : ℤ) ^ (i : ℕ) •
            (selectedCechFreeSimplicialObject 𝒰).δ i).app X) by
      simpa using map_sum ev
        (fun i : Fin (n + 2) => ((-1 : ℤ) ^ (i : ℕ) •
          (selectedCechFreeSimplicialObject 𝒰).δ i).app X) Finset.univ]
  dsimp [ev]
  calc
    _ = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        FreeAbelianGroup.of (selectedCechFreeFaceGenerator 𝒰 n i g) := by
      apply Finset.sum_congr rfl
      intro i _
      exact selectedCechFreeSimplicial_delta_app_of 𝒰 n i X g
    _ = _ := by
      change (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          FreeAbelianGroup.of (selectedCechFreeFaceGenerator 𝒰 n i g)) =
        FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n)
          (FreeAbelianGroup.of g)
      rw [FreeAbelianGroup.lift_apply_of]
      rfl

def selectedCechPrependSimplex
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} (i : 𝒰.Index)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    (canonicalCoverRelative 𝒰).simplex (n + 1) :=
  Fin.cases i σ

theorem selectedCechPrependSimplex_face_zero
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} (i : 𝒰.Index)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    (canonicalCoverRelative 𝒰).face n 0 (selectedCechPrependSimplex 𝒰 i σ) = σ := by
  funext k
  rfl

theorem selectedCechPrependSimplex_face_succ
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} (i : 𝒰.Index)
    (σ : (canonicalCoverRelative 𝒰).simplex (n + 1))
    (j : Fin (n + 2)) :
    (canonicalCoverRelative 𝒰).face (n + 1) j.succ
        (selectedCechPrependSimplex 𝒰 i σ) =
      selectedCechPrependSimplex 𝒰 i ((canonicalCoverRelative 𝒰).face n j σ) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · simp [canonicalCoverRelative_face,
      Site.FinitePosetCechCanonicalTupleSimplex.simplexMap_apply,
      SimplexCategory.δ, selectedCechPrependSimplex]

noncomputable def selectedCechPrependLift
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (g : SelectedCechFreeGenerator 𝒰 n Y) :
    Y ⟶ (canonicalCoverRelative 𝒰).overlap (n + 1)
      (selectedCechPrependSimplex 𝒰 i g.1) :=
  canonicalTupleOverlapLift 𝒰 (selectedCechPrependSimplex 𝒰 i g.1)
    (Fin.cases a (fun k => g.2 ≫ canonicalTupleOverlapProjection 𝒰 g.1 k))

noncomputable def selectedCechPrependGenerator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (g : SelectedCechFreeGenerator 𝒰 n Y) : SelectedCechFreeGenerator 𝒰 (n + 1) Y :=
  ⟨selectedCechPrependSimplex 𝒰 i g.1, selectedCechPrependLift 𝒰 i a g⟩

def selectedCechContractionGenerator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i) :
    SelectedCechFreeGenerator 𝒰 n Y → FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y) :=
  fun g => FreeAbelianGroup.of (selectedCechPrependGenerator 𝒰 i a g)

def selectedCechContraction
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i) :
    FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 n Y) →+
      FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y) :=
  FreeAbelianGroup.lift (selectedCechContractionGenerator 𝒰 i a)

theorem selectedCechFreeFaceGenerator_zero_prepend
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (g : SelectedCechFreeGenerator 𝒰 n Y) :
    selectedCechFreeFaceGenerator 𝒰 n 0 (selectedCechPrependGenerator 𝒰 i a g) = g := by
  have hface := selectedCechPrependSimplex_face_zero 𝒰 i g.1
  apply Sigma.ext hface
  apply Quiver.heq_of_homOfEq_ext rfl
    (congrArg ((canonicalCoverRelative 𝒰).overlap n) hface)
  exact Subsingleton.elim _ _

theorem selectedCechFreeFaceGenerator_succ_prepend
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {n : ℕ} {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (g : SelectedCechFreeGenerator 𝒰 (n + 1) Y) (j : Fin (n + 2)) :
    selectedCechFreeFaceGenerator 𝒰 (n + 1) j.succ (selectedCechPrependGenerator 𝒰 i a g) =
      selectedCechPrependGenerator 𝒰 i a (selectedCechFreeFaceGenerator 𝒰 n j g) := by
  have hface := selectedCechPrependSimplex_face_succ 𝒰 i g.1 j
  apply Sigma.ext hface
  apply Quiver.heq_of_homOfEq_ext rfl
    (congrArg ((canonicalCoverRelative 𝒰).overlap (n + 1)) hface)
  exact Subsingleton.elim _ _

theorem selectedCechFreeBoundary_contraction_generator
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (g : SelectedCechFreeGenerator 𝒰 (n + 1) Y) :
    FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 (n + 1))
        (selectedCechContraction 𝒰 i a (FreeAbelianGroup.of g)) +
      selectedCechContraction 𝒰 i a
        (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n)
          (FreeAbelianGroup.of g)) =
      FreeAbelianGroup.of g := by
  simp only [selectedCechContraction, selectedCechContractionGenerator,
    FreeAbelianGroup.lift_apply_of,
    selectedCechFreeBoundaryGenerator, map_sum, map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul,
    selectedCechFreeFaceGenerator_zero_prepend, Fin.val_succ,
    selectedCechFreeFaceGenerator_succ_prepend]
  have hpow (x : Fin (n + 2)) :
      (-1 : ℤ) ^ (x.1 + 1) = -((-1 : ℤ) ^ x.1) := by
    rw [pow_succ]
    ring
  simp_rw [hpow]
  simp only [neg_zsmul, Finset.sum_neg_distrib]
  abel

theorem selectedCechFreeBoundary_contraction
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) {Y : S.category} (i : 𝒰.Index)
    (a : Y ⟶ (canonicalCoverRelative 𝒰).chart i)
    (x : FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y)) :
    FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 (n + 1))
        (selectedCechContraction 𝒰 i a x) +
      selectedCechContraction 𝒰 i a
        (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n) x) = x := by
  let lhs : FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y) →+
      FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y) :=
    (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 (n + 1))).comp
        (selectedCechContraction 𝒰 i a) +
      (selectedCechContraction 𝒰 i a).comp
        (FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n))
  have hlhs : lhs = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro g
    exact selectedCechFreeBoundary_contraction_generator 𝒰 n i a g
  exact DFunLike.congr_fun hlhs x

theorem selectedCechFreeBoundaryToCycles_isLocallySurjective
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) :
    Presheaf.IsLocallySurjective S.topology
      ((selectedCechFreeChain 𝒰).sc' (n + 2) (n + 1) n).toCycles := by
  classical
  let SC := (selectedCechFreeChain 𝒰).sc' (n + 2) (n + 1) n
  constructor
  intro X s
  let x : FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) X) :=
    (SC.iCycles.app (Opposite.op X)).hom s
  cases isEmpty_or_nonempty (SelectedCechFreeGenerator 𝒰 (n + 1) X) with
  | inl hEmpty =>
      haveI : IsEmpty (SelectedCechFreeGenerator 𝒰 (n + 1) X) := hEmpty
      have hx : x = 0 := Subsingleton.elim _ _
      refine S.topology.superset_covering ?_ (S.topology.top_mem X)
      intro Y f _
      rw [Presheaf.imageSieve_apply]
      refine ⟨0, ?_⟩
      apply (AddCommGrpCat.mono_iff_injective
        (SC.iCycles.app (Opposite.op Y))).mp inferInstance
      change (((SC.toCycles ≫ SC.iCycles).app (Opposite.op Y)).hom 0) =
        (SC.iCycles.app (Opposite.op Y)).hom
          ((SC.cycles.map f.op).hom s)
      rw [SC.toCycles_i]
      simp only [map_zero]
      rw [NatTrans.naturality_apply SC.iCycles f.op s]
      change 0 = (selectedCechFreePresheaf 𝒰 (n + 1)).map f.op x
      rw [hx, map_zero]
  | inr hNonempty =>
      let g₀ : SelectedCechFreeGenerator 𝒰 (n + 1) X := Classical.choice hNonempty
      let b : X ⟶ base :=
        g₀.2 ≫ canonicalTupleOverlapProjection 𝒰 g₀.1 0 ≫
          (canonicalCoverRelative 𝒰).inclusion (g₀.1 0)
      refine S.topology.superset_covering ?_
        (S.topology.pullback_stable b (Site.AATCoverageFamily.mem_topology 𝒰))
      intro Y f hf
      rw [Presheaf.imageSieve_apply]
      rw [Sieve.pullback_apply] at hf
      rcases hf with ⟨Z, a, c, hc, hfac⟩
      let i : 𝒰.Index := hc.idx
      let chartFactor : Y ⟶ (canonicalCoverRelative 𝒰).chart i :=
        a ≫ eqToHom hc.obj_idx.symm
      let xY : FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 1) Y) :=
        (selectedCechFreePresheaf 𝒰 (n + 1)).map f.op x
      let primitive : (SC.X₁.obj (Opposite.op Y) : Type (u + 1)) := by
        change FreeAbelianGroup (SelectedCechFreeGenerator 𝒰 (n + 2) Y)
        exact selectedCechContraction 𝒰 i chartFactor xY
      refine ⟨primitive, ?_⟩
      apply (AddCommGrpCat.mono_iff_injective
        (SC.iCycles.app (Opposite.op Y))).mp inferInstance
      change (((SC.toCycles ≫ SC.iCycles).app (Opposite.op Y)).hom primitive) =
        (SC.iCycles.app (Opposite.op Y)).hom
          ((SC.cycles.map f.op).hom s)
      rw [SC.toCycles_i]
      rw [NatTrans.naturality_apply SC.iCycles f.op s]
      change (((selectedCechFreeChain 𝒰).d (n + 2) (n + 1)).app
          (Opposite.op Y)).hom primitive = xY
      rw [selectedCechFreeChain_d_eq_selectedCechFreeBoundary]
      change FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 (n + 1))
          primitive = xY
      have hcycleX : (SC.g.app (Opposite.op X)).hom x = 0 := by
        dsimp [x]
        change (((SC.iCycles ≫ SC.g).app (Opposite.op X)).hom s) = 0
        rw [SC.iCycles_g]
        rfl
      have hcycleY' : (SC.g.app (Opposite.op Y)).hom xY = 0 := by
        dsimp [xY]
        change (SC.g.app (Opposite.op Y)).hom
          ((SC.X₂.map f.op).hom x) = 0
        rw [NatTrans.naturality_apply SC.g f.op x, hcycleX, map_zero]
      have hcycleY :
          FreeAbelianGroup.lift (selectedCechFreeBoundaryGenerator 𝒰 n) xY = 0 := by
        change ((selectedCechFreeBoundary 𝒰 n).app (Opposite.op Y)).hom xY = 0
        rw [← selectedCechFreeChain_d_eq_selectedCechFreeBoundary]
        exact hcycleY'
      have hcontract := selectedCechFreeBoundary_contraction 𝒰 n i chartFactor xY
      dsimp [primitive]
      rw [hcycleY, map_zero, add_zero] at hcontract
      exact hcontract

noncomputable def selectedCechFreePresheafHomOfCochain
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (c : SelectedCechCochain 𝒰 F n) : selectedCechFreePresheaf 𝒰 n ⟶ F where
  app X := AddCommGrpCat.ofHom
    (FreeAbelianGroup.lift (fun g => F.map g.2.op (c g.1)))
  naturality X Y f := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro g
    change FreeAbelianGroup.lift (fun g => F.map g.2.op (c g.1))
        (FreeAbelianGroup.map (selectedCechFreeGeneratorMap 𝒰 n f)
          (FreeAbelianGroup.of g)) =
      F.map f
        (FreeAbelianGroup.lift (fun g => F.map g.2.op (c g.1))
          (FreeAbelianGroup.of g))
    rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
    rw [← ConcreteCategory.comp_apply, ← F.map_comp]
    rfl

@[simp] theorem selectedCechFreePresheafHomOfCochain_app_of
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (c : SelectedCechCochain 𝒰 F n) (X : S.categoryᵒᵖ)
    (g : SelectedCechFreeGenerator 𝒰 n X.unop) :
    (selectedCechFreePresheafHomOfCochain 𝒰 F n c).app X
        (FreeAbelianGroup.of g) = F.map g.2.op (c g.1) :=
  FreeAbelianGroup.lift_apply_of _ _

noncomputable def selectedCechFreePresheafHomAddEquiv
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    ((selectedCechFreePresheaf 𝒰 n ⟶ F) : Type (u + 1)) ≃+
      SelectedCechCochain 𝒰 F n := by
  let toFun : (selectedCechFreePresheaf 𝒰 n ⟶ F) →
      SelectedCechCochain 𝒰 F n := fun η σ =>
    η.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap n σ))
      (FreeAbelianGroup.of ⟨σ, 𝟙 _⟩)
  let invFun : SelectedCechCochain 𝒰 F n →
      (selectedCechFreePresheaf 𝒰 n ⟶ F) :=
    selectedCechFreePresheafHomOfCochain 𝒰 F n
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro η
        apply NatTrans.ext
        funext X
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro g
        dsimp [invFun]
        calc
          _ = F.map g.2.op (toFun η g.1) :=
            selectedCechFreePresheafHomOfCochain_app_of 𝒰 F n (toFun η) X g
          _ = η.app X ((selectedCechFreePresheaf 𝒰 n).map g.2.op
              (FreeAbelianGroup.of ⟨g.1, 𝟙 _⟩)) :=
            (NatTrans.naturality_apply η g.2.op
              (FreeAbelianGroup.of ⟨g.1, 𝟙 _⟩)).symm
          _ = η.app X (FreeAbelianGroup.of g) := by
            rw [selectedCechFreePresheaf_map_of]
            congr 3
      right_inv := by
        intro c
        funext σ
        dsimp [invFun, toFun]
        rw [selectedCechFreePresheafHomOfCochain_app_of]
        change F.map (𝟙 _).op (c σ) = c σ
        simpa only using FunctorToTypes.map_id_apply
          (F := F ⋙ forget AddCommGrpCat.{u + 1}) (c σ)
      map_add' := by
        intro η θ
        funext σ
        rfl }

@[simp] theorem selectedCechFreePresheafHomAddEquiv_apply
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (η : selectedCechFreePresheaf 𝒰 n ⟶ F)
    (σ : (canonicalCoverRelative 𝒰).simplex n) :
    selectedCechFreePresheafHomAddEquiv 𝒰 F n η σ =
      η.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap n σ))
        (FreeAbelianGroup.of ⟨σ, 𝟙 _⟩) :=
  rfl

theorem selectedCechFreePresheafHomAddEquiv_precomp_boundary
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (η : selectedCechFreePresheaf 𝒰 n ⟶ F) :
    selectedCechFreePresheafHomAddEquiv 𝒰 F (n + 1)
        (selectedCechFreeBoundary 𝒰 n ≫ η) =
      (((selectedCechComplexFunctor 𝒰).obj F).d n (n + 1)).hom
        (selectedCechFreePresheafHomAddEquiv 𝒰 F n η) := by
  funext σ
  rw [selectedCechComplexFunctor_obj_d_apply]
  rw [selectedCechFreePresheafHomAddEquiv_apply]
  change η.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap (n + 1) σ))
      ((selectedCechFreeBoundary 𝒰 n).app
        (Opposite.op ((canonicalCoverRelative 𝒰).overlap (n + 1) σ))
        (FreeAbelianGroup.of ⟨σ, 𝟙 _⟩)) = _
  rw [selectedCechFreeBoundary_app_of]
  simp_rw [selectedCechFreePresheafHomAddEquiv_apply]
  simp only [selectedCechFreeBoundaryGenerator, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  let τ := (canonicalCoverRelative 𝒰).face n i σ
  let r := (canonicalCoverRelative 𝒰).faceRestriction n i σ
  change ((-1 : ℤ) ^ (i : ℕ)) •
      η.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap (n + 1) σ))
        (FreeAbelianGroup.of (selectedCechFreeFaceGenerator 𝒰 n i ⟨σ, 𝟙 _⟩)) =
    ((-1 : ℤ) ^ (i : ℕ)) •
      F.map r.op
        (η.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap n τ))
          (FreeAbelianGroup.of ⟨τ, 𝟙 _⟩))
  congr 1
  simpa [τ, r, selectedCechFreeFaceGenerator] using
    NatTrans.naturality_apply η r.op
      (FreeAbelianGroup.of ⟨τ, 𝟙 _⟩)

noncomputable def selectedCechFreeSheafChain
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ChainComplex (Sheaf S.topology AddCommGrpCat.{u + 1}) ℕ :=
  ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (selectedCechFreeChain 𝒰)

noncomputable def selectedCechFreeSheafHomAddEquiv
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (I : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (((selectedCechFreeSheafChain 𝒰).X n ⟶ I) : Type (u + 1)) ≃+
      SelectedCechCochain 𝒰 I.val n := by
  change ((((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).obj
    (selectedCechFreePresheaf 𝒰 n)) ⟶ I) : Type (u + 1)) ≃+ _
  exact ((sheafificationAdjunction S.topology
    AddCommGrpCat.{u + 1}).homAddEquiv (selectedCechFreePresheaf 𝒰 n) I).trans
      (selectedCechFreePresheafHomAddEquiv 𝒰 I.val n)

@[simp] theorem selectedCechFreeSheafHomAddEquiv_apply
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (I : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (f : (selectedCechFreeSheafChain 𝒰).X n ⟶ I) :
    selectedCechFreeSheafHomAddEquiv 𝒰 I n f =
      selectedCechFreePresheafHomAddEquiv 𝒰 I.val n
        ((sheafificationAdjunction S.topology
          AddCommGrpCat.{u + 1}).homAddEquiv (selectedCechFreePresheaf 𝒰 n) I f) :=
  rfl

theorem selectedCechFreeSheafHomAddEquiv_precomp_d
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (I : Sheaf S.topology AddCommGrpCat.{u + 1}) (n : ℕ)
    (f : (selectedCechFreeSheafChain 𝒰).X n ⟶ I) :
    selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 1)
        ((selectedCechFreeSheafChain 𝒰).d (n + 1) n ≫ f) =
      (((selectedCechComplexFunctor 𝒰).obj I.val).d n (n + 1)).hom
        (selectedCechFreeSheafHomAddEquiv 𝒰 I n f) := by
  rw [selectedCechFreeSheafHomAddEquiv_apply,
    selectedCechFreeSheafHomAddEquiv_apply]
  have hd : (selectedCechFreeSheafChain 𝒰).d (n + 1) n =
      (presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
        (selectedCechFreeBoundary 𝒰 n) := by
    change (presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
        ((selectedCechFreeChain 𝒰).d (n + 1) n) = _
    rw [selectedCechFreeChain_d_eq_selectedCechFreeBoundary]
  rw [hd]
  have hadj := (sheafificationAdjunction S.topology
    AddCommGrpCat.{u + 1}).homEquiv_naturality_left
      (selectedCechFreeBoundary 𝒰 n) f
  change
    ((sheafificationAdjunction S.topology
      AddCommGrpCat.{u + 1}).homAddEquiv (selectedCechFreePresheaf 𝒰 (n + 1)) I)
        ((presheafToSheaf S.topology AddCommGrpCat.{u + 1}).map
          (selectedCechFreeBoundary 𝒰 n) ≫ f) =
      selectedCechFreeBoundary 𝒰 n ≫
        ((sheafificationAdjunction S.topology
          AddCommGrpCat.{u + 1}).homAddEquiv (selectedCechFreePresheaf 𝒰 n) I) f at hadj
  rw [hadj]
  exact selectedCechFreePresheafHomAddEquiv_precomp_boundary 𝒰 I.val n _

theorem selectedCechFreeSheafChain_exactAt_succ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : ℕ) :
    (selectedCechFreeSheafChain 𝒰).ExactAt (n + 1) := by
  let F := presheafToSheaf S.topology AddCommGrpCat.{u + 1}
  let P := (selectedCechFreeChain 𝒰).sc' (n + 2) (n + 1) n
  have hlocal : Presheaf.IsLocallySurjective S.topology P.toCycles :=
    selectedCechFreeBoundaryToCycles_isLocallySurjective 𝒰 n
  have hsheafLocal : Sheaf.IsLocallySurjective (F.map P.toCycles) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
      S.topology P.toCycles).mpr hlocal
  letI : Sheaf.IsLocallySurjective (F.map P.toCycles) := hsheafLocal
  haveI : Epi (F.map P.toCycles) := inferInstance
  have hmapCycles :
      F.map P.toCycles =
        (P.map F).toCycles ≫ (P.mapCyclesIso F).hom := by
    rw [← cancel_mono (F.map P.iCycles)]
    rw [Category.assoc, P.mapCyclesIso_hom_iCycles,
      (P.map F).toCycles_i]
    rw [← F.map_comp, P.toCycles_i]
    rfl
  haveI : Epi ((P.map F).toCycles ≫ (P.mapCyclesIso F).hom) := by
    rw [← hmapCycles]
    infer_instance
  haveI : Epi (P.map F).toCycles :=
    (epi_comp_iff_of_isIso (P.map F).toCycles (P.mapCyclesIso F).hom).mp
      inferInstance
  have hExact : (P.map F).Exact :=
    (ShortComplex.exact_iff_epi_toCycles (P.map F)).mpr inferInstance
  rw [(selectedCechFreeSheafChain 𝒰).exactAt_iff'
    (n + 2) (n + 1) n (by simp) (by simp)]
  change (P.map F).Exact
  exact hExact

theorem injectiveSheaf_selectedCech_exactAt
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (I : Sheaf S.topology AddCommGrpCat.{u + 1})
    [Injective I]
    (p : ℕ) (hp : 0 < p) :
    ((selectedCechComplexFunctor 𝒰).obj I.val).ExactAt p := by
  rcases p with _ | n
  · omega
  rw [((selectedCechComplexFunctor 𝒰).obj I.val).exactAt_iff'
    n (n + 1) (n + 2) (CochainComplex.prev_nat_succ n) (by simp)]
  rw [ShortComplex.ab_exact_iff_ker_le_range]
  intro c hc
  let T := (selectedCechFreeSheafChain 𝒰).sc' (n + 2) (n + 1) n
  have hT : T.Exact := by
    rw [← (selectedCechFreeSheafChain 𝒰).exactAt_iff'
      (n + 2) (n + 1) n (by simp) (by simp)]
    exact selectedCechFreeSheafChain_exactAt_succ 𝒰 n
  let f : T.X₂ ⟶ I :=
    (selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 1)).symm c
  have hf : T.f ≫ f = 0 := by
    apply (selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 2)).injective
    change selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 2)
        ((selectedCechFreeSheafChain 𝒰).d (n + 2) (n + 1) ≫ f) =
      selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 2) 0
    rw [selectedCechFreeSheafHomAddEquiv_precomp_d, map_zero]
    rw [(selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 1)).apply_symm_apply c]
    change (((selectedCechComplexFunctor 𝒰).obj I.val).d
      (n + 1) (n + 2)).hom c = 0
    exact hc
  let primitive : T.X₃ ⟶ I := hT.descToInjective f hf
  refine ⟨selectedCechFreeSheafHomAddEquiv 𝒰 I n primitive, ?_⟩
  change (((selectedCechComplexFunctor 𝒰).obj I.val).d n (n + 1)).hom
      (selectedCechFreeSheafHomAddEquiv 𝒰 I n primitive) = c
  rw [← selectedCechFreeSheafHomAddEquiv_precomp_d]
  change selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 1)
      (T.g ≫ primitive) = c
  rw [hT.comp_descToInjective]
  exact (selectedCechFreeSheafHomAddEquiv 𝒰 I (n + 1)).apply_symm_apply c

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

noncomputable def selectedCechResolutionTotalProjection
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p n : ℕ) (_h : q + p = n) :
    (selectedCechResolutionTotalComplex 𝒰 Ob).X n ⟶
      ((selectedCechResolutionBicomplex 𝒰 Ob).X q).X p :=
  (selectedCechResolutionBicomplex 𝒰 Ob).totalDesc
    (fun q' p' _ =>
      if hq : q' = q then
        if hp : p' = p then
          ((selectedCechResolutionBicomplex 𝒰 Ob).XXIsoOfEq _ _ _ hq hp).hom
        else 0
      else 0)

theorem selectedCechResolutionTotal_ι_projection_general
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p n : ℕ) (h : q + p = n)
    (q' p' : ℕ) (h' : q' + p' = n) :
    (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
        (ComplexShape.up ℕ) q' p' n h' ≫
      selectedCechResolutionTotalProjection 𝒰 Ob q p n h =
        if hq : q' = q then
          if hp : p' = p then
            ((selectedCechResolutionBicomplex 𝒰 Ob).XXIsoOfEq _ _ _ hq hp).hom
          else 0
        else 0 := by
  rw [selectedCechResolutionTotalProjection]
  exact (selectedCechResolutionBicomplex 𝒰 Ob).ι_totalDesc _ _ _ _

@[simp] theorem selectedCechResolutionTotal_ι_projection_self
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p n : ℕ) (h : q + p = n) :
    (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
        (ComplexShape.up ℕ) q p n h ≫
      selectedCechResolutionTotalProjection 𝒰 Ob q p n h = 𝟙 _ := by
  rw [selectedCechResolutionTotal_ι_projection_general]
  simp

noncomputable def selectedCechResolutionTotalDiagonalProjection
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) (q : Fin (n + 1)) :
    (selectedCechResolutionTotalComplex 𝒰 Ob).X n ⟶
      ((selectedCechResolutionBicomplex 𝒰 Ob).X q).X (n - q) :=
  selectedCechResolutionTotalProjection 𝒰 Ob q (n - q) n (by omega)

theorem selectedCechResolutionTotal_ι_projection
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n q' p' : ℕ) (h : q' + p' = n)
    (q : Fin (n + 1)) :
    (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
        (ComplexShape.up ℕ) q' p' n h ≫
      selectedCechResolutionTotalDiagonalProjection 𝒰 Ob n q =
        if hq : q' = q then
          ((selectedCechResolutionBicomplex 𝒰 Ob).XXIsoOfEq _ _ _ hq (by
            subst hq
            omega)).hom
        else 0 := by
  rw [selectedCechResolutionTotalDiagonalProjection,
    selectedCechResolutionTotal_ι_projection_general]
  by_cases hq : q' = q
  · subst hq
    have hp : p' = n - q := by omega
    simp [hp]
  · simp [hq]

noncomputable def selectedCechResolutionTotalDiagonalInclusion
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) (q : Fin (n + 1)) :
    ((selectedCechResolutionBicomplex 𝒰 Ob).X q).X (n - q) ⟶
      (selectedCechResolutionTotalComplex 𝒰 Ob).X n :=
  (selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
    (ComplexShape.up ℕ) q (n - q) n (by
      change (q : ℕ) + (n - q) = n
      omega)

@[simp] theorem selectedCechResolutionTotal_projection_inclusion
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) (q : Fin (n + 1)) :
    selectedCechResolutionTotalDiagonalInclusion 𝒰 Ob n q ≫
      selectedCechResolutionTotalDiagonalProjection 𝒰 Ob n q = 𝟙 _ := by
  rw [selectedCechResolutionTotalDiagonalInclusion,
    selectedCechResolutionTotal_ι_projection]
  simp

theorem selectedCechResolutionTotal_inclusion_projection_ne
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) (q r : Fin (n + 1)) (hqr : q ≠ r) :
    selectedCechResolutionTotalDiagonalInclusion 𝒰 Ob n q ≫
      selectedCechResolutionTotalDiagonalProjection 𝒰 Ob n r = 0 := by
  have hval : (q : ℕ) ≠ (r : ℕ) := by
    intro h
    exact hqr (Fin.ext h)
  rw [selectedCechResolutionTotalDiagonalInclusion,
    selectedCechResolutionTotal_ι_projection]
  simp [hval]

theorem selectedCechResolutionTotal_decomposition
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ) :
    ∑ q : Fin (n + 1),
        selectedCechResolutionTotalDiagonalProjection 𝒰 Ob n q ≫
          selectedCechResolutionTotalDiagonalInclusion 𝒰 Ob n q =
      𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro q' p' h
  change q' + p' = n at h
  let q : Fin (n + 1) := ⟨q', by omega⟩
  rw [Preadditive.comp_sum]
  rw [Finset.sum_eq_single q]
  · rw [← Category.assoc, selectedCechResolutionTotal_ι_projection]
    simp [q, selectedCechResolutionTotalDiagonalInclusion]
    exact (Category.comp_id _).symm
  · intro r _ hr
    rw [← Category.assoc, selectedCechResolutionTotal_ι_projection]
    have hqr : q' ≠ r := by
      intro eq
      apply hr
      apply Fin.ext
      exact eq.symm
    simp [hqr]
  · simp

theorem selectedCechResolutionTotal_ι_d_projection_resolution
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p : ℕ) :
    ((selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) q p (q + p) (by
            change q + p = q + p
            rfl) ≫
        (selectedCechResolutionTotalComplex 𝒰 Ob).d (q + p) (q + p + 1)) ≫
      selectedCechResolutionTotalProjection 𝒰 Ob (q + 1) p
        (q + p + 1) (by omega) =
      ((selectedCechResolutionBicomplex 𝒰 Ob).d q (q + 1)).f p := by
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    (i₁ := q) (i₁' := q + 1) (by simp) p (q + p + 1) (by
      change q + 1 + p = q + p + 1
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    q (i₂ := p) (i₂' := p + 1) (by simp) (q + p + 1) (by
      change q + (p + 1) = q + p + 1
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  simp

theorem selectedCechResolutionTotal_ι_d_projection_cech
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p : ℕ) :
    ((selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) q p (q + p) (by
            change q + p = q + p
            rfl) ≫
        (selectedCechResolutionTotalComplex 𝒰 Ob).d (q + p) (q + p + 1)) ≫
      selectedCechResolutionTotalProjection 𝒰 Ob q (p + 1)
        (q + p + 1) (by omega) =
      ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
          (ComplexShape.up ℕ) (q, p) •
        ((selectedCechResolutionBicomplex 𝒰 Ob).X q).d p (p + 1) := by
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    (i₁ := q) (i₁' := q + 1) (by simp) p (q + p + 1) (by
      change q + 1 + p = q + p + 1
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    q (i₂ := p) (i₂' := p + 1) (by simp) (q + p + 1) (by
      change q + (p + 1) = q + p + 1
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  simp

theorem selectedCechResolutionTotal_d_projection_succ_succ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p : ℕ) :
    (selectedCechResolutionTotalComplex 𝒰 Ob).d
          (q + p + 1) (q + p + 2) ≫
        selectedCechResolutionTotalProjection 𝒰 Ob (q + 1) (p + 1)
          (q + p + 2) (by omega) =
      selectedCechResolutionTotalProjection 𝒰 Ob q (p + 1)
          (q + p + 1) (by omega) ≫
          ((selectedCechResolutionBicomplex 𝒰 Ob).d q (q + 1)).f (p + 1) +
        selectedCechResolutionTotalProjection 𝒰 Ob (q + 1) p
          (q + p + 1) (by omega) ≫
          (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
              (ComplexShape.up ℕ) (q + 1, p) •
            ((selectedCechResolutionBicomplex 𝒰 Ob).X (q + 1)).d p (p + 1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change a + b = q + p + 1 at h
  simp only [← Category.assoc, Preadditive.comp_add]
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    (i₁ := a) (i₁' := a + 1) (by simp) b (q + p + 2) (by
      change a + 1 + b = q + p + 2
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    a (i₂ := b) (i₂' := b + 1) (by simp) (q + p + 2) (by
      change a + (b + 1) = q + p + 2
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  by_cases haq : a = q
  · have hb : b = p + 1 := by omega
    subst a
    subst b
    simp
  · by_cases haqs : a = q + 1
    · have hb : b = p := by omega
      subst a
      subst b
      simp
    · simp [haq, haqs]

theorem selectedCechResolutionTotal_d_projection_succ_zero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q : ℕ) :
    (selectedCechResolutionTotalComplex 𝒰 Ob).d q (q + 1) ≫
        selectedCechResolutionTotalProjection 𝒰 Ob (q + 1) 0 (q + 1) (by omega) =
      selectedCechResolutionTotalProjection 𝒰 Ob q 0 q (by omega) ≫
        ((selectedCechResolutionBicomplex 𝒰 Ob).d q (q + 1)).f 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change a + b = q at h
  simp only [← Category.assoc]
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    (i₁ := a) (i₁' := a + 1) (by simp) b (q + 1) (by
      change a + 1 + b = q + 1
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    a (i₂ := b) (i₂' := b + 1) (by simp) (q + 1) (by
      change a + (b + 1) = q + 1
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  by_cases haq : a = q
  · have hb : b = 0 := by omega
    subst a
    subst b
    simp
  · simp [haq]

theorem selectedCechResolutionTotal_d_projection_zero_succ
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (p : ℕ) :
    (selectedCechResolutionTotalComplex 𝒰 Ob).d p (p + 1) ≫
        selectedCechResolutionTotalProjection 𝒰 Ob 0 (p + 1) (p + 1) (by omega) =
      selectedCechResolutionTotalProjection 𝒰 Ob 0 p p (by omega) ≫
        (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
            (ComplexShape.up ℕ) (0, p) •
          ((selectedCechResolutionBicomplex 𝒰 Ob).X 0).d p (p + 1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change a + b = p at h
  simp only [← Category.assoc]
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    (i₁ := a) (i₁' := a + 1) (by simp) b (p + 1) (by
      change a + 1 + b = p + 1
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    a (i₂ := b) (i₂' := b + 1) (by simp) (p + 1) (by
      change a + (b + 1) = p + 1
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  by_cases ha0 : a = 0
  · have hb : b = p := by omega
    subst a
    subst b
    simp
  · simp [ha0]

theorem selectedCechResolutionTotal_ι_d_projection_zero
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p r s : ℕ)
    (htotal : r + s = q + p + 1)
    (hres : q + 1 ≠ r ∨ p ≠ s)
    (hcech : q ≠ r ∨ p + 1 ≠ s) :
    ((selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) q p (q + p) (by
            change q + p = q + p
            rfl) ≫
        (selectedCechResolutionTotalComplex 𝒰 Ob).d (q + p) (q + p + 1)) ≫
      selectedCechResolutionTotalProjection 𝒰 Ob r s (q + p + 1) htotal = 0 := by
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    (i₁ := q) (i₁' := q + 1) (by simp) p (q + p + 1) (by
      change q + 1 + p = q + p + 1
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    q (i₂ := p) (i₂' := p + 1) (by simp) (q + p + 1) (by
      change q + (p + 1) = q + p + 1
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  rcases hres with hres | hres <;> rcases hcech with hcech | hcech <;>
    simp [hres, hcech]

theorem selectedCechResolutionTotal_ι_d_projection_resolution_explicit
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p n n' : ℕ)
    (hn : q + p = n) (hn' : q + 1 + p = n') :
    ((selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) q p n hn ≫
        (selectedCechResolutionTotalComplex 𝒰 Ob).d n n') ≫
      selectedCechResolutionTotalProjection 𝒰 Ob (q + 1) p n' hn' =
      ((selectedCechResolutionBicomplex 𝒰 Ob).d q (q + 1)).f p := by
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    (i₁ := q) (i₁' := q + 1) (by simp) p n' hn']
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    q (i₂ := p) (i₂' := p + 1) (by simp) n' (by
      change q + (p + 1) = n'
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  simp

theorem selectedCechResolutionTotal_ι_d_projection_zero_explicit
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (q p n n' r s : ℕ)
    (hn : q + p = n) (hn' : q + p + 1 = n') (htarget : r + s = n')
    (hres : q + 1 ≠ r ∨ p ≠ s)
    (hcech : q ≠ r ∨ p + 1 ≠ s) :
    ((selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
          (ComplexShape.up ℕ) q p n hn ≫
        (selectedCechResolutionTotalComplex 𝒰 Ob).d n n') ≫
      selectedCechResolutionTotalProjection 𝒰 Ob r s n' htarget = 0 := by
  rw [selectedCechResolutionTotalComplex_ι_d,
    Preadditive.add_comp]
  rw [HomologicalComplex₂.d₁_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    (i₁ := q) (i₁' := q + 1) (by simp) p n' (by
      change q + 1 + p = n'
      omega)]
  rw [HomologicalComplex₂.d₂_eq
    (selectedCechResolutionBicomplex 𝒰 Ob) (ComplexShape.up ℕ)
    q (i₂ := p) (i₂' := p + 1) (by simp) n' (by
      change q + (p + 1) = n'
      omega)]
  rw [Linear.units_smul_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    selectedCechResolutionTotal_ι_projection_general,
    selectedCechResolutionTotal_ι_projection_general]
  rcases hres with hres | hres <;> rcases hcech with hcech | hcech <;>
    simp [hres, hcech]

def SelectedCechResolutionTotalSupportedAtMost
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n m : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 Ob).X n) : Prop :=
  ∀ q p : ℕ, ∀ h : q + p = n, m < q →
    (selectedCechResolutionTotalProjection 𝒰 Ob q p n h).hom x = 0

theorem selectedCechResolutionTotal_supportedAtMost_top
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 Ob).X n) :
    SelectedCechResolutionTotalSupportedAtMost 𝒰 Ob n n x := by
  intro q p hqp hq
  omega

theorem IsLerayFor.selectedCechResolutionTotal_eliminateColumn
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    {𝒰 : Site.AATCoverageFamily S.requirements S.overlap base}
    {Ob : ObstructionSheaf S}
    (hLeray : IsLerayFor 𝒰 Ob)
    (m p : ℕ)
    (x : (selectedCechResolutionTotalComplex 𝒰 Ob).X (m + 1 + p))
    (hcycle : ((selectedCechResolutionTotalComplex 𝒰 Ob).d
      (m + 1 + p) (m + 1 + p + 1)).hom x = 0)
    (hsupp : SelectedCechResolutionTotalSupportedAtMost
      𝒰 Ob (m + 1 + p) (m + 1) x) :
    ∃ y : (selectedCechResolutionTotalComplex 𝒰 Ob).X (m + p),
      let x' := x -
        ((selectedCechResolutionTotalComplex 𝒰 Ob).d
          (m + p) (m + 1 + p)).hom y
      SelectedCechResolutionTotalSupportedAtMost 𝒰 Ob (m + 1 + p) m x' ∧
        ((selectedCechResolutionTotalComplex 𝒰 Ob).d
          (m + 1 + p) (m + 1 + p + 1)).hom x' = 0 := by
  let xcomp : ((selectedCechResolutionBicomplex 𝒰 Ob).X (m + 1)).X p :=
    (selectedCechResolutionTotalProjection 𝒰 Ob (m + 1) p
      (m + 1 + p) (by omega)).hom x
  have hxcycle :
      (((selectedCechResolutionBicomplex 𝒰 Ob).d (m + 1) (m + 2)).f p).hom
        xcomp = 0 := by
    rcases p with _ | p
    · calc
        _ = (selectedCechResolutionTotalProjection 𝒰 Ob (m + 1) 0
              (m + 1) (by omega) ≫
            ((selectedCechResolutionBicomplex 𝒰 Ob).d (m + 1) (m + 2)).f 0).hom x := by
              rfl
        _ = (((selectedCechResolutionTotalComplex 𝒰 Ob).d (m + 1) (m + 2) ≫
              selectedCechResolutionTotalProjection 𝒰 Ob (m + 2) 0
                (m + 2) (by omega)).hom x) := by
              rw [selectedCechResolutionTotal_d_projection_succ_zero]
        _ = 0 := by
              change (selectedCechResolutionTotalProjection 𝒰 Ob (m + 2) 0
                (m + 2) (by omega)).hom
                  (((selectedCechResolutionTotalComplex 𝒰 Ob).d
                    (m + 1) (m + 2)).hom x) = 0
              rw [hcycle, map_zero]
    · have hrzero :
          (selectedCechResolutionTotalProjection 𝒰 Ob (m + 2) p
            (m + 1 + (p + 1)) (by omega)).hom x = 0 :=
        hsupp (m + 2) p (by omega) (by omega)
      have hleft :
          (((selectedCechResolutionTotalComplex 𝒰 Ob).d
              (m + 1 + (p + 1)) (m + 1 + (p + 1) + 1) ≫
            selectedCechResolutionTotalProjection 𝒰 Ob (m + 2) (p + 1)
              (m + 1 + (p + 1) + 1) (by omega)).hom x) = 0 := by
        change (selectedCechResolutionTotalProjection 𝒰 Ob (m + 2) (p + 1)
          (m + 1 + (p + 1) + 1) (by omega)).hom
            (((selectedCechResolutionTotalComplex 𝒰 Ob).d
              (m + 1 + (p + 1)) (m + 1 + (p + 1) + 1)).hom x) = 0
        rw [hcycle, map_zero]
      have hformula := ConcreteCategory.congr_hom
        (selectedCechResolutionTotal_d_projection_succ_succ 𝒰 Ob (m + 1) p) x
      have hformula' :
          (((selectedCechResolutionTotalComplex 𝒰 Ob).d
              (m + 1 + (p + 1)) (m + 1 + (p + 1) + 1) ≫
            selectedCechResolutionTotalProjection 𝒰 Ob (m + 2) (p + 1)
              (m + 1 + (p + 1) + 1) (by omega)).hom x) =
            (((selectedCechResolutionBicomplex 𝒰 Ob).d (m + 1) (m + 2)).f
                (p + 1)).hom xcomp +
              (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
                  (ComplexShape.up ℕ) (m + 2, p) •
                ((selectedCechResolutionBicomplex 𝒰 Ob).X (m + 2)).d
                  p (p + 1)).hom
                ((selectedCechResolutionTotalProjection 𝒰 Ob (m + 2) p
                  (m + 1 + (p + 1)) (by omega)).hom x) := by
        simpa only [Nat.add_assoc] using hformula
      have hsum :
          (((selectedCechResolutionBicomplex 𝒰 Ob).d (m + 1) (m + 2)).f
              (p + 1)).hom xcomp +
            (ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
                (ComplexShape.up ℕ) (m + 2, p) •
              ((selectedCechResolutionBicomplex 𝒰 Ob).X (m + 2)).d
                p (p + 1)).hom
              ((selectedCechResolutionTotalProjection 𝒰 Ob (m + 2) p
                (m + 1 + (p + 1)) (by omega)).hom x) = 0 := by
        calc
          _ = (((selectedCechResolutionTotalComplex 𝒰 Ob).d
                (m + 1 + (p + 1)) (m + 1 + (p + 1) + 1) ≫
              selectedCechResolutionTotalProjection 𝒰 Ob (m + 2) (p + 1)
                (m + 1 + (p + 1) + 1) (by omega)).hom x) := hformula'.symm
          _ = 0 := hleft
      rw [hrzero, map_zero, add_zero] at hsum
      exact hsum
  let C := selectedCechResolutionColumn 𝒰 Ob p
  have hexact : C.ExactAt (m + 1) :=
    hLeray.selectedCechResolutionColumn_exactAt (m + 1) (by omega) p
  rw [C.exactAt_iff' m (m + 1) (m + 2) (by simp) (by simp)] at hexact
  rw [ShortComplex.ab_exact_iff_ker_le_range] at hexact
  have hxmem : xcomp ∈ ((C.d (m + 1) (m + 2)).hom).ker := by
    change ((C.d (m + 1) (m + 2)).hom xcomp = 0)
    exact hxcycle
  rcases hexact hxmem with ⟨ycomp, hycomp⟩
  change (C.d m (m + 1)).hom ycomp = xcomp at hycomp
  let y : (selectedCechResolutionTotalComplex 𝒰 Ob).X (m + p) :=
    ((selectedCechResolutionBicomplex 𝒰 Ob).ιTotal
      (ComplexShape.up ℕ) m p (m + p) (by
        change m + p = m + p
        rfl)).hom ycomp
  refine ⟨y, ?_, ?_⟩
  · intro r s hrs hmr
    change (selectedCechResolutionTotalProjection 𝒰 Ob r s
      (m + 1 + p) hrs).hom
      (x - ((selectedCechResolutionTotalComplex 𝒰 Ob).d
        (m + p) (m + 1 + p)).hom y) = 0
    rw [map_sub]
    by_cases hr : r = m + 1
    · subst r
      have hs : s = p := by omega
      subst s
      have hboundary := ConcreteCategory.congr_hom
        (selectedCechResolutionTotal_ι_d_projection_resolution_explicit
          𝒰 Ob m p (m + p) (m + 1 + p) (by rfl) (by rfl)) ycomp
      have hboundary' :
          (selectedCechResolutionTotalProjection 𝒰 Ob (m + 1) p
            (m + 1 + p) (by omega)).hom
            (((selectedCechResolutionTotalComplex 𝒰 Ob).d
              (m + p) (m + 1 + p)).hom y) =
            (C.d m (m + 1)).hom ycomp := by
        simpa only [y, Nat.add_assoc] using hboundary
      change xcomp -
        (selectedCechResolutionTotalProjection 𝒰 Ob (m + 1) p
          (m + 1 + p) (by omega)).hom
          (((selectedCechResolutionTotalComplex 𝒰 Ob).d
            (m + p) (m + 1 + p)).hom y) = 0
      rw [hboundary', hycomp]
      simp
    · have hxzero := hsupp r s hrs (by omega)
      rw [hxzero, zero_sub]
      have hzero := ConcreteCategory.congr_hom
        (selectedCechResolutionTotal_ι_d_projection_zero_explicit
          𝒰 Ob m p (m + p) (m + 1 + p) r s
          (by rfl) (by omega) hrs
          (Or.inl (by omega)) (Or.inl (by omega))) ycomp
      have hzero' :
          (selectedCechResolutionTotalProjection 𝒰 Ob r s
            (m + 1 + p) hrs).hom
            (((selectedCechResolutionTotalComplex 𝒰 Ob).d
              (m + p) (m + 1 + p)).hom y) = 0 := by
        simpa only [y, Nat.add_assoc, map_zero] using hzero
      change -(selectedCechResolutionTotalProjection 𝒰 Ob r s
        (m + 1 + p) hrs).hom
          (((selectedCechResolutionTotalComplex 𝒰 Ob).d
            (m + p) (m + 1 + p)).hom y) = 0
      rw [hzero']
      simp
  · rw [map_sub, hcycle]
    change 0 -
      (((selectedCechResolutionTotalComplex 𝒰 Ob).d (m + p) (m + 1 + p) ≫
        (selectedCechResolutionTotalComplex 𝒰 Ob).d
          (m + 1 + p) (m + 1 + p + 1)).hom y) = 0
    rw [HomologicalComplex.d_comp_d]
    simp

end AAT.AG.Cohomology
