import Formal.AG.ReadingFunctoriality.Coverage
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

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

end AAT.AG.Cohomology
