import Formal.AG.ReadingFunctoriality.Coverage
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
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
-/

namespace AAT.AG.Cohomology.CoverRelativeCechComplex

universe u

open CategoryTheory

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 𝒱 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}

/-- The Mathlib cochain complex defined by the selected Čech differential. -/
noncomputable def toCochainComplex
    (K : CoverRelativeCechComplex 𝒰 Ob) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of
    (fun n ↦ AddCommGrpCat.of (K.AdditiveCochain n))
    (fun n ↦ AddCommGrpCat.ofHom (K.d n))
    (fun n ↦ by
      ext c
      exact K.differential_comp n c)

/-- The degree-`n` object is the selected additive Čech cochain group. -/
@[simp] theorem toCochainComplex_X
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    (K.toCochainComplex.X n : Type u) = K.AdditiveCochain n :=
  rfl

/-- The Mathlib differential is the selected Čech differential. -/
@[simp] theorem toCochainComplex_d
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    letI := K.cochainAddCommGroup n
    letI := K.cochainAddCommGroup (n + 1)
    K.toCochainComplex.d n (n + 1) = AddCommGrpCat.ofHom (K.d n) := by
  letI := K.cochainAddCommGroup n
  letI := K.cochainAddCommGroup (n + 1)
  exact CochainComplex.of_d _ _ _ n

namespace Hom

/-- A selected Čech cochain map as a Mathlib cochain-complex morphism. -/
noncomputable def toCochainMap
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) : K.toCochainComplex ⟶ L.toCochainComplex :=
  CochainComplex.ofHom _ _ _ _ _ _
    (fun n ↦ AddCommGrpCat.ofHom (f.app n))
    (fun n ↦ by
      ext c
      exact (f.commutes n c).symm)

/-- The degreewise component is the original additive map. -/
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

/-- Additive Čech cohomology is the homology of the actual cochain complex. -/
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

/-- A selected Čech cocycle as a cycle in the Mathlib cochain complex. -/
noncomputable def cocycleToCycles
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : ℕ) :
    AddCommGrpCat.of (K.CechCocycleSubgroup n) ⟶
      K.toCochainComplex.cycles n :=
  K.toCochainComplex.liftCycles (K.cocycleInclusion n) (n + 1)
    (by simp)
    (K.cocycleInclusion_comp_d n)

/-- The actual cycle underlying the canonical lift is the original cocycle. -/
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

/-- The comparison sends an additive Čech class to its actual homology class. -/
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

/-- The quotient-level Čech map agrees with the Mathlib homology map. -/
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
