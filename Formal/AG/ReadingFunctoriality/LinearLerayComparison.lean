import Formal.AG.ReadingFunctoriality.Coefficient
import Formal.AG.ReadingFunctoriality.LargeLerayComparison

/-!
# Linear Leray comparison and actual sheaf-cohomology base change

This module transports the generic large additive-sheaf Leray comparison to
the canonical linear Čech complex.  It equips actual terminal `Sheaf.H` with
the transported coefficient-module structure and conjugates the canonical
Čech base-change map into actual sheaf cohomology.
-/

noncomputable section

namespace AAT.AG.Cohomology

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

namespace LinearCoefficientSheaf

/-- The underlying additive canonical linear Čech complex is the generic selected Čech complex. -/
private noncomputable def linearSelectedCechComplexIso
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (Ob.canonicalLinearCech 𝒰).complex ≅
      (selectedCechComplexFunctor 𝒰).obj Ob.toAddCommGrpSheaf.val := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro i j hij
  obtain rfl := hij
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  funext σ
  simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
    Functor.mapHomologicalComplex_obj_d]
  rw [canonicalLinearCech_d]
  simp only [canonicalLinearCech, Iso.refl_hom, Category.id_comp]
  change
    (((selectedCechComplexFunctor 𝒰).obj
      Ob.toAddCommGrpSheaf.val).d i (i + 1)).hom c σ =
      (linearCechDifferential Ob 𝒰 i).hom c σ
  rw [selectedCechComplexFunctor_obj_d_apply]
  symm
  simp only [linearCechDifferential,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.coe_sum,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  rfl

/-- Canonical additive identification of linear Čech homology with selected additive Čech homology. -/
private noncomputable def linearCechHomologyAddEquiv
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    ((Ob.canonicalLinearCech 𝒰).complex.homology n : Type (u + 1)) ≃+
      (((selectedCechComplexFunctor 𝒰).obj
          Ob.toAddCommGrpSheaf.val).homology n : Type (u + 1)) := by
  let F := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  exact
    ((Ob.canonicalLinearCech 𝒰).complex.sc n).mapHomologyIso F |>.symm
      |>.addCommGroupIsoToAddEquiv |>.trans
        ((HomologicalComplex.homologyMapIso
          (linearSelectedCechComplexIso Ob 𝒰) n).addCommGroupIsoToAddEquiv)

/-- The generic Leray condition specialized to a linear coefficient sheaf. -/
def IsLinearLerayFor
    {R : Type u} [CommRing R]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})] :
    Prop :=
  ∀ q, 0 < q →
    ∀ p, ∀ σ : (canonicalCoverRelative 𝒰).simplex p,
      Subsingleton
        ((Ob.toAddCommGrpSheaf).H' q
          ((canonicalCoverRelative 𝒰).overlap p σ))

/-- Canonical additive comparison from linear Čech homology to actual terminal sheaf cohomology. -/
private noncomputable def linearCechToTerminalHAddEquiv
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (hbase : IsTerminal base)
    (hLeray : IsLinearLerayFor 𝒰 Ob)
    (n : Nat) :
    ((Ob.canonicalLinearCech 𝒰).complex.homology n : Type (u + 1)) ≃+
      ((Ob.toAddCommGrpSheaf).H n : Type (u + 2)) :=
  (linearCechHomologyAddEquiv Ob 𝒰 n).trans
    ((selectedCechToSheafHAtBaseEquivForSheaf
      𝒰 Ob.toAddCommGrpSheaf hLeray n).trans
        (terminalHComparison Ob.toAddCommGrpSheaf base hbase n))

/-- Actual terminal sheaf cohomology with its coefficient-module structure transported from Čech homology. -/
noncomputable def terminalLerayHModule
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (hbase : IsTerminal base)
    (hLeray : IsLinearLerayFor 𝒰 Ob)
    (n : Nat) :
    ModuleCat.{u + 2} R :=
  let e := linearCechToTerminalHAddEquiv Ob 𝒰 hbase hLeray n
  letI : Module R ((Ob.toAddCommGrpSheaf).H n : Type (u + 2)) :=
    e.symm.module R
  ModuleCat.of R ((Ob.toAddCommGrpSheaf).H n : Type (u + 2))

/-- The transported module has actual terminal `Sheaf.H` as its carrier. -/
@[simp] theorem terminalLerayHModule_carrier
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (hbase : IsTerminal base)
    (hLeray : IsLinearLerayFor 𝒰 Ob)
    (n : Nat) :
    (Ob.terminalLerayHModule 𝒰 hbase hLeray n : Type (u + 2)) =
      (Ob.toAddCommGrpSheaf).H n :=
  rfl

/-- Canonical linear Leray comparison from Čech homology to actual terminal sheaf cohomology. -/
noncomputable def cechToSheafHLinearIso
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (hbase : IsTerminal base)
    (hLeray : IsLinearLerayFor 𝒰 Ob)
    (n : Nat) :
    (Ob.canonicalLinearCech 𝒰).complex.homology n ≃ₗ[R]
      Ob.terminalLerayHModule 𝒰 hbase hLeray n := by
  let e := linearCechToTerminalHAddEquiv Ob 𝒰 hbase hLeray n
  letI : Module R ((Ob.toAddCommGrpSheaf).H n : Type (u + 2)) :=
    e.symm.module R
  change (Ob.canonicalLinearCech 𝒰).complex.homology n ≃ₗ[R]
    ((Ob.toAddCommGrpSheaf).H n : Type (u + 2))
  exact e.toLinearEquiv (by
    intro r x
    change e (r • x) = e (r • e.symm (e x))
    rw [e.symm_apply_apply])

/-- Canonical actual-`Sheaf.H` flat base-change map obtained by conjugating the Čech Hn map. -/
noncomputable def sheafHFlatBaseChangeMap
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLinearLerayFor 𝒰 Ob)
    (htarget : IsLinearLerayFor 𝒰 (Ob.baseChange f))
    (n : Nat) :
    Derived.Intersection.moduleScalarExtension.{u, u + 2} f
        (Ob.terminalLerayHModule 𝒰 hbase hsource n) ⟶
      (Ob.baseChange f).terminalLerayHModule 𝒰 hbase htarget n := by
  letI : Algebra R R' := f.hom.toAlgebra
  let eSource := Ob.cechToSheafHLinearIso 𝒰 hbase hsource n
  let eTargetAdd := linearCechToTerminalHAddEquiv
    (Ob.baseChange f) 𝒰 hbase htarget n
  letI : Module R'
      (((Ob.baseChange f).toAddCommGrpSheaf).H n : Type (u + 2)) :=
    eTargetAdd.symm.module R'
  let eTarget := (Ob.baseChange f).cechToSheafHLinearIso
    𝒰 hbase htarget n
  exact ModuleCat.ofHom
    (eTarget.toLinearMap.comp
      ((canonicalCechHnBaseChangeMap Ob f 𝒰 n).hom.comp
        (LinearMap.baseChange R' eSource.symm.toLinearMap)))

/-- Pure-tensor formula for the canonical actual-`Sheaf.H` base-change map. -/
theorem sheafHFlatBaseChangeMap_formula
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLinearLerayFor 𝒰 Ob)
    (htarget : IsLinearLerayFor 𝒰 (Ob.baseChange f))
    (n : Nat)
    (r' : R')
    (x : Ob.terminalLerayHModule 𝒰 hbase hsource n) :
    sheafHFlatBaseChangeMap Ob f 𝒰 hbase hsource htarget n
        (r' ⊗ₜ[R, f.hom] x) =
      (Ob.baseChange f).cechToSheafHLinearIso
        𝒰 hbase htarget n
        (canonicalCechHnBaseChangeMap Ob f 𝒰 n
          (r' ⊗ₜ[R, f.hom]
            (Ob.cechToSheafHLinearIso 𝒰 hbase hsource n).symm x)) := by
  letI : Algebra R R' := f.hom.toAlgebra
  let eSource := Ob.cechToSheafHLinearIso 𝒰 hbase hsource n
  let eTargetAdd := linearCechToTerminalHAddEquiv
    (Ob.baseChange f) 𝒰 hbase htarget n
  letI : Module R'
      (((Ob.baseChange f).toAddCommGrpSheaf).H n : Type (u + 2)) :=
    eTargetAdd.symm.module R'
  let eTarget := (Ob.baseChange f).cechToSheafHLinearIso
    𝒰 hbase htarget n
  change
    eTarget
        (canonicalCechHnBaseChangeMap Ob f 𝒰 n
          ((LinearMap.baseChange R'
            eSource.symm.toLinearMap)
              (r' ⊗ₜ[R, f.hom] x))) = _
  rw [LinearMap.baseChange_tmul]
  change
    linearCechToTerminalHAddEquiv (Ob.baseChange f) 𝒰 hbase htarget n
        (canonicalCechHnBaseChangeMap Ob f 𝒰 n
          (r' ⊗ₜ[R, f.hom] eSource.symm x)) =
      linearCechToTerminalHAddEquiv (Ob.baseChange f) 𝒰 hbase htarget n
        (canonicalCechHnBaseChangeMap Ob f 𝒰 n
          (r' ⊗ₜ[R, f.hom] eSource.symm x))
  rfl

/-- Class formula for the canonical actual-`Sheaf.H` base-change map. -/
theorem sheafHFlatBaseChangeMap_on_class
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLinearLerayFor 𝒰 Ob)
    (htarget : IsLinearLerayFor 𝒰 (Ob.baseChange f))
    (n : Nat)
    (c : (Ob.canonicalLinearCech 𝒰).complex.cycles n) :
    sheafHFlatBaseChangeMap Ob f 𝒰 hbase hsource htarget n
        (Derived.Intersection.moduleScalarExtensionUnit.{u, u + 2} f
          (Ob.terminalLerayHModule 𝒰 hbase hsource n)
          (Ob.cechToSheafHLinearIso 𝒰 hbase hsource n
            ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n c))) =
      (Ob.baseChange f).cechToSheafHLinearIso 𝒰 hbase htarget n
        (((Ob.baseChange f).canonicalLinearCech 𝒰).complex.homologyπ n
          (canonicalCocycleBaseChange Ob f 𝒰 n c)) := by
  rw [Derived.Intersection.moduleScalarExtensionUnit_apply]
  rw [sheafHFlatBaseChangeMap_formula]
  rw [LinearEquiv.symm_apply_apply]
  rw [canonicalCocycleBaseChange_class]
  rfl

/-- Coefficient compatibility makes the canonical actual-`Sheaf.H` base-change map an isomorphism. -/
theorem sheafHFlatBaseChangeMap_isIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hcompat : CechCoefficientBaseChangeCompatible Ob f 𝒰)
    (hsource : IsLinearLerayFor 𝒰 Ob)
    (htarget : IsLinearLerayFor 𝒰 (Ob.baseChange f))
    (n : Nat) :
    IsIso (sheafHFlatBaseChangeMap Ob f 𝒰 hbase hsource htarget n) := by
  letI : IsIso (canonicalCechHnBaseChangeMap Ob f 𝒰 n) :=
    canonicalCechHnBaseChangeMap_isIso Ob f 𝒰 hcompat n
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  letI : Algebra R R' := f.hom.toAlgebra
  let eSource := Ob.cechToSheafHLinearIso 𝒰 hbase hsource n
  let eTargetAdd := linearCechToTerminalHAddEquiv
    (Ob.baseChange f) 𝒰 hbase htarget n
  letI : Module R'
      (((Ob.baseChange f).toAddCommGrpSheaf).H n : Type (u + 2)) :=
    eTargetAdd.symm.module R'
  let eTarget := (Ob.baseChange f).cechToSheafHLinearIso
    𝒰 hbase htarget n
  simpa only [sheafHFlatBaseChangeMap, Function.comp_apply] using
    eTarget.bijective.comp
      (((ConcreteCategory.isIso_iff_bijective
        (canonicalCechHnBaseChangeMap Ob f 𝒰 n)).mp inferInstance).comp
          (LinearEquiv.baseChange R R'
            (Ob.terminalLerayHModule 𝒰 hbase hsource n)
            ((Ob.canonicalLinearCech 𝒰).complex.homology n)
            eSource.symm).bijective)

/-- Canonical actual-`Sheaf.H` flat base-change isomorphism. -/
noncomputable def sheafHFlatBaseChangeIso
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hcompat : CechCoefficientBaseChangeCompatible Ob f 𝒰)
    (hsource : IsLinearLerayFor 𝒰 Ob)
    (htarget : IsLinearLerayFor 𝒰 (Ob.baseChange f))
    (n : Nat) :
    Derived.Intersection.moduleScalarExtension.{u, u + 2} f
        (Ob.terminalLerayHModule 𝒰 hbase hsource n) ≅
      (Ob.baseChange f).terminalLerayHModule 𝒰 hbase htarget n := by
  letI : IsIso (sheafHFlatBaseChangeMap Ob f 𝒰 hbase hsource htarget n) :=
    sheafHFlatBaseChangeMap_isIso Ob f 𝒰 hbase hcompat hsource htarget n
  exact asIso (sheafHFlatBaseChangeMap Ob f 𝒰 hbase hsource htarget n)

/-- The canonical flat base-change isomorphism has the canonical base-change map as its hom. -/
theorem sheafHFlatBaseChangeIso_hom
    {R R' : Type u} [CommRing R] [CommRing R']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hcompat : CechCoefficientBaseChangeCompatible Ob f 𝒰)
    (hsource : IsLinearLerayFor 𝒰 Ob)
    (htarget : IsLinearLerayFor 𝒰 (Ob.baseChange f))
    (n : Nat) :
    (sheafHFlatBaseChangeIso Ob f 𝒰 hbase hcompat hsource htarget n).hom =
      sheafHFlatBaseChangeMap Ob f 𝒰 hbase hsource htarget n :=
  rfl

end LinearCoefficientSheaf

end AAT.AG.Cohomology
