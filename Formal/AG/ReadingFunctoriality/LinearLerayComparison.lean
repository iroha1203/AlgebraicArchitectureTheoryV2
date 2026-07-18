import Formal.AG.ReadingFunctoriality.Coefficient
import Formal.AG.ReadingFunctoriality.LargeLerayComparison

/-!
# Linear Leray comparison and actual sheaf-cohomology base change

This module transports the generic large additive-sheaf Leray comparison to
the canonical linear Čech complex.  It equips actual terminal `Sheaf.H` with
the transported coefficient-module structure and conjugates the canonical
Čech base-change map into actual sheaf cohomology.

## Implementation notes

This is the R8d / AC37 bridge from the module-valued Čech theory to actual
terminal `Sheaf.H`.  The underlying additive linear Čech complex is identified
with the generic selected Čech complex by identity component isomorphisms;
differential compatibility is proved from the two canonical alternating
restriction formulas.  The resulting cross-universe additive equivalence from
Čech homology in `Type (u + 1)` to actual `Sheaf.H` in `Type (u + 2)` transports
the `R`-module structure onto the actual carrier.

The base-change map is composed directly as `LinearMap.baseChange` of the
source comparison inverse, the canonical Čech Hn base-change map, and the
target comparison.  The target module instance is reconstructed from the same
additive equivalence so that this cross-universe composition uses exactly the
transported structure exposed by `terminalLerayHModule`.

Caller-supplied H-level module structures, comparison maps, or isomorphisms are
not used because they would add the conclusion-level data that R8d constructs.
An independent module-valued sheafification route is also not used: it would
require another comparison with actual `Sheaf.H` and would not by itself fix
the carrier required by AC37.  A single-category morphism composition is not
used because the Čech and actual-cohomology carriers live in different
universes; the direct linear-map composition preserves both carrier levels.
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

/-- A presheaf isomorphism acts componentwise on canonical linear Čech cochains. -/
private noncomputable def linearCechCochainIsoOfPresheafIso
    {R : Type u} [CommRing R]
    (Ob Ob' : LinearCoefficientSheaf R S)
    (e : Ob.modulePresheaf ≅ Ob'.modulePresheaf)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    (Ob.canonicalLinearCech 𝒰).complex.X n ≅
      (Ob'.canonicalLinearCech 𝒰).complex.X n := by
  change ModuleCat.of R
      (∀ σ : (canonicalCoverRelative 𝒰).simplex n,
        Ob.modulePresheaf.obj
          (Opposite.op ((canonicalCoverRelative 𝒰).overlap n σ))) ≅
    ModuleCat.of R
      (∀ σ : (canonicalCoverRelative 𝒰).simplex n,
        Ob'.modulePresheaf.obj
          (Opposite.op ((canonicalCoverRelative 𝒰).overlap n σ)))
  exact (LinearEquiv.piCongrRight fun σ =>
    (e.app (Opposite.op
      ((canonicalCoverRelative 𝒰).overlap n σ))).toLinearEquiv).toModuleIso

/-- A coefficient-presheaf isomorphism induces the canonical linear Čech complex isomorphism. -/
private noncomputable def linearCechComplexIsoOfPresheafIso
    {R : Type u} [CommRing R]
    (Ob Ob' : LinearCoefficientSheaf R S)
    (e : Ob.modulePresheaf ≅ Ob'.modulePresheaf)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    (Ob.canonicalLinearCech 𝒰).complex ≅
      (Ob'.canonicalLinearCech 𝒰).complex := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => linearCechCochainIsoOfPresheafIso Ob Ob' e 𝒰 n) ?_
  intro i j hij
  obtain rfl := hij
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext σ
  rw [canonicalLinearCech_d, canonicalLinearCech_d]
  simp only [canonicalLinearCech, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp]
  change
    (linearCechDifferential Ob' 𝒰 i).hom
        (fun τ => e.hom.app (Opposite.op
          ((canonicalCoverRelative 𝒰).overlap i τ)) (c τ)) σ =
      e.hom.app (Opposite.op
          ((canonicalCoverRelative 𝒰).overlap (i + 1) σ))
        ((linearCechDifferential Ob 𝒰 i).hom c σ)
  simp only [linearCechDifferential,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.coe_sum,
    Finset.sum_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  change
    (-1 : ℤ) ^ (k : ℕ) •
        Ob'.modulePresheaf.map
          (canonicalTupleOverlapMap 𝒰 (SimplexCategory.δ k) σ).op
          (e.hom.app (Opposite.op ((canonicalCoverRelative 𝒰).overlap i
              (fun l => σ ((SimplexCategory.δ k).toOrderHom l))))
            (c (fun l => σ ((SimplexCategory.δ k).toOrderHom l)))) =
      e.hom.app (Opposite.op
          ((canonicalCoverRelative 𝒰).overlap (i + 1) σ))
        ((-1 : ℤ) ^ (k : ℕ) •
          Ob.modulePresheaf.map
            (canonicalTupleOverlapMap 𝒰 (SimplexCategory.δ k) σ).op
            (c (fun l => σ ((SimplexCategory.δ k).toOrderHom l))))
  have hnat := e.hom.naturality
    (canonicalTupleOverlapMap 𝒰 (SimplexCategory.δ k) σ).op
  simpa only [map_zsmul] using congrArg
    (fun x => (-1 : ℤ) ^ (k : ℕ) • x)
    (ConcreteCategory.congr_hom hnat
      (c (fun i => σ ((SimplexCategory.δ k).toOrderHom i)))).symm

/-- The homology isomorphism induced by a coefficient-presheaf isomorphism. -/
private noncomputable def linearCechHnIsoOfPresheafIso
    {R : Type u} [CommRing R]
    (Ob Ob' : LinearCoefficientSheaf R S)
    (e : Ob.modulePresheaf ≅ Ob'.modulePresheaf)
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    (Ob.canonicalLinearCech 𝒰).complex.homology n ≅
      (Ob'.canonicalLinearCech 𝒰).complex.homology n :=
  HomologicalComplex.homologyMapIso
    (linearCechComplexIsoOfPresheafIso Ob Ob' e 𝒰) n

/-- On canonical cocycles, identity coefficient change followed by the
coefficient-presheaf identity isomorphism is the identity. -/
private theorem canonicalCocycleBaseChange_id
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (c : (Ob.canonicalLinearCech 𝒰).complex.cycles n) :
    HomologicalComplex.cyclesMap
        (linearCechComplexIsoOfPresheafIso
          (Ob.baseChange (FlatCoefficientChange.refl R)) Ob
          Ob.baseChangeIdIso 𝒰).hom n
        (canonicalCocycleBaseChange Ob (FlatCoefficientChange.refl R) 𝒰 n c) =
      c := by
  let eComplex := linearCechComplexIsoOfPresheafIso
    (Ob.baseChange (FlatCoefficientChange.refl R)) Ob
    Ob.baseChangeIdIso 𝒰
  let c' := canonicalCocycleBaseChange Ob
    (FlatCoefficientChange.refl R) 𝒰 n c
  apply (ModuleCat.mono_iff_injective
    ((Ob.canonicalLinearCech 𝒰).complex.iCycles n)).mp inferInstance
  funext σ
  have hmap := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i eComplex.hom n) c'
  have hmap' :
      ((Ob.canonicalLinearCech 𝒰).complex.iCycles n).hom
          (HomologicalComplex.cyclesMap eComplex.hom n c') σ =
        (eComplex.hom.f n).hom
          (((Ob.baseChange (FlatCoefficientChange.refl R)).canonicalLinearCech
            𝒰).complex.iCycles n c') σ := by
    simpa only [ConcreteCategory.comp_apply] using congrArg (fun z => z σ) hmap
  rw [hmap']
  change
    Ob.baseChangeIdIso.hom.app (Opposite.op
        ((canonicalCoverRelative 𝒰).overlap n σ))
      ((((Ob.baseChange (FlatCoefficientChange.refl R)).canonicalLinearCech
        𝒰).complex.iCycles n).hom c' σ) =
      ((Ob.canonicalLinearCech 𝒰).complex.iCycles n).hom c σ
  rw [canonicalCocycleBaseChange_iCycles_apply]
  have hsection := ConcreteCategory.congr_hom
    (Ob.baseChangeSectionMap_id
      ((canonicalCoverRelative 𝒰).overlap n σ))
    ((1 : R) ⊗ₜ[R, RingHom.id R]
      (((Ob.canonicalLinearCech 𝒰).complex.iCycles n).hom c σ))
  exact hsection.trans
    (ModuleCat.extendScalarsId_hom_app_one_tmul.{u, u + 1}
      (Ob.modulePresheaf.obj (Opposite.op
        ((canonicalCoverRelative 𝒰).overlap n σ)))
      (((Ob.canonicalLinearCech 𝒰).complex.iCycles n).hom c σ))

/-- The canonical Čech Hn base-change map satisfies identity coherence. -/
private theorem canonicalCechHnBaseChangeMap_id
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    canonicalCechHnBaseChangeMap Ob (FlatCoefficientChange.refl R) 𝒰 n ≫
        (linearCechHnIsoOfPresheafIso
          (Ob.baseChange (FlatCoefficientChange.refl R)) Ob
          Ob.baseChangeIdIso 𝒰 n).hom =
      (Derived.Intersection.moduleScalarExtensionIdIso.{u, u + 1}
        ((Ob.canonicalLinearCech 𝒰).complex.homology n)).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul r x =>
      change R at r
      have hsurj : Function.Surjective
          ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n).hom :=
        (ModuleCat.epi_iff_surjective
          ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n)).mp inferInstance
      obtain ⟨c, rfl⟩ := hsurj x
      let unitClass :=
        Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
          (FlatCoefficientChange.refl R)
          ((Ob.canonicalLinearCech 𝒰).complex.homology n)
          ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n c)
      have htmul :
          r ⊗ₜ[R, RingHom.id R]
              ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n).hom c =
            r • unitClass := by
        change r ⊗ₜ[R]
              ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n).hom c =
            (r * 1) ⊗ₜ[R]
              ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n).hom c
        rw [mul_one]
      rw [htmul]
      simp only [map_smul]
      apply congrArg (fun q => r • q)
      let eComplex := linearCechComplexIsoOfPresheafIso
        (Ob.baseChange (FlatCoefficientChange.refl R)) Ob
        Ob.baseChangeIdIso 𝒰
      let eH := linearCechHnIsoOfPresheafIso
        (Ob.baseChange (FlatCoefficientChange.refl R)) Ob
        Ob.baseChangeIdIso 𝒰 n
      let c' := canonicalCocycleBaseChange Ob
        (FlatCoefficientChange.refl R) 𝒰 n c
      have hclass := canonicalCocycleBaseChange_class Ob
        (FlatCoefficientChange.refl R) 𝒰 n c
      have hnat := ConcreteCategory.congr_hom
        (HomologicalComplex.homologyπ_naturality eComplex.hom n) c'
      calc
        eH.hom
            (canonicalCechHnBaseChangeMap Ob
              (FlatCoefficientChange.refl R) 𝒰 n
              unitClass) =
          eH.hom
            (((Ob.baseChange (FlatCoefficientChange.refl R)).canonicalLinearCech
              𝒰).complex.homologyπ n c') := by
                rw [hclass]
        _ = (Ob.canonicalLinearCech 𝒰).complex.homologyπ n
            (HomologicalComplex.cyclesMap eComplex.hom n c') := by
              simpa only [eH, linearCechHnIsoOfPresheafIso,
                ConcreteCategory.comp_apply] using hnat
        _ = (Ob.canonicalLinearCech 𝒰).complex.homologyπ n c := by
              rw [canonicalCocycleBaseChange_id]
        _ = (Derived.Intersection.moduleScalarExtensionIdIso.{u, u + 1}
              ((Ob.canonicalLinearCech 𝒰).complex.homology n)).hom
            unitClass := by
              symm
              simpa only [unitClass,
                Derived.Intersection.moduleScalarExtensionUnit_apply] using
                ModuleCat.extendScalarsId_hom_app_one_tmul.{u, u + 1}
                  ((Ob.canonicalLinearCech 𝒰).complex.homology n)
                  ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n c)

set_option maxHeartbeats 1000000 in
/-- Iterated canonical base change on cocycles agrees with composite base
change after the coefficient-presheaf compositor. -/
private theorem canonicalCocycleBaseChange_comp
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat)
    (c : (Ob.canonicalLinearCech 𝒰).complex.cycles n) :
    HomologicalComplex.cyclesMap
        (linearCechComplexIsoOfPresheafIso
          ((Ob.baseChange f).baseChange g) (Ob.baseChange (f.comp g))
          (Ob.baseChangeCompIso f g) 𝒰).hom n
        (canonicalCocycleBaseChange (Ob.baseChange f) g 𝒰 n
          (canonicalCocycleBaseChange Ob f 𝒰 n c)) =
      canonicalCocycleBaseChange Ob (f.comp g) 𝒰 n c := by
  let eComplex := linearCechComplexIsoOfPresheafIso
    ((Ob.baseChange f).baseChange g) (Ob.baseChange (f.comp g))
    (Ob.baseChangeCompIso f g) 𝒰
  let cf := canonicalCocycleBaseChange Ob f 𝒰 n c
  let cfg := canonicalCocycleBaseChange (Ob.baseChange f) g 𝒰 n cf
  let ccomp := canonicalCocycleBaseChange Ob (f.comp g) 𝒰 n c
  apply (ModuleCat.mono_iff_injective
    (((Ob.baseChange (f.comp g)).canonicalLinearCech 𝒰).complex.iCycles n)).mp
      inferInstance
  funext σ
  have hmap := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i eComplex.hom n) cfg
  have hmap' :
      (((Ob.baseChange (f.comp g)).canonicalLinearCech 𝒰).complex.iCycles n).hom
          (HomologicalComplex.cyclesMap eComplex.hom n cfg) σ =
        (eComplex.hom.f n).hom
          ((((Ob.baseChange f).baseChange g).canonicalLinearCech
            𝒰).complex.iCycles n cfg) σ := by
    simpa only [ConcreteCategory.comp_apply] using congrArg (fun z => z σ) hmap
  rw [hmap']
  change
    (Ob.baseChangeCompIso f g).hom.app (Opposite.op
        ((canonicalCoverRelative 𝒰).overlap n σ))
      (((((Ob.baseChange f).baseChange g).canonicalLinearCech
        𝒰).complex.iCycles n).hom cfg σ) =
      ((((Ob.baseChange (f.comp g)).canonicalLinearCech
        𝒰).complex.iCycles n).hom ccomp σ)
  rw [canonicalCocycleBaseChange_iCycles_apply,
    canonicalCocycleBaseChange_iCycles_apply,
    canonicalCocycleBaseChange_iCycles_apply]
  let W := (canonicalCoverRelative 𝒰).overlap n σ
  let x := ((Ob.canonicalLinearCech 𝒰).complex.iCycles n).hom c σ
  let iteratedUnit :=
    (1 : R'') ⊗ₜ[R', g.hom] ((1 : R') ⊗ₜ[R, f.hom] x)
  let compositeUnit := (1 : R'') ⊗ₜ[R, (f.comp g).hom] x
  have hsection := ConcreteCategory.congr_hom
    (Ob.baseChangeSectionMap_comp f g W) iteratedUnit
  have hcompHom := ModuleCat.extendScalarsComp_hom_app_one_tmul.{u, u + 1}
    f.hom g.hom (Ob.modulePresheaf.obj (Opposite.op W)) x
  let e := (ModuleCat.extendScalarsComp.{u, u + 1} f.hom g.hom).app
    (Ob.modulePresheaf.obj (Opposite.op W))
  have hcompInv : e.inv iteratedUnit = compositeUnit := by
    exact (LinearEquiv.symm_apply_eq e.toLinearEquiv).2 hcompHom.symm
  simp only [ConcreteCategory.comp_apply] at hsection
  have hmapTensor := ModuleCat.ExtendScalars.map_tmul.{u + 1, u, u}
    g.hom (Ob.baseChangeSectionMap f W) (1 : R'')
    ((1 : R') ⊗ₜ[R, f.hom] x)
  rw [hmapTensor] at hsection
  change
    (Ob.baseChangeCompIso f g).hom.app (Opposite.op W)
        ((Ob.baseChange f).baseChangeSectionMap g W
          ((1 : R'') ⊗ₜ[R', g.hom]
            (Ob.baseChangeSectionMap f W
              ((1 : R') ⊗ₜ[R, f.hom] x)))) =
      Ob.baseChangeSectionMap (f.comp g) W (e.inv iteratedUnit) at hsection
  rw [hcompInv] at hsection
  exact hsection

set_option maxHeartbeats 2000000 in
/-- The canonical Čech Hn base-change map satisfies composition coherence. -/
private theorem canonicalCechHnBaseChangeMap_comp
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) :
    (ModuleCat.extendScalars.{u, u, u + 1} g.hom).map
          (canonicalCechHnBaseChangeMap Ob f 𝒰 n) ≫
        canonicalCechHnBaseChangeMap (Ob.baseChange f) g 𝒰 n ≫
        (linearCechHnIsoOfPresheafIso
          ((Ob.baseChange f).baseChange g) (Ob.baseChange (f.comp g))
          (Ob.baseChangeCompIso f g) 𝒰 n).hom =
      (Derived.Intersection.moduleScalarExtensionCompIso.{u, u + 1} f g
          ((Ob.canonicalLinearCech 𝒰).complex.homology n)).hom ≫
        canonicalCechHnBaseChangeMap Ob (f.comp g) 𝒰 n := by
  letI : Algebra R R' := f.hom.toAlgebra
  letI : Algebra R' R'' := g.hom.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul s y =>
      change R'' at s
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          simpa only [TensorProduct.tmul_add, map_add] using
            congrArg₂ (· + ·) hx hy
      | tmul r x =>
          change R' at r
          have hsurj : Function.Surjective
              ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n).hom :=
            (ModuleCat.epi_iff_surjective
              ((Ob.canonicalLinearCech 𝒰).complex.homologyπ n)).mp inferInstance
          obtain ⟨c, rfl⟩ := hsurj x
          let H := (Ob.canonicalLinearCech 𝒰).complex.homology n
          let hClass := (Ob.canonicalLinearCech 𝒰).complex.homologyπ n c
          let unitF := Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
            f H hClass
          let unitIter := Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
            g (Derived.Intersection.moduleScalarExtension.{u, u + 1} f H) unitF
          have htmul :
              s ⊗ₜ[R', g.hom] (r ⊗ₜ[R, f.hom] hClass) =
                (s * g.hom r) • unitIter := by
            change s ⊗ₜ[R'] (r ⊗ₜ[R] hClass) =
              ((s * g.hom r) * 1) ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] hClass)
            rw [mul_one]
            have hinner : r ⊗ₜ[R] hClass =
                r • ((1 : R') ⊗ₜ[R] hClass) := by
              change r ⊗ₜ[R] hClass = (r * 1) ⊗ₜ[R] hClass
              rw [mul_one]
            rw [hinner, TensorProduct.tmul_smul]
            change (g.hom r * s) ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] hClass) = _
            rw [mul_comm]
          rw [htmul]
          simp only [map_smul]
          apply congrArg (fun q => (s * g.hom r) • q)
          let eComplex := linearCechComplexIsoOfPresheafIso
            ((Ob.baseChange f).baseChange g) (Ob.baseChange (f.comp g))
            (Ob.baseChangeCompIso f g) 𝒰
          let eH := linearCechHnIsoOfPresheafIso
            ((Ob.baseChange f).baseChange g) (Ob.baseChange (f.comp g))
            (Ob.baseChangeCompIso f g) 𝒰 n
          let cf := canonicalCocycleBaseChange Ob f 𝒰 n c
          let cfg := canonicalCocycleBaseChange (Ob.baseChange f) g 𝒰 n cf
          let ccomp := canonicalCocycleBaseChange Ob (f.comp g) 𝒰 n c
          have hclassF := canonicalCocycleBaseChange_class Ob f 𝒰 n c
          have hclassG := canonicalCocycleBaseChange_class
            (Ob.baseChange f) g 𝒰 n cf
          have hclassComp := canonicalCocycleBaseChange_class Ob
            (f.comp g) 𝒰 n c
          have hnat := ConcreteCategory.congr_hom
            (HomologicalComplex.homologyπ_naturality eComplex.hom n) cfg
          let compIso :=
            (ModuleCat.extendScalarsComp.{u, u + 1} f.hom g.hom).app H
          let unitComp :=
            Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
              (f.comp g) H hClass
          have hcompHom :=
            ModuleCat.extendScalarsComp_hom_app_one_tmul.{u, u + 1}
              f.hom g.hom H hClass
          have hcompInv : compIso.inv unitIter = unitComp := by
            exact (LinearEquiv.symm_apply_eq compIso.toLinearEquiv).2 hcompHom.symm
          have hinput :
              (ModuleCat.extendScalars.{u, u, u + 1} g.hom).map
                  (canonicalCechHnBaseChangeMap Ob f 𝒰 n) unitIter =
                Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1} g
                  (((Ob.baseChange f).canonicalLinearCech 𝒰).complex.homology n)
                  (((Ob.baseChange f).canonicalLinearCech 𝒰).complex.homologyπ
                    n cf) := by
            change
              (1 : R'') ⊗ₜ[R', g.hom]
                  (canonicalCechHnBaseChangeMap Ob f 𝒰 n unitF) =
                (1 : R'') ⊗ₜ[R', g.hom]
                  (((Ob.baseChange f).canonicalLinearCech 𝒰).complex.homologyπ
                    n cf)
            rw [← hclassF]
          calc
            eH.hom
                (canonicalCechHnBaseChangeMap (Ob.baseChange f) g 𝒰 n
                  ((ModuleCat.extendScalars.{u, u, u + 1} g.hom).map
                    (canonicalCechHnBaseChangeMap Ob f 𝒰 n) unitIter)) =
              eH.hom
                ((((Ob.baseChange f).baseChange g).canonicalLinearCech
                  𝒰).complex.homologyπ n cfg) := by
                    rw [hinput, ← hclassG]
            _ = ((Ob.baseChange (f.comp g)).canonicalLinearCech
                  𝒰).complex.homologyπ n
                (HomologicalComplex.cyclesMap eComplex.hom n cfg) := by
                  simpa only [eH, linearCechHnIsoOfPresheafIso,
                    ConcreteCategory.comp_apply] using hnat
            _ = ((Ob.baseChange (f.comp g)).canonicalLinearCech
                  𝒰).complex.homologyπ n ccomp := by
                    rw [canonicalCocycleBaseChange_comp]
            _ = canonicalCechHnBaseChangeMap Ob (f.comp g) 𝒰 n
                  unitComp := hclassComp
            _ = canonicalCechHnBaseChangeMap Ob (f.comp g) 𝒰 n
                  (compIso.inv unitIter) := by rw [hcompInv]

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

/-- Identity coherence for the terminal Leray module, transported through the
canonical Čech comparison and the coefficient-presheaf identity isomorphism. -/
noncomputable def baseChangeIdTerminalLerayHModuleIso
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLinearLerayFor 𝒰 Ob)
    (htarget : IsLinearLerayFor 𝒰
      (Ob.baseChange (FlatCoefficientChange.refl R)))
    (n : Nat) :
    (Ob.baseChange (FlatCoefficientChange.refl R)).terminalLerayHModule
        𝒰 hbase htarget n ≅
      Ob.terminalLerayHModule 𝒰 hbase hsource n := by
  let eTarget :=
    (Ob.baseChange (FlatCoefficientChange.refl R)).cechToSheafHLinearIso
      𝒰 hbase htarget n
  let eCech := (linearCechHnIsoOfPresheafIso
    (Ob.baseChange (FlatCoefficientChange.refl R)) Ob
    Ob.baseChangeIdIso 𝒰 n).toLinearEquiv
  let eSource := Ob.cechToSheafHLinearIso 𝒰 hbase hsource n
  exact (eTarget.symm.trans (eCech.trans eSource)).toModuleIso

/-- Composition coherence for the terminal Leray module, transported through
the canonical Čech comparison and the coefficient-presheaf compositor. -/
noncomputable def baseChangeCompTerminalLerayHModuleIso
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hiterated : IsLinearLerayFor 𝒰 ((Ob.baseChange f).baseChange g))
    (hcomposite : IsLinearLerayFor 𝒰 (Ob.baseChange (f.comp g)))
    (n : Nat) :
    ((Ob.baseChange f).baseChange g).terminalLerayHModule
        𝒰 hbase hiterated n ≅
      (Ob.baseChange (f.comp g)).terminalLerayHModule
        𝒰 hbase hcomposite n := by
  let eIterated := ((Ob.baseChange f).baseChange g).cechToSheafHLinearIso
    𝒰 hbase hiterated n
  let eCech := (linearCechHnIsoOfPresheafIso
    ((Ob.baseChange f).baseChange g) (Ob.baseChange (f.comp g))
    (Ob.baseChangeCompIso f g) 𝒰 n).toLinearEquiv
  let eComposite := (Ob.baseChange (f.comp g)).cechToSheafHLinearIso
    𝒰 hbase hcomposite n
  exact (eIterated.symm.trans (eCech.trans eComposite)).toModuleIso

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
/-- The actual-sheaf-cohomology base-change map satisfies identity coherence. -/
@[simp] theorem sheafHFlatBaseChangeMap_id
    {R : Type u} [CommRing R]
    (Ob : LinearCoefficientSheaf R S)
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLinearLerayFor 𝒰 Ob)
    (htarget : IsLinearLerayFor 𝒰
      (Ob.baseChange (FlatCoefficientChange.refl R)))
    (n : Nat) :
    sheafHFlatBaseChangeMap Ob (FlatCoefficientChange.refl R)
          𝒰 hbase hsource htarget n ≫
        (Ob.baseChangeIdTerminalLerayHModuleIso
          𝒰 hbase hsource htarget n).hom =
      (Derived.Intersection.moduleScalarExtensionIdIso.{u, u + 2}
        (Ob.terminalLerayHModule 𝒰 hbase hsource n)).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul r x =>
      change R at r
      let T := Ob.terminalLerayHModule 𝒰 hbase hsource n
      let unitT := Derived.Intersection.moduleScalarExtensionUnit.{u, u + 2}
        (FlatCoefficientChange.refl R) T x
      have htmul : r ⊗ₜ[R, RingHom.id R] x = r • unitT := by
        change r ⊗ₜ[R] x = (r * 1) ⊗ₜ[R] x
        rw [mul_one]
      rw [htmul]
      simp only [map_smul]
      apply congrArg (fun q => r • q)
      let eSource := Ob.cechToSheafHLinearIso 𝒰 hbase hsource n
      let eTarget :=
        (Ob.baseChange (FlatCoefficientChange.refl R)).cechToSheafHLinearIso
          𝒰 hbase htarget n
      let eH := linearCechHnIsoOfPresheafIso
        (Ob.baseChange (FlatCoefficientChange.refl R)) Ob
        Ob.baseChangeIdIso 𝒰 n
      let C := (Ob.canonicalLinearCech 𝒰).complex.homology n
      let unitC := Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
        (FlatCoefficientChange.refl R) C (eSource.symm x)
      have hCech := ConcreteCategory.congr_hom
        (canonicalCechHnBaseChangeMap_id Ob 𝒰 n) unitC
      have hCech' :
          eH.hom
              (canonicalCechHnBaseChangeMap Ob
                (FlatCoefficientChange.refl R) 𝒰 n unitC) =
            eSource.symm x := by
        calc
          _ = (Derived.Intersection.moduleScalarExtensionIdIso.{u, u + 1}
                C).hom unitC := by
                  simpa only [ConcreteCategory.comp_apply] using hCech
          _ = eSource.symm x := by
                simpa only [unitC, C,
                  Derived.Intersection.moduleScalarExtensionUnit_apply] using
                  ModuleCat.extendScalarsId_hom_app_one_tmul.{u, u + 1}
                    C (eSource.symm x)
      calc
        (sheafHFlatBaseChangeMap Ob (FlatCoefficientChange.refl R)
              𝒰 hbase hsource htarget n ≫
                (Ob.baseChangeIdTerminalLerayHModuleIso
              𝒰 hbase hsource htarget n).hom) unitT =
          eSource
            (eH.hom
              (canonicalCechHnBaseChangeMap Ob
                (FlatCoefficientChange.refl R) 𝒰 n unitC)) := by
                  simp only [ConcreteCategory.comp_apply,
                    sheafHFlatBaseChangeMap,
                    baseChangeIdTerminalLerayHModuleIso,
                    LinearEquiv.toModuleIso_hom,
                    unitT,
                    Derived.Intersection.moduleScalarExtensionUnit_apply]
                  change
                    (eTarget.symm.trans (eH.toLinearEquiv.trans eSource))
                        (eTarget
                          (canonicalCechHnBaseChangeMap Ob
                            (FlatCoefficientChange.refl R) 𝒰 n
                            ((LinearMap.baseChange R eSource.symm.toLinearMap)
                              ((1 : R) ⊗ₜ[R] x)))) = _
                  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
                    LinearEquiv.symm_apply_apply,
                    LinearMap.baseChange_tmul]
                  rfl
        _ = eSource (eSource.symm x) := congrArg eSource hCech'
        _ = x := eSource.apply_symm_apply x
        _ = (Derived.Intersection.moduleScalarExtensionIdIso.{u, u + 2}
              T).hom unitT := by
                symm
                simpa only [unitT, T,
                  Derived.Intersection.moduleScalarExtensionUnit_apply] using
                  ModuleCat.extendScalarsId_hom_app_one_tmul.{u, u + 2} T x

set_option maxRecDepth 3000 in
set_option maxHeartbeats 3000000 in
/-- The actual-sheaf-cohomology base-change map satisfies composition coherence. -/
theorem sheafHFlatBaseChangeMap_comp
    {R R' R'' : Type u}
    [CommRing R] [CommRing R'] [CommRing R'']
    (Ob : LinearCoefficientSheaf R S)
    (f : FlatCoefficientChange R R')
    (g : FlatCoefficientChange R' R'')
    [HasSheafify S.topology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1})]
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (hbase : IsTerminal base)
    (hsource : IsLinearLerayFor 𝒰 Ob)
    (hmiddle : IsLinearLerayFor 𝒰 (Ob.baseChange f))
    (hiterated : IsLinearLerayFor 𝒰 ((Ob.baseChange f).baseChange g))
    (hcomposite : IsLinearLerayFor 𝒰 (Ob.baseChange (f.comp g)))
    (n : Nat) :
    (ModuleCat.extendScalars g.hom).map
          (sheafHFlatBaseChangeMap Ob f
            𝒰 hbase hsource hmiddle n) ≫
        sheafHFlatBaseChangeMap (Ob.baseChange f) g
          𝒰 hbase hmiddle hiterated n ≫
        (Ob.baseChangeCompTerminalLerayHModuleIso f g
          𝒰 hbase hiterated hcomposite n).hom =
      (Derived.Intersection.moduleScalarExtensionCompIso.{u, u + 2} f g
          (Ob.terminalLerayHModule 𝒰 hbase hsource n)).hom ≫
        sheafHFlatBaseChangeMap Ob (f.comp g)
          𝒰 hbase hsource hcomposite n := by
  letI : Algebra R R' := f.hom.toAlgebra
  letI : Algebra R' R'' := g.hom.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul s y =>
      change R'' at s
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          simpa only [TensorProduct.tmul_add, map_add] using
            congrArg₂ (· + ·) hx hy
      | tmul r x =>
          change R' at r
          let T0 := Ob.terminalLerayHModule 𝒰 hbase hsource n
          let unitF_T := Derived.Intersection.moduleScalarExtensionUnit.{u, u + 2}
            f T0 x
          let unitIter_T :=
            Derived.Intersection.moduleScalarExtensionUnit.{u, u + 2} g
              (Derived.Intersection.moduleScalarExtension.{u, u + 2} f T0)
              unitF_T
          have htmul :
              s ⊗ₜ[R', g.hom] (r ⊗ₜ[R, f.hom] x) =
                (s * g.hom r) • unitIter_T := by
            change s ⊗ₜ[R'] (r ⊗ₜ[R] x) =
              ((s * g.hom r) * 1) ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] x)
            rw [mul_one]
            have hinner : r ⊗ₜ[R] x =
                r • ((1 : R') ⊗ₜ[R] x) := by
              change r ⊗ₜ[R] x = (r * 1) ⊗ₜ[R] x
              rw [mul_one]
            rw [hinner, TensorProduct.tmul_smul]
            change (g.hom r * s) ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] x) = _
            rw [mul_comm]
          rw [htmul]
          simp only [map_smul]
          apply congrArg (fun q => (s * g.hom r) • q)
          let e0 := Ob.cechToSheafHLinearIso 𝒰 hbase hsource n
          let e1 := (Ob.baseChange f).cechToSheafHLinearIso
            𝒰 hbase hmiddle n
          let e2 := ((Ob.baseChange f).baseChange g).cechToSheafHLinearIso
            𝒰 hbase hiterated n
          let ec := (Ob.baseChange (f.comp g)).cechToSheafHLinearIso
            𝒰 hbase hcomposite n
          let eH := linearCechHnIsoOfPresheafIso
            ((Ob.baseChange f).baseChange g) (Ob.baseChange (f.comp g))
            (Ob.baseChangeCompIso f g) 𝒰 n
          let C0 := (Ob.canonicalLinearCech 𝒰).complex.homology n
          let unitF_C := Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
            f C0 (e0.symm x)
          let unitIter_C :=
            Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1} g
              (Derived.Intersection.moduleScalarExtension.{u, u + 1} f C0)
              unitF_C
          let compIsoC :=
            (ModuleCat.extendScalarsComp.{u, u + 1} f.hom g.hom).app C0
          let unitCompC :=
            Derived.Intersection.moduleScalarExtensionUnit.{u, u + 1}
              (f.comp g) C0 (e0.symm x)
          have hcompCHom :=
            ModuleCat.extendScalarsComp_hom_app_one_tmul.{u, u + 1}
              f.hom g.hom C0 (e0.symm x)
          have hcompCInv : compIsoC.inv unitIter_C = unitCompC := by
            exact (LinearEquiv.symm_apply_eq compIsoC.toLinearEquiv).2 hcompCHom.symm
          let compIsoT :=
            (ModuleCat.extendScalarsComp.{u, u + 2} f.hom g.hom).app T0
          let unitCompT :=
            Derived.Intersection.moduleScalarExtensionUnit.{u, u + 2}
              (f.comp g) T0 x
          have hcompTHom :=
            ModuleCat.extendScalarsComp_hom_app_one_tmul.{u, u + 2}
              f.hom g.hom T0 x
          have hcompTInv : compIsoT.inv unitIter_T = unitCompT := by
            exact (LinearEquiv.symm_apply_eq compIsoT.toLinearEquiv).2 hcompTHom.symm
          have hCech := ConcreteCategory.congr_hom
            (canonicalCechHnBaseChangeMap_comp Ob f g 𝒰 n) unitIter_C
          have hCech' :
              eH.hom
                  (canonicalCechHnBaseChangeMap (Ob.baseChange f) g 𝒰 n
                    ((ModuleCat.extendScalars.{u, u, u + 1} g.hom).map
                      (canonicalCechHnBaseChangeMap Ob f 𝒰 n) unitIter_C)) =
                canonicalCechHnBaseChangeMap Ob (f.comp g) 𝒰 n unitCompC := by
            calc
              _ = canonicalCechHnBaseChangeMap Ob (f.comp g) 𝒰 n
                    (compIsoC.inv unitIter_C) := by
                      simpa only [ConcreteCategory.comp_apply] using hCech
              _ = _ := by rw [hcompCInv]
          calc
            ((ModuleCat.extendScalars g.hom).map
                  (sheafHFlatBaseChangeMap Ob f
                    𝒰 hbase hsource hmiddle n) ≫
                sheafHFlatBaseChangeMap (Ob.baseChange f) g
                  𝒰 hbase hmiddle hiterated n ≫
                (Ob.baseChangeCompTerminalLerayHModuleIso f g
                  𝒰 hbase hiterated hcomposite n).hom) unitIter_T =
              ec
                (eH.hom
                  (canonicalCechHnBaseChangeMap (Ob.baseChange f) g 𝒰 n
                    ((ModuleCat.extendScalars.{u, u, u + 1} g.hom).map
                      (canonicalCechHnBaseChangeMap Ob f 𝒰 n) unitIter_C))) := by
                        simp only [ConcreteCategory.comp_apply,
                          sheafHFlatBaseChangeMap,
                          baseChangeCompTerminalLerayHModuleIso,
                          LinearEquiv.toModuleIso_hom,
                          unitIter_T, unitF_T, unitIter_C, unitF_C,
                          Derived.Intersection.moduleScalarExtensionUnit_apply]
                        change
                          (e2.symm.trans (eH.toLinearEquiv.trans ec))
                              (e2
                                (canonicalCechHnBaseChangeMap (Ob.baseChange f)
                                  g 𝒰 n
                                  ((LinearMap.baseChange R'' e1.symm.toLinearMap)
                                    ((1 : R'') ⊗ₜ[R', g.hom]
                                      (e1
                                        (canonicalCechHnBaseChangeMap Ob f 𝒰 n
                                          ((LinearMap.baseChange R'
                                            e0.symm.toLinearMap)
                                            ((1 : R') ⊗ₜ[R, f.hom] x)))))))) = _
                        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
                          LinearEquiv.symm_apply_apply,
                          LinearMap.baseChange_tmul]
                        have he1Tensor :
                            (1 : R'') ⊗ₜ[R', g.hom]
                                (e1.symm.toLinearMap
                                  (e1
                                    (canonicalCechHnBaseChangeMap Ob f 𝒰 n
                                      ((LinearMap.baseChange R'
                                        e0.symm.toLinearMap)
                                        ((1 : R') ⊗ₜ[R, f.hom] x))))) =
                              (1 : R'') ⊗ₜ[R', g.hom]
                                (canonicalCechHnBaseChangeMap Ob f 𝒰 n
                                  ((LinearMap.baseChange R'
                                    e0.symm.toLinearMap)
                                    ((1 : R') ⊗ₜ[R, f.hom] x))) :=
                          congrArg
                            (fun q => (1 : R'') ⊗ₜ[R', g.hom] q)
                            (e1.symm_apply_apply _)
                        have hmap :
                            ((ModuleCat.extendScalars g.hom).map
                                (canonicalCechHnBaseChangeMap Ob f 𝒰 n))
                                ((1 : R'') ⊗ₜ[R', g.hom]
                                  ((1 : R') ⊗ₜ[R, f.hom] e0.symm x)) =
                              (1 : R'') ⊗ₜ[R', g.hom]
                                (canonicalCechHnBaseChangeMap Ob f 𝒰 n
                                  ((1 : R') ⊗ₜ[R, f.hom] e0.symm x)) := by
                          apply ModuleCat.ExtendScalars.map_tmul
                        rw [he1Tensor, LinearMap.baseChange_tmul, hmap]
                        rfl
            _ = ec
                (canonicalCechHnBaseChangeMap Ob (f.comp g) 𝒰 n unitCompC) :=
                  congrArg ec hCech'
            _ = ((Derived.Intersection.moduleScalarExtensionCompIso.{u, u + 2}
                    f g T0).hom ≫
                  sheafHFlatBaseChangeMap Ob (f.comp g)
                    𝒰 hbase hsource hcomposite n) unitIter_T := by
                      rw [ConcreteCategory.comp_apply]
                      change ec
                        (canonicalCechHnBaseChangeMap Ob (f.comp g) 𝒰 n unitCompC) =
                          sheafHFlatBaseChangeMap Ob (f.comp g)
                            𝒰 hbase hsource hcomposite n
                            (compIsoT.inv unitIter_T)
                      rw [hcompTInv]
                      simpa only [unitCompT, unitCompC,
                        Derived.Intersection.moduleScalarExtensionUnit_apply]
                        using
                          (sheafHFlatBaseChangeMap_formula Ob (f.comp g)
                            𝒰 hbase hsource hcomposite n (1 : R'') x).symm

end LinearCoefficientSheaf

end AAT.AG.Cohomology
