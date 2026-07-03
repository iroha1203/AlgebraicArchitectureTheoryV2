import Formal.AG.Cohomology.Basic
import Formal.AG.LawAlgebra.LawfulLocus
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.RingTheory.Ideal.Cotangent

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u v w

open CategoryTheory
open Opposite

/--
IV.定義2.1 / 定義2.2: obstruction coefficient sheaf.

The carrier is still the PRD-2 Type-valued AAT sheaf surface.  The extra field
records the abelian group structure needed before Cech cochains can use this as
an obstruction coefficient object.
-/
structure ObstructionSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) where
  carrier : Site.AATSheaf S
  addCommGroup : ∀ W : S.category, AddCommGroup (carrier.toPresheaf.obj (op W))
  map_zero :
    ∀ {source target : S.category} (f : source ⟶ target),
      letI := addCommGroup target
      letI := addCommGroup source
      carrier.toPresheaf.map f.op 0 = 0
  map_add :
    ∀ {source target : S.category} (f : source ⟶ target)
      (x y : carrier.toPresheaf.obj (op target)),
      letI := addCommGroup target
      letI := addCommGroup source
      carrier.toPresheaf.map f.op (x + y) =
        carrier.toPresheaf.map f.op x + carrier.toPresheaf.map f.op y

attribute [instance] ObstructionSheaf.addCommGroup

namespace ObstructionSheaf

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}

/--
Build an obstruction coefficient sheaf from an `AddCommGrpCat`-valued
presheaf whose underlying Type-valued presheaf satisfies the AAT sheaf
condition.

This keeps the existing `ObstructionSheaf` surface unchanged: the bundled
abelian-group values provide the objectwise groups and the presheaf morphisms
provide the additive-map laws.
-/
def ofAddCommGrpValued
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u})
    (isSheaf : Site.AATSheafCondition S (F ⋙ forget AddCommGrpCat.{u})) :
    ObstructionSheaf S where
  carrier := {
    carrier := F ⋙ forget AddCommGrpCat.{u}
    isSheaf := isSheaf
  }
  addCommGroup W := inferInstanceAs (AddCommGroup (F.obj (op W)))
  map_zero {source target} f := by
    letI := inferInstanceAs (AddCommGroup (F.obj (op target)))
    letI := inferInstanceAs (AddCommGroup (F.obj (op source)))
    exact (F.map f.op).hom.map_zero
  map_add {source target} f x y := by
    letI := inferInstanceAs (AddCommGroup (F.obj (op target)))
    letI := inferInstanceAs (AddCommGroup (F.obj (op source)))
    exact (F.map f.op).hom.map_add x y

@[simp]
theorem ofAddCommGrpValued_toPresheaf
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u})
    (isSheaf : Site.AATSheafCondition S (F ⋙ forget AddCommGrpCat.{u})) :
    (ofAddCommGrpValued F isSheaf).carrier.toPresheaf =
      F ⋙ forget AddCommGrpCat.{u} :=
  rfl

/--
Accessor for the zero-preserving law supplied by `ofAddCommGrpValued`.
-/
@[simp]
theorem ofAddCommGrpValued_map_zero
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u})
    (isSheaf : Site.AATSheafCondition S (F ⋙ forget AddCommGrpCat.{u}))
    {source target : S.category} (f : source ⟶ target) :
    letI := (ofAddCommGrpValued F isSheaf).addCommGroup target
    letI := (ofAddCommGrpValued F isSheaf).addCommGroup source
    (ofAddCommGrpValued F isSheaf).carrier.toPresheaf.map f.op 0 = 0 :=
  (ofAddCommGrpValued F isSheaf).map_zero f

/--
Accessor for the addition-preserving law supplied by `ofAddCommGrpValued`.
-/
@[simp]
theorem ofAddCommGrpValued_map_add
    (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u})
    (isSheaf : Site.AATSheafCondition S (F ⋙ forget AddCommGrpCat.{u}))
    {source target : S.category} (f : source ⟶ target)
    (x y :
      (ofAddCommGrpValued F isSheaf).carrier.toPresheaf.obj (op target)) :
    letI := (ofAddCommGrpValued F isSheaf).addCommGroup target
    letI := (ofAddCommGrpValued F isSheaf).addCommGroup source
    (ofAddCommGrpValued F isSheaf).carrier.toPresheaf.map f.op (x + y) =
      (ofAddCommGrpValued F isSheaf).carrier.toPresheaf.map f.op x +
        (ofAddCommGrpValued F isSheaf).carrier.toPresheaf.map f.op y :=
  (ofAddCommGrpValued F isSheaf).map_add f x y

end ObstructionSheaf

/-- IV.定義2.1: PRD notation `Ob_U` for an obstruction coefficient sheaf. -/
abbrev Ob_U {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) :=
  ObstructionSheaf S

/--
IV.定義2.2: module-valued obstruction coefficient sheaf.

This specializes `Ob_U` to the case where each coefficient group is a module
over the selected law-algebra sheaf section ring `O_X^U(W)`.
-/
structure ModuleObstructionSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k]
    (P : LawAlgebra.LawAlgebraSheafPackage S k) extends ObstructionSheaf S where
  moduleStructure :
    ∀ W : S.category,
      Module ((P.sheafification.OXPresheaf.obj (op W)).right)
        (toObstructionSheaf.carrier.toPresheaf.obj (op W))

attribute [instance] ModuleObstructionSheaf.moduleStructure

/-- IV.定義2.2: PRD notation for an `O_X^U`-module-valued `Ob_U`. -/
abbrev OXModuleOb_U {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k]
    (P : LawAlgebra.LawAlgebraSheafPackage S k) :=
  ModuleObstructionSheaf S k P

namespace StandardObstruction

variable (A : Type v) [CommRing A]

/-- IV.定義2.4: `Def_U := I_U`, read from the PRD-3 local obstruction ideal. -/
def Def_U (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A) :
    Ideal A :=
  F.localObstructionIdeal

/-- IV.定義2.4: lawful-locus algebra over which `I_U / I_U^2` is a module. -/
abbrev LawfulLocusAlgebra
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A) :=
  A ⧸ Def_U A F

/-- IV.定義2.4: `ConDef_U := I_U / I_U^2`, using Mathlib `Ideal.Cotangent`. -/
abbrev ConDef_U
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A) :=
  (Def_U A F).Cotangent

/--
IV.定義2.4: the conormal object is a module over the lawful-locus quotient
`O_X^U / I_U`.
-/
instance conDefModule
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A) :
    Module (LawfulLocusAlgebra A F) (ConDef_U A F) :=
  inferInstance

/-- IV.定義2.4: the canonical map from `I_U` to `I_U / I_U^2`. -/
def toConDef
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A) :
    Def_U A F →ₗ[A] ConDef_U A F :=
  (Def_U A F).toCotangent

/--
IV.定義2.4: a selected pushforward carrier for `i_* ConDef_U`.

This deliberately keeps the pushforward carrier distinct from the conormal
module on the lawful locus.  Later geometry can instantiate `pushforwardCarrier`
with a concrete direct image sheaf without changing the R1 package boundary.
-/
structure PushforwardConDef
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A) where
  pushforwardCarrier : Type v
  addCommGroup : AddCommGroup pushforwardCarrier
  fromConDef : ConDef_U A F →+ pushforwardCarrier

attribute [instance] PushforwardConDef.addCommGroup

/--
IV.定義2.4: standard obstruction package.

It records the PRD-3 local obstruction ideal as `Def_U`, exposes
`ConDef_U = I_U / I_U^2`, and keeps the selected `i_* ConDef_U` carrier
separate from the lawful-locus module.
-/
structure CanonicalPackage where
  selectedIdeals : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A
  pushforwardConDef : PushforwardConDef A selectedIdeals

namespace CanonicalPackage

/-- IV.定義2.4: read `Def_U` from the standard package. -/
def defU (P : CanonicalPackage A) : Ideal A :=
  Def_U A P.selectedIdeals

/-- IV.定義2.4: read `ConDef_U` from the standard package. -/
abbrev conDefU (P : CanonicalPackage A) : Type v :=
  ConDef_U A P.selectedIdeals

/-- IV.定義2.4: the package's `Def_U` is definitionally the PRD-3 local obstruction ideal. -/
theorem defU_eq_localObstructionIdeal (P : CanonicalPackage A) :
    P.defU = P.selectedIdeals.localObstructionIdeal :=
  rfl

/-- IV.定義2.4: the package records a distinct selected carrier for `i_* ConDef_U`. -/
def pushforwardCarrier (P : CanonicalPackage A) : Type v :=
  P.pushforwardConDef.pushforwardCarrier

end CanonicalPackage

/--
IV.定義2.4 placeholder: derived obstruction object.

This is only the type signature for `DerOb_U(M)`.  The cotangent complex,
`Ext^1`, and derived-category construction are intentionally delegated to the
Part V PRD and are not constructed here.
-/
opaque DerOb_U
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A)
    (M : Type w) [AddCommGroup M] [Module A M] : Type (max v w)

end StandardObstruction

end Cohomology
end AAT.AG
