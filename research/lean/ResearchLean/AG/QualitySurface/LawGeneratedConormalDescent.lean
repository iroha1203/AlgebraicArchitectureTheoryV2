import Formal.AG.Site.Descent
import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.AddTorsor.Defs
import Mathlib.Tactic

/-!
# Generic additive first-order lift descent

This is the D0 engine for G-07.  Its Čech data are constructed from all
twofold and threefold common refinements of the selected sieve.  The overlap
difference, its cocycle equation, the correction equation, and change of local
lift are theorems derived from restriction functoriality and objectwise kernel
exactness; none is a field of the input structure.
-/

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace LawGeneratedConormalDescent

open CategoryTheory
open Opposite

universe u

/-- Generic additive short-exact lift input on a selected AAT cover. -/
structure ShortExactLiftProblem
    {U : AAT.AG.AtomCarrier.{u}} {A : AAT.AG.ArchitectureObject U}
    (S : AAT.AG.Site.AATSite A) where
  N : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u}
  E : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u}
  Q : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u}
  kernel : N ⟶ E
  projection : E ⟶ Q
  projection_kernel : ∀ W n, projection.app W (kernel.app W n) = 0
  kernelEquiv : ∀ W, N.obj W ≃+ AddMonoidHom.ker (projection.app W).hom
  kernelEquiv_apply : ∀ W n, ((kernelEquiv W n).1 : E.obj W) = kernel.app W n
  base : S.category
  cover : Sieve base
  cover_mem : cover ∈ S.topology base
  baseSection : Q.obj (op base)
  localLifts :
    ∀ {Y : S.category} (f : Y ⟶ base), cover f → E.obj (op Y)
  localLifts_project :
    ∀ {Y : S.category} (f : Y ⟶ base) (hf : cover f),
      projection.app (op Y) (localLifts f hf) = Q.map f.op baseSection
  eIsSheaf : AAT.AG.Site.AATSheafCondition S (E ⋙ forget AddCommGrpCat)
  qIsSheaf : AAT.AG.Site.AATSheafCondition S (Q ⋙ forget AddCommGrpCat)

namespace ShortExactLiftProblem

variable {U : AAT.AG.AtomCarrier.{u}} {A : AAT.AG.ArchitectureObject U}
variable {S : AAT.AG.Site.AATSite A}

/-- Degree-zero kernel sections indexed by all arrows of the selected sieve. -/
def C0 (P : ShortExactLiftProblem S) : Type u :=
  ∀ {Y : S.category} (f : Y ⟶ P.base), P.cover f → P.N.obj (op Y)

instance (P : ShortExactLiftProblem S) : AddCommGroup P.C0 := by
  dsimp [C0]
  infer_instance

/-- A common refinement of two selected cover arrows. -/
structure OverlapIndex (P : ShortExactLiftProblem S) where
  leftObj : S.category
  rightObj : S.category
  common : S.category
  leftArrow : leftObj ⟶ P.base
  rightArrow : rightObj ⟶ P.base
  left_mem : P.cover leftArrow
  right_mem : P.cover rightArrow
  toLeft : common ⟶ leftObj
  toRight : common ⟶ rightObj
  commutes : toLeft ≫ leftArrow = toRight ≫ rightArrow

/-- Degree-one kernel cochains on all twofold common refinements. -/
def C1 (P : ShortExactLiftProblem S) : Type u :=
  (o : P.OverlapIndex) → P.N.obj (op o.common)

instance (P : ShortExactLiftProblem S) : AddCommGroup P.C1 := by
  dsimp [C1]
  infer_instance

/-- A simultaneous common refinement of three selected cover arrows. -/
structure TripleIndex (P : ShortExactLiftProblem S) where
  obj0 : S.category
  obj1 : S.category
  obj2 : S.category
  common : S.category
  arrow0 : obj0 ⟶ P.base
  arrow1 : obj1 ⟶ P.base
  arrow2 : obj2 ⟶ P.base
  mem0 : P.cover arrow0
  mem1 : P.cover arrow1
  mem2 : P.cover arrow2
  to0 : common ⟶ obj0
  to1 : common ⟶ obj1
  to2 : common ⟶ obj2
  comm01 : to0 ≫ arrow0 = to1 ≫ arrow1
  comm02 : to0 ≫ arrow0 = to2 ≫ arrow2
  comm12 : to1 ≫ arrow1 = to2 ≫ arrow2

namespace TripleIndex

/-- The `(0,1)` overlap underlying a triple refinement. -/
def overlap01 {P : ShortExactLiftProblem S} (t : P.TripleIndex) : P.OverlapIndex where
  leftObj := t.obj0
  rightObj := t.obj1
  common := t.common
  leftArrow := t.arrow0
  rightArrow := t.arrow1
  left_mem := t.mem0
  right_mem := t.mem1
  toLeft := t.to0
  toRight := t.to1
  commutes := t.comm01

/-- The `(0,2)` overlap underlying a triple refinement. -/
def overlap02 {P : ShortExactLiftProblem S} (t : P.TripleIndex) : P.OverlapIndex where
  leftObj := t.obj0
  rightObj := t.obj2
  common := t.common
  leftArrow := t.arrow0
  rightArrow := t.arrow2
  left_mem := t.mem0
  right_mem := t.mem2
  toLeft := t.to0
  toRight := t.to2
  commutes := t.comm02

/-- The `(1,2)` overlap underlying a triple refinement. -/
def overlap12 {P : ShortExactLiftProblem S} (t : P.TripleIndex) : P.OverlapIndex where
  leftObj := t.obj1
  rightObj := t.obj2
  common := t.common
  leftArrow := t.arrow1
  rightArrow := t.arrow2
  left_mem := t.mem1
  right_mem := t.mem2
  toLeft := t.to1
  toRight := t.to2
  commutes := t.comm12

end TripleIndex

/-- Degree-two kernel cochains on all triple common refinements. -/
def C2 (P : ShortExactLiftProblem S) : Type u :=
  (t : P.TripleIndex) → P.N.obj (op t.common)

instance (P : ShortExactLiftProblem S) : AddCommGroup P.C2 := by
  dsimp [C2]
  infer_instance

/-- The Čech degree-zero differential, constructed from restrictions. -/
def d0 (P : ShortExactLiftProblem S) : P.C0 →+ P.C1 where
  toFun a o :=
    P.N.map o.toRight.op (a o.rightArrow o.right_mem) -
      P.N.map o.toLeft.op (a o.leftArrow o.left_mem)
  map_zero' := by
    funext o
    simp
  map_add' a b := by
    funext o
    simp
    abel

/-- The Čech degree-one differential, constructed on triple refinements. -/
def d1 (P : ShortExactLiftProblem S) : P.C1 →+ P.C2 where
  toFun c t := c t.overlap12 - c t.overlap02 + c t.overlap01
  map_zero' := by
    funext t
    simp
  map_add' a b := by
    funext t
    dsimp
    abel

/-- The constructed Čech differential squares to zero. -/
theorem d1_d0 (P : ShortExactLiftProblem S) (a : P.C0) :
    P.d1 (P.d0 a) = 0 := by
  funext t
  dsimp [d0, d1, TripleIndex.overlap01, TripleIndex.overlap02,
    TripleIndex.overlap12]
  abel

/-- Local lift families to the fixed base section. -/
def LocalLiftFamily (P : ShortExactLiftProblem S) : Type u :=
  {lifts : ∀ {Y : S.category} (f : Y ⟶ P.base), P.cover f → P.E.obj (op Y) //
    ∀ {Y : S.category} (f : Y ⟶ P.base) (hf : P.cover f),
      P.projection.app (op Y) (lifts f hf) = P.Q.map f.op P.baseSection}

/-- The chosen local lifts as a member of the local-lift fiber. -/
def chosenLocalLiftFamily (P : ShortExactLiftProblem S) : P.LocalLiftFamily :=
  ⟨P.localLifts, P.localLifts_project⟩

/-- Projection of two local lifts agrees after restriction to a common refinement. -/
theorem projection_overlap_difference_eq_zero
    (P : ShortExactLiftProblem S) (L : P.LocalLiftFamily) (o : P.OverlapIndex) :
    P.projection.app (op o.common)
      (P.E.map o.toRight.op (L.1 o.rightArrow o.right_mem) -
        P.E.map o.toLeft.op (L.1 o.leftArrow o.left_mem)) = 0 := by
  rw [map_sub, ← P.projection.naturality_apply, ← P.projection.naturality_apply,
    L.2, L.2]
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, o.commutes, sub_self]

/-- Kernel-valued difference of two local lifts on an overlap. -/
def localLiftDifferenceAt (P : ShortExactLiftProblem S)
    (L : P.LocalLiftFamily) (o : P.OverlapIndex) : P.N.obj (op o.common) :=
  (P.kernelEquiv (op o.common)).symm
    ⟨P.E.map o.toRight.op (L.1 o.rightArrow o.right_mem) -
      P.E.map o.toLeft.op (L.1 o.leftArrow o.left_mem),
      P.projection_overlap_difference_eq_zero L o⟩

/-- The overlap-difference cochain generated from an explicit local-lift family. -/
def localLiftDifference (P : ShortExactLiftProblem S)
    (L : P.LocalLiftFamily) : P.C1 :=
  fun o => P.localLiftDifferenceAt L o

/-- Applying the kernel inclusion recovers the literal overlap difference. -/
theorem kernel_localLiftDifferenceAt (P : ShortExactLiftProblem S)
    (L : P.LocalLiftFamily) (o : P.OverlapIndex) :
    P.kernel.app (op o.common) (P.localLiftDifferenceAt L o) =
      P.E.map o.toRight.op (L.1 o.rightArrow o.right_mem) -
        P.E.map o.toLeft.op (L.1 o.leftArrow o.left_mem) := by
  rw [← P.kernelEquiv_apply]
  change ((P.kernelEquiv (op o.common))
    ((P.kernelEquiv (op o.common)).symm _)).1 = _
  rw [AddEquiv.apply_symm_apply]

/-- Kernel-valued change between two explicit choices of local lifts. -/
def changePrimitive (P : ShortExactLiftProblem S)
    (left right : P.LocalLiftFamily) : P.C0 :=
  fun {Y} f hf =>
    (P.kernelEquiv (op Y)).symm
      ⟨right.1 f hf - left.1 f hf, by
        rw [map_sub, right.2, left.2, sub_self]⟩

/-- Applying the kernel inclusion recovers the literal change of local lift. -/
theorem kernel_changePrimitive (P : ShortExactLiftProblem S)
    (left right : P.LocalLiftFamily) {Y : S.category}
    (f : Y ⟶ P.base) (hf : P.cover f) :
    P.kernel.app (op Y) (P.changePrimitive left right f hf) =
      right.1 f hf - left.1 f hf := by
  rw [← P.kernelEquiv_apply]
  change ((P.kernelEquiv (op Y)) ((P.kernelEquiv (op Y)).symm _)).1 = _
  rw [AddEquiv.apply_symm_apply]

/-- Changing explicit local lifts changes the overlap cochain by a coboundary. -/
theorem localLiftDifference_change (P : ShortExactLiftProblem S)
    (left right : P.LocalLiftFamily) :
    P.localLiftDifference right - P.localLiftDifference left =
      P.d0 (P.changePrimitive left right) := by
  funext o
  apply (P.kernelEquiv (op o.common)).injective
  apply Subtype.ext
  rw [P.kernelEquiv_apply]
  change P.kernel.app (op o.common)
      (P.localLiftDifference right o - P.localLiftDifference left o) = _
  rw [map_sub, P.kernel_localLiftDifferenceAt, P.kernel_localLiftDifferenceAt]
  change _ = P.kernel.app (op o.common)
    (P.N.map o.toRight.op (P.changePrimitive left right o.rightArrow o.right_mem) -
      P.N.map o.toLeft.op (P.changePrimitive left right o.leftArrow o.left_mem))
  rw [map_sub, ← P.kernel.naturality_apply, ← P.kernel.naturality_apply,
    P.kernel_changePrimitive, P.kernel_changePrimitive]
  abel

/-- The generated local-lift difference satisfies the Čech cocycle equation. -/
theorem localLiftDifference_cocycle (P : ShortExactLiftProblem S)
    (L : P.LocalLiftFamily) : P.d1 (P.localLiftDifference L) = 0 := by
  funext t
  apply (P.kernelEquiv (op t.common)).injective
  apply Subtype.ext
  rw [P.kernelEquiv_apply]
  change P.kernel.app (op t.common)
      ((P.localLiftDifference L) t.overlap12 -
        (P.localLiftDifference L) t.overlap02 +
          (P.localLiftDifference L) t.overlap01) = 0
  rw [map_add, map_sub]
  simp only [localLiftDifference]
  rw [P.kernel_localLiftDifferenceAt, P.kernel_localLiftDifferenceAt,
    P.kernel_localLiftDifferenceAt]
  abel

/-- Degree-one cocycles in the constructed complex. -/
def cocycleSubgroup (P : ShortExactLiftProblem S) : AddSubgroup P.C1 :=
  AddMonoidHom.ker P.d1

/-- The connecting cocycle generated by the chosen local lifts. -/
def CechConnectingCocycle (P : ShortExactLiftProblem S) : P.cocycleSubgroup :=
  ⟨P.localLiftDifference P.chosenLocalLiftFamily,
    P.localLiftDifference_cocycle P.chosenLocalLiftFamily⟩

/-- A degree-zero correction as a degree-one cocycle. -/
def coboundaryCocycle (P : ShortExactLiftProblem S) (a : P.C0) :
    P.cocycleSubgroup :=
  ⟨P.d0 a, P.d1_d0 a⟩

/-- Connecting cocycle for any explicit choice of local lifts. -/
def connectingCocycleFor (P : ShortExactLiftProblem S)
    (L : P.LocalLiftFamily) : P.cocycleSubgroup :=
  ⟨P.localLiftDifference L, P.localLiftDifference_cocycle L⟩

/-- Coboundaries inside the constructed cocycle group. -/
def coboundarySubgroup (P : ShortExactLiftProblem S) :
    AddSubgroup P.cocycleSubgroup :=
  {
    carrier := fun c => ∃ a, c = P.coboundaryCocycle a
    zero_mem' := by
      refine ⟨0, ?_⟩
      apply Subtype.ext
      simp [coboundaryCocycle]
    add_mem' := by
      rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      apply Subtype.ext
      simp [coboundaryCocycle]
    neg_mem' := by
      rintro x ⟨a, rfl⟩
      refine ⟨-a, ?_⟩
      apply Subtype.ext
      simp [coboundaryCocycle]
  }

/-- Cover-relative additive first cohomology of the constructed refinement complex. -/
abbrev CechH1 (P : ShortExactLiftProblem S) : Type u :=
  P.cocycleSubgroup ⧸ P.coboundarySubgroup

/-- The section-specific connecting class. -/
def connectingClass (P : ShortExactLiftProblem S) : P.CechH1 :=
  P.CechConnectingCocycle

/-- Connecting class for any explicit choice of local lifts. -/
def connectingClassFor (P : ShortExactLiftProblem S)
    (L : P.LocalLiftFamily) : P.CechH1 :=
  P.connectingCocycleFor L

/-- The connecting class is independent of the explicit local-lift choice. -/
theorem connectingClass_choice_independent (P : ShortExactLiftProblem S)
    (left right : P.LocalLiftFamily) :
    P.connectingClassFor left = P.connectingClassFor right := by
  change ((P.connectingCocycleFor left : P.cocycleSubgroup) : P.CechH1) =
    ((P.connectingCocycleFor right : P.cocycleSubgroup) : P.CechH1)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  refine ⟨-(P.changePrimitive left right), ?_⟩
  apply Subtype.ext
  change P.localLiftDifference left - P.localLiftDifference right =
    P.d0 (-(P.changePrimitive left right))
  rw [map_neg, ← P.localLiftDifference_change left right]
  simp

/-- The connecting class is zero exactly when the overlap difference is a correction boundary. -/
theorem connectingClass_eq_zero_iff (P : ShortExactLiftProblem S) :
    P.connectingClass = 0 ↔
      ∃ a : P.C0, P.localLiftDifference P.chosenLocalLiftFamily = P.d0 a := by
  change (P.CechConnectingCocycle : P.CechH1) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by apply Subtype.ext; exact ha⟩

/-- Correct the chosen local lifts by a kernel-valued degree-zero cochain. -/
def correctedLocalLifts (P : ShortExactLiftProblem S) (a : P.C0) :
    Presieve.FamilyOfElements (P.E ⋙ forget AddCommGrpCat)
      (P.cover : Presieve P.base) :=
  fun {Y} f hf =>
    letI : AddCommGroup ((P.E ⋙ forget AddCommGrpCat).obj (op Y)) :=
      inferInstanceAs (AddCommGroup (P.E.obj (op Y)))
    P.localLifts f hf - P.kernel.app (op Y) (a f hf)

/-- The correction equation is exactly compatibility of the corrected family. -/
theorem correctedLocalLifts_compatible_iff (P : ShortExactLiftProblem S)
    (a : P.C0) :
    (P.correctedLocalLifts a).Compatible ↔
      P.localLiftDifference P.chosenLocalLiftFamily = P.d0 a := by
  constructor
  · intro hcompatible
    funext o
    apply (P.kernelEquiv (op o.common)).injective
    apply Subtype.ext
    rw [P.kernelEquiv_apply]
    rw [P.kernel_localLiftDifferenceAt]
    change _ = P.kernel.app (op o.common)
      (P.N.map o.toRight.op (a o.rightArrow o.right_mem) -
        P.N.map o.toLeft.op (a o.leftArrow o.left_mem))
    rw [map_sub, ← P.kernel.naturality_apply, ← P.kernel.naturality_apply]
    have hc := hcompatible o.toLeft o.toRight o.left_mem o.right_mem o.commutes
    dsimp [correctedLocalLifts] at hc
    abel
  · intro hdifference
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    let o : P.OverlapIndex :=
      { leftObj := Y₁, rightObj := Y₂, common := Z
        leftArrow := f₁, rightArrow := f₂
        left_mem := h₁, right_mem := h₂
        toLeft := g₁, toRight := g₂, commutes := hcomm }
    have ho := congrFun hdifference o
    apply_fun P.kernel.app (op Z) at ho
    rw [P.kernel_localLiftDifferenceAt] at ho
    change _ = P.kernel.app (op Z)
      (P.N.map g₂.op (a f₂ h₂) - P.N.map g₁.op (a f₁ h₁)) at ho
    rw [map_sub, ← P.kernel.naturality_apply, ← P.kernel.naturality_apply] at ho
    dsimp [correctedLocalLifts]
    abel

/-- Correcting by kernel sections preserves the quotient section locally. -/
theorem correctedLocalLifts_project (P : ShortExactLiftProblem S)
    (a : P.C0) {Y : S.category} (f : Y ⟶ P.base) (hf : P.cover f) :
    P.projection.app (op Y) (P.correctedLocalLifts a f hf) =
      P.Q.map f.op P.baseSection := by
  letI : AddCommGroup ((P.E ⋙ forget AddCommGrpCat).obj (op Y)) :=
    inferInstanceAs (AddCommGroup (P.E.obj (op Y)))
  rw [show P.correctedLocalLifts a f hf =
      P.localLifts f hf - P.kernel.app (op Y) (a f hf) from rfl]
  rw [map_sub, P.localLifts_project, P.projection_kernel, sub_zero]

/-- Actual global lifts of the fixed quotient section. -/
def GlobalLift (P : ShortExactLiftProblem S) : Type u :=
  {e : P.E.obj (op P.base) // P.projection.app (op P.base) e = P.baseSection}

/-- Kernel-valued local differences between chosen local lifts and a global lift. -/
def primitiveOfGlobal (P : ShortExactLiftProblem S) (lift : P.GlobalLift) : P.C0 :=
  fun {Y} f hf =>
    (P.kernelEquiv (op Y)).symm
      ⟨P.localLifts f hf - P.E.map f.op lift.1, by
        rw [map_sub, P.localLifts_project]
        rw [← P.projection.naturality_apply f.op, lift.2, sub_self]⟩

/-- A global lift realizes the family corrected by its canonical primitive. -/
theorem globalLift_realizes_correctedLocalLifts
    (P : ShortExactLiftProblem S) (lift : P.GlobalLift) :
    (P.correctedLocalLifts (P.primitiveOfGlobal lift)).IsAmalgamation lift.1 := by
  intro Y f hf
  letI : AddCommGroup ((P.E ⋙ forget AddCommGrpCat).obj (op Y)) :=
    inferInstanceAs (AddCommGroup (P.E.obj (op Y)))
  change P.E.map f.op lift.1 = P.localLifts f hf -
    P.kernel.app (op Y) (P.primitiveOfGlobal lift f hf)
  rw [← P.kernelEquiv_apply]
  change _ = _ - ((P.kernelEquiv (op Y)) ((P.kernelEquiv (op Y)).symm _)).1
  rw [AddEquiv.apply_symm_apply]
  simp

/-- A global lift makes the connecting class zero. -/
theorem connectingClass_eq_zero_of_globalLift
    (P : ShortExactLiftProblem S) (lift : P.GlobalLift) :
    P.connectingClass = 0 := by
  apply P.connectingClass_eq_zero_iff.2
  refine ⟨P.primitiveOfGlobal lift, ?_⟩
  exact (P.correctedLocalLifts_compatible_iff (P.primitiveOfGlobal lift)).1
    (Presieve.is_compatible_of_exists_amalgamation _
      ⟨lift.1, P.globalLift_realizes_correctedLocalLifts lift⟩)

/-- A zero connecting class glues corrected local lifts to an actual global lift. -/
theorem exists_global_of_connectingClass_eq_zero
    (P : ShortExactLiftProblem S) (hzero : P.connectingClass = 0) :
    Nonempty P.GlobalLift := by
  rcases P.connectingClass_eq_zero_iff.1 hzero with ⟨a, ha⟩
  let gluing : AAT.AG.Site.AATGluingData S
      (P.E ⋙ forget AddCommGrpCat) P.cover :=
    { localSections := P.correctedLocalLifts a
      overlapAgreement := (P.correctedLocalLifts_compatible_iff a).2 ha }
  obtain ⟨global, hglobal⟩ :=
    (AAT.AG.Site.AATSheafCondition.descent
      P.eIsSheaf P.cover P.cover_mem).exists_global gluing
  let baseFamily : Presieve.FamilyOfElements
      (P.Q ⋙ forget AddCommGrpCat) (P.cover : Presieve P.base) :=
    fun {Y} f _ => P.Q.map f.op P.baseSection
  have hbaseCompatible : baseFamily.Compatible :=
    Presieve.is_compatible_of_exists_amalgamation baseFamily
      ⟨P.baseSection, by intro Y f hf; rfl⟩
  let qGluing : AAT.AG.Site.AATGluingData S
      (P.Q ⋙ forget AddCommGrpCat) P.cover :=
    { localSections := baseFamily, overlapAgreement := hbaseCompatible }
  have hprojectGlobal : AAT.AG.Site.AATGlobalSectionRealizes qGluing
      (P.projection.app (op P.base) global) := by
    intro Y f hf
    change P.Q.map f.op (P.projection.app (op P.base) global) =
      P.Q.map f.op P.baseSection
    rw [← P.projection.naturality_apply f.op]
    calc
      P.projection.app (op Y) (P.E.map f.op global) =
          P.projection.app (op Y) (P.correctedLocalLifts a f hf) :=
        congrArg _ (hglobal f hf)
      _ = _ := P.correctedLocalLifts_project a f hf
  have hbaseRealizes :
      AAT.AG.Site.AATGlobalSectionRealizes qGluing P.baseSection := by
    intro Y f hf
    rfl
  obtain ⟨q, _hq, hunique⟩ := AAT.AG.Site.AATSheafCondition.descent
    P.qIsSheaf P.cover P.cover_mem qGluing
  exact ⟨⟨global, (hunique _ hprojectGlobal).trans (hunique _ hbaseRealizes).symm⟩⟩

/-- D0: the generated connecting class vanishes exactly when an actual global lift exists. -/
theorem connectingClass_zero_iff_exists_globalLift (P : ShortExactLiftProblem S) :
    P.connectingClass = 0 ↔ Nonempty P.GlobalLift := by
  constructor
  · exact P.exists_global_of_connectingClass_eq_zero
  · rintro ⟨lift⟩
    exact P.connectingClass_eq_zero_of_globalLift lift

/-- Kernel sections act on the actual global-lift fiber. -/
def kernelAction (P : ShortExactLiftProblem S)
    (n : P.N.obj (op P.base)) (lift : P.GlobalLift) : P.GlobalLift :=
  ⟨lift.1 + P.kernel.app (op P.base) n, by
    rw [map_add, lift.2, P.projection_kernel, add_zero]⟩

/-- Difference of two global lifts as the unique kernel section between them. -/
def kernelVSub (P : ShortExactLiftProblem S)
    (left right : P.GlobalLift) : P.N.obj (op P.base) :=
  (P.kernelEquiv (op P.base)).symm
    ⟨left.1 - right.1, by rw [map_sub, left.2, right.2, sub_self]⟩

/-- A nonempty global-lift fiber carries the actual kernel-section `AddTorsor`. -/
noncomputable instance (P : ShortExactLiftProblem S) [Nonempty P.GlobalLift] :
    AddTorsor (P.N.obj (op P.base)) P.GlobalLift where
  vadd := P.kernelAction
  zero_vadd := by
    intro p
    apply Subtype.ext
    simp [kernelAction]
  add_vadd := by
    intro a b p
    apply Subtype.ext
    simp [kernelAction]
    abel
  vsub := P.kernelVSub
  nonempty := inferInstance
  vsub_vadd' := by
    intro left right
    apply Subtype.ext
    change right.1 + P.kernel.app (op P.base) (P.kernelVSub left right) = left.1
    rw [← P.kernelEquiv_apply]
    change right.1 + ((P.kernelEquiv (op P.base))
      ((P.kernelEquiv (op P.base)).symm _)).1 = left.1
    rw [AddEquiv.apply_symm_apply]
    abel
  vadd_vsub' := by
    intro n p
    apply (P.kernelEquiv (op P.base)).injective
    apply Subtype.ext
    rw [P.kernelEquiv_apply]
    change P.kernel.app (op P.base) (P.kernelVSub (P.kernelAction n p) p) =
      P.kernel.app (op P.base) n
    rw [← P.kernelEquiv_apply]
    change ((P.kernelEquiv (op P.base))
      ((P.kernelEquiv (op P.base)).symm _)).1 = _
    rw [AddEquiv.apply_symm_apply]
    dsimp [kernelAction]
    abel

/-- The kernel action is free and transitive on every nonempty global-lift fiber. -/
theorem globalLiftFiber_addTorsor (P : ShortExactLiftProblem S)
    (left right : P.GlobalLift) :
    ∃! n : P.N.obj (op P.base), P.kernelAction n left = right := by
  let difference : AddMonoidHom.ker (P.projection.app (op P.base)).hom :=
    ⟨right.1 - left.1, by rw [map_sub, right.2, left.2, sub_self]⟩
  let n := (P.kernelEquiv (op P.base)).symm difference
  refine ⟨n, ?_, ?_⟩
  · apply Subtype.ext
    change left.1 + P.kernel.app (op P.base) n = right.1
    rw [← P.kernelEquiv_apply]
    change left.1 + ((P.kernelEquiv (op P.base)) n).1 = right.1
    rw [AddEquiv.apply_symm_apply]
    dsimp [difference]
    abel
  · intro m hm
    apply (P.kernelEquiv (op P.base)).injective
    apply Subtype.ext
    rw [P.kernelEquiv_apply, P.kernelEquiv_apply]
    have hm' := congrArg Subtype.val hm
    have hn' : P.kernelAction n left = right := by
      apply Subtype.ext
      change left.1 + P.kernel.app (op P.base) n = right.1
      rw [← P.kernelEquiv_apply]
      change left.1 + ((P.kernelEquiv (op P.base)) n).1 = right.1
      rw [AddEquiv.apply_symm_apply]
      dsimp [difference]
      abel
    have hn'' := congrArg Subtype.val hn'
    dsimp [kernelAction] at hm' hn''
    exact add_left_cancel (hm'.trans hn''.symm)

end ShortExactLiftProblem

end LawGeneratedConormalDescent
end ResearchLean.AG.QualitySurface

#assert_standard_axioms_only ResearchLean.AG.QualitySurface.LawGeneratedConormalDescent
