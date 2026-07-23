import Formal.AG.Site.ContextCategory
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Atom-indexed architectural equation systems

This module formalizes Part I, Definitions 7.1--7.3.  An equation system keeps
the symbolic violation coordinates used by later ideal constructions separate
from the object-dependent residuals whose vanishing defines fulfillment.

Implementation notes: restriction is stored explicitly as ring homomorphisms
with identity and composition laws.  This matches the migration contract of
Issue #3729 and the existing low-level restriction API while yielding the
Mathlib `CommRingCat` presheaf below.  A free predicate and a reverse
legacy-to-equation construction are deliberately absent because neither can
recover the required coordinate data.
-/

namespace AAT.AG

open CategoryTheory
open Opposite

universe u

/-- I.定義7.1: the role of an equation in the selected equation family. -/
inductive EquationRole where
  | required
  | optional
  | derived
  deriving DecidableEq

/--
I.定義7.1: a restriction-compatible Atom-indexed architectural equation system.

`violationCoordinate` is the symbolic family used to generate witness ideals.
`equationResidual` evaluates an equation on an architecture object and is the
only source of the fulfillment predicates defined below.  The structure stores
no ideal-membership, quotient-vanishing, cohomology, comparison, coherence, or
descent conclusion.
-/
structure ArchitecturalEquationSystem
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    (C : Site.ContextPreorderCategory A₀) where
  /-- The selected equation-index type. -/
  Index : Type u
  /-- Required, optional, or derived role of each equation. -/
  role : Index -> EquationRole
  /-- Observable ring at each architecture context. -/
  Observable : Site.ContextCategoryObject C -> Type u
  /-- Each observable carrier is a commutative ring. -/
  observableCommRing : ∀ W : Site.ContextCategoryObject C, CommRing (Observable W)
  /-- Restriction along a readable context morphism. -/
  restrict :
    ∀ {source target : Site.ContextCategoryObject C},
      (source ⟶ target) -> Observable target →+* Observable source
  /-- Restriction along the identity context morphism is the identity. -/
  restrict_id :
    ∀ (W : Site.ContextCategoryObject C) (x : Observable W),
      restrict (𝟙 W) x = x
  /-- Restriction respects composition of context morphisms. -/
  restrict_comp :
    ∀ {W₀ W₁ W₂ : Site.ContextCategoryObject C}
      (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂) (x : Observable W₂),
      restrict (f ≫ g) x = restrict f (restrict g x)
  /-- Symbolic Atom-indexed coordinates used by later witness-ideal generation. -/
  violationCoordinate :
    ∀ W : Site.ContextCategoryObject C, Index -> U.Atom -> Observable W
  /-- Symbolic violation coordinates commute with context restriction. -/
  violationCoordinate_restrict :
    ∀ {source target : Site.ContextCategoryObject C} (f : source ⟶ target)
      (index : Index) (atom : U.Atom),
      restrict f (violationCoordinate target index atom) =
        violationCoordinate source index atom
  /-- Object-dependent residual coordinates used to decide equation fulfillment. -/
  equationResidual :
    ∀ W : Site.ContextCategoryObject C,
      ArchitectureObject U -> Index -> U.Atom -> Observable W
  /-- Object-dependent residuals commute with context restriction. -/
  equationResidual_restrict :
    ∀ {source target : Site.ContextCategoryObject C} (f : source ⟶ target)
      (object : ArchitectureObject U) (index : Index) (atom : U.Atom),
      restrict f (equationResidual target object index atom) =
        equationResidual source object index atom

attribute [instance] ArchitecturalEquationSystem.observableCommRing

namespace ArchitecturalEquationSystem

variable {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
variable {C : Site.ContextPreorderCategory A₀}

/-- I.定義7.2: required-equation membership. -/
def Required (E : ArchitecturalEquationSystem C) (index : E.Index) : Prop :=
  E.role index = EquationRole.required

/-- I.定義7.2: optional-equation membership. -/
def Optional (E : ArchitecturalEquationSystem C) (index : E.Index) : Prop :=
  E.role index = EquationRole.optional

/-- I.定義7.2: derived-equation membership. -/
def Derived (E : ArchitecturalEquationSystem C) (index : E.Index) : Prop :=
  E.role index = EquationRole.derived

/-- I.定義7.2: an equation index whose role is required. -/
abbrev RequiredIndex (E : ArchitecturalEquationSystem C) :=
  {index : E.Index // E.Required index}

/-- II.定義6.1: an Atom-indexed coordinate selected from the equation family. -/
abbrev Coordinate (E : ArchitecturalEquationSystem C) :=
  E.Index × U.Atom

/--
II.定義6.1: an Atom-indexed coordinate whose equation role is required.

The subtype makes required-role selection part of the coordinate type rather
than a detached proposition supplied to the coverage layer.
-/
abbrev RequiredCoordinate (E : ArchitecturalEquationSystem C) :=
  E.RequiredIndex × U.Atom

/--
I.定義7.3: an equation holds on an architecture object when every local,
Atom-indexed residual coordinate vanishes.
-/
def EquationHolds (E : ArchitecturalEquationSystem C) (index : E.Index)
    (object : ArchitectureObject U) : Prop :=
  ∀ (W : Site.ContextCategoryObject C) (atom : U.Atom),
    E.equationResidual W object index atom = 0

/-- I.定義7.3: equation lawfulness is fulfillment of every required equation. -/
def EquationLawful (E : ArchitecturalEquationSystem C)
    (object : ArchitectureObject U) : Prop :=
  ∀ index : E.Index, E.Required index -> E.EquationHolds index object

/-- I.定義7.3: full equation lawfulness includes required, optional, and derived equations. -/
def FullyEquationLawful (E : ArchitecturalEquationSystem C)
    (object : ArchitectureObject U) : Prop :=
  ∀ index : E.Index, E.EquationHolds index object

/-- I.定義7.3: characterization of fulfillment by residual vanishing. -/
theorem equationHolds_iff (E : ArchitecturalEquationSystem C) (index : E.Index)
    (object : ArchitectureObject U) :
    E.EquationHolds index object ↔
      ∀ (W : Site.ContextCategoryObject C) (atom : U.Atom),
        E.equationResidual W object index atom = 0 :=
  Iff.rfl

/-- I.定義7.3: characterization of required equation lawfulness. -/
theorem equationLawful_iff (E : ArchitecturalEquationSystem C)
    (object : ArchitectureObject U) :
    E.EquationLawful object ↔
      ∀ index : E.Index, E.Required index -> E.EquationHolds index object :=
  Iff.rfl

/-- I.定義7.3: characterization of full equation lawfulness. -/
theorem fullyEquationLawful_iff (E : ArchitecturalEquationSystem C)
    (object : ArchitectureObject U) :
    E.FullyEquationLawful object ↔
      ∀ index : E.Index, E.EquationHolds index object :=
  Iff.rfl

/-- I.定義7.3: required lawfulness exposes fulfillment of a selected equation. -/
theorem equationLawful_holds (E : ArchitecturalEquationSystem C)
    {object : ArchitectureObject U} {index : E.Index}
    (h : E.EquationLawful object) (hrequired : E.Required index) :
    E.EquationHolds index object :=
  h index hrequired

/-- I.定義7.3: full lawfulness exposes fulfillment of every equation. -/
theorem fullyEquationLawful_holds (E : ArchitecturalEquationSystem C)
    {object : ArchitectureObject U} (h : E.FullyEquationLawful object)
    (index : E.Index) : E.EquationHolds index object :=
  h index

/--
I.定義7.1: the observable rings and restriction laws form a Mathlib
`CommRingCat`-valued presheaf on the selected context category.
-/
def observablePresheaf (E : ArchitecturalEquationSystem C) :
    (Site.ContextCategoryObject C)ᵒᵖ ⥤ CommRingCat where
  obj W := CommRingCat.of (E.Observable W.unop)
  map f := CommRingCat.ofHom (E.restrict f.unop)
  map_id W := by
    apply CommRingCat.hom_ext
    ext x
    simpa using E.restrict_id W.unop x
  map_comp f g := by
    apply CommRingCat.hom_ext
    ext x
    simpa only [CommRingCat.comp_apply, unop_comp] using
      E.restrict_comp g.unop f.unop x

/-- The generated presheaf has the selected observable ring at each context. -/
@[simp] theorem observablePresheaf_obj (E : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) :
    E.observablePresheaf.obj (op W) = CommRingCat.of (E.Observable W) :=
  rfl

/-- The generated presheaf maps an opposite arrow by the selected restriction. -/
@[simp] theorem observablePresheaf_map_apply (E : ArchitecturalEquationSystem C)
    {source target : Site.ContextCategoryObject C} (f : source ⟶ target)
    (x : E.Observable target) :
    E.observablePresheaf.map f.op x = E.restrict f x :=
  rfl

end ArchitecturalEquationSystem

end AAT.AG
