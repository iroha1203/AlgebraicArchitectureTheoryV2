import Formal.AG.Evolution.Bootstrap

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v

/-!
PRD-9 R1 / AC2 selected trace category surface.

The trace category is selected data. Objects are selected time points,
operation stages, or abstract event states; arrows are selected transitions.
No claim is made about transitions outside the chosen profile.
-/

/--
IX.定義2.1: selected trace category `Tr_E`.

This is a small category-like interface used by Part IX. It is intentionally
profile-relative and does not manufacture external runtime events.
-/
structure TraceCategory where
  Obj : Type u
  Hom : Obj -> Obj -> Type v
  id : (t : Obj) -> Hom t t
  comp : {t₀ t₁ t₂ : Obj} -> Hom t₀ t₁ -> Hom t₁ t₂ -> Hom t₀ t₂
  id_comp :
    ∀ {t₀ t₁ : Obj} (f : Hom t₀ t₁), comp (id t₀) f = f
  comp_id :
    ∀ {t₀ t₁ : Obj} (f : Hom t₀ t₁), comp f (id t₁) = f
  assoc :
    ∀ {t₀ t₁ t₂ t₃ : Obj} (f : Hom t₀ t₁) (g : Hom t₁ t₂)
      (h : Hom t₂ t₃), comp (comp f g) h = comp f (comp g h)

namespace TraceCategory

/-- IX.定義2.1: expose the selected identity transition. -/
def selectedIdentity (Tr : TraceCategory.{u, v}) (t : Tr.Obj) :
    Tr.Hom t t :=
  Tr.id t

/-- IX.定義2.1: expose selected transition composition. -/
def selectedComposition (Tr : TraceCategory.{u, v})
    {t₀ t₁ t₂ : Tr.Obj} (f : Tr.Hom t₀ t₁) (g : Tr.Hom t₁ t₂) :
    Tr.Hom t₀ t₂ :=
  Tr.comp f g

/-- IX.定義2.1: left identity law for selected transitions. -/
theorem id_comp_holds (Tr : TraceCategory.{u, v})
    {t₀ t₁ : Tr.Obj} (f : Tr.Hom t₀ t₁) :
    Tr.comp (Tr.id t₀) f = f :=
  Tr.id_comp f

/-- IX.定義2.1: right identity law for selected transitions. -/
theorem comp_id_holds (Tr : TraceCategory.{u, v})
    {t₀ t₁ : Tr.Obj} (f : Tr.Hom t₀ t₁) :
    Tr.comp f (Tr.id t₁) = f :=
  Tr.comp_id f

/-- IX.定義2.1: associativity law for selected transitions. -/
theorem assoc_holds (Tr : TraceCategory.{u, v})
    {t₀ t₁ t₂ t₃ : Tr.Obj} (f : Tr.Hom t₀ t₁) (g : Tr.Hom t₁ t₂)
    (h : Tr.Hom t₂ t₃) :
    Tr.comp (Tr.comp f g) h = Tr.comp f (Tr.comp g h) :=
  Tr.assoc f g h

/--
IX.R1: finite trace category regime.

The finite regime records a selected finite object set, finite selected hom
sets, and closure of the certified finite subfamily under identity and
composition. `Hom` is the profile's transition interface; `selectedArrow`
marks the arrows admitted by this finite regime.
-/
structure FiniteRegime (Tr : TraceCategory.{u, v}) where
  finiteObj : Finite Tr.Obj
  finiteHom : ∀ t₀ t₁ : Tr.Obj, Finite (Tr.Hom t₀ t₁)
  selectedArrow : ∀ {t₀ t₁ : Tr.Obj}, Tr.Hom t₀ t₁ -> Prop
  idSelected : ∀ t : Tr.Obj, selectedArrow (Tr.id t)
  compSelected :
    ∀ {t₀ t₁ t₂ : Tr.Obj} {f : Tr.Hom t₀ t₁} {g : Tr.Hom t₁ t₂},
      selectedArrow f -> selectedArrow g -> selectedArrow (Tr.comp f g)

namespace FiniteRegime

/-- IX.R1: the selected trace object type is finite. -/
theorem object_finite {Tr : TraceCategory.{u, v}} (R : FiniteRegime Tr) :
    Finite Tr.Obj :=
  R.finiteObj

/-- IX.R1: each selected trace hom type is finite. -/
theorem hom_finite {Tr : TraceCategory.{u, v}} (R : FiniteRegime Tr)
    (t₀ t₁ : Tr.Obj) : Finite (Tr.Hom t₀ t₁) :=
  R.finiteHom t₀ t₁

/-- IX.R1: identity transitions are inside the selected finite regime. -/
theorem id_selected {Tr : TraceCategory.{u, v}} (R : FiniteRegime Tr)
    (t : Tr.Obj) : R.selectedArrow (Tr.id t) :=
  R.idSelected t

/-- IX.R1: selected transitions are closed under selected composition. -/
theorem comp_selected {Tr : TraceCategory.{u, v}} (R : FiniteRegime Tr)
    {t₀ t₁ t₂ : Tr.Obj} {f : Tr.Hom t₀ t₁} {g : Tr.Hom t₁ t₂}
    (hf : R.selectedArrow f) (hg : R.selectedArrow g) :
    R.selectedArrow (Tr.comp f g) :=
  R.compSelected hf hg

end FiniteRegime

end TraceCategory

end Evolution
end AAT.AG
