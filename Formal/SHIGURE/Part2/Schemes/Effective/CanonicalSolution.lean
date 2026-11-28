import Formal.SHIGURE.Part2.Schemes.Effective.TestComparison

/-! # The canonical local solution on a component of a descent datum -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v

private theorem constantComponentHom {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {ι κ : Type v} {X : C} {U : ι → C} {V : κ → C}
    (f : ∀ i, U i ⟶ X) (i : ι) (f' : ∀ j, V j ⟶ U i)
    (D : F.DescentData f) {T : C} (q : T ⟶ U i) {j k : κ}
    (a : T ⟶ V j) (b : T ⟶ V k) (ha : a ≫ f' j = q) (hb : b ≫ f' k = q) :
    DescentData.pullFunctorObjHom (F := F) (f := f) (f' := f') (p := f i)
      (α := fun _ => i) (p' := f') (fun _ => rfl) D q a b ha hb =
      ((F.toDescentData f').obj (D.obj i)).hom q a b ha hb := by
  rw [DescentData.pullFunctorObjHom_eq (fun _ => rfl) D q a b (q ≫ f i) q q
    ha hb rfl ha hb, D.hom_self (q ≫ f i) q rfl]
  simp only [Category.id_comp]
  rfl

/-- Restricting a descent datum through a fixed component gives the
canonical comparison of that component. This calculation is independent of
schemes and quasi-coherent modules. -/
private def constantComponentComparison {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {ι κ : Type v} {X : C} {U : ι → C} {V : κ → C}
    (f : ∀ i, U i ⟶ X) (i : ι) (f' : ∀ j, V j ⟶ U i)
    (D : F.DescentData f) :
    (F.toDescentData f').obj (D.obj i) ≅
      (DescentData.pullFunctor F (p := f i) (f' := f') (α := fun _ => i)
        (p' := f') (fun _ => rfl)).obj D := by
  let w (j : κ) : f' j ≫ f i = f' j ≫ f i := rfl
  let H := DescentData.pullFunctor F (p := f i) (f' := f')
    (α := fun _ => i) (p' := f') w
  refine DescentData.isoMk (F := F) (f := f')
    (D₁ := (F.toDescentData f').obj (D.obj i)) (D₂ := H.obj D)
    (fun j => Iso.refl ((F.map (f' j).op.toLoc).toFunctor.obj (D.obj i))) ?_
  intro T q j k a b ha hb
  subst q
  change (F.map a.op.toLoc).toFunctor.map (𝟙 _) ≫ (H.obj D).hom (a ≫ f' j) a b rfl hb =
    ((F.toDescentData f').obj (D.obj i)).hom (a ≫ f' j) a b rfl hb ≫
      (F.map b.op.toLoc).toFunctor.map (𝟙 _)
  calc
    _ = (H.obj D).hom (a ≫ f' j) a b rfl hb := by
      rw [(F.map a.op.toLoc).toFunctor.map_id]
      exact Category.id_comp _
    _ = ((F.toDescentData f').obj (D.obj i)).hom (a ≫ f' j) a b rfl hb := by
      dsimp only [H, DescentData.pullFunctor_obj, DescentData.pullFunctorObj_hom]
      exact constantComponentHom (F := F) f i f' D (a ≫ f' j) a b rfl hb
    _ = _ := by
      rw [(F.map b.op.toLoc).toFunctor.map_id]
      exact (Category.comp_id _).symm

private theorem constantComponentComparison_hom {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {ι κ : Type v} {X : C} {U : ι → C} {V : κ → C}
    (f : ∀ i, U i ⟶ X) (i : ι) (f' : ∀ j, V j ⟶ U i)
    (D : F.DescentData f) (j : κ) :
    (constantComponentComparison (F := F) f i f' D).hom.hom j =
      𝟙 ((F.map (f' j).op.toLoc).toFunctor.obj (D.obj i)) := rfl

private theorem constantComponentTransition {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {ι : Type v} {X : C} {U V : ι → C} (f : ∀ i, U i ⟶ X) (i : ι)
    (f' : ∀ j, V j ⟶ U i) (p' : ∀ j, V j ⟶ U j)
    (w' : ∀ j, p' j ≫ f j = f' j ≫ f i) (D : F.DescentData f) (j : ι) :
    ((constantComponentComparison (F := F) f i f' D ≪≫
      (DescentData.pullFunctorIso F (f := f) (p := f i) (f' := f')
        (α := fun _ => i) (p' := f') (fun _ => rfl) (β := id) (p'' := p') w').app D).hom).hom j =
      D.hom (f' j ≫ f i) (f' j) (p' j) rfl (w' j) := by
  change (constantComponentComparison (F := F) f i f' D).hom.hom j ≫
    D.hom (f' j ≫ f i) (f' j) (p' j) rfl (w' j) = _
  rw [constantComponentComparison_hom]
  exact Category.id_comp _

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X : Scheme.{u}} {cover : FppfCover.{u,v} X}
  (D : FppfModuleDescentData cover) (i : cover.I₀)

set_option maxHeartbeats 750000 in
/-- On a component, the module already given by the datum solves the
restricted descent problem. The comparison is built from the original
transition isomorphisms on the actual pullbacks. -/
def canonicalComponentSolution : EffectiveLocalSolution D (cover.f i) := by
  let C := cover.pullback₁ (cover.f i)
  let w (j : C.I₀) : C.f j ≫ cover.f i = C.f j ≫ cover.f i := rfl
  let H := DescentData.pullFunctor Q (p := cover.f i) (f' := C.f)
    (α := fun _ => i) (p' := fun j => C.f j) w
  have identityChart : (fppfModuleComparison C).obj (D.obj i) ≅ H.obj D :=
    constantComponentComparison (F := Q) cover.f i C.f D
  let switch := DescentData.pullFunctorIso Q w (cover.pullbackHom_map (cover.f i))
  exact ⟨D.obj i, identityChart ≪≫ switch.app D⟩

/-- On a pulled-back component the canonical solution's comparison is the
transition already present in the original datum. -/
theorem canonicalComponent_chartHom (j : cover.I₀) :
    (canonicalComponentSolution D i).chartHom j =
      D.hom ((cover.pullback₁ (cover.f i)).f j ≫ cover.f i)
        ((cover.pullback₁ (cover.f i)).f j) (cover.pullbackHom (cover.f i) j)
        rfl (cover.pullbackHom_map (cover.f i) j) :=
  constantComponentTransition (F := Q) cover.f i (cover.pullback₁ (cover.f i)).f
    (fun j => cover.pullbackHom (cover.f i) j) (cover.pullbackHom_map (cover.f i)) D j

/-- Evaluating the canonical component solution on a test chart recovers the
corresponding original descent transition. -/
theorem canonicalComponent_testHom {W : Scheme.{u}} {j : cover.I₀}
    (a : W ⟶ cover.X i) (b : W ⟶ cover.X j) (e : a ≫ cover.f i = b ≫ cover.f j) :
    (canonicalComponentSolution D i).testHom a b e = D.hom (a ≫ cover.f i) a b rfl e.symm := by
  rw [(canonicalComponentSolution D i).testHom_eq_pull, canonicalComponent_chartHom]
  have fstEq : pullback.lift a b e ≫ (cover.pullback₁ (cover.f i)).f j = a :=
    pullback.lift_fst _ _ _
  exact D.pullHom_hom (pullback.lift a b e)
    ((cover.pullback₁ (cover.f i)).f j ≫ cover.f i) (a ≫ cover.f i)
    (by rw [← Category.assoc, fstEq])
    ((cover.pullback₁ (cover.f i)).f j) (cover.pullbackHom (cover.f i) j)
    rfl (cover.pullbackHom_map (cover.f i) j) a b
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end

end SHIGURE.SchemeDescent
