import Formal.SHIGURE.Part2.Recovery.CopyingDescent

/-!
# Descent of constant models and the diagonal condition

Constant chart structures produce effective descent data on any open
cover. A two-label chart equipped with the flip as its self-transition
shows that an overlap isomorphism alone need not satisfy the unit law.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} {T : Theory.{u}}

private def constantCharts (C : Scheme.OpenCover.{u} S) (M : Model T) : StructureCharts C T.signature where
  chart i := constantStructure (C.X i) M.obj
  transition i j := Iso.refl (constantStructure (CoverOverlap C i j) M.obj)

private theorem constantCharts_coherent (C : Scheme.OpenCover.{u} S) (M : Model T) :
    (constantCharts C M).Coherent := by
  intro s
  have h {i j : C.I₀} {V : Over S} (a : CoverLift C i V) (b : CoverLift C j V)
      (x : LocallyConstant V.left (M.obj.carrier s)) :
      ((constantCharts C M).carrierCharts s).transitionAt a b x = x := by
    apply LocallyConstant.ext
    intro p
    rfl
  exact ⟨fun a x => h a a x, fun a b c x => by rw [h a b x, h b c x, h a c x]⟩

private theorem constantCharts_models (C : Scheme.OpenCover.{u} S) (M : Model T) (i : C.I₀) :
    zariskiCopyingProperty T (C.X i) ((constantCharts C M).chart i) :=
  ⟨isZariskiSplit_constant T M, fun l => constantStructure_holdsLaw M.obj (T.law l) (M.property l)⟩

/-- Descent applied to a constant model and any open cover. -/
def constantModelDescent (C : Scheme.OpenCover.{u} S) (M : Model T) :
    (zariskiCopyingProperty T S).FullSubcategory :=
  StructureCharts.glueModel (constantCharts_coherent C M) (constantCharts_models C M)

/-- The effective descent of a constant model recovers it on each chart. -/
def constantModelDescent_restrict (C : Scheme.OpenCover.{u} S) (M : Model T) (i : C.I₀) :
    (restrictCopyingCoefficients T (C.f i)).obj (constantModelDescent C M) ≅
      ⟨constantStructure (C.X i) M.obj, constantCharts_models C M i⟩ :=
  StructureCharts.glueModelRestrictIso (constantCharts_coherent C M) (constantCharts_models C M) i

private def boolFlip (S : Scheme.{0}) : constantCarrier S Bool ≅ constantCarrier S Bool where
  hom := constantCarrierMap S (! ·)
  inv := constantCarrierMap S (! ·)
  hom_inv_id := by
    ext T f
    apply LocallyConstant.ext
    intro p
    exact Bool.not_not ((show LocallyConstant T.unop.left Bool from f) p)
  inv_hom_id := by
    ext T f
    apply LocallyConstant.ext
    intro p
    exact Bool.not_not ((show LocallyConstant T.unop.left Bool from f) p)

private def boolFlipCharts (S : Scheme.{0}) : SheafCharts (Scheme.coverOfIsIso (P := @IsOpenImmersion) (𝟙 S)) where
  chart _ := constantCarrier S Bool
  transition i j := boolFlip (CoverOverlap (Scheme.coverOfIsIso (P := @IsOpenImmersion) (𝟙 S)) i j)

/-- The flip on a nonempty identity chart fails the diagonal condition for descent. -/
theorem boolFlipCharts_not_coherent (S : Scheme.{0}) [Nonempty S] : ¬ (boolFlipCharts S).Coherent := by
  intro h
  let C := Scheme.coverOfIsIso (P := @IsOpenImmersion) (𝟙 S)
  let V := Over.mk (𝟙 S)
  let i : C.I₀ := PUnit.unit
  let a : CoverLift C i V := ⟨𝟙 S, Category.id_comp _⟩
  let x : LocallyConstant S Bool := LocallyConstant.const S false
  let p : S := Classical.choice inferInstance
  have h' := congrArg (fun g : LocallyConstant S Bool => g p) (h.unit a x)
  change true = false at h'
  cases h'

private def duplicateCover (S : Scheme.{0}) : Scheme.OpenCover S :=
  Scheme.Cover.mkOfCovers Bool (fun _ => S) (fun _ => 𝟙 S) (fun x => ⟨false, x, rfl⟩)

private def duplicateArrows (S : Scheme.{0}) (i : (duplicateCover S).I₀) :
    (Scheme.zariskiTopology.overMapPullback (Type 0) ((duplicateCover S).f i)).obj (constantCarrier S Bool) ⟶
      (Scheme.zariskiTopology.overMapPullback (Type 0) ((duplicateCover S).f i)).obj (constantCarrier S Bool) :=
  if (show Bool from i) = true then (boolFlip S).hom else 𝟙 (constantCarrier S Bool)

/-- The identity and the flip do not agree on the overlap of two copies of a nonempty chart. -/
theorem duplicateArrows_not_agree (S : Scheme.{0}) [Nonempty S] :
    ¬ SheafArrowsAgreeOnOverlaps (duplicateArrows S) := by
  intro h
  let C := duplicateCover S
  let T := Over.mk (𝟙 S)
  let p : S ⟶ CoverOverlap C false true :=
    pullback.lift (𝟙 S) (𝟙 S) rfl
  have hp : p ≫ pullback.fst (C.f false) (C.f true) ≫ C.f false = T.hom := by
    rw [← Category.assoc]
    change pullback.lift (𝟙 S) (𝟙 S) rfl ≫ pullback.fst (𝟙 S) (𝟙 S) ≫ 𝟙 S = 𝟙 S
    rw [pullback.lift_fst_assoc, Category.id_comp]
  let x : LocallyConstant S Bool := LocallyConstant.const S false
  let z : S := Classical.choice inferInstance
  have he := congrArg (fun y : LocallyConstant S Bool => y z) (h false true T p hp x)
  change false = true at he
  cases he

private def constantLabelCharts (S : Scheme.{0}) : SheafCharts (duplicateCover S) where
  chart _ := constantCarrier S Bool
  transition _ _ := Iso.refl _

private abbrev testContext : List Unit := []

private def differentPredicates (S : Scheme.{0}) (i : (duplicateCover S).I₀) :
    SheafPredicate ((SheafCharts.tuples (fun _ : Unit => constantLabelCharts S) testContext).chart i) :=
  (constantPredicate S (if (show Bool from i) = true then
    (∅ : Set (Assignment (fun _ : Unit => Bool) testContext)) else Set.univ)).preimage
      (constantTupleMap S (fun _ : Unit => Bool) testContext)

/-- The full and empty predicates on a repeated nonempty chart fail to match under the identity. -/
theorem differentPredicates_not_preserved (S : Scheme.{0}) [Nonempty S] :
    ¬ SheafCharts.PreservesPredicates (fun _ : Unit => constantLabelCharts S) testContext (differentPredicates S) := by
  intro h
  let C := duplicateCover S
  let p : S ⟶ CoverOverlap C false true := pullback.lift (𝟙 S) (𝟙 S) rfl
  let U := Over.mk p
  let W := (Over.map (pullback.fst (C.f false) (C.f true))).obj U
  let V := (Over.map (pullback.snd (C.f false) (C.f true))).obj U
  let x : Assignment (fun _ : Unit => LocallyConstant S Bool) testContext := ⟨fun i => nomatch i⟩
  have hx : x ∈ (restrictPredicate (pullback.fst (C.f false) (C.f true)) (differentPredicates S false)).carrier.obj
      (op U) :=
    (mem_constantPredicate S Set.univ (op W) ((constantTupleMap S (fun _ : Unit => Bool) testContext).val.app
      (op W) x)).mpr (fun _ => Set.mem_univ _)
  have he := h.hom false true (op U) hx
  let y := ((SheafCharts.tuples (fun _ : Unit => constantLabelCharts S) testContext).transition false true).hom.val.app
    (op U) x
  have ha := (mem_constantPredicate S (∅ : Set (Assignment (fun _ : Unit => Bool) testContext)) (op V)
    ((constantTupleMap S (fun _ : Unit => Bool) testContext).val.app (op V) y)).mp he
  exact ha (Classical.choice (inferInstance : Nonempty S))

end SHIGURE.Copying
