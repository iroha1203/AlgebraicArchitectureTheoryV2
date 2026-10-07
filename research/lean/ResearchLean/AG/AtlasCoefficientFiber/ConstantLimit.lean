import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Formal.Util.AssertStandardAxioms

/-!
# G-135 A：定数係数の極限と連結成分

## Implementation notes

有限セルのcomma圏の極限を、mathlibの連結成分上の関数として計算する。
極限の普遍性は任意のconeからの線形射を構成して証明する。
係数のuniverseを揃えるためULift ℚを用い、そのdownは元の有理係数への同定である。
compatible sectionsを部分加群として直接表示する案では、各セルの等式条件が
局所成分式に残るため、ここではzigzag商を使ってそれらを成分上の関数へ降ろす。
係数をType 0のℚのまま固定する案は、任意universeのセル圏への同じ極限APIを
妨げるため採らず、ULiftによる同型な係数表示を使う。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CategoryTheory.Limits
universe u v

/-- 同じ有理係数のuniverse表示。 -/
abbrev RationalObject : ModuleCat.{u} ℚ := ModuleCat.of ℚ (ULift.{u} ℚ)

/-- 任意のセル圏における定数有理係数。 -/
def constantRational (J : Type u) [Category.{v} J] : J ⥤ ModuleCat.{u} ℚ :=
  (Functor.const J).obj RationalObject

/-- 定数係数のincidence射は恒等線形射。下流の自然性証明の公開API。 -/
@[simp] theorem constantRational_map {J : Type u} [Category.{v} J] {i j : J}
    (f : i ⟶ j) : (constantRational J).map f = 𝟙 RationalObject := rfl

/-- incidence射に沿い一定な評価はzigzag全体でも一定である。 -/
theorem invariant_of_zigzag {J : Type u} [Category.{v} J] {X : Type u}
    (z : J → X) (hz : ∀ {i j : J}, (i ⟶ j) → z i = z j)
    {i j : J} (h : Zigzag i j) : z i = z j := by
  let F : J ⥤ Discrete X := {
    obj := fun j => Discrete.mk (z j)
    map := fun f => Discrete.eqToHom (hz f) }
  exact eq_of_zigzag X (zigzag_obj_of_zigzag F h)

/-- 連結成分上の関数から各セルの値へ評価するcone。 -/
def constantRationalCone (J : Type u) [Category.{v} J] : Cone (constantRational J) where
  pt := ModuleCat.of ℚ (ConnectedComponents J → ULift.{u} ℚ)
  π := {
    app := fun j => ModuleCat.ofHom (LinearMap.proj (ConnectedComponents.mk j))
    naturality := by
      intro i j f
      simp only [constantRational, Functor.const_obj_map]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (congrArg z (Quotient.sound (Zigzag.of_hom f))).symm }

/-- 定数diagram上の任意coneの評価は各射に沿って一定である。 -/
theorem cone_value_invariant {J : Type u} [Category.{v} J]
    (s : Cone (constantRational J)) (x : s.pt) {i j : J} (f : i ⟶ j) :
    s.π.app i x = s.π.app j x := by
  have h := s.π.naturality f
  simp only [constantRational, Functor.const_obj_map] at h
  exact (congrArg (fun g : s.pt ⟶ RationalObject => g x) h).symm

/-- coneの値を連結成分へ降ろす線形射。 -/
def constantRationalConeLift {J : Type u} [Category.{v} J]
    (s : Cone (constantRational J)) : s.pt ⟶ (constantRationalCone J).pt :=
  ModuleCat.ofHom {
    toFun x := Quotient.lift (fun j => s.π.app j x)
      (fun i j h => invariant_of_zigzag _ (cone_value_invariant s x) h)
    map_add' x y := by
      funext c
      induction c using Quotient.inductionOn
      simp only [Quotient.lift_mk]
      exact map_add _ x y
    map_smul' r x := by
      funext c
      induction c using Quotient.inductionOn
      simp only [Quotient.lift_mk]
      exact map_smul _ r x }

/-- coneの線形liftのセル評価式。 -/
@[simp] theorem constantRationalConeLift_apply {J : Type u} [Category.{v} J]
    (s : Cone (constantRational J)) (x : s.pt) (j : J) :
    constantRationalConeLift s x (ConnectedComponents.mk j) = s.π.app j x := rfl

/-- 連結成分上の関数は定数有理係数diagramの極限である。 -/
def constantRationalConeIsLimit (J : Type u) [Category.{v} J] :
    IsLimit (constantRationalCone J) where
  lift := constantRationalConeLift
  fac s j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  uniq s m hm := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext c
    induction c using Quotient.inductionOn with
    | h j =>
      have h := ModuleCat.hom_ext_iff.mp (hm j)
      exact LinearMap.congr_fun h x

/-- mathlibの極限と連結成分上の関数の標準同型。 -/
def constantRationalLimitIso (J : Type u) [Category.{v} J] :
    limit (constantRational J) ≅ (constantRationalCone J).pt :=
  (limit.isLimit (constantRational J)).conePointUniqueUpToIso (constantRationalConeIsLimit J)

/-- 極限同型の各セルでの評価は標準射影に一致する。 -/
theorem constantRationalLimitIso_eval (J : Type u) [Category.{v} J]
    (x : ↑(limit (constantRational J))) (j : J) :
    (constantRationalLimitIso J).hom x (ConnectedComponents.mk j) =
      limit.π (constantRational J) j x := by
  have h := (limit.isLimit (constantRational J)).conePointUniqueUpToIso_hom_comp
    (constantRationalConeIsLimit J) j
  exact congrArg (fun m : limit (constantRational J) ⟶ RationalObject => m x) h

/-- セル関手に沿う定数有理係数の順像。comma圏の極限から独立生成する。 -/
def coefficientPushforward {J K : Type u} [Category.{u} J] [Category.{u} K]
    (φ : J ⥤ K) : K ⥤ ModuleCat.{u} ℚ :=
  φ.pointwiseRightKanExtension (constantRational J)

/-- 順像のcounitは、恒等incidenceを持つcomma対象における評価である。 -/
def coefficientCounit {J K : Type u} [Category.{u} J] [Category.{u} K]
    (φ : J ⥤ K) : φ ⋙ coefficientPushforward φ ⟶ constantRational J :=
  φ.pointwiseRightKanExtensionCounit (constantRational J)

/-- 順像はmathlibの右Kan拡張の普遍性を満たす。 -/
instance coefficientIsRightKanExtension {J K : Type u} [Category.{u} J] [Category.{u} K]
    (φ : J ⥤ K) : (coefficientPushforward φ).IsRightKanExtension (coefficientCounit φ) :=
  inferInstanceAs ((φ.pointwiseRightKanExtension (constantRational J)).IsRightKanExtension
    (φ.pointwiseRightKanExtensionCounit (constantRational J)))

/-- 順像のセル値をcomma圏の連結成分上の関数へ同定する。 -/
def coefficientCellIso {J K : Type u} [Category.{u} J] [Category.{u} K]
    (φ : J ⥤ K) (k : K) :
    (coefficientPushforward φ).obj k ≅ (constantRationalCone (StructuredArrow k φ)).pt :=
  constantRationalLimitIso (StructuredArrow k φ)

/-- 順像のセル同型は、comma対象に対する標準極限射影を評価する。 -/
theorem coefficientCellIso_eval {J K : Type u} [Category.{u} J] [Category.{u} K]
    (φ : J ⥤ K) (k : K) (x : (coefficientPushforward φ).obj k)
    (j : StructuredArrow k φ) :
    (coefficientCellIso φ k).hom x (ConnectedComponents.mk j) =
      limit.π (StructuredArrow.proj k φ ⋙ constantRational J) j x :=
  constantRationalLimitIso_eval (StructuredArrow k φ) x j

/-- counitの細セル評価は恒等comma対象の成分での評価に一致する。 -/
theorem coefficientCounit_eval {J K : Type u} [Category.{u} J] [Category.{u} K]
    (φ : J ⥤ K) (j : J) (x : (coefficientPushforward φ).obj (φ.obj j)) :
    (coefficientCounit φ).app j x =
      (coefficientCellIso φ (φ.obj j)).hom x
        (ConnectedComponents.mk (StructuredArrow.mk (𝟙 (φ.obj j)))) := by
  rw [coefficientCellIso_eval]
  rfl

/-- 順像のincidence射はcomma対象の前合成による関数の制限である。 -/
theorem coefficientPushforward_map_eval {J K : Type u} [Category.{u} J] [Category.{u} K]
    (φ : J ⥤ K) {k l : K} (f : k ⟶ l) (x : (coefficientPushforward φ).obj k)
    (j : StructuredArrow l φ) :
    (coefficientCellIso φ l).hom ((coefficientPushforward φ).map f x)
      (ConnectedComponents.mk j) =
    (coefficientCellIso φ k).hom x
      (ConnectedComponents.mk ((StructuredArrow.map f).obj j)) := by
  rw [coefficientCellIso_eval, coefficientCellIso_eval]
  have h : (coefficientPushforward φ).map f ≫
      limit.π (StructuredArrow.proj l φ ⋙ constantRational J) j =
      limit.π (StructuredArrow.proj k φ ⋙ constantRational J)
        ((StructuredArrow.map f).obj j) := by
    simp [coefficientPushforward, Functor.pointwiseRightKanExtension_map]
  exact congrArg (fun m : (coefficientPushforward φ).obj k ⟶ RationalObject => m x) h

/-- 任意のcomma成分で読む右Kan incidence射。対象代表元への依存をquotientで消す。 -/
theorem coefficientPushforward_map_component_eval {J K : Type u} [Category.{u} J] [Category.{u} K]
    (φ : J ⥤ K) {k l : K} (f : k ⟶ l) (x : (coefficientPushforward φ).obj k)
    (c : CategoryTheory.ConnectedComponents (StructuredArrow l φ)) :
    (coefficientCellIso φ l).hom ((coefficientPushforward φ).map f x) c =
    (coefficientCellIso φ k).hom x ((StructuredArrow.map f).mapConnectedComponents c) := by
  induction c using Quotient.inductionOn with
  | h j =>
    rw [Functor.mapConnectedComponents_mk]
    exact coefficientPushforward_map_eval φ f x j

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.RationalObject
#print axioms AAT.AG.AtlasCoefficientFiber.constantRational
#print axioms AAT.AG.AtlasCoefficientFiber.invariant_of_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.constantRationalCone
#print axioms AAT.AG.AtlasCoefficientFiber.cone_value_invariant
#print axioms AAT.AG.AtlasCoefficientFiber.constantRationalConeLift
#print axioms AAT.AG.AtlasCoefficientFiber.constantRationalConeLift_apply
#print axioms AAT.AG.AtlasCoefficientFiber.constantRationalConeIsLimit
#print axioms AAT.AG.AtlasCoefficientFiber.constantRationalLimitIso
#print axioms AAT.AG.AtlasCoefficientFiber.constantRationalLimitIso_eval
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientPushforward
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCounit
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientIsRightKanExtension
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCellIso
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCellIso_eval
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientPushforward_map_eval
#print axioms AAT.AG.AtlasCoefficientFiber.constantRational_map
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCounit_eval
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientPushforward_map_component_eval
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
