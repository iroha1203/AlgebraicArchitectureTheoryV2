import Formal.SHIGURE.Part2.Copying.ConstantScheme
import Formal.SHIGURE.Part2.Realizations.PositiveSheaves
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over

/-!
# Constant carriers on the relative Zariski site

The constant carrier sheaf in Definition 4.1 is the sheaf of points of the
constant scheme from Construction 4.2. Its sections are locally constant
state functions of the test scheme by Theorem 4.3.

## Implementation notes

The relative points are obtained by imposing the structure-map equation on
an absolute representable sheaf. This uses subcanonicity on the big Zariski
site directly. A gluing proof for locally constant functions would repeat
the representable sheaf property and the constant-scheme point equivalence.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable (S : Scheme.{u})

/-- The Zariski sheaves on the category of schemes over a coefficient scheme. -/
abbrev ZariskiSheaf :=
  Sheaf (Scheme.zariskiTopology.over S) (Type u)

/-- Restrict an absolute representable sheaf to the relative test category. -/
private def absolutePoints (X : Scheme.{u}) : ZariskiSheaf S :=
  (Scheme.zariskiTopology.overPullback (Type u) S).obj (Scheme.zariskiTopology.yoneda.obj X)

/-- The previously specified structure morphism of every test scheme is a natural section. -/
private def structurePoint (X : Scheme.{u}) : absolutePoints S X ⟶ absolutePoints S S :=
  ⟨{ app := fun T => ↾fun _ => T.unop.hom
     naturality := by
       intro U V f
       ext p
       exact (Over.w f.unop).symm }⟩

/-- The points of a relative scheme form a sheaf on the relative Zariski site. -/
def relativePoints (Y : Over S) : ZariskiSheaf S :=
  let mapped := (Scheme.zariskiTopology.overPullback (Type u) S).map
    (Scheme.zariskiTopology.yoneda.map Y.hom)
  (SheafPredicate.equal mapped (structurePoint S Y.left)).toSheaf

/-- Relative sections are precisely morphisms over the chosen base scheme. -/
def relativePointsEquiv (T Y : Over S) : (relativePoints S Y).val.obj (op T) ≃ (T ⟶ Y) where
  toFun h := Over.homMk h.val h.property
  invFun f := ⟨f.left, Over.w f⟩
  left_inv _ := rfl
  right_inv _ := Over.OverMorphism.ext rfl

/-- The presheaf of locally constant sections of a set-valued state carrier. -/
private def labelPresheaf (X : Type u) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := LocallyConstant T.unop.left X
  map f := ↾LocallyConstant.comap ⟨f.unop.left, f.unop.left.continuous⟩
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The point equivalence identifies restriction of relative points with restriction of their labels. -/
private def relativeLabelIso (X : Type u) :
    (relativePoints S (constantSchemeOver S X)).val ≅ labelPresheaf S X :=
  NatIso.ofComponents
    (fun T => ((relativePointsEquiv S T.unop (constantSchemeOver S X)).trans
      (constantPointLabelsEquiv T.unop X)).toIso)
    (by
      intro T U f
      ext p
      rfl)

/-- The constant state sheaf is realized as locally constant functions on all test schemes. -/
def constantCarrier (X : Type u) : ZariskiSheaf S where
  val := labelPresheaf S X
  cond := (Presheaf.isSheaf_of_iso_iff (J := Scheme.zariskiTopology.over S) (relativeLabelIso S X)).mp
    (relativePoints S (constantSchemeOver S X)).cond

/-- A native state map acts on the corresponding constant sheaves by postcomposition. -/
def constantCarrierMap {X Y : Type u} (f : X → Y) : constantCarrier S X ⟶ constantCarrier S Y :=
  ⟨{ app := fun _ => ↾LocallyConstant.map f
     naturality := by
       intro T U i
       ext p
       rfl }⟩

end SHIGURE.Copying
