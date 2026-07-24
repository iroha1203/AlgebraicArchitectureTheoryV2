import Formal.AG.SemanticRepair.Saga.Cover
import Formal.AG.Cohomology.CochainComparison

/-!
# Part X §2: increasing three-term Čech complex over `Int_{≤2}(𝒰)`

* `IntersectionCoefficientData`: abelian-group coefficient data on the
  intersection diagram, with restriction along generating faces only and the
  two-path coherence law (Part X Definition 6.1 quantification, fixed by R0).
* `SitePresheafData`: sitewide abelian-group presheaf data (the carrier shape
  of generated coefficients such as `M_sem`), with its restriction
  `onIntersections` to the intersection diagram.
* `incComplex`: Part X Definition 2.1 three-term complex `C⁰/C¹/C²` with
  `δ⁰/δ¹` over increasing kept intersections, Lemma 2.2 (`δ¹δ⁰ = 0`), and the
  cover-relative `H¹` of Definition 2.3 obtained through the semantic-free
  `Cohomology.AdditiveThreeTermComplex` hub.

The comparison with the Part IV full ordered-tuple complex (Lemma 2.1A) lives
in `Formal.AG.SemanticRepair.Saga.OrderedComparison`.
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

open CategoryTheory

universe u w

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}

/--
X.定義6.1 の座(R0 §4.2): `Int_{≤2}(𝒰)` 上の可換群値係数データ。
restriction は生成 face に沿ってだけ持ち、`restrict_coh` は triple から chart への
2経路一致(presheaf functoriality の `Int_{≤2}` での実体)である。
-/
structure IntersectionCoefficientData (𝒰 : MonomorphicOrderedCover S) where
  carrier : IntersectionIndex 𝒰 -> Type w
  addCommGroup : ∀ σ, AddCommGroup (carrier σ)
  restrict : ∀ {σ τ : IntersectionIndex 𝒰}, Face 𝒰 σ τ -> carrier τ →+ carrier σ
  restrict_coh :
      ∀ {σ τ₁ τ₂ ρ : IntersectionIndex 𝒰}
        (f₁ : Face 𝒰 σ τ₁) (g₁ : Face 𝒰 τ₁ ρ)
        (f₂ : Face 𝒰 σ τ₂) (g₂ : Face 𝒰 τ₂ ρ) (x : carrier ρ),
        restrict f₁ (restrict g₁ x) = restrict f₂ (restrict g₂ x)

attribute [instance] IntersectionCoefficientData.addCommGroup

/--
site 全域の可換群値 presheaf データ。`M_sem` など生成係数の担体の形であり、
明示 restriction + 恒等・合成則のイディオム(`Equation/Basic` と同形)を使う。
-/
structure SitePresheafData (S : Site.AATSite A) where
  carrier : S.category -> Type w
  addCommGroup : ∀ V, AddCommGroup (carrier V)
  restrict : ∀ {V' V : S.category}, (V' ⟶ V) -> carrier V →+ carrier V'
  restrict_id : ∀ (V : S.category) (x : carrier V), restrict (𝟙 V) x = x
  restrict_comp :
      ∀ {V'' V' V : S.category} (f : V'' ⟶ V') (g : V' ⟶ V) (x : carrier V),
        restrict (f ≫ g) x = restrict f (restrict g x)

attribute [instance] SitePresheafData.addCommGroup

namespace SitePresheafData

variable (F : SitePresheafData.{u, w} S)

/--
site 全域 presheaf の `Int_{≤2}(𝒰)` への制限。2経路一致は thin category の
射の一意性(`Subsingleton`)と合成則から従う。
-/
def onIntersections (𝒰 : MonomorphicOrderedCover S) :
    IntersectionCoefficientData.{u, w} 𝒰 where
  carrier σ := F.carrier σ.ctx
  addCommGroup σ := F.addCommGroup σ.ctx
  restrict f := F.restrict f.hom
  restrict_coh {σ τ₁ τ₂ ρ} f₁ g₁ f₂ g₂ x := by
    have h₁ : F.restrict f₁.hom (F.restrict g₁.hom x) =
        F.restrict (f₁.hom ≫ g₁.hom) x := (F.restrict_comp f₁.hom g₁.hom x).symm
    have h₂ : F.restrict f₂.hom (F.restrict g₂.hom x) =
        F.restrict (f₂.hom ≫ g₂.hom) x := (F.restrict_comp f₂.hom g₂.hom x).symm
    rw [h₁, h₂, Subsingleton.elim (f₁.hom ≫ g₁.hom) (f₂.hom ≫ g₂.hom)]

@[simp]
theorem onIntersections_carrier (𝒰 : MonomorphicOrderedCover S)
    (σ : IntersectionIndex 𝒰) :
    (F.onIntersections 𝒰).carrier σ = F.carrier σ.ctx :=
  rfl

@[simp]
theorem onIntersections_restrict (𝒰 : MonomorphicOrderedCover S)
    {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ) (x : F.carrier τ.ctx) :
    (F.onIntersections 𝒰).restrict f x = F.restrict f.hom x :=
  rfl

end SitePresheafData

variable {𝒰 : MonomorphicOrderedCover S}

/-- X.定義2.1: `C⁰(𝒰, Q) = ∏_i Q(U_i)`。 -/
abbrev Cochain0 (Q : IntersectionCoefficientData.{u, w} 𝒰) : Type (max u w) :=
  ∀ i : 𝒰.Index, Q.carrier (.chart i)

/-- X.定義2.1: `C¹(𝒰, Q) = ∏_{i<j, 非省略} Q(U_ij)`。 -/
abbrev Cochain1 (Q : IntersectionCoefficientData.{u, w} 𝒰) : Type (max u w) :=
  ∀ p : KeptPair 𝒰, Q.carrier (.pair p)

/-- X.定義2.1: `C²(𝒰, Q) = ∏_{i<j<k, 非省略} Q(U_ijk)`。 -/
abbrev Cochain2 (Q : IntersectionCoefficientData.{u, w} 𝒰) : Type (max u w) :=
  ∀ t : KeptTriple 𝒰, Q.carrier (.triple t)

/-- X.定義2.1: `(δ⁰ a)_{ij} = a_j|_{U_ij} - a_i|_{U_ij}`。 -/
def delta0 (Q : IntersectionCoefficientData.{u, w} 𝒰) :
    Cochain0 Q →+ Cochain1 Q :=
  AddMonoidHom.mk'
    (fun a p =>
      Q.restrict (Face.pairRight p) (a p.snd) -
        Q.restrict (Face.pairLeft p) (a p.fst))
    (by
      intro a b
      funext p
      simp only [Pi.add_apply, map_add]
      abel)

/-- X.定義2.1: `(δ¹ c)_{ijk} = c_{jk}| - c_{ik}| + c_{ij}|`。 -/
def delta1 (Q : IntersectionCoefficientData.{u, w} 𝒰) :
    Cochain1 Q →+ Cochain2 Q :=
  AddMonoidHom.mk'
    (fun c t =>
      Q.restrict (Face.tripleJK t) (c t.pairJK) -
        Q.restrict (Face.tripleIK t) (c t.pairIK) +
        Q.restrict (Face.tripleIJ t) (c t.pairIJ))
    (by
      intro c d
      funext t
      simp only [Pi.add_apply, map_add]
      abel)

/-- X.補題2.2: `δ¹ δ⁰ = 0`。三つの chart への2経路一致(`restrict_coh`)から従う。 -/
theorem delta1_delta0 (Q : IntersectionCoefficientData.{u, w} 𝒰)
    (a : Cochain0 Q) : delta1 Q (delta0 Q a) = 0 := by
  funext t
  have htrd :
      Q.restrict (Face.tripleJK t) (Q.restrict (Face.pairRight t.pairJK) (a t.trd)) =
        Q.restrict (Face.tripleIK t) (Q.restrict (Face.pairRight t.pairIK) (a t.trd)) :=
    Q.restrict_coh (Face.tripleJK t) (Face.pairRight t.pairJK)
      (Face.tripleIK t) (Face.pairRight t.pairIK) (a t.trd)
  have hsnd :
      Q.restrict (Face.tripleJK t) (Q.restrict (Face.pairLeft t.pairJK) (a t.snd)) =
        Q.restrict (Face.tripleIJ t) (Q.restrict (Face.pairRight t.pairIJ) (a t.snd)) :=
    Q.restrict_coh (Face.tripleJK t) (Face.pairLeft t.pairJK)
      (Face.tripleIJ t) (Face.pairRight t.pairIJ) (a t.snd)
  have hfst :
      Q.restrict (Face.tripleIK t) (Q.restrict (Face.pairLeft t.pairIK) (a t.fst)) =
        Q.restrict (Face.tripleIJ t) (Q.restrict (Face.pairLeft t.pairIJ) (a t.fst)) :=
    Q.restrict_coh (Face.tripleIK t) (Face.pairLeft t.pairIK)
      (Face.tripleIJ t) (Face.pairLeft t.pairIJ) (a t.fst)
  have key : ∀ x y z x' y' z' : Q.carrier (.triple t),
      x = x' -> y = y' -> z = z' -> x - y - (x' - z) + (y' - z') = 0 := by
    intro x y z x' y' z' hx hy hz
    subst hx
    subst hy
    subst hz
    abel
  simp only [delta1, delta0, AddMonoidHom.mk'_apply, map_sub, Pi.zero_apply]
  exact key _ _ _ _ _ _ htrd hsnd hfst

/--
X.定義2.1–2.3: 増加添字三項複体。`H¹` は semantic-free な
`Cohomology.AdditiveThreeTermComplex` hub から得る(定義2.3 の
`Z¹ = ker δ¹` / `B¹ = im δ⁰` / `Ȟ¹ = Z¹/B¹`)。
-/
def incComplex (Q : IntersectionCoefficientData.{u, w} 𝒰) :
    Cohomology.AdditiveThreeTermComplex (Cochain0 Q) (Cochain1 Q) (Cochain2 Q) where
  d0 := delta0 Q
  d1 := delta1 Q
  d_comp := delta1_delta0 Q

/-- X.定義2.3: cover-relative `Ȟ¹(𝒰, Q)`。 -/
abbrev IncH1 (Q : IntersectionCoefficientData.{u, w} 𝒰) : Type (max u w) :=
  (incComplex Q).H1

end Saga
end SemanticRepair
end AAT.AG
