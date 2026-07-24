import Formal.AG.SemanticRepair.Saga.CechThreeTerm
import Mathlib.Data.Finsupp.Basic

/-!
# Part X §3: semantic repair presentation and the coefficient `M_sem`

* `AtomOccurrence` / `AtomOccurrenceReading`: the context-local `At(V)`
  occurrence surface and its selected restriction reading (Part II data that
  the site layer does not generate; R0 §4.1).
* `SemanticAtomData`: Part X Definition 3.1 primitive data — semantic atoms,
  functorial restriction, projection to occurrences, supported subset.
* `SupportedWord` / `wordRestrict`: the free abelian group `F_sem(V) = ℤ^(S(V))`
  and its induced restriction.
* `SemanticRepairPresentation`: Definition 3.1 relation layer `Rel_rep`.
* `MSem`: Definition 3.2 quotient coefficient `M_sem = F_sem / R_rep`, with
  Proposition 3.3 (presheaf laws derived from semantic atom functoriality)
  packaged as `mSemPresheaf : SitePresheafData`.
* `semanticComplex` / `SemanticH1`: Definition 3.4 `C_sem = C(𝒰, M_sem)` and
  `H¹_sem`, generated purely from the presentation (no equation-side input).
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

open CategoryTheory

universe u v

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}

/--
II 由来の `At(V)`: context `V` の support 読みが読む Atom occurrence。
`ContextCategoryObject` は `ArchCtx` の素朴な wrapper なので直接定義できる。
-/
def AtomOccurrence (S : Site.AATSite A) (V : S.category) : Type u :=
  {sa : V.ctx.Support × U.Atom // V.ctx.minimal.supportReads sa.1 sa.2}

/-- occurrence の台 Atom。 -/
def AtomOccurrence.atom {V : S.category} (o : AtomOccurrence S V) : U.Atom :=
  o.1.2

/-- II-3: occurrence の台 Atom は selected object family に属する。 -/
theorem AtomOccurrence.atom_objectFamily {V : S.category}
    (o : AtomOccurrence S V) : A.configuration.family.mem o.atom :=
  V.ctx.supportReads_objectFamily o.2

/--
II 由来の `At(V)` presheaf 読み。site 層の `ContextMorphism` は support map を
source → target 方向にしか持たないため、occurrence restriction は
selected structure として受ける(R0 §4.1)。
-/
structure AtomOccurrenceReading (S : Site.AATSite A) where
  occRestrict : ∀ {V' V : S.category}, (V' ⟶ V) ->
      AtomOccurrence S V -> AtomOccurrence S V'
  occRestrict_id : ∀ (V : S.category) (o : AtomOccurrence S V),
      occRestrict (𝟙 V) o = o
  occRestrict_comp :
      ∀ {V'' V' V : S.category} (f : V'' ⟶ V') (g : V' ⟶ V)
        (o : AtomOccurrence S V),
        occRestrict (f ≫ g) o = occRestrict f (occRestrict g o)
  occRestrict_atom : ∀ {V' V : S.category} (f : V' ⟶ V) (o : AtomOccurrence S V),
      (occRestrict f o).atom = o.atom

/--
X.定義3.1 前半: semantic atom / restriction / projection / support の
primitive data。relation 層(`SemanticRepairPresentation`)はこの上に載る。
-/
structure SemanticAtomData (S : Site.AATSite A) (R : AtomOccurrenceReading S) where
  SemanticAtom : S.category -> Type v
  restrictAtom : ∀ {V' V : S.category}, (V' ⟶ V) ->
      SemanticAtom V -> SemanticAtom V'
  restrictAtom_id : ∀ (V : S.category) (l : SemanticAtom V),
      restrictAtom (𝟙 V) l = l
  restrictAtom_comp :
      ∀ {V'' V' V : S.category} (f : V'' ⟶ V') (g : V' ⟶ V) (l : SemanticAtom V),
        restrictAtom (f ≫ g) l = restrictAtom f (restrictAtom g l)
  projection : ∀ V : S.category, SemanticAtom V -> AtomOccurrence S V
  projection_natural : ∀ {V' V : S.category} (f : V' ⟶ V) (l : SemanticAtom V),
      projection V' (restrictAtom f l) = R.occRestrict f (projection V l)
  supported : ∀ V : S.category, SemanticAtom V -> Prop
  supported_restrict : ∀ {V' V : S.category} (f : V' ⟶ V) {l : SemanticAtom V},
      supported V l -> supported V' (restrictAtom f l)

namespace SemanticAtomData

variable {R : AtomOccurrenceReading S} (D : SemanticAtomData.{u, v} S R)

/-- X.定義3.1: supported semantic atom `S(V)`。 -/
abbrev SupportedAtom (V : S.category) : Type v :=
  {l : D.SemanticAtom V // D.supported V l}

/-- supported atom の restriction(support 安定性で放電)。 -/
def restrictSupported {V' V : S.category} (f : V' ⟶ V)
    (l : D.SupportedAtom V) : D.SupportedAtom V' :=
  ⟨D.restrictAtom f l.1, D.supported_restrict f l.2⟩

@[simp]
theorem restrictSupported_id (V : S.category) (l : D.SupportedAtom V) :
    D.restrictSupported (𝟙 V) l = l :=
  Subtype.ext (D.restrictAtom_id V l.1)

theorem restrictSupported_comp {V'' V' V : S.category}
    (f : V'' ⟶ V') (g : V' ⟶ V) (l : D.SupportedAtom V) :
    D.restrictSupported (f ≫ g) l =
      D.restrictSupported f (D.restrictSupported g l) :=
  Subtype.ext (D.restrictAtom_comp f g l.1)

/-- X.定義3.2: `F_sem(V) = ℤ^(S(V))`(supported atom 上の free abelian group)。 -/
abbrev SupportedWord (V : S.category) : Type v :=
  D.SupportedAtom V →₀ ℤ

/-- `F_sem` の induced restriction(`Finsupp.mapDomain`)。 -/
def wordRestrict {V' V : S.category} (f : V' ⟶ V) :
    D.SupportedWord V →+ D.SupportedWord V' :=
  Finsupp.mapDomain.addMonoidHom (D.restrictSupported f)

@[simp]
theorem wordRestrict_id (V : S.category) (x : D.SupportedWord V) :
    D.wordRestrict (𝟙 V) x = x := by
  have hfun : D.restrictSupported (𝟙 V) = id := by
    funext l
    exact D.restrictSupported_id V l
  simp [wordRestrict, hfun, Finsupp.mapDomain.addMonoidHom_id]

theorem wordRestrict_comp {V'' V' V : S.category}
    (f : V'' ⟶ V') (g : V' ⟶ V) (x : D.SupportedWord V) :
    D.wordRestrict (f ≫ g) x = D.wordRestrict f (D.wordRestrict g x) := by
  have hfun : D.restrictSupported (f ≫ g) =
      D.restrictSupported f ∘ D.restrictSupported g := by
    funext l
    exact D.restrictSupported_comp f g l
  simp only [wordRestrict, Finsupp.mapDomain.addMonoidHom_apply, hfun]
  exact Finsupp.mapDomain_comp

/-- generator `[λ]` の word。 -/
def singleWord {V : S.category} (l : D.SupportedAtom V) : D.SupportedWord V :=
  Finsupp.single l 1

@[simp]
theorem wordRestrict_singleWord {V' V : S.category} (f : V' ⟶ V)
    (l : D.SupportedAtom V) :
    D.wordRestrict f (D.singleWord l) =
      D.singleWord (D.restrictSupported f l) := by
  simp [wordRestrict, singleWord, Finsupp.mapDomain_single]

end SemanticAtomData

/--
X.定義3.1 後半 + 定義3.2: local repair relation `Rel_rep` 込みの presentation。
`rel_restrict` は本文の `res_f(Rel_rep(V)) ⊆ ⟨Rel_rep(V')⟩`。
-/
structure SemanticRepairPresentation (S : Site.AATSite A)
    (R : AtomOccurrenceReading S) where
  atomData : SemanticAtomData.{u, v} S R
  rel : ∀ V : S.category, Set (atomData.SupportedWord V)
  rel_restrict : ∀ {V' V : S.category} (f : V' ⟶ V),
      atomData.wordRestrict f '' rel V ⊆
        ↑(AddSubgroup.closure (rel V'))

namespace SemanticRepairPresentation

variable {R : AtomOccurrenceReading S} (P : SemanticRepairPresentation.{u, v} S R)

/-- X.定義3.2: `R_rep(V) = ⟨Rel_rep(V)⟩`。 -/
def relSpan (V : S.category) : AddSubgroup (P.atomData.SupportedWord V) :=
  AddSubgroup.closure (P.rel V)

/-- relation span は restriction で保たれる(`rel_restrict` の閉包)。 -/
theorem relSpan_le_comap {V' V : S.category} (f : V' ⟶ V) :
    P.relSpan V ≤ (P.relSpan V').comap (P.atomData.wordRestrict f) := by
  rw [← AddSubgroup.map_le_iff_le_comap, relSpan, AddMonoidHom.map_closure]
  exact (AddSubgroup.closure_le _).2 (P.rel_restrict f)

/-- X.定義3.2: semantic repair coefficient `M_sem(V) = F_sem(V) / R_rep(V)`。 -/
abbrev MSem (V : S.category) : Type v :=
  P.atomData.SupportedWord V ⧸ P.relSpan V

/-- `M_sem(V)` の class 写像。 -/
def mSemMk (V : S.category) : P.atomData.SupportedWord V →+ P.MSem V :=
  QuotientAddGroup.mk' (P.relSpan V)

/-- 商へ降りた restriction(命題3.3 の写像部分)。 -/
def mSemRestrict {V' V : S.category} (f : V' ⟶ V) : P.MSem V →+ P.MSem V' :=
  QuotientAddGroup.map (P.relSpan V) (P.relSpan V')
    (P.atomData.wordRestrict f) (P.relSpan_le_comap f)

@[simp]
theorem mSemRestrict_mk {V' V : S.category} (f : V' ⟶ V)
    (x : P.atomData.SupportedWord V) :
    P.mSemRestrict f (P.mSemMk V x) =
      P.mSemMk V' (P.atomData.wordRestrict f x) :=
  rfl

/-- X.命題3.3: restriction の恒等則。 -/
theorem mSemRestrict_id (V : S.category) (x : P.MSem V) :
    P.mSemRestrict (𝟙 V) x = x := by
  refine QuotientAddGroup.induction_on x ?_
  intro w
  show P.mSemRestrict (𝟙 V) (P.mSemMk V w) = P.mSemMk V w
  rw [mSemRestrict_mk, P.atomData.wordRestrict_id]

/-- X.命題3.3: restriction の合成則。 -/
theorem mSemRestrict_comp {V'' V' V : S.category}
    (f : V'' ⟶ V') (g : V' ⟶ V) (x : P.MSem V) :
    P.mSemRestrict (f ≫ g) x = P.mSemRestrict f (P.mSemRestrict g x) := by
  refine QuotientAddGroup.induction_on x ?_
  intro w
  show P.mSemRestrict (f ≫ g) (P.mSemMk V w) =
    P.mSemRestrict f (P.mSemRestrict g (P.mSemMk V w))
  rw [mSemRestrict_mk, mSemRestrict_mk, mSemRestrict_mk,
    P.atomData.wordRestrict_comp]

/--
X.命題3.3: `M_sem` は `S_X` 上の可換群値 presheaf をなす。
presheaf 則は semantic atom restriction の functoriality
(`restrictAtom_id` / `restrictAtom_comp`)から導かれる。
-/
def mSemPresheaf : SitePresheafData.{u, v} S where
  carrier := P.MSem
  addCommGroup _ := inferInstance
  restrict f := P.mSemRestrict f
  restrict_id := P.mSemRestrict_id
  restrict_comp f g x := P.mSemRestrict_comp f g x

/--
X.定義3.4: semantic repair complex `C_sem^•(𝒰) = C^•(𝒰, M_sem)`。
presentation だけから生成され、`Q_E`・幾何側複体・comparison map を参照しない。
-/
def semanticComplex (𝒰 : MonomorphicOrderedCover S) :
    Cohomology.AdditiveThreeTermComplex
      (Cochain0 (P.mSemPresheaf.onIntersections 𝒰))
      (Cochain1 (P.mSemPresheaf.onIntersections 𝒰))
      (Cochain2 (P.mSemPresheaf.onIntersections 𝒰)) :=
  incComplex (P.mSemPresheaf.onIntersections 𝒰)

/-- X.定義3.4: `H¹_sem(𝒰) = Ȟ¹(𝒰, M_sem)`。 -/
abbrev SemanticH1 (𝒰 : MonomorphicOrderedCover S) : Type (max u v) :=
  (P.semanticComplex 𝒰).H1

end SemanticRepairPresentation

end Saga
end SemanticRepair
end AAT.AG
