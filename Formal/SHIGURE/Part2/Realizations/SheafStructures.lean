import Formal.SHIGURE.Part1.Laws
import Formal.SHIGURE.Part2.Realizations.PositiveSheaves
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Primitive structures and positive Laws in sheaves

The typed assignment objects are products of the carrier sheaves. Atomic
formulas pull back primitive relations, domains or graphs. The recursively
defined interpretation extends these atoms to the positive syntax of
Part I on the relative Zariski site.

## Implementation notes

The signature and its variable positions are shared with the set semantics.
The finite product of the carrier sheaves is constructed sectionwise using
`Assignment` and componentwise gluing. Choosing an abstract categorical
product would require an additional comparison on every restriction to a
test scheme. The sectionwise product gives that restriction directly.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

noncomputable section

namespace SHIGURE

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
variable {S : Type u}

/-- A tuple of sections restricts by restricting every component. -/
private def sheafTuplePresheaf (A : S → Sheaf J (Type u)) (Γ : List S) : Cᵒᵖ ⥤ Type u where
  obj U := Assignment (fun s => (A s).val.obj U) Γ
  map f := ↾fun x => ⟨fun {s} i => (A s).val.map f (x i)⟩
  map_id U := by
    ext x s i
    change (A s).val.map (𝟙 U) (x i) = x i
    rw [(A s).val.map_id U]
    rfl
  map_comp f g := by
    ext x s i
    change (A s).val.map (f ≫ g) (x i) = ((A s).val.map f ≫ (A s).val.map g) (x i)
    rw [Functor.map_comp]

/-- The sheaf of assignments to the variables in a typed context. -/
def sheafTuple (A : S → Sheaf J (Type u)) (Γ : List S) : Sheaf J (Type u) where
  val := sheafTuplePresheaf A Γ
  cond := by
    apply (isSheaf_iff_isSheaf_of_type J _).mpr
    intro U cover hcover x compatible
    let part {s : S} (i : Var Γ s) : Presieve.FamilyOfElements ((A s).val) (cover : Presieve U) :=
      fun _ f hf => (x f hf).get i
    have hpart {s : S} (i : Var Γ s) : (part i).Compatible := by
      intro U₁ U₂ V f₁ f₂ g₁ g₂ hg₁ hg₂ he
      exact congrArg (fun z : Assignment (fun t => (A t).val.obj (op V)) Γ => z.get i)
        (compatible f₁ f₂ hg₁ hg₂ he)
    let gluing (s : S) := (isSheaf_iff_isSheaf_of_type J (A s).val).mp (A s).cond cover hcover
    refine ⟨⟨fun {s} i => (gluing s).amalgamate (part i) (hpart i)⟩, ?_, ?_⟩
    · intro V f hf
      apply Assignment.ext
      intro s i
      exact (gluing s).valid_glue (hpart i) f hf
    · intro z hz
      apply Assignment.ext
      intro s i
      apply (gluing s).isSeparatedFor.ext
      intro V f hf
      exact (congrArg (fun y : Assignment (fun t => (A t).val.obj (op V)) Γ => y.get i)
        (hz f hf)).trans ((gluing s).valid_glue (hpart i) f hf).symm

/-- The projection of a tuple of sections onto its specified variable. -/
def sheafTupleProj (A : S → Sheaf J (Type u)) {Γ : List S} {s : S} (i : Var Γ s) :
    sheafTuple A Γ ⟶ A s :=
  ⟨{ app := fun _ => ↾fun xs => xs.get i }⟩

/-- The tuple sheaf and its variable projections form a fan of the carrier sheaves. -/
def sheafTupleFan (A : S → Sheaf J (Type u)) (Γ : List S) :
    Fan (fun i : (s : S) × Var Γ s => A i.1) :=
  Fan.mk (sheafTuple A Γ) (fun i => sheafTupleProj A i.2)

/-- The sectionwise tuple sheaf is the product of its carrier sheaves in mathlib. -/
def sheafTupleFanIsLimit (A : S → Sheaf J (Type u)) (Γ : List S) :
    IsLimit (sheafTupleFan A Γ) := by
  refine mkFanLimit _ (fun F => ⟨{
    app := fun U => ↾fun x => ⟨fun {s} i => (F.proj ⟨s, i⟩).val.app U x⟩
    naturality := by
      intro U V m
      ext x
      apply Assignment.ext
      intro s i
      exact FunctorToTypes.naturality _ _ (F.proj ⟨s, i⟩).val m x }⟩)
    (fun _ _ => rfl) ?_
  intro F m h
  ext U x
  apply Assignment.ext
  intro s i
  exact congrArg (fun f : F.pt ⟶ A s => f.val.app U x) (h ⟨s, i⟩)

/-- Pick out an input tuple along a renaming of variables. -/
def sheafTupleRename (A : S → Sheaf J (Type u)) {Γ Δ : List S} (f : Renaming Γ Δ) :
    sheafTuple A Δ ⟶ sheafTuple A Γ :=
  ⟨{ app := fun _ => ↾fun xs => ⟨fun i => xs.get (f i)⟩ }⟩

/-- A family of maps between the carrier sheaves acts on every tuple. -/
def sheafTupleMap {A B : S → Sheaf J (Type u)} (f : ∀ s, A s ⟶ B s) (Γ : List S) :
    sheafTuple A Γ ⟶ sheafTuple B Γ :=
  ⟨{ app := fun U => ↾fun xs => ⟨fun {s} i => (f s).val.app U (xs.get i)⟩
     naturality := by
       intro U V g
       ext xs
       apply Assignment.ext
       intro s i
       exact FunctorToTypes.naturality _ _ (f s).val g (xs.get i) }⟩

/-- The category identity on carrier sheaves acts as the identity on all tuples. -/
@[simp]
theorem sheafTupleMap_id (A : S → Sheaf J (Type u)) (Γ : List S) :
    sheafTupleMap (fun s => 𝟙 (A s)) Γ = 𝟙 (sheafTuple A Γ) := by
  ext U xs
  rfl

/-- Tuple maps compose with the same order as the carrier maps. -/
theorem sheafTupleMap_comp {A B D : S → Sheaf J (Type u)} (f : ∀ s, A s ⟶ B s)
    (g : ∀ s, B s ⟶ D s) (Γ : List S) :
    sheafTupleMap (fun s => f s ≫ g s) Γ = sheafTupleMap f Γ ≫ sheafTupleMap g Γ := by
  ext U xs
  rfl

/-- A signature has carrier sheaves, primitive maps, and chosen relation and domain subsheaves. -/
structure SheafStructure (sig : Signature.{u}) (J : GrothendieckTopology C) where
  /-- The sheaf of sections of each sort. -/
  carrier : sig.SortType → Sheaf J (Type u)
  /-- The total operations are morphisms defined on the full input sheaf. -/
  total (f : sig.Total) :
    sheafTuple carrier (sig.totalArity f).inputs ⟶ carrier (sig.totalArity f).output
  /-- A basic relation is a subsheaf of its input tuples. -/
  relation (r : sig.Rel) : SheafPredicate (sheafTuple carrier (sig.relInputs r))
  /-- The domain of a partial operation is a subsheaf of its input tuples. -/
  partialDomain (p : sig.Partial) : SheafPredicate (sheafTuple carrier (sig.partialArity p).inputs)
  /-- The partial operation is defined on its domain subsheaf. -/
  partialValue (p : sig.Partial) : (partialDomain p).toSheaf ⟶ carrier (sig.partialArity p).output
  /-- A marked quantity is a total map from its input sheaf. -/
  quantity (q : sig.Quantity) :
    sheafTuple carrier (sig.quantityArity q).inputs ⟶ carrier (sig.quantityArity q).output

namespace SheafStructure

variable {sig : Signature.{u}} (A : SheafStructure sig J)
variable {Γ : List sig.SortType}

/-- The graph of a partial operation uses the domain pulled back along the argument tuple. -/
def partialGraph (p : sig.Partial) (x : Renaming (sig.partialArity p).inputs Γ)
    (y : Var Γ (sig.partialArity p).output) : SheafPredicate (sheafTuple A.carrier Γ) :=
  let f := sheafTupleRename A.carrier x
  let D := (A.partialDomain p).preimage f
  let g := D.inclusion ≫ sheafTupleProj A.carrier y
  let h := SheafPredicate.mapAlong f (P := D) (Q := A.partialDomain p) le_rfl ≫ A.partialValue p
  SheafPredicate.existsAlong D.inclusion (SheafPredicate.equal h g)

/-- A section lies in the partial graph precisely when its inputs belong to the
domain and the partial value equals its specified output. -/
theorem mem_partialGraph_iff (p : sig.Partial) (x : Renaming (sig.partialArity p).inputs Γ)
    (y : Var Γ (sig.partialArity p).output) (U : Cᵒᵖ)
    (a : (sheafTuple A.carrier Γ).val.obj U) :
    let f := sheafTupleRename A.carrier x
    let D := (A.partialDomain p).preimage f
    a ∈ (A.partialGraph p x y).carrier.obj U ↔
      ∃ h : a ∈ D.carrier.obj U,
        (A.partialValue p).val.app U ⟨f.val.app U a, h⟩ = a.get y := by
  dsimp only
  rw [partialGraph, SheafPredicate.mem_existsAlong_inclusion_iff]
  exact exists_congr fun _ => SheafPredicate.mem_equal_iff _ _ _ _

/-- Interpret each atomic formula by its equality, relation, domain or operation graph. -/
def interpretAtom : Atomic sig Γ → SheafPredicate (sheafTuple A.carrier Γ)
  | .eq x y => SheafPredicate.equal (sheafTupleProj A.carrier x) (sheafTupleProj A.carrier y)
  | .rel r x => (A.relation r).preimage (sheafTupleRename A.carrier x)
  | .domain p x => (A.partialDomain p).preimage (sheafTupleRename A.carrier x)
  | .graph (.total f) x y =>
      SheafPredicate.equal (sheafTupleRename A.carrier x ≫ A.total f) (sheafTupleProj A.carrier y)
  | .graph (.partialOp p) x y => A.partialGraph p x y
  | .graph (.quantity q) x y =>
      SheafPredicate.equal (sheafTupleRename A.carrier x ≫ A.quantity q) (sheafTupleProj A.carrier y)

/-- The positive formula interpretation on the sheaf of its typed assignments. -/
def interpretFormula : {Γ : List sig.SortType} → Formula sig Γ → SheafPredicate (sheafTuple A.carrier Γ)
  | _, .atom a => A.interpretAtom a
  | _, .truth => SheafPredicate.truth
  | _, .falsehood => SheafPredicate.falsehood
  | _, .conj p q => (interpretFormula p).conj (interpretFormula q)
  | _, .disj p q => (interpretFormula p).disj (interpretFormula q)
  | _, .ex p => SheafPredicate.existsAlong (sheafTupleRename A.carrier (fun x => .there x))
      (interpretFormula p)

/-- For a sheaf structure, a Law is the inclusion of the two interpreted subsheaves. -/
def holdsLaw (law : Law sig) : Prop :=
  (A.interpretFormula law.input).holds (A.interpretFormula law.conclusion)

/-- A Law imposes the inclusion at every test object and on every section of its context. -/
theorem holdsLaw_iff (law : Law sig) :
    A.holdsLaw law ↔
      ∀ (U : Cᵒᵖ) (a : (sheafTuple A.carrier law.context).val.obj U),
        a ∈ (A.interpretFormula law.input).carrier.obj U →
          a ∈ (A.interpretFormula law.conclusion).carrier.obj U :=
  Iff.rfl

end SheafStructure

end SHIGURE
