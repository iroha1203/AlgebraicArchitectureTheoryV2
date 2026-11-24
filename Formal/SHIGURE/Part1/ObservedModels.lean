import Formal.SHIGURE.Part1.FixedModels

/-! # Models with observations

Equation (2.2) determines the arrows in the observed-model category.

## Implementation notes

A fresh sum tag gives every observation its own value sort and total unary operation.
The value signature contains just those sorts. This lets the fixed-data category enforce
identity on the value components, including when different observations have equal value types.
The original Laws are renamed along the original signature's inclusion, and satisfaction
is transported through the exact reduct. Formula substitution is unnecessary for this
inclusion because it preserves each primitive symbol and its arity.
-/

universe u

namespace SHIGURE

open CategoryTheory

/-- A family of observations with source sorts and independently fixed value types. -/
structure ObservationShape (sig : Signature.{u}) where
  Index : Type u
  source : Index → sig.SortType
  Value : Index → Type u

/-- The observations are maps on the model's specified carriers. -/
structure ObservedModel (T : Theory.{u}) (shape : ObservationShape T.signature) where
  model : Model T
  observe (i : shape.Index) : model.obj.carrier (shape.source i) → shape.Value i

namespace ObservedModel

variable {T : Theory.{u}} {shape : ObservationShape T.signature}

/-- An observed map preserves each specified observation pointwise, as in equation (2.2). -/
structure Hom (A B : ObservedModel T shape) where
  modelHom : A.model ⟶ B.model
  commutes (i : shape.Index) (x : A.model.obj.carrier (shape.source i)) :
    B.observe i (modelHom.hom.onSort (shape.source i) x) = A.observe i x

namespace Hom

variable {A B C : ObservedModel T shape}

/-- A map of observed models is determined by the underlying model map. -/
@[ext] theorem ext {f g : Hom A B} (same : f.modelHom = g.modelHom) : f = g := by
  cases f
  cases g
  cases same
  rfl

/-- Identity preserves each observation. -/
def id (A : ObservedModel T shape) : Hom A A :=
  ⟨𝟙 A.model, fun _ _ => rfl⟩

/-- The composite preserves an observation by applying the two observation squares in order. -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  modelHom := f.modelHom ≫ g.modelHom
  commutes i x := by
    rw [Model.comp_apply, g.commutes, f.commutes]

end Hom

/-- Observed models and the arrows preserving their observations form a category. -/
instance category : Category.{u} (ObservedModel T shape) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (Category.id_comp f.modelHom)
  comp_id f := Hom.ext (Category.comp_id f.modelHom)
  assoc f g h := Hom.ext (Category.assoc f.modelHom g.modelHom h.modelHom)

end ObservedModel


namespace ObservationShape

variable {sig : Signature.{u}} (shape : ObservationShape sig)

/-- Add one value sort and one total unary operation for each observation.
The sum tags distinguish the new symbols from all existing symbols. -/
def signature (sig : Signature.{u}) (shape : ObservationShape sig) : Signature.{u} where
  SortType := sig.SortType ⊕ shape.Index
  Total := sig.Total ⊕ shape.Index
  Rel := sig.Rel
  Partial := sig.Partial
  Quantity := sig.Quantity
  totalArity
    | .inl f => ⟨(sig.totalArity f).inputs.map Sum.inl, .inl (sig.totalArity f).output⟩
    | .inr i => ⟨[.inl (shape.source i)], .inr i⟩
  relInputs r := (sig.relInputs r).map Sum.inl
  partialArity p := ⟨(sig.partialArity p).inputs.map Sum.inl, .inl (sig.partialArity p).output⟩
  quantityArity q := ⟨(sig.quantityArity q).inputs.map Sum.inl, .inl (sig.quantityArity q).output⟩

/-- The old symbols retain their original arities under the left injection. -/
def original : SignatureNames sig shape.signature where
  onSort := Sum.inl
  onTotal := Sum.inl
  onRel := id
  onPartial := id
  onQuantity := id
  totalArity _ := rfl
  relInputs _ := rfl
  partialArity _ := rfl
  quantityArity _ := rfl

/-- Adding observations embeds every old name. -/
theorem original_isInclusion : shape.original.IsInclusion :=
  ⟨Sum.inl_injective, Sum.inl_injective, Function.injective_id, Function.injective_id, Function.injective_id⟩

/-- The signature of the fixed value data has just the value sorts. -/
def valueSignature : Signature.{u} where
  SortType := shape.Index
  Total := PEmpty
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PEmpty
  totalArity n := nomatch n
  relInputs n := nomatch n
  partialArity n := nomatch n
  quantityArity n := nomatch n

/-- Include the value sorts as the right summand of the extended signature. -/
def values : Subsignature shape.valueSignature (shape.signature) where
  val := {
    onSort := Sum.inr
    onTotal n := nomatch n
    onRel n := nomatch n
    onPartial n := nomatch n
    onQuantity n := nomatch n
    totalArity n := nomatch n
    relInputs n := nomatch n
    partialArity n := nomatch n
    quantityArity n := nomatch n }
  property := by
    refine ⟨Sum.inr_injective, ?_, ?_, ?_, ?_⟩ <;>
      intro n _ _ <;> exact PEmpty.elim n

/-- The fixed structure interprets each value sort as its prescribed carrier. -/
def valueData : Structure shape.valueSignature where
  carrier := shape.Value
  total n := nomatch n
  relation n := nomatch n
  partialDomain n := nomatch n
  partialValue n := nomatch n
  quantity n := nomatch n

/-- The larger signature carries the original Laws with their names retyped.
There are no further required Laws on the observation operations. -/
def theory (T : Theory.{u}) (shape : ObservationShape T.signature) : Theory.{u} :=
  ⟨shape.signature, T.LawName, fun name => shape.original.law (T.law name)⟩

end ObservationShape

namespace ObservedModel

variable {T : Theory.{u}} {shape : ObservationShape T.signature}

/-- Read a tuple of original sorts in the extended structure at its original positions. -/
private def originalTuple {X : (T.signature.SortType ⊕ shape.Index) → Type u}
    {Γ : List T.signature.SortType} (xs : Assignment X (Γ.map Sum.inl)) :
    Assignment (X ∘ Sum.inl) Γ :=
  ⟨fun i => xs (i.mapSorts Sum.inl)⟩

/-- Put the observation functions into the new total operation slots. -/
def extendStructure (A : ObservedModel T shape) : Structure (shape.theory T).signature where
  carrier := Sum.elim A.model.obj.carrier shape.Value
  total
    | .inl f, xs => A.model.obj.total f (originalTuple xs)
    | .inr i, xs => A.observe i (xs .here)
  relation r := {xs | originalTuple xs ∈ A.model.obj.relation r}
  partialDomain p := {xs | originalTuple xs ∈ A.model.obj.partialDomain p}
  partialValue p xs := A.model.obj.partialValue p ⟨originalTuple xs.val, xs.property⟩
  quantity q xs := A.model.obj.quantity q (originalTuple xs)

/-- The new operation is the specified observation on the source coordinate. -/
@[simp] theorem extendStructure_observe (A : ObservedModel T shape) (i : shape.Index)
    (x : A.model.obj.carrier (shape.source i)) :
    A.extendStructure.total (.inr i) (Assignment.cons x Assignment.empty) = A.observe i x :=
  rfl

/-- Retype an original tuple for use in the extended signature. -/
private def extendedTuple (A : ObservedModel T shape)
    {Γ : List T.signature.SortType} (xs : Assignment A.model.obj.carrier Γ) :
    Assignment A.extendStructure.carrier (Γ.map Sum.inl) :=
  Assignment.mapSorts Sum.inl xs

/-- Retyping an original tuple and reading it back preserves every coordinate. -/
private theorem originalTuple_roundtrip (A : ObservedModel T shape)
    {Γ : List T.signature.SortType} (xs : Assignment A.model.obj.carrier Γ) :
    originalTuple (A.extendedTuple xs) = xs :=
  Assignment.ext (fun i => Assignment.mapSorts_apply (X := A.extendStructure.carrier) Sum.inl xs i)

/-- Partial operations on equal domains agree if they return equal values on each input. -/
private theorem partialValue_heq {ι : Type u} {Inputs Output : ι → Type u}
    {D E : (p : ι) → Set (Inputs p)} (domains : D = E)
    (f : (p : ι) → D p → Output p) (g : (p : ι) → E p → Output p)
    (values : ∀ p (xs : D p) (hx : xs.val ∈ E p), f p xs = g p ⟨xs.val, hx⟩) : HEq f g := by
  cases domains
  exact heq_of_eq (funext fun p => funext fun xs => values p xs xs.property)

/-- The original reduct of an extended structure recovers the source structure. -/
theorem restrict_extendStructure (A : ObservedModel T shape) :
    shape.original.restrict A.extendStructure = A.model.obj := by
  have domains : (shape.original.restrict A.extendStructure).partialDomain = A.model.obj.partialDomain := by
    funext p
    exact Set.ext fun xs => iff_of_eq
      (congrArg (fun ys => ys ∈ A.model.obj.partialDomain p) (originalTuple_roundtrip A xs))
  refine Structure.ext rfl ?_ ?_ ?_ ?_ ?_
  · apply heq_of_eq
    funext f xs
    exact congrArg (A.model.obj.total f) (originalTuple_roundtrip A xs)
  · apply heq_of_eq
    funext r
    exact Set.ext fun xs => iff_of_eq
      (congrArg (fun ys => ys ∈ A.model.obj.relation r) (originalTuple_roundtrip A xs))
  · exact heq_of_eq domains
  · apply partialValue_heq domains
    intro p xs _
    exact congrArg (A.model.obj.partialValue p) (Subtype.ext (originalTuple_roundtrip A xs.val))
  · apply heq_of_eq
    funext q xs
    exact congrArg (A.model.obj.quantity q) (originalTuple_roundtrip A xs)

/-- The value reduct of the extended structure is the prescribed fixed data. -/
theorem restrict_values_extendStructure (A : ObservedModel T shape) :
    shape.values.val.restrict A.extendStructure = shape.valueData := by
  refine Structure.ext rfl ?_ ?_ ?_ ?_ ?_
  all_goals apply Function.hfunext rfl
  all_goals intro n
  all_goals exact PEmpty.elim n

/-- Encoding an observed model yields an extended model with fixed value data. -/
def encode (A : ObservedModel T shape) : FixedModel (shape.theory T) shape.values shape.valueData where
  model := ⟨A.extendStructure, fun name =>
    (shape.original.restrict_law_iff _ (T.law name)).1
      (A.restrict_extendStructure.symm ▸ A.model.property name)⟩
  fixed := A.restrict_values_extendStructure

/-- Restricting an extended assignment after mapping its components commutes with the old maps. -/
private theorem originalTuple_map {X Y : (T.signature.SortType ⊕ shape.Index) → Type u}
    {Γ : List T.signature.SortType} (xs : Assignment X (Γ.map Sum.inl)) (f : ∀ s, X s → Y s) :
    originalTuple (xs.map f) = (originalTuple xs).map (fun s => f (.inl s)) :=
  rfl

variable {A B C : ObservedModel T shape}

/-- Extend a map preserving observations by identities on all value sorts. -/
private def extendMap (f : Hom A B) : StructureMap A.extendStructure B.extendStructure where
  onSort
    | .inl s => f.modelHom.hom.onSort s
    | .inr _ => id
  total_comm
    | .inl g, xs => f.modelHom.hom.total_comm g (originalTuple xs)
    | .inr i, xs => (f.commutes i (xs .here)).symm
  relation_mem r xs held := f.modelHom.hom.relation_mem r (originalTuple xs) held
  partial_mem p xs held := f.modelHom.hom.partial_mem p (originalTuple xs) held
  partial_comm p xs := f.modelHom.hom.partial_comm p ⟨originalTuple xs.val, xs.property⟩
  quantity_comm q xs := f.modelHom.hom.quantity_comm q (originalTuple xs)

/-- Observation-preserving arrows become the corresponding fixed-data arrows. -/
def encodeHom (f : Hom A B) : FixedModel.Hom A.encode B.encode where
  modelHom := ObjectProperty.homMk (extendMap f)
  fixes _ _ := rfl

/-- The original components of an encoded arrow are its source model maps. -/
@[simp] theorem encodeHom_original (f : Hom A B) (s : T.signature.SortType) (x : A.model.obj.carrier s) :
    (encodeHom f).modelHom.hom.onSort (.inl s) x = f.modelHom.hom.onSort s x := rfl

/-- Each value component of an encoded arrow stays fixed. -/
@[simp] theorem encodeHom_value (f : Hom A B) (i : shape.Index) (x : shape.Value i) :
    (encodeHom f).modelHom.hom.onSort (.inr i) x = x := rfl

/-- The observation encoding is a functor to models with fixed value data. -/
def embedding (T : Theory.{u}) (shape : ObservationShape T.signature) :
    ObservedModel T shape ⥤ FixedModel (shape.theory T) shape.values shape.valueData where
  obj := encode
  map f := encodeHom f
  map_id A := FixedModel.Hom.ext (Model.hom_ext (by
    intro s x
    cases s <;> rfl))
  map_comp f g := FixedModel.Hom.ext (Model.hom_ext (by
    intro s x
    cases s <;> rfl))

/-- Retyping followed by mapping and reading back applies the original carrier maps. -/
private theorem originalTuple_extended_map (f : StructureMap A.extendStructure B.extendStructure)
    {Γ : List T.signature.SortType} (xs : Assignment A.model.obj.carrier Γ) :
    originalTuple ((A.extendedTuple xs).map f.onSort) =
      xs.map (fun s => f.onSort (.inl s)) := by
  rw [originalTuple_map, originalTuple_roundtrip A]

/-- Reading the old components of a map between extended structures preserves the old operations. -/
private def originalMap (f : StructureMap A.extendStructure B.extendStructure) :
    StructureMap A.model.obj B.model.obj where
  onSort s := f.onSort (.inl s)
  total_comm g xs := by
    have commutes :
        f.onSort (.inl (T.signature.totalArity g).output)
          (A.model.obj.total g (originalTuple (A.extendedTuple xs))) =
        B.model.obj.total g (originalTuple ((A.extendedTuple xs).map f.onSort)) :=
      f.total_comm (.inl g) (A.extendedTuple xs)
    rwa [originalTuple_roundtrip A, originalTuple_extended_map] at commutes
  relation_mem r xs held := by
    have source : originalTuple (A.extendedTuple xs) ∈ A.model.obj.relation r :=
      (originalTuple_roundtrip A xs).symm ▸ held
    have target : originalTuple ((A.extendedTuple xs).map f.onSort) ∈ B.model.obj.relation r :=
      f.relation_mem r _ source
    rwa [originalTuple_extended_map] at target
  partial_mem p xs held := by
    have source : originalTuple (A.extendedTuple xs) ∈ A.model.obj.partialDomain p :=
      (originalTuple_roundtrip A xs).symm ▸ held
    have target : originalTuple ((A.extendedTuple xs).map f.onSort) ∈ B.model.obj.partialDomain p :=
      f.partial_mem p _ source
    rwa [originalTuple_extended_map] at target
  partial_comm p xs := by
    let tuple := A.extendedTuple xs.val
    have source : originalTuple tuple ∈ A.model.obj.partialDomain p :=
      (originalTuple_roundtrip A xs.val).symm ▸ xs.property
    have target : originalTuple (tuple.map f.onSort) ∈ B.model.obj.partialDomain p :=
      f.partial_mem p _ source
    have commutes : f.onSort (.inl (T.signature.partialArity p).output)
          (A.model.obj.partialValue p ⟨originalTuple tuple, source⟩) =
        B.model.obj.partialValue p ⟨originalTuple (tuple.map f.onSort), target⟩ :=
      f.partial_comm p ⟨tuple, source⟩
    have source_eq : (⟨originalTuple tuple, source⟩ : A.model.obj.partialDomain p) = xs :=
      Subtype.ext (originalTuple_roundtrip A xs.val)
    have target_eq : (⟨originalTuple (tuple.map f.onSort), target⟩ : B.model.obj.partialDomain p) =
        ⟨xs.val.map (fun s => f.onSort (.inl s)), by
          rwa [originalTuple_extended_map] at target⟩ :=
      Subtype.ext (originalTuple_extended_map f xs.val)
    rwa [source_eq, target_eq] at commutes
  quantity_comm q xs := by
    have commutes :
        f.onSort (.inl (T.signature.quantityArity q).output)
          (A.model.obj.quantity q (originalTuple (A.extendedTuple xs))) =
        B.model.obj.quantity q (originalTuple ((A.extendedTuple xs).map f.onSort)) :=
      f.quantity_comm q (A.extendedTuple xs)
    rwa [originalTuple_roundtrip A, originalTuple_extended_map] at commutes

/-- A fixed arrow between encodings recovers precisely the observation-preserving arrow. -/
def decodeHom (f : FixedModel.Hom A.encode B.encode) : Hom A B where
  modelHom := ObjectProperty.homMk (originalMap f.modelHom.hom)
  commutes i x := by
    have fixed : f.modelHom.hom.onSort (.inr i) (A.observe i x) = A.observe i x :=
      f.fixes i (A.observe i x)
    let input : Assignment A.extendStructure.carrier [.inl (shape.source i)] :=
      Assignment.cons (X := A.extendStructure.carrier) x Assignment.empty
    have square : f.modelHom.hom.onSort (.inr i) (A.extendStructure.total (.inr i) input) =
        B.extendStructure.total (.inr i) (input.map f.modelHom.hom.onSort) :=
      f.modelHom.hom.total_comm (.inr i) input
    dsimp only [input] at square
    rw [extendStructure_observe, fixed, Assignment.map_cons, Assignment.map_empty,
      extendStructure_observe] at square
    exact square.symm

/-- Encoding and decoding are inverse on the Hom types of encoded objects. -/
def embeddingFullyFaithful (T : Theory.{u}) (shape : ObservationShape T.signature) :
    (embedding T shape).FullyFaithful where
  preimage f := decodeHom f
  map_preimage f := FixedModel.Hom.ext (Model.hom_ext (by
    intro s x
    cases s with
    | inl s => rfl
    | inr i => exact (f.fixes i x).symm))
  preimage_map f := Hom.ext (Model.hom_ext (fun _ _ => rfl))

instance : (embedding T shape).Full := (embeddingFullyFaithful T shape).full

instance : (embedding T shape).Faithful := (embeddingFullyFaithful T shape).faithful

end ObservedModel

end SHIGURE
