import Formal.SHIGURE.Part1.FixedModels

/-! # Models with observations

Equation (2.2) determines the arrows in the observed-model category. Giving
observed objects the induced category of underlying model maps retains both
endpoint observations. The wide subcategory restricts those maps by equation
(2.2); a predicate on the original model arrows would lose the observations.

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
  /-- A separate index for each observation. -/
  Index : Type u
  /-- The original carrier read by each observation. -/
  source : Index → sig.SortType
  /-- The prescribed value type for each observation. -/
  Value : Index → Type u

/-- The observations are maps on the model's specified carriers. -/
structure ObservedModel (T : Theory.{u}) (shape : ObservationShape T.signature) where
  /-- The underlying theory model in Definition 2.2. -/
  model : Model T
  /-- The specified readout on each source carrier. -/
  observe (i : shape.Index) : model.obj.carrier (shape.source i) → shape.Value i

namespace ObservedModel

variable {T : Theory.{u}} {shape : ObservationShape T.signature}

/-- Equation (2.2) as a predicate on the underlying model arrow. -/
def Preserves (A B : ObservedModel T shape) (f : A.model ⟶ B.model) : Prop :=
  ∀ i x, B.observe i (f.hom.onSort (shape.source i) x) = A.observe i x

/-- Retain the observations at both endpoints of an underlying theory arrow. -/
private abbrev Ambient :=
  InducedCategory (Model T) (ObservedModel.model (T := T) (shape := shape))

/-- Restrict the induced arrows by the observation squares from equation (2.2). -/
private def condition : MorphismProperty (Ambient (T := T) (shape := shape)) :=
  fun A B f => Preserves A B f.hom

/-- Identity and composition preserve all observations. -/
private instance condition_multiplicative :
    (condition (T := T) (shape := shape)).IsMultiplicative where
  id_mem _ := fun _ _ => rfl
  comp_mem f g hf hg := by
    intro i x
    rw [InducedCategory.comp_hom, Model.comp_apply, hg i, hf i]

/-- Present the same object in the induced category used by the wide subcategory. -/
private def includeAmbient (A : ObservedModel T shape) : Ambient (T := T) (shape := shape) := A

/-- Observation-preserving model arrows form mathlib's wide subcategory. -/
instance category : Category.{u} (ObservedModel T shape) :=
  InducedWideCategory.category includeAmbient condition

/-- An arrow of the observed-model category. -/
abbrev Hom (A B : ObservedModel T shape) := A ⟶ B

namespace Hom

variable {A B : ObservedModel T shape}

/-- A model map satisfying equation (2.2) is an observed-model arrow. -/
def mk (f : A.model ⟶ B.model) (preserves : Preserves A B f) : Hom A B :=
  ⟨InducedCategory.homMk f, preserves⟩

/-- The model arrow underlying an observed-model arrow. -/
def modelHom (f : Hom A B) : A.model ⟶ B.model :=
  f.val.hom

/-- The underlying arrow commutes with every specified observation. -/
theorem commutes (f : Hom A B) : Preserves A B f.modelHom :=
  f.property

/-- A map of observed models is determined by the underlying model map. -/
@[ext] theorem ext {f g : Hom A B} (same : f.modelHom = g.modelHom) : f = g :=
  Subtype.ext (InducedCategory.hom_ext same)

/-- The model arrow underlying an identity is the model identity. -/
@[simp] theorem modelHom_id (A : ObservedModel T shape) :
    (show Hom A A from 𝟙 A).modelHom = 𝟙 A.model := rfl

/-- Composition of underlying model arrows follows the order of the restricted arrows. -/
@[simp] theorem modelHom_comp {C : ObservedModel T shape} (f : Hom A B) (g : Hom B C) :
    (show Hom A C from f ≫ g).modelHom = f.modelHom ≫ g.modelHom := rfl

end Hom

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
def originalTuple {X : (T.signature.SortType ⊕ shape.Index) → Type u}
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

/-- An old total operation uses the original tuple in the source model. -/
theorem extendStructure_total (A : ObservedModel T shape) (f : T.signature.Total)
    (xs : Assignment A.extendStructure.carrier ((T.signature.totalArity f).inputs.map Sum.inl)) :
    A.extendStructure.total (.inl f) xs = A.model.obj.total f (originalTuple xs) :=
  rfl

/-- An old relation is tested on the original tuple in the source model. -/
theorem extendStructure_relation_iff (A : ObservedModel T shape) (r : T.signature.Rel)
    (xs : Assignment A.extendStructure.carrier ((T.signature.relInputs r).map Sum.inl)) :
    xs ∈ A.extendStructure.relation r ↔ originalTuple xs ∈ A.model.obj.relation r :=
  Iff.rfl

/-- An old quantity uses the original tuple in the source model. -/
theorem extendStructure_quantity (A : ObservedModel T shape) (q : T.signature.Quantity)
    (xs : Assignment A.extendStructure.carrier ((T.signature.quantityArity q).inputs.map Sum.inl)) :
    A.extendStructure.quantity q xs = A.model.obj.quantity q (originalTuple xs) :=
  rfl

/-- Membership in an old partial domain is read on the original tuple. -/
theorem extendStructure_partialDomain_iff (A : ObservedModel T shape) (p : T.signature.Partial)
    (xs : Assignment A.extendStructure.carrier ((T.signature.partialArity p).inputs.map Sum.inl)) :
    xs ∈ A.extendStructure.partialDomain p ↔ originalTuple xs ∈ A.model.obj.partialDomain p :=
  Iff.rfl

/-- The graph of an old partial operation is read on the original tuple and carrier. -/
theorem extendStructure_graph_partial_iff (A : ObservedModel T shape) (p : T.signature.Partial)
    (xs : Assignment A.extendStructure.carrier ((T.signature.partialArity p).inputs.map Sum.inl))
    (y : A.model.obj.carrier (T.signature.partialArity p).output) :
    A.extendStructure.Graph (.partialOp p) xs y ↔ A.model.obj.Graph (.partialOp p) (originalTuple xs) y :=
  (A.extendStructure.graph_partial_iff p xs y).trans (A.model.obj.graph_partial_iff p (originalTuple xs) y).symm

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
def encodeHom (f : Hom A B) : FixedModel.Hom A.encode B.encode :=
  FixedModel.Hom.mk (ObjectProperty.homMk (extendMap f)) (fun _ _ => rfl)

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
  map_id A := by
    apply FixedModel.Hom.ext (Model.hom_ext _)
    intro s x
    cases s with
    | inl s =>
      simp only [encodeHom_original, Hom.modelHom_id, FixedModel.Hom.modelHom_id, Model.id_apply]
    | inr i =>
      simp only [encodeHom_value, FixedModel.Hom.modelHom_id, Model.id_apply]
  map_comp f g := by
    apply FixedModel.Hom.ext (Model.hom_ext _)
    intro s x
    rw [FixedModel.Hom.modelHom_comp, Model.comp_apply]
    cases s with
    | inl s =>
      simp only [encodeHom_original, Hom.modelHom_comp, Model.comp_apply]
    | inr i =>
      simp only [encodeHom_value]

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
    have commutes := f.total_comm (.inl g) (A.extendedTuple xs)
    rwa [A.extendStructure_total, B.extendStructure_total, originalTuple_roundtrip A,
      originalTuple_extended_map] at commutes
  relation_mem r xs held := by
    have original : originalTuple (A.extendedTuple xs) ∈ A.model.obj.relation r :=
      (originalTuple_roundtrip A xs).symm ▸ held
    have source := (A.extendStructure_relation_iff r _).2 original
    have target := (B.extendStructure_relation_iff r _).1 (f.relation_mem r _ source)
    rwa [originalTuple_extended_map] at target
  partial_mem p xs held := by
    have original : originalTuple (A.extendedTuple xs) ∈ A.model.obj.partialDomain p :=
      (originalTuple_roundtrip A xs).symm ▸ held
    have source := (A.extendStructure_partialDomain_iff p _).2 original
    have target := (B.extendStructure_partialDomain_iff p _).1 (f.partial_mem p _ source)
    rwa [originalTuple_extended_map] at target
  partial_comm p xs := by
    have original : A.model.obj.Graph (.partialOp p) xs.val (A.model.obj.partialValue p xs) :=
      (A.model.obj.graph_partial_iff p _ _).2 ⟨xs.property, rfl⟩
    have source := (A.extendStructure_graph_partial_iff p (A.extendedTuple xs.val) _).2
      ((originalTuple_roundtrip A xs.val).symm ▸ original)
    have mapped := f.map_graph (.partialOp p) _ _ source
    have target := (B.extendStructure_graph_partial_iff p _ _).1 mapped
    rw [originalTuple_extended_map] at target
    obtain ⟨_, value⟩ := (B.model.obj.graph_partial_iff p _ _).1 target
    exact value.symm
  quantity_comm q xs := by
    have commutes := f.quantity_comm q (A.extendedTuple xs)
    rwa [A.extendStructure_quantity, B.extendStructure_quantity, originalTuple_roundtrip A,
      originalTuple_extended_map] at commutes

/-- A fixed arrow between encodings recovers precisely the observation-preserving arrow. -/
def decodeHom (f : FixedModel.Hom A.encode B.encode) : Hom A B :=
  Hom.mk (ObjectProperty.homMk (originalMap f.modelHom.hom)) (by
    intro i x
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
    exact square.symm)

/-- Decoding retains the component on every original sort. -/
@[simp] theorem decodeHom_original (f : FixedModel.Hom A.encode B.encode)
    (s : T.signature.SortType) (x : A.model.obj.carrier s) :
    (decodeHom f).modelHom.hom.onSort s x = f.modelHom.hom.onSort (.inl s) x :=
  rfl

/-- Decoding an encoded arrow recovers the source arrow on all original sorts. -/
@[simp] theorem decodeHom_encodeHom (f : Hom A B) : decodeHom (encodeHom f) = f := by
  apply Hom.ext (Model.hom_ext _)
  intro s x
  rw [decodeHom_original, encodeHom_original]

/-- Encoding a decoded fixed arrow recovers its original and fixed components. -/
@[simp] theorem encodeHom_decodeHom (f : FixedModel.Hom A.encode B.encode) :
    encodeHom (decodeHom f) = f := by
  apply FixedModel.Hom.ext (Model.hom_ext _)
  intro s x
  cases s with
  | inl s => rw [encodeHom_original, decodeHom_original]
  | inr i => exact (encodeHom_value (decodeHom f) i x).trans (f.fixes i x).symm

/-- Encoding and decoding are inverse on the Hom types of encoded objects. -/
def embeddingFullyFaithful (T : Theory.{u}) (shape : ObservationShape T.signature) :
    (embedding T shape).FullyFaithful where
  preimage f := decodeHom f
  map_preimage f := encodeHom_decodeHom f
  preimage_map f := decodeHom_encodeHom f

/-- Decoding supplies a preimage for every fixed-data arrow between the encoded objects. -/
instance embeddingFull : (embedding T shape).Full := (embeddingFullyFaithful T shape).full

/-- Encoding is injective on arrows by recovering every source component. -/
instance embeddingFaithful : (embedding T shape).Faithful := (embeddingFullyFaithful T shape).faithful

end ObservedModel

end SHIGURE
