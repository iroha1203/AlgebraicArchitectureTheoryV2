import Formal.SHIGURE.Part2.Realizations.TensorMode
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Tensor diagrams with specified domains

A specified tensor relation or partial domain is a submodule of its
typed input tensor. A preserving arrow factors the input map through
the target submodule and commutes with the value on the entire domain.

## Implementation notes

The modes share the carrier and input rules. Module subobjects retain
linear combinations of defined input tensors, which a predicate on pure
tuples alone need not detect. Pure tuples still give the points at which
the partial operation is defined.
-/

open CategoryTheory SHIGURE.TensorRealization

universe u

noncomputable section

namespace SHIGURE

/-- A tensor structure may specify relations and domains in the actual input tensor modules. -/
structure TensorDomainStructure (R : Type u) [CommRing R] (sig : Signature.{u})
    extends TensorStructure R sig where
  /-- The submodule represented by each relation. -/
  rel (r : sig.Rel) : Submodule R (InputTensor R carrier (sig.relInputs r))
  /-- The submodule on which each partial operation is defined. -/
  dom (p : sig.Partial) : Submodule R (InputTensor R carrier (sig.partialArity p).inputs)
  /-- The linear value map on the chosen domain. -/
  partialValue (p : sig.Partial) : dom p →ₗ[R] carrier (sig.partialArity p).output

namespace TensorDomainStructure

variable {R : Type u} [CommRing R] {sig : Signature.{u}}

private def submoduleMonoOver {X : Type u} [AddCommGroup X] [Module R X]
    (P : Submodule R X) : MonoOver (ModuleCat.of R X) := by
  letI : Mono (ModuleCat.ofHom P.subtype) := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  exact MonoOver.mk (ModuleCat.ofHom P.subtype)

/-- The primitive rule of Definition 4.1 with the actual submodule inclusions and partial values. -/
def rule (R : Type u) [CommRing R] (sig : Signature.{u}) :
    StructureRule sig (Cat.of (ModuleCat.{u} R)) (TensorDomainStructure R sig) :=
  tensorPrimitiveRule R sig TensorDomainStructure.toTensorStructure
    (fun A r => submoduleMonoOver (A.rel r)) (fun A p => submoduleMonoOver (A.dom p))
    (fun A p => ModuleCat.ofHom (A.partialValue p))

/-- Objects with their fixed-coefficient maps, including every compatible linear family. -/
abbrev Diagrams (R : Type u) [CommRing R] (sig : Signature.{u}) := (rule R sig).Category

/-- Forget the submodule diagrams while retaining the maps that preserve total operations and quantities. -/
def forgetHom {A B : Diagrams R sig} (f : A ⟶ B) : A.toTensorStructure ⟶ B.toTensorStructure where
  onSort s := (f.val s).hom
  preservesTotal p := (tensorSquare_iff f.val (f.val _) (A.total p) (B.total p)).mp (f.property.total p)
  preservesQuantity q := (tensorSquare_iff f.val (f.val _) (A.quantity q) (B.quantity q)).mp
    (f.property.quantity q)

/-- The carrier maps determine a preserving arrow also in the presence of domains. -/
theorem hom_ext {A B : Diagrams R sig} {f g : A ⟶ B}
    (h : ∀ s, (f.val s).hom = (g.val s).hom) : f = g :=
  Subtype.ext (funext fun s => ModuleCat.hom_ext (h s))

/-- The linear map on the input tensor induced by a family of carrier maps. -/
def inputMap {A B : TensorStructure R sig}
    (f : A ⟶ B) (Γ : List sig.SortType) :
    InputTensor R A.carrier Γ →ₗ[R] InputTensor R B.carrier Γ :=
  PiTensorProduct.map (fun i : TensorPosition Γ => f.onSort i.1)

/-- Restrict a linear map to a submodule whose image is contained in the target submodule. -/
def factorThrough {X Y : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    {P : Submodule R X} {Q : Submodule R Y} (f : X →ₗ[R] Y) (h : ∀ x : P, f x ∈ Q) : P →ₗ[R] Q :=
  (f.comp P.subtype).codRestrict Q h

/-- Build the actual diagram arrow from its linear maps, membership preservation and partial values. -/
def homOfLinearMaps {A B : Diagrams R sig} (f : A.toTensorStructure ⟶ B.toTensorStructure)
    (rel : ∀ r : sig.Rel, ∀ x : A.rel r, inputMap f (sig.relInputs r) x ∈ B.rel r)
    (dom : ∀ p : sig.Partial, ∀ x : A.dom p, inputMap f (sig.partialArity p).inputs x ∈ B.dom p)
    (value : ∀ p : sig.Partial, ∀ x : A.dom p,
      f.onSort _ (A.partialValue p x) = B.partialValue p (factorThrough (inputMap f _) (dom p) x)) : A ⟶ B := by
  let F s := ModuleCat.ofHom (f.onSort s)
  refine ⟨F, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro p
    exact (tensorSquare_iff F (F _) (A.total p) (B.total p)).mpr (f.preservesTotal p)
  · intro r
    exact ⟨ModuleCat.ofHom (factorThrough (inputMap f _) (rel r)), ModuleCat.hom_ext rfl⟩
  · intro p
    refine ⟨ModuleCat.ofHom (factorThrough (inputMap f _) (dom p)), ModuleCat.hom_ext rfl, ?_⟩
    exact ModuleCat.hom_ext (LinearMap.ext fun x => (value p x).symm)
  · intro q
    exact (tensorSquare_iff F (F _) (A.quantity q) (B.quantity q)).mpr (f.preservesQuantity q)

/-- The target inclusion on a relation factor is the original linear input map on that submodule. -/
theorem rel_factor {A B : Diagrams R sig} (f : A ⟶ B) (r : sig.Rel) :
    ∃ d : A.rel r →ₗ[R] B.rel r, (B.rel r).subtype.comp d = (inputMap (forgetHom f) _).comp (A.rel r).subtype := by
  obtain ⟨d, hd⟩ := f.property.relation r
  exact ⟨d.hom, congrArg ModuleCat.Hom.hom hd⟩

/-- The partial-domain factor preserves both the input inclusion and the whole value map. -/
theorem dom_factor {A B : Diagrams R sig} (f : A ⟶ B) (p : sig.Partial) :
    ∃ d : A.dom p →ₗ[R] B.dom p,
      (B.dom p).subtype.comp d = (inputMap (forgetHom f) _).comp (A.dom p).subtype ∧
        (B.partialValue p).comp d = ((forgetHom f).onSort _).comp (A.partialValue p) := by
  obtain ⟨d, hd, hv⟩ := f.property.partialOp p
  exact ⟨d.hom, congrArg ModuleCat.Hom.hom hd, congrArg ModuleCat.Hom.hom hv⟩

/-- All linear families preserving the specified relation submodules, domains and their values. -/
structure LinearArrow (A B : TensorDomainStructure R sig) where
  /-- The carrier maps preserving total operations and quantities. -/
  underlying : A.toTensorStructure ⟶ B.toTensorStructure
  /-- Relation submodules map into the corresponding target submodules. -/
  relation (r : sig.Rel) (x : A.rel r) : inputMap underlying (sig.relInputs r) x ∈ B.rel r
  /-- Domain submodules map into the corresponding target submodules. -/
  domain (p : sig.Partial) (x : A.dom p) : inputMap underlying (sig.partialArity p).inputs x ∈ B.dom p
  /-- The output map commutes with each partial value on its entire domain. -/
  value (p : sig.Partial) (x : A.dom p) :
    underlying.onSort _ (A.partialValue p x) = B.partialValue p (factorThrough (inputMap underlying _) (domain p) x)

/-- Read the actual diagram factorization as linear maps and membership conditions. -/
def readLinearArrow {A B : Diagrams R sig} (f : A ⟶ B) : LinearArrow A B := by
  let base := forgetHom f
  have rel (r : sig.Rel) (x : A.rel r) : inputMap base (sig.relInputs r) x ∈ B.rel r := by
    obtain ⟨g, hg⟩ := rel_factor f r
    exact DFunLike.congr_fun hg x ▸ (g x).property
  have dom (p : sig.Partial) (x : A.dom p) : inputMap base (sig.partialArity p).inputs x ∈ B.dom p := by
    obtain ⟨g, hg, _⟩ := dom_factor f p
    exact DFunLike.congr_fun hg x ▸ (g x).property
  refine ⟨base, rel, dom, ?_⟩
  intro p x
  obtain ⟨g, hg, hv⟩ := dom_factor f p
  have h : g x = factorThrough (inputMap base _) (dom p) x := Subtype.ext (DFunLike.congr_fun hg x)
  rw [← h]
  exact (DFunLike.congr_fun hv x).symm

/-- The primitive diagram arrows are exactly the structure-preserving linear families. -/
def diagramHomEquiv (A B : Diagrams R sig) : (A ⟶ B) ≃ LinearArrow A B where
  toFun := readLinearArrow
  invFun f := homOfLinearMaps f.underlying f.relation f.domain f.value
  left_inv _ := hom_ext fun _ => rfl
  right_inv f := by cases f; rfl

/-- The fixed-coefficient category of these structures satisfying the specified Laws. -/
abbrev Models (T : RealizationTheory.{u}) (holds : TensorDomainStructure R T.signature → T.Statement → Prop) :=
  (show ObjectProperty (Diagrams R T.signature) from fun A => ∀ l : T.LawName, holds A (T.law l)).FullSubcategory

/-- The Law model category includes all the preserving arrows for its primitive diagrams. -/
def modelHomEquiv (T : RealizationTheory.{u}) (holds : TensorDomainStructure R T.signature → T.Statement → Prop)
    (A B : Models T holds) : (A ⟶ B) ≃ LinearArrow A.obj B.obj :=
  (show (A ⟶ B) ≃ (A.obj ⟶ B.obj) from ⟨fun f => f.hom, ObjectProperty.homMk, fun _ => rfl, fun _ => rfl⟩).trans
    (diagramHomEquiv A.obj B.obj)

end TensorDomainStructure
end SHIGURE
