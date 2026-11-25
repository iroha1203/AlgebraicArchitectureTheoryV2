import Formal.SHIGURE.Part1.ContextSelectedPresentation
import Formal.SHIGURE.Part2.Realizations.CoefficientModels
import Formal.SHIGURE.Part2.Realizations.TensorExpressions
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The tensor mode as a coefficient realization

The mode uses arbitrary module carriers and includes every linear family
preserving the specified operations. The coefficient rule compares the
changed carriers with actual scalar extensions and specifies the primitive
operations there on generating tuples. Construction 4.8 supplies this rule.
-/

open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE

/-- Tensor structures over a specified coefficient ring. -/
abbrev TensorAt (R : CoefficientRing.{u}) (sig : Signature.{u}) :=
  letI := R.ring
  TensorStructure R.Carrier sig

variable {sig : Signature.{u}}

/-- A tensor coefficient rule specifies scalar-extended carriers and the
values of the changed operations on the generating tuples. -/
structure TensorCoefficientRule (sig : Signature.{u}) where
  /-- The raw structure at the new coefficient ring. -/
  change {R S : CoefficientRing.{u}} (f : R.Hom S) : TensorAt R sig → TensorAt S sig
  /-- The carrier comparison with extension of scalars. -/
  carrierIso {R S : CoefficientRing.{u}} (f : R.Hom S) (A : TensorAt R sig) (s : sig.SortType) :
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    (S.Carrier ⊗[R.Carrier] A.carrier s) ≃ₗ[S.Carrier] (change f A).carrier s
  /-- Changed operations take a tuple of unit tensors to the unit tensor of the original value. -/
  total_unit {R S : CoefficientRing.{u}} (f : R.Hom S) (A : TensorAt R sig) (op : sig.Total) :
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    ∀ (x : ∀ i : (s : sig.SortType) × Var (sig.totalArity op).inputs s, A.carrier i.1),
      (change f A).total op (fun i => carrierIso f A i.1 ((1 : S.Carrier) ⊗ₜ[R.Carrier] x i)) =
        carrierIso f A _ ((1 : S.Carrier) ⊗ₜ[R.Carrier] (A.total op x))
  /-- Changed quantities take a tuple of unit tensors to the unit tensor of the original value. -/
  quantity_unit {R S : CoefficientRing.{u}} (f : R.Hom S) (A : TensorAt R sig) (q : sig.Quantity) :
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    ∀ (x : ∀ i : (s : sig.SortType) × Var (sig.quantityArity q).inputs s, A.carrier i.1),
      (change f A).quantity q (fun i => carrierIso f A i.1 ((1 : S.Carrier) ⊗ₜ[R.Carrier] x i)) =
        carrierIso f A _ ((1 : S.Carrier) ⊗ₜ[R.Carrier] (A.quantity q x))

/-- The coefficient map on a state sends it to its unit tensor under the carrier comparison. -/
def TensorCoefficientRule.changeState (rule : TensorCoefficientRule sig)
    {R S : CoefficientRing.{u}} (f : R.Hom S) (A : TensorAt R sig) (s : sig.SortType) :
    letI := R.ring
    letI := S.ring
    A.carrier s → (rule.change f A).carrier s :=
  letI := R.ring
  letI := S.ring
  letI := f.toAlgebra
  fun x => rule.carrierIso f A s ((1 : S.Carrier) ⊗ₜ[R.Carrier] x)

variable {R : Type u} [CommRing R]

private def tensorPositionInputs (R : Type u) [CommRing R] (I : Type u) :
    (I → ModuleCat.{u} R) ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R (⨂[R] i : I, A i)
  map f := ModuleCat.ofHom (PiTensorProduct.map (fun i => (f i).hom))
  map_id A := by
    apply ModuleCat.hom_ext
    exact PiTensorProduct.map_id (s := fun i : I => A i)
  map_comp {A B D} f g := by
    apply ModuleCat.hom_ext
    have h := PiTensorProduct.map_comp (R := R)
      (s := fun i : I => (A i : Type u))
      (t := fun i : I => (B i : Type u))
      (t' := fun i : I => (D i : Type u))
      (fun i => (g i).hom) (fun i => (f i).hom)
    exact h

private abbrev tensorInputs (R : Type u) [CommRing R] {K : Type u} (Γ : List K) :
    (K → ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  Pi.comap (fun _ : K => ModuleCat.{u} R) (fun i : TensorPosition Γ => i.1) ⋙
    tensorPositionInputs R (TensorPosition Γ)

private def tensorUnaryIso (R : Type u) [CommRing R] {K : Type u} (s : K) :
    tensorInputs R [s] ≅ Pi.eval (fun _ : K => ModuleCat.{u} R) s :=
  NatIso.ofComponents (fun A => (singleArgumentEquiv A s).toModuleIso) (by
    intro A B f
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change singleArgumentEquiv B s
        (PiTensorProduct.map (fun i : TensorPosition [s] => (f i.1).hom) (PiTensorProduct.tprod R x)) =
      (f s).hom (singleArgumentEquiv A s (PiTensorProduct.tprod R x))
    rw [PiTensorProduct.map_tprod]
    exact (singleArgumentEquiv_tprod B s _).trans
      (congrArg (fun x => (f s).hom x) (singleArgumentEquiv_tprod A s x)).symm)

/-- Total operations and quantities are the maps from their typed input tensor
products. The full-domain signature has no relation or partial symbols. -/
def tensorStructureRule (R : Type u) [CommRing R] (sig : Signature.{u})
    (scope : FullDomainTensorSignature sig) :
    StructureRule sig (Cat.of (ModuleCat.{u} R)) (TensorStructure R sig) where
  carrier A := A.carrier
  input := tensorInputs R
  positionalInput Γ := tensorPositionInputs R (TensorPosition Γ)
  inputIso _ := Iso.refl _
  unaryIso := tensorUnaryIso R
  total A op := ModuleCat.ofHom (PiTensorProduct.lift (A.total op))
  relation _ r := False.elim (scope.noRelations.false r)
  domain _ p := False.elim (scope.noPartial.false p)
  partialValue _ p := False.elim (scope.noPartial.false p)
  quantity A q := ModuleCat.ofHom (PiTensorProduct.lift (A.quantity q))

private theorem tensorSquare_iff {K : Type u} {Γ : List K}
    {A B : K → ModuleCat.{u} R} {X Y : ModuleCat.{u} R}
    (f : ∀ s, A s ⟶ B s) (g : X ⟶ Y)
    (a : MultilinearMap R (fun i : TensorPosition Γ => A i.1) X)
    (b : MultilinearMap R (fun i : TensorPosition Γ => B i.1) Y) :
    ModuleCat.ofHom (PiTensorProduct.lift a) ≫ g =
      (tensorInputs R Γ).map f ≫ ModuleCat.ofHom (PiTensorProduct.lift b) ↔
    ∀ xs, g.hom (a xs) = b (fun i => (f i.1).hom (xs i)) := by
  constructor
  · intro h xs
    have h' := congrArg (fun k : (tensorInputs R Γ).obj A ⟶ Y =>
      k.hom (PiTensorProduct.tprod R xs)) h
    change g.hom (PiTensorProduct.lift a (PiTensorProduct.tprod R xs)) =
      PiTensorProduct.lift b
        (PiTensorProduct.map (fun i : TensorPosition Γ => (f i.1).hom)
          (PiTensorProduct.tprod R xs)) at h'
    simpa only [PiTensorProduct.lift.tprod, PiTensorProduct.map_tprod] using h'
  · intro h
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro xs
    change g.hom (PiTensorProduct.lift a (PiTensorProduct.tprod R xs)) =
      PiTensorProduct.lift b
        (PiTensorProduct.map (fun i : TensorPosition Γ => (f i.1).hom)
          (PiTensorProduct.tprod R xs))
    simpa only [PiTensorProduct.lift.tprod, PiTensorProduct.map_tprod] using h xs

/-- The primitive diagrams give exactly the linear families preserving the
tensor operations and quantities. -/
def tensorStructureHomEquiv (sig : Signature.{u}) (scope : FullDomainTensorSignature sig)
    (A B : (tensorStructureRule R sig scope).Category) :
    (A ⟶ B) ≃ TensorStructure.Hom A B where
  toFun h :=
    { onSort := fun s => (h.val s).hom
      preservesTotal := fun op => (tensorSquare_iff h.val (h.val _) (A.total op) (B.total op)).mp
        (h.property.total op)
      preservesQuantity := fun q => (tensorSquare_iff h.val (h.val _) (A.quantity q) (B.quantity q)).mp
        (h.property.quantity q) }
  invFun h := ⟨fun s => ModuleCat.ofHom (h.onSort s),
    { total := fun op => (tensorSquare_iff (fun s => ModuleCat.ofHom (h.onSort s)) _
        (A.total op) (B.total op)).mpr (h.preservesTotal op)
      relation := fun r => False.elim (scope.noRelations.false r)
      partialOp := fun p => False.elim (scope.noPartial.false p)
      quantity := fun q => (tensorSquare_iff (fun s => ModuleCat.ofHom (h.onSort s)) _
        (A.quantity q) (B.quantity q)).mpr (h.preservesQuantity q) }⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := TensorStructure.Hom.ext rfl

/-- A linear point from the scalar module is precisely an element of the carrier module. -/
def tensorPointEquiv (M : ModuleCat.{u} R) : (ModuleCat.of R R ⟶ M) ≃ M where
  toFun p := p.hom 1
  invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)
  left_inv p := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r • p.hom 1 = p.hom r
    rw [← map_smul, smul_eq_mul, mul_one]
  right_inv x := one_smul R x

/-- Acting on a tensor point agrees with applying the carrier linear map to its element. -/
theorem tensorPointEquiv_map {M N : ModuleCat.{u} R} (p : ModuleCat.of R R ⟶ M) (f : M ⟶ N) :
    tensorPointEquiv N (p ≫ f) = f.hom (tensorPointEquiv M p) :=
  rfl

/-- A tensor presentation gives the written equation of every required
declaration over the base coefficients. -/
structure TensorTheory (base : CoefficientRing.{u}) (sig : Signature.{u}) (Required : Type u) where
  /-- The primitive symbols interpreted by this full-domain presentation. -/
  scope : FullDomainTensorSignature sig
  /-- Each declaration's actual typed statement. -/
  law (name : Required) :
    letI := base.ring
    TensorLaw base.Carrier sig

/-- Use the written tensor equations as the required Law statements. -/
def TensorTheory.presentation {base : CoefficientRing.{u}} {L : Type u}
    (T : TensorTheory base sig L) : RealizationTheory.{u} where
  signature := sig
  LawName := L
  Statement :=
    letI := base.ring
    TensorLaw base.Carrier sig
  law := T.law

/-- The full-domain tensor mode of Definition 4.1 evaluates the equations of
its tensor presentation and uses the specified scalar extension rule. -/
def tensorMode (base : CoefficientRing.{u}) {L : Type u}
    (T : TensorTheory base sig L) (rule : TensorCoefficientRule sig) :
    CoefficientRealizationMode base T.presentation where
  Object S := TensorAt S.scalars sig
  Carrier S :=
    letI := S.scalars.ring
    Cat.of (ModuleCat.{u} S.scalars.Carrier)
  rule S :=
    letI := S.scalars.ring
    tensorStructureRule S.scalars.Carrier sig T.scope
  admissible _ _ := True
  Native := TensorAt base sig
  nativeStates A s :=
    letI := base.ring
    A.carrier s
  pointCarrier S _ :=
    letI := S.scalars.ring
    ModuleCat.of S.scalars.Carrier S.scalars.Carrier
  realizeNative S := rule.change S.fromBase
  nativePoints S A s x :=
    letI := S.scalars.ring
    (tensorPointEquiv ((rule.change S.fromBase A).carrier s)).symm (rule.changeState S.fromBase A s x)
  change f := rule.change f
  changePoints {S S'} f A s p :=
    letI := S.scalars.ring
    letI := S'.ring
    (tensorPointEquiv ((rule.change f A).carrier s)).symm
      (rule.changeState f A s (tensorPointEquiv (A.carrier s) p))
  holds S A law :=
    letI := base.ring
    letI := S.scalars.ring
    (law.mapScalars S.fromBase).holds A

/-- Evaluate the primitive symbols on the elements of the module carriers. -/
def TensorStructure.elementStructure (A : TensorStructure R sig) (scope : FullDomainTensorSignature sig) :
    Structure sig where
  carrier s := A.carrier s
  total op xs := A.total op (fun i => xs.get i.2)
  relation r := False.elim (scope.noRelations.false r)
  partialDomain p := False.elim (scope.noPartial.false p)
  partialValue p := False.elim (scope.noPartial.false p)
  quantity q xs := A.quantity q (fun i => xs.get i.2)

/-- Read an existing positive Law by a typed tensor equation when its two
readings agree on the actual primitive operations at every coefficient algebra. -/
structure TensorLawReading (base : CoefficientRing.{u}) (scope : FullDomainTensorSignature sig)
    (source : Law sig) where
  /-- Its proposed tensor equation over the base. -/
  equation :
    letI := base.ring
    TensorLaw base.Carrier sig
  /-- The equation interprets the written source Law at every coefficient. -/
  correct (S : CoefficientAlgebra base) (A : TensorAt S.scalars sig) :
    letI := base.ring
    letI := S.scalars.ring
    (equation.mapScalars S.fromBase).holds A ↔ source.Holds (A.elementStructure scope)

namespace TensorTheory

/-- A tensor presentation of a previously written theory uses all its required
names and the reading of the original statement at each name. -/
def read {base : CoefficientRing.{u}} (T : Theory.{u})
    (scope : FullDomainTensorSignature T.signature)
    (reading : ∀ l : T.LawName, TensorLawReading base scope (T.law l)) :
    TensorTheory base T.signature T.LawName :=
  ⟨scope, fun l => (reading l).equation⟩

/-- The semantic object condition reads every written Law of the source theory. -/
theorem modelProperty_read_iff {base : CoefficientRing.{u}} (T : Theory.{u})
    (scope : FullDomainTensorSignature T.signature)
    (reading : ∀ l : T.LawName, TensorLawReading base scope (T.law l))
    (rule : TensorCoefficientRule T.signature) (S : CoefficientAlgebra base)
    (A : TensorAt S.scalars T.signature) :
    (tensorMode base (read T scope reading) rule).modelProperty S A ↔
      (letI := S.scalars.ring
       ∀ l, (T.law l).Holds (A.elementStructure scope)) :=
  ⟨fun h l => ((reading l).correct S A).mp (h.2 l),
    fun h => ⟨trivial, fun l => ((reading l).correct S A).mpr (h l)⟩⟩

end TensorTheory

/-- The tensor meaning of exactly the required Law declarations retained by
a Part I context, with a tensor reading of each original statement. -/
abbrev SelectedTensorModels {P : PrimitivePresentation.{u}} (U : DeclarationContext P)
    {base : CoefficientRing.{u}} (S : CoefficientAlgebra base)
    (scope : FullDomainTensorSignature (DeclarationContext.Selected.presentation U).signature)
    (reading : ∀ l : (DeclarationContext.Selected.presentation U).theory.LawName,
      TensorLawReading base scope ((DeclarationContext.Selected.presentation U).theory.law l))
    (rule : TensorCoefficientRule (DeclarationContext.Selected.presentation U).signature) :=
  (tensorMode base
    (TensorTheory.read (DeclarationContext.Selected.presentation U).theory scope reading) rule).Models S

/-- An object of the selected tensor meaning satisfies each original required statement. -/
theorem selectedTensorModel_holds {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {base : CoefficientRing.{u}} {S : CoefficientAlgebra base}
    {scope : FullDomainTensorSignature (DeclarationContext.Selected.presentation U).signature}
    {reading : ∀ l : (DeclarationContext.Selected.presentation U).theory.LawName,
      TensorLawReading base scope ((DeclarationContext.Selected.presentation U).theory.law l)}
    {rule : TensorCoefficientRule (DeclarationContext.Selected.presentation U).signature}
    (A : SelectedTensorModels U S scope reading rule)
    (l : (DeclarationContext.Selected.presentation U).theory.LawName) :
    letI := S.scalars.ring
    ((DeclarationContext.Selected.presentation U).theory.law l).Holds (A.obj.elementStructure scope) :=
  (TensorTheory.modelProperty_read_iff (DeclarationContext.Selected.presentation U).theory
    scope reading rule S A.obj).mp A.property l

end SHIGURE
