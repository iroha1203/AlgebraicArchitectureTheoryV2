import Formal.SHIGURE.Part1.ContextSelectedPresentation
import Formal.SHIGURE.Part2.Realizations.CoefficientModels
import Formal.SHIGURE.Part2.Realizations.TensorInputs
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The tensor mode as a coefficient realization

The mode uses arbitrary module carriers and includes every linear family
preserving the specified operations. The coefficient rule compares the
changed carriers with actual scalar extensions and specifies the primitive
operations there on generating tuples. Construction 4.8 supplies this rule.

## Implementation notes

The comparison with scalar extension identifies the changed carriers
while permitting a mode to choose their representation. The unit
tensors generate each extended input module. Their images fix the
multilinear operations and give the coefficient map on specified points.
-/

open CategoryTheory SHIGURE.TensorRealization
open scoped TensorProduct MonoidalCategory

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

private def tensorNullaryIso (R : Type u) [CommRing R] (K : Type u) :
    tensorInputs R ([] : List K) ≅ (Functor.const (K → ModuleCat.{u} R)).obj (𝟙_ (ModuleCat.{u} R)) :=
  NatIso.ofComponents (fun A => (inputTensorUnit R A).toModuleIso) (by
    intro A B f
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change inputTensorUnit R B
      (PiTensorProduct.map (fun i : TensorPosition ([] : List K) => (f i.1).hom)
        (PiTensorProduct.tprod R x)) = inputTensorUnit R A (PiTensorProduct.tprod R x)
    rw [PiTensorProduct.map_tprod, inputTensorUnit_tprod, inputTensorUnit_tprod])

private def tensorConsIso (R : Type u) [CommRing R] {K : Type u} (s : K) (Γ : List K) :
    tensorInputs R (s :: Γ) ≅
      ((Pi.eval (fun _ : K => ModuleCat.{u} R) s).prod' (tensorInputs R Γ)) ⋙
        MonoidalCategory.tensor (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun A => (inputTensorCons R A s Γ).toModuleIso) (by
    intro A B f
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change inputTensorCons R B s Γ
        (PiTensorProduct.map (fun i : TensorPosition (s :: Γ) => (f i.1).hom)
          (PiTensorProduct.tprod R x)) =
      TensorProduct.map (f s).hom (PiTensorProduct.map (fun i : TensorPosition Γ => (f i.1).hom))
        (inputTensorCons R A s Γ (PiTensorProduct.tprod R x))
    rw [PiTensorProduct.map_tprod, inputTensorCons_tprod, inputTensorCons_tprod,
      TensorProduct.map_tmul, PiTensorProduct.map_tprod])

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

private def tensorTuplePoint {K : Type u} (Γ : List K) (A : K → ModuleCat.{u} R)
    (p : ∀ i : TensorPosition Γ, ModuleCat.of R R ⟶ A i.1) :
    ModuleCat.of R R ⟶ (tensorInputs R Γ).obj A :=
  (tensorPointEquiv _).symm (PiTensorProduct.tprod R (fun i => tensorPointEquiv (A i.1) (p i)))

/-- Total operations and quantities are the maps from their typed input tensor
products. The full-domain signature has no relation or partial symbols. -/
def tensorStructureRule (R : Type u) [CommRing R] (sig : Signature.{u})
    (scope : FullDomainTensorSignature sig) :
    StructureRule sig (Cat.of (ModuleCat.{u} R)) (TensorStructure R sig) where
  carrier A := A.carrier
  Ambient := Cat.of (ModuleCat.{u} R)
  view := 𝟭 _
  view_faithful := inferInstance
  input := tensorInputs R
  positionalInput Γ := tensorPositionInputs R (TensorPosition Γ)
  inputIso _ := Iso.refl _
  unaryIso := tensorUnaryIso R
  monoidal := inferInstanceAs (MonoidalCategory (ModuleCat.{u} R))
  fullInput := tensorInputs R
  fullInput_nil := tensorNullaryIso R _
  fullInput_cons := tensorConsIso R
  positiveInputComparison s Γ := 𝟙 (tensorInputs R (s :: Γ))
  positiveInputComparison_epi _ _ _ := inferInstanceAs (Epi (𝟙 _))
  pointObject := ModuleCat.of R R
  pointUnit := Iso.refl _
  nullaryInput := (tensorNullaryIso R _).symm
  total A op := ModuleCat.ofHom (PiTensorProduct.lift (A.total op))
  relation _ r := False.elim (scope.noRelations.false r)
  domain _ p := False.elim (scope.noPartial.false p)
  partialValue _ p := False.elim (scope.noPartial.false p)
  quantity A q := ModuleCat.ofHom (PiTensorProduct.lift (A.quantity q))

/-- The tensor input is generated by the comparisons of pure tuples of module elements. -/
def tensorInputPoints (R : Type u) [CommRing R] (sig : Signature.{u})
    (scope : FullDomainTensorSignature sig) : StructureInputPoints (tensorStructureRule R sig scope) where
  Probe := Cat.of (Discrete PUnit.{1})
  probe := (Functor.const _).obj (ModuleCat.of R R)
  tuplePoint _ Γ A p := tensorTuplePoint Γ A p
  tuplePoint_map P Γ {A B} f p := by
    apply (tensorPointEquiv _).injective
    change tensorPointEquiv ((tensorInputs R Γ).obj B) (tensorTuplePoint Γ A p ≫ (tensorInputs R Γ).map f) =
      tensorPointEquiv ((tensorInputs R Γ).obj B) (tensorTuplePoint Γ B (fun i => p i ≫ f i.1))
    simp only [tensorTuplePoint, tensorPointEquiv_map, Equiv.apply_symm_apply]
    exact PiTensorProduct.map_tprod (fun i : TensorPosition Γ => (f i.1).hom) _
  tuplePoint_restrict {P Q} f Γ A p := by
    change tensorTuplePoint Γ A (fun i => 𝟙 (ModuleCat.of R R) ≫ p i) = 𝟙 _ ≫ tensorTuplePoint Γ A p
    simp only [Category.id_comp]
  tuplePoint_ext Γ A {Y f g} h := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    have hx := congrArg (tensorPointEquiv Y)
      (h ⟨PUnit.unit⟩ (fun i => (tensorPointEquiv (A i.1)).symm (x i)))
    let point := tensorTuplePoint Γ A (fun i => (tensorPointEquiv (A i.1)).symm (x i))
    change f.hom (tensorPointEquiv ((tensorInputs R Γ).obj A) point) =
      g.hom (tensorPointEquiv ((tensorInputs R Γ).obj A) point) at hx
    simpa only [point, tensorTuplePoint, Equiv.apply_symm_apply] using hx

/-- A nullary tensor input is the coefficient module. -/
def tensorStructureRule_nullaryIso (R : Type u) [CommRing R] (sig : Signature.{u})
    (scope : FullDomainTensorSignature sig) :
    (tensorStructureRule R sig scope).input [] ≅
      (Functor.const (sig.SortType → ModuleCat.{u} R)).obj (𝟙_ (ModuleCat.{u} R)) :=
  tensorNullaryIso R _

/-- A further tensor input attaches its carrier by tensor product. -/
def tensorStructureRule_consIso (R : Type u) [CommRing R] (sig : Signature.{u})
    (scope : FullDomainTensorSignature sig) (s : sig.SortType) (Γ : List sig.SortType) :
    (tensorStructureRule R sig scope).input (s :: Γ) ≅
      ((Pi.eval (fun _ : sig.SortType => ModuleCat.{u} R) s).prod'
        ((tensorStructureRule R sig scope).input Γ)) ⋙ MonoidalCategory.tensor (ModuleCat.{u} R) :=
  tensorConsIso R s Γ

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

/-- The required equations define the tensor object property at one coefficient,
before supplying any rule for changing coefficients. -/
def tensorModelProperty {base : CoefficientRing.{u}} (T : RealizationTheory.{u})
    (S : CoefficientAlgebra base) (scope : FullDomainTensorSignature T.signature)
    (holds : TensorAt S.scalars T.signature → T.Statement → Prop) :
    letI := S.scalars.ring
    ObjectProperty (tensorStructureRule S.scalars.Carrier T.signature scope).Category :=
  fun A => True ∧ ∀ l : T.LawName, holds A (T.law l)

/-- The fixed-coefficient semantic category of any full-domain tensor presentation. -/
abbrev TensorModelsAt {base : CoefficientRing.{u}} (T : RealizationTheory.{u})
    (S : CoefficientAlgebra base) (scope : FullDomainTensorSignature T.signature)
    (holds : TensorAt S.scalars T.signature → T.Statement → Prop) :=
  (tensorModelProperty T S scope holds).FullSubcategory

/-- Evaluate the equation originally written in a tensor presentation. -/
def TensorTheory.holds {base : CoefficientRing.{u}} {L : Type u}
    (T : TensorTheory base sig L) (S : CoefficientAlgebra base)
    (A : TensorAt S.scalars sig) (law : T.presentation.Statement) : Prop :=
  letI := base.ring
  letI := S.scalars.ring
  (law.mapScalars S.fromBase).holds A

/-- The fixed-coefficient models of a theory of written tensor equations. -/
abbrev TensorTheory.Models {base : CoefficientRing.{u}} {L : Type u}
    (T : TensorTheory base sig L) (S : CoefficientAlgebra base) :=
  TensorModelsAt T.presentation S T.scope (T.holds S)

/-- The module carriers and primitive operations of a tensor mode, together with
the evaluation of its written statements. -/
def tensorModeOfPresentation (base : CoefficientRing.{u}) (T : RealizationTheory.{u})
    (scope : FullDomainTensorSignature T.signature) (rule : TensorCoefficientRule T.signature)
    (holds : ∀ S : CoefficientAlgebra base, TensorAt S.scalars T.signature → T.Statement → Prop) :
    CoefficientRealizationMode base T where
  Object S := TensorAt S.scalars T.signature
  Carrier S :=
    letI := S.scalars.ring
    Cat.of (ModuleCat.{u} S.scalars.Carrier)
  rule S :=
    letI := S.scalars.ring
    tensorStructureRule S.scalars.Carrier T.signature scope
  admissible _ _ := True
  Native := TensorAt base T.signature
  nativeStates A s :=
    letI := base.ring
    A.carrier s
  nativePointSource S _ :=
    letI := S.scalars.ring
    (tensorStructureRule S.scalars.Carrier T.signature scope).pointObject
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
  holds := holds

/-- Supplying a coefficient-change rule gives the same models at each fixed coefficient. -/
theorem tensorMode_modelProperty_eq (base : CoefficientRing.{u}) (T : RealizationTheory.{u})
    (scope : FullDomainTensorSignature T.signature) (rule : TensorCoefficientRule T.signature)
    (holds : ∀ S : CoefficientAlgebra base, TensorAt S.scalars T.signature → T.Statement → Prop)
    (S : CoefficientAlgebra base) :
    (tensorModeOfPresentation base T scope rule holds).modelProperty S =
      tensorModelProperty T S scope (holds S) := rfl

/-- The full-domain tensor mode evaluates the written equations of its
presentation using the specified scalar extension rule. -/
def tensorModeWithRule (base : CoefficientRing.{u}) {L : Type u}
    (T : TensorTheory base sig L) (rule : TensorCoefficientRule sig) :
    CoefficientRealizationMode base T.presentation :=
  tensorModeOfPresentation base T.presentation T.scope rule T.holds

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
    (S : CoefficientAlgebra base)
    (A : TensorAt S.scalars T.signature) :
    tensorModelProperty (read T scope reading).presentation S scope ((read T scope reading).holds S) A ↔
      (letI := S.scalars.ring
       ∀ l, (T.law l).Holds (A.elementStructure scope)) :=
  ⟨fun h l => ((reading l).correct S A).mp (h.2 l),
    fun h => ⟨trivial, fun l => ((reading l).correct S A).mpr (h l)⟩⟩

end TensorTheory

/-- The tensor meaning of exactly the required Law declarations retained by
a Part I context, with a tensor reading of each original statement. -/
abbrev PositiveLawTensorModels {P : PrimitivePresentation.{u}} (U : DeclarationContext P)
    {base : CoefficientRing.{u}} (S : CoefficientAlgebra base)
    (scope : FullDomainTensorSignature (DeclarationContext.Selected.presentation U).signature)
    (reading : ∀ l : (DeclarationContext.Selected.presentation U).theory.LawName,
      TensorLawReading base scope ((DeclarationContext.Selected.presentation U).theory.law l)) :=
  (TensorTheory.read (DeclarationContext.Selected.presentation U).theory scope reading).Models S

/-- An object of the selected tensor meaning satisfies each original required statement. -/
theorem positiveLawTensorModel_holds {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {base : CoefficientRing.{u}} {S : CoefficientAlgebra base}
    {scope : FullDomainTensorSignature (DeclarationContext.Selected.presentation U).signature}
    {reading : ∀ l : (DeclarationContext.Selected.presentation U).theory.LawName,
      TensorLawReading base scope ((DeclarationContext.Selected.presentation U).theory.law l)}
    (A : PositiveLawTensorModels U S scope reading)
    (l : (DeclarationContext.Selected.presentation U).theory.LawName) :
    letI := S.scalars.ring
    ((DeclarationContext.Selected.presentation U).theory.law l).Holds (A.obj.elementStructure scope) :=
  (TensorTheory.modelProperty_read_iff (DeclarationContext.Selected.presentation U).theory
    scope reading S A.obj).mp A.property l

end SHIGURE
