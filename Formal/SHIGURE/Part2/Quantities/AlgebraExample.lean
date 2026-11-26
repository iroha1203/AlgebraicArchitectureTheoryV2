import Formal.SHIGURE.Part2.Quantities.Representation

/-!
# Recovering commutative and symmetric algebras

Example 5.6 recovers a commutative algebra from the equations stating that
the one quantity on its underlying set is an algebra homomorphism. The same
construction with the two linearity Laws recovers the symmetric algebra.
-/

universe u

noncomputable section

namespace SHIGURE.Quantities

variable (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]

/-- The fixed state sort in Example 5.6 carries the underlying elements. -/
private def algebraStateSignature : Signature.{u} where
  SortType := PUnit
  Total := PEmpty
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PEmpty
  totalArity := PEmpty.elim
  relInputs := PEmpty.elim
  partialArity := PEmpty.elim
  quantityArity := PEmpty.elim

/-- The state set is fixed while the coefficient-valued quantity varies. -/
private def elementStates : Structure algebraStateSignature.{u} where
  carrier _ := B
  total x := PEmpty.elim x
  relation x := PEmpty.elim x
  partialDomain x := PEmpty.elim x
  partialValue x := PEmpty.elim x
  quantity x := PEmpty.elim x

/-- The four groups of equations for the algebra recovery in Example 5.6. -/
inductive AlgebraLaw : Type u
  /-- Additivity. -/
  | add
  /-- Multiplicativity. -/
  | mul
  /-- Preservation of the unit. -/
  | one
  /-- Preservation of each coefficient from the base ring. -/
  | scalar

/-- Give the exact Law inputs, including all ordered pairs and every base coefficient. -/
private def algebraInput : AlgebraLaw.{u} → Type u
  | .add => B × B
  | .mul => B × B
  | .one => PUnit
  | .scalar => k

/-- The literal equality Laws from Example 5.6 on the single quantity of the elements. -/
def algebraPresentation : Presentation k (elementStates B) where
  Quantity := PUnit
  Domain _ := B
  Law := AlgebraLaw
  Input := algebraInput k B
  left
    | .add, x => .quantity ⟨PUnit.unit, x.1 + x.2⟩
    | .mul, x => .quantity ⟨PUnit.unit, x.1 * x.2⟩
    | .one, _ => .quantity ⟨PUnit.unit, 1⟩
    | .scalar, a => .quantity ⟨PUnit.unit, algebraMap k B a⟩
  right
    | .add, x => .add (.quantity ⟨PUnit.unit, x.1⟩) (.quantity ⟨PUnit.unit, x.2⟩)
    | .mul, x => .mul (.quantity ⟨PUnit.unit, x.1⟩) (.quantity ⟨PUnit.unit, x.2⟩)
    | .one, _ => .scalar 1
    | .scalar, a => .scalar a

variable {k B} {R : Type u} [CommRing R] [Algebra k R]

/-- An algebra homomorphism evaluates the one quantity and satisfies all four groups of equations. -/
def algebraModel (f : B →ₐ[k] R) : (algebraPresentation k B).Model R :=
  ⟨fun _ b => f b, by
    intro l e
    cases l with
    | add => exact map_add f e.1 e.2
    | mul => exact map_mul f e.1 e.2
    | one =>
      change f (1 : B) = algebraMap k R 1
      rw [map_one, map_one]
    | scalar => exact f.commutes e⟩

/-- The four groups of laws turn the quantity function into an actual algebra homomorphism. -/
def algebraHomOfModel (q : (algebraPresentation k B).Model R) : B →ₐ[k] R where
  toFun := q.val PUnit.unit
  map_zero' := by
    have h : q.val PUnit.unit (algebraMap k B 0) = algebraMap k R 0 := q.property AlgebraLaw.scalar (0 : k)
    simpa only [map_zero] using h
  map_one' := by
    have h : q.val PUnit.unit (1 : B) = algebraMap k R 1 := q.property AlgebraLaw.one PUnit.unit
    simpa only [map_one] using h
  map_add' b c := q.property AlgebraLaw.add (b, c)
  map_mul' b c := q.property AlgebraLaw.mul (b, c)
  commutes' a := q.property AlgebraLaw.scalar a

variable (k B)

/-- The Law algebra of this presentation recovers the original commutative algebra. -/
def lawAlgebraEquiv : (algebraPresentation k B).LawAlgebra ≃ₐ[k] B := by
  let P := algebraPresentation k B
  let f := P.modelAlgHomEquiv (algebraModel (AlgHom.id k B))
  let g : B →ₐ[k] P.LawAlgebra := algebraHomOfModel P.universalModel
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply AlgHom.ext
    intro b
    change P.evaluate (fun _ (x : B) => x) (P.universalQuantity PUnit.unit b) = b
    exact P.evaluate_X (fun _ (x : B) => x) ⟨PUnit.unit, b⟩
  · rw [← P.modelAlgHomEquiv_natural]
    have h : P.map g (algebraModel (AlgHom.id k B)) = P.universalModel := by
      apply Subtype.ext
      funext j b
      change P.universalModel.val PUnit.unit b = P.universalModel.val j b
      have hj : j = PUnit.unit := Subsingleton.elim (α := PUnit) _ _
      rw [hj]
    rw [h]
    exact P.modelAlgHomEquiv.apply_symm_apply _

section Symmetric

variable (N : Type u) [AddCommGroup N] [Module k N]

/-- The two linearity Laws for the second construction of Example 5.6. -/
inductive ModuleLaw : Type u
  /-- Preservation of addition on the module. -/
  | add
  /-- Preservation of scalar multiplication by every base coefficient. -/
  | smul

/-- Give the two kinds of inputs for the linearity Laws. -/
private def moduleInput : ModuleLaw.{u} → Type u
  | .add => N × N
  | .smul => k × N

/-- Equip the module's underlying set with the written additive and scalar Laws. -/
def modulePresentation : Presentation k (elementStates N) where
  Quantity := PUnit
  Domain _ := N
  Law := ModuleLaw
  Input := moduleInput k N
  left
    | .add, e => .quantity ⟨PUnit.unit, e.1 + e.2⟩
    | .smul, e => .quantity ⟨PUnit.unit, e.1 • e.2⟩
  right
    | .add, e => .add (.quantity ⟨PUnit.unit, e.1⟩) (.quantity ⟨PUnit.unit, e.2⟩)
    | .smul, e => .mul (.scalar e.1) (.quantity ⟨PUnit.unit, e.2⟩)

variable {k N}

/-- A linear map supplies a lawful quantity on the module. -/
def linearModel (f : N →ₗ[k] R) : (modulePresentation k N).Model R :=
  ⟨fun _ n => f n, by
    intro l e
    cases l with
    | add => exact map_add f e.1 e.2
    | smul =>
      change f (e.1 • e.2) = algebraMap k R e.1 * f e.2
      rw [map_smul, Algebra.smul_def]⟩

/-- The two Law families force the model's quantity function to be linear. -/
def linearMapOfModel (q : (modulePresentation k N).Model R) : N →ₗ[k] R where
  toFun := q.val PUnit.unit
  map_add' a b := q.property ModuleLaw.add (a, b)
  map_smul' a x := (q.property ModuleLaw.smul (a, x)).trans (Algebra.smul_def a _).symm

variable (k N)

/-- The Law algebra of the module presentation is the symmetric algebra. -/
def symmetricLawAlgebraEquiv : (modulePresentation k N).LawAlgebra ≃ₐ[k] SymmetricAlgebra k N := by
  let P := modulePresentation k N
  let q := linearModel (SymmetricAlgebra.ι k N)
  let f := P.modelAlgHomEquiv q
  let g := SymmetricAlgebra.lift (linearMapOfModel P.universalModel)
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    change f (g (SymmetricAlgebra.ι k N x)) = SymmetricAlgebra.ι k N x
    rw [SymmetricAlgebra.lift_ι_apply]
    change P.evaluate q.val (P.universalQuantity PUnit.unit x) = _
    exact P.evaluate_X q.val ⟨PUnit.unit, x⟩
  · rw [← P.modelAlgHomEquiv_natural]
    have h : P.map g q = P.universalModel := by
      apply Subtype.ext
      funext j x
      change g (SymmetricAlgebra.ι k N x) = P.universalModel.val j x
      have hj : j = PUnit.unit := Subsingleton.elim (α := PUnit) _ _
      rw [SymmetricAlgebra.lift_ι_apply, hj]
      rfl
    rw [h]
    exact P.modelAlgHomEquiv.apply_symm_apply _

end Symmetric

end SHIGURE.Quantities
