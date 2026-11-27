import Formal.SHIGURE.Part2.Realizations.PolynomialTerms
import Formal.SHIGURE.Part2.Tensor.CoefficientCoherence

/-! # Pulling back written polynomial Laws along affine coefficient maps -/

namespace SHIGURE.RealizationFamilies

open CategoryTheory SHIGURE.TensorRealization

noncomputable section

universe u

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S] [Algebra R S]
  {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}

/-- An arbitrary coefficient map preserves a written Law on the actual
extended realization, by comparing direct and iterated scalar extension. -/
theorem PolynomialLaw.holds_baseChange (l : PolynomialLaw k sig Γ s)
    (c : k →+* R) (A : TensorStructure R sig) (h : l.Holds c A) :
    l.Holds ((algebraMap R S).comp c) (extendStructure R S A) := by
  intro T _ _ x
  letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let e := structureScalarTower (k := R) (R := S) (S := T) A
  have injective : Function.Injective (e.hom.onSort s) := by
    change Function.Injective ((structureScalarTower (k := R) (R := S) (S := T) A).hom.onSort s)
    rw [structureScalarTower_hom_onSort]
    exact (scalarTower (k := R) (R := S) (S := T)).injective
  apply injective
  have sameCoefficients : (algebraMap S T).comp ((algebraMap R S).comp c) =
      (algebraMap R T).comp c := rfl
  rw [sameCoefficients, PolynomialTerm.eval_map, PolynomialTerm.eval_map]
  exact h T (fun i => e.hom.onSort i.1 (x i))

/-- Isomorphisms of tensor realizations preserve the truth of written Laws. -/
theorem PolynomialLaw.holds_iff_of_iso (l : PolynomialLaw k sig Γ s)
    (c : k →+* R) {A B : TensorStructure R sig} (e : A ≅ B) :
    l.Holds c A ↔ l.Holds c B := by
  have transport {X Y : TensorStructure R sig} (d : X ≅ Y) (h : l.Holds c X) : l.Holds c Y := by
    intro T _ _ y
    let X' := extendStructure R T X
    let Y' := extendStructure R T Y
    let d' : X' ≅ Y' := (extendStructureFunctor R T sig).mapIso d
    let x (i : TensorPosition Γ) : X'.carrier i.1 := d'.inv.onSort i.1 (y i)
    let c' := (algebraMap R T).comp c
    have recovered : (fun i : TensorPosition Γ => d'.hom.onSort i.1 (x i)) = y :=
      funext fun i => congrArg (fun f : Y' ⟶ Y' => f.onSort i.1 (y i)) d'.inv_hom_id
    have compare (t : PolynomialTerm k sig Γ s) :
        d'.hom.onSort s (t.eval c' X' x) = t.eval c' Y' y :=
      (PolynomialTerm.eval_map c' d'.hom x t).trans (congrArg (fun w => t.eval c' Y' w) recovered)
    exact (compare l.left).symm.trans ((congrArg (d'.hom.onSort s) (h T x)).trans (compare l.right))
  exact ⟨transport e, transport e.symm⟩

end

end SHIGURE.RealizationFamilies
