import Formal.SHIGURE.Part2.QuantityModels

/-!
# Transport of quantity coordinates and Laws

The coordinate map is induced by the map of named quantity inputs.
The equations are compared as written finite expressions. Each named
residual then maps to the residual at the transported Law input.

## Implementation notes

`QuantityMap` supplies the maps needed to form the correspondence.
`LawMap` adds the comparison of written equations needed to descend
through the whole target Law scheme. Recording only the quotient map
would lose its value on named coordinates and its derivation from the
Law inputs.
-/

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace SHIGURE.Quantities

variable {k : Type u} [CommRing k] {sig sig' sig'' : Signature.{u}}
variable {A : Structure sig} {B : Structure sig'} {D : Structure sig''}
variable {P : Presentation k A} {Q : Presentation k B} {W : Presentation k D}

/-- A map of the names and fixed domains of quantities. -/
structure QuantityMap (P : Presentation k A) (Q : Presentation k B) where
  /-- The corresponding name at the target. -/
  name : P.Quantity → Q.Quantity
  /-- The actual map on the fixed domain of the quantity. -/
  argument (j : P.Quantity) : P.Domain j → Q.Domain (name j)

namespace QuantityMap

variable (h : QuantityMap P Q)

/-- Transport the tagged coordinate, retaining its quantity name and argument. -/
def coordinate (x : P.Coordinate) : Q.Coordinate := ⟨h.name x.1, h.argument x.1 x.2⟩

/-- The polynomial map sends each universal variable to the variable of the transported input. -/
def polynomial : P.CoordinateAlgebra →ₐ[k] Q.CoordinateAlgebra :=
  MvPolynomial.rename h.coordinate

/-- The variable of a quantity is sent to the variable at its new name and argument. -/
@[simp]
theorem polynomial_X (x : P.Coordinate) :
    h.polynomial (MvPolynomial.X x) = MvPolynomial.X (h.coordinate x) :=
  MvPolynomial.rename_X h.coordinate x

/-- Pull back a candidate by precomposing all its quantities with the domain maps. -/
def candidate {R : Type u} (q : Q.Candidate R) : P.Candidate R :=
  fun j x => q (h.name j) (h.argument j x)

/-- Evaluation at the pullback candidate is evaluation after applying the coordinate map. -/
theorem evaluate_candidate {R : Type u} [CommRing R] [Algebra k R] (q : Q.Candidate R) :
    P.evaluate (h.candidate q) = (Q.evaluate q).comp h.polynomial := by
  symm
  apply P.evaluate_unique
  intro x
  rw [AlgHom.comp_apply, polynomial_X, Q.evaluate_X]
  rfl

/-- The identity preserves every name and every input. -/
def id (P : Presentation k A) : QuantityMap P P where
  name := _root_.id
  argument _ := _root_.id

/-- Compose the maps on names and domains. -/
def comp (g : QuantityMap Q W) : QuantityMap P W where
  name := g.name ∘ h.name
  argument j := g.argument (h.name j) ∘ h.argument j

/-- The coordinate map of the identity is the identity algebra map. -/
theorem polynomial_id : (QuantityMap.id P).polynomial = AlgHom.id k P.CoordinateAlgebra :=
  MvPolynomial.algHom_ext fun x => by rw [polynomial_X]; rfl

/-- The polynomial maps agree under composition. -/
theorem polynomial_comp (g : QuantityMap Q W) :
    (h.comp g).polynomial = g.polynomial.comp h.polynomial := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [polynomial_X, AlgHom.comp_apply, polynomial_X, polynomial_X]
  rfl

end QuantityMap

/-- A quantity map carries each required Law input and the two written sides of its equality. -/
structure LawMap (P : Presentation k A) (Q : Presentation k B) extends QuantityMap P Q where
  /-- The corresponding Law name. -/
  law : P.Law → Q.Law
  /-- The transport of specified inputs for that Law. -/
  input (l : P.Law) : P.Input l → Q.Input (law l)
  /-- Renaming the applications on the left gives the target's same written expression. -/
  left (l : P.Law) (e : P.Input l) :
    (P.left l e).rename toQuantityMap.coordinate = Q.left (law l) (input l e)
  /-- The same comparison for the right side. -/
  right (l : P.Law) (e : P.Input l) :
    (P.right l e).rename toQuantityMap.coordinate = Q.right (law l) (input l e)

namespace LawMap

variable (h : LawMap P Q)

omit [CommRing k] in
/-- Renaming coordinates with the identity preserves each written expression. -/
private theorem rename_identity {L : Type u} (t : Expression k L) : t.rename _root_.id = t := by
  induction t <;> simp [Expression.rename, *]

/-- The identity comparison keeps the written Laws and every required input. -/
def id (P : Presentation k A) : LawMap P P where
  toQuantityMap := QuantityMap.id P
  law := _root_.id
  input _ := _root_.id
  left l e := rename_identity (P.left l e)
  right l e := rename_identity (P.right l e)

/-- Compose the actual input maps by renaming each written expression twice. -/
def comp (g : LawMap Q W) : LawMap P W where
  toQuantityMap := h.toQuantityMap.comp g.toQuantityMap
  law := g.law ∘ h.law
  input l := g.input (h.law l) ∘ h.input l
  left l e := by
    change (P.left l e).rename (g.toQuantityMap.coordinate ∘ h.toQuantityMap.coordinate) = _
    rw [← Expression.rename_comp, h.left, g.left]
    rfl
  right l e := by
    change (P.right l e).rename (g.toQuantityMap.coordinate ∘ h.toQuantityMap.coordinate) = _
    rw [← Expression.rename_comp, h.right, g.right]
    rfl

/-- The coordinate algebra map sends the original residual to the designated target residual. -/
theorem polynomial_residual (l : P.Law) (e : P.Input l) :
    h.toQuantityMap.polynomial (P.residual l e) = Q.residual (h.law l) (h.input l e) := by
  have vars : h.toQuantityMap.polynomial ∘ (fun x : P.Coordinate => P.universalQuantity x.1 x.2) =
    (fun x : Q.Coordinate => Q.universalQuantity x.1 x.2) ∘ h.toQuantityMap.coordinate :=
    funext h.toQuantityMap.polynomial_X
  rw [Presentation.residual, Presentation.residual, map_sub, ← Expression.eval_map, ← Expression.eval_map,
    vars, ← Expression.eval_rename, ← Expression.eval_rename, h.left, h.right]

/-- The transported residual ideal is contained in the actual target residual ideal. -/
theorem residualIdeal_map_le : P.residualIdeal.map h.toQuantityMap.polynomial.toRingHom ≤ Q.residualIdeal := by
  rw [Ideal.map_le_iff_le_comap, P.residualIdeal_le_iff]
  intro l e
  change h.toQuantityMap.polynomial (P.residual l e) ∈ Q.residualIdeal
  rw [h.polynomial_residual]
  exact Q.residualIdeal_le_iff.mp le_rfl (h.law l) (h.input l e)

/-- The pullback of the target ideal contains the source ideal. -/
theorem residualIdeal_le_comap :
    P.residualIdeal ≤ Q.residualIdeal.comap h.toQuantityMap.polynomial.toRingHom :=
  Ideal.map_le_iff_le_comap.mp h.residualIdeal_map_le

/-- The induced map of the residual quotients. -/
def algebra : P.LawAlgebra →ₐ[k] Q.LawAlgebra :=
  Ideal.quotientMapₐ Q.residualIdeal h.toQuantityMap.polynomial h.residualIdeal_le_comap

/-- The comparison of Law quotients for the identity is the identity algebra map. -/
theorem algebra_id : (LawMap.id P).algebra = AlgHom.id k P.LawAlgebra := by
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk P.residualIdeal ((QuantityMap.id P).polynomial b) = _
  rw [QuantityMap.polynomial_id]
  rfl

/-- The comparison of Law quotients for a composite is the composite algebra map. -/
theorem algebra_comp (g : LawMap Q W) : (h.comp g).algebra = g.algebra.comp h.algebra := by
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk W.residualIdeal ((h.toQuantityMap.comp g.toQuantityMap).polynomial b) =
    Ideal.Quotient.mk W.residualIdeal (g.toQuantityMap.polynomial (h.toQuantityMap.polynomial b))
  rw [QuantityMap.polynomial_comp]
  rfl

/-- The map of the represented model spaces runs opposite the map of fixed domains. -/
def scheme : Q.lawScheme ⟶ P.lawScheme := specOverMap h.algebra

/-- The scheme comparison for the identity on the fixed structure is the identity. -/
theorem scheme_id : (LawMap.id P).scheme = 𝟙 P.lawScheme := by
  apply Over.OverMorphism.ext
  rw [scheme, specOverMap_left, algebra_id, Over.id_left]
  exact Spec.map_id _

/-- Taking spectra reverses the composition order of the structure comparisons. -/
theorem scheme_comp (g : LawMap Q W) : (h.comp g).scheme = g.scheme ≫ h.scheme := by
  apply Over.OverMorphism.ext
  simp only [scheme, Over.comp_left, specOverMap_left, algebra_comp]
  exact Spec.map_comp (CommRingCat.ofHom h.algebra.toRingHom) (CommRingCat.ofHom g.algebra.toRingHom)

/-- Pullback along a Law-preserving map takes every lawful target model to a lawful source model. -/
def model {R : Type u} [CommRing R] [Algebra k R] (q : Q.Model R) : P.Model R :=
  ⟨h.toQuantityMap.candidate q.val, fun l e => by
    change (P.left l e).eval ((fun x : Q.Coordinate => q.val x.1 x.2) ∘ h.toQuantityMap.coordinate) =
      (P.right l e).eval ((fun x : Q.Coordinate => q.val x.1 x.2) ∘ h.toQuantityMap.coordinate)
    rw [← Expression.eval_rename, ← Expression.eval_rename, h.left, h.right]
    exact q.property (h.law l) (h.input l e)⟩

/-- The map of the Law algebras computes pullback of model points before taking spectra. -/
theorem modelAlgHomEquiv_model {R : Type u} [CommRing R] [Algebra k R] (q : Q.Model R) :
    P.modelAlgHomEquiv (h.model q) = (Q.modelAlgHomEquiv q).comp h.algebra := by
  apply AlgHom.ext
  intro a
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change P.evaluate (h.toQuantityMap.candidate q.val) x = Q.evaluate q.val (h.toQuantityMap.polynomial x)
  exact AlgHom.congr_fun (h.toQuantityMap.evaluate_candidate q.val) x

/-- On every affine coefficient the scheme map is pullback by precomposition on the domains. -/
theorem modelAffinePointEquiv_model {R : Type u} [CommRing R] [Algebra k R] (q : Q.Model R) :
    P.modelAffinePointEquiv (h.model q) = Q.modelAffinePointEquiv q ≫ h.scheme := by
  apply Over.OverMorphism.ext
  change (specOverMap (P.modelAlgHomEquiv (h.model q))).left =
    (specOverMap (Q.modelAlgHomEquiv q)).left ≫ (specOverMap h.algebra).left
  rw [modelAlgHomEquiv_model, specOverMap_left, specOverMap_left, specOverMap_left]
  exact Spec.map_comp (CommRingCat.ofHom h.algebra.toRingHom) (CommRingCat.ofHom (Q.modelAlgHomEquiv q).toRingHom)

/-- Changing coefficients and pulling back domains commute on all models. -/
theorem model_map {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) (q : Q.Model R) : h.model (Q.map f q) = P.map f (h.model q) :=
  rfl

end LawMap
end SHIGURE.Quantities
