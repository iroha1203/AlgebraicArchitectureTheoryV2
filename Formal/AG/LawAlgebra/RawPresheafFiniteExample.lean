import Formal.AG.Examples.FiniteModel
import Formal.AG.LawAlgebra.StructureSheaf

noncomputable section

namespace AAT.AG.LawAlgebra.FiniteExamples.RawPresheaf

open CategoryTheory
open MvPolynomial

/-- The selected two-patch site used by the raw presheaf firing example. -/
abbrev Site := AAT.AG.FiniteModel.twoPatchSite

/-- SD3: the left patch as an object of the selected two-patch site. -/
def left : Site.category :=
  Site.ContextCategoryObject.of AAT.AG.FiniteModel.twoPatchContextPreorder
    (AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.left)

/-- SD3: one semantic coordinate on every context. -/
def coordFamily (W : Site.category) : CoordinateFamily W.ctx where
  Coord := Unit
  label := fun _ => CoordinateLabel.semantic
  LocalData := fun _ => Unit

/-- SD3: the selected nonzero structural equation `X² - 1`. -/
def relationFamily (W : Site.category) :
    StructuralRelationFamily (coordFamily W) Int where
  Relation := Unit
  polynomial := fun _ => X () ^ 2 - 1

/-- An objectwise sign used to make one restriction visibly nonidentity. -/
noncomputable def gauge (W : Site.category) : Int := by
  classical
  exact if W.ctx = left.ctx then -1 else 1

theorem gauge_sq (W : Site.category) : gauge W * gauge W = 1 := by
  classical
  unfold gauge
  split <;> simp

/-- SD3: variable restriction by the relative objectwise sign. -/
def coordinateRestriction {X Y : Site.category} (f : X ⟶ Y) :
  TypedCoordinateRestriction (coordFamily X) (coordFamily Y) Int
      (Site.contextPreorder.morphism (CategoryTheory.leOfHom f)) where
  variableImage := fun _ => C (gauge X * gauge Y) * MvPolynomial.X ()

theorem coordinateRestriction_polynomialMap_X {X Y : Site.category}
    (f : X ⟶ Y) :
    (coordinateRestriction f).polynomialMap (MvPolynomial.X ()) =
      C (gauge X * gauge Y) * MvPolynomial.X () := by
  rw [TypedCoordinateRestriction.polynomialMap_X]
  rfl

private theorem sign_sq {X Y : Site.category} :
    (gauge X * gauge Y) * (gauge X * gauge Y) = 1 := by
  calc
    (gauge X * gauge Y) * (gauge X * gauge Y) =
        (gauge X * gauge X) * (gauge Y * gauge Y) := by ring
    _ = 1 := by rw [gauge_sq, gauge_sq, one_mul]

private theorem polynomialMap_relation {X Y : Site.category} (f : X ⟶ Y) :
    (coordinateRestriction f).polynomialMap (MvPolynomial.X () ^ 2 - 1) =
      MvPolynomial.X () ^ 2 - 1 := by
  rw [map_sub, map_pow, coordinateRestriction_polynomialMap_X, map_one]
  simp only [mul_pow]
  rw [show C (gauge X * gauge Y) ^ 2 = 1 by
    rw [pow_two, ← C_mul, sign_sq, C_1]]
  simp

/-- SD3: the structural ideal is preserved by every selected restriction. -/
def restrictionStable {X Y : Site.category} (f : X ⟶ Y) :
    RestrictionStableStructuralRelations (relationFamily X) (relationFamily Y)
      (Site.contextPreorder.morphism (CategoryTheory.leOfHom f)) where
  restriction := coordinateRestriction f
  maps_JStruct := by
    intro p hp
    have hmap : Ideal.map (coordinateRestriction f).polynomialMap
        (relationFamily Y).JStruct ≤ (relationFamily X).JStruct := by
      rw [StructuralRelationFamily.JStruct, StructuralRelationFamily.JStruct,
        Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro q ⟨r, ⟨s, rfl⟩, rfl⟩
      cases s
      change (coordinateRestriction f).polynomialMap
          (MvPolynomial.X () ^ 2 - 1) ∈
        (relationFamily X).JStruct
      rw [polynomialMap_relation]
      exact Ideal.subset_span ⟨(), rfl⟩
    exact hmap (Ideal.mem_map_of_mem (coordinateRestriction f).polynomialMap hp)

private theorem coordinateRestriction_id (W : Site.category) :
    (coordinateRestriction (𝟙 W)).polynomialMap =
      RingHom.id (FreeTypedCommAlg (coordFamily W) Int) := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [TypedCoordinateRestriction.polynomialMap]
  · intro x
    cases x
    rw [coordinateRestriction_polynomialMap_X]
    simp [gauge_sq]

private theorem coordinateRestriction_comp {X Y Z : Site.category}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (coordinateRestriction (f ≫ g)).polynomialMap =
      ((coordinateRestriction f).polynomialMap).comp
        ((coordinateRestriction g).polynomialMap) := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [TypedCoordinateRestriction.polynomialMap]
  · intro x
    cases x
    by_cases hX : X.ctx = left.ctx
    · by_cases hY : Y.ctx = left.ctx
      · by_cases hZ : Z.ctx = left.ctx <;>
          simp [coordinateRestriction,
            TypedCoordinateRestriction.polynomialMap, gauge, hX, hY, hZ]
      · by_cases hZ : Z.ctx = left.ctx <;>
          simp [coordinateRestriction,
            TypedCoordinateRestriction.polynomialMap, gauge, hX, hY, hZ]
    · by_cases hY : Y.ctx = left.ctx
      · by_cases hZ : Z.ctx = left.ctx <;>
          simp [coordinateRestriction,
            TypedCoordinateRestriction.polynomialMap, gauge, hX, hY, hZ]
      · by_cases hZ : Z.ctx = left.ctx <;>
          simp [coordinateRestriction,
            TypedCoordinateRestriction.polynomialMap, gauge, hX, hY, hZ]

/-- SD3: a finite typed raw restriction system with a nonzero relation. -/
def system : RawAmbientRestrictionSystem Site Int where
  coordFamily := coordFamily
  relationFamily := relationFamily
  restrictionStable := restrictionStable
  identity_polynomialMap := coordinateRestriction_id
  composition_polynomialMap := coordinateRestriction_comp

/-- Characterization of the concrete restriction stored by the finite system. -/
theorem system_restriction {X Y : Site.category} (f : X ⟶ Y) :
    (system.restrictionStable f).restriction = coordinateRestriction f :=
  rfl

/-- SD3: the left patch includes into the base object. -/
def leftToBase : left ⟶ AAT.AG.FiniteModel.twoPatchBase :=
  CategoryTheory.homOfLE
    (AAT.AG.FiniteModel.twoPatchContextLe_sound
      (i := AAT.AG.FiniteModel.TwoPatchContextIndex.left)
      (j := AAT.AG.FiniteModel.TwoPatchContextIndex.base)
      (by simp [AAT.AG.FiniteModel.twoPatchContextIndexLe]))

/-- The selected left-to-base restriction sends the coordinate to its negative. -/
theorem leftToBase_polynomialMap_X :
    (system.restrictionStable leftToBase).restriction.polynomialMap (X ()) =
      -(X ()) := by
  rw [system_restriction]
  erw [coordinateRestriction_polynomialMap_X]
  have hne : AAT.AG.FiniteModel.twoPatchBase.ctx ≠ left.ctx := by
    intro h
    have heq := congrArg
      (fun W : Site.ArchitectureContext AAT.AG.FiniteModel.corePackage.object =>
        (⟨W.Extension, W.extension⟩ : Sigma fun T : Type => T)) h
    injection heq with _ hindex
    exact AAT.AG.FiniteModel.TwoPatchContextIndex.noConfusion hindex
  simp [gauge, hne]

/-- The structural relation vanishes in the raw quotient on the left patch. -/
theorem relation_vanishes :
    (system.relationFamily left).quotientMap (X () ^ 2 - 1) = 0 :=
  (system.relationFamily left).quotientMap_polynomial_eq_zero ()

/-- The selected structural polynomial is nonzero before quotienting. -/
theorem relation_polynomial_ne_zero :
    (MvPolynomial.X () ^ 2 - 1 : FreeTypedCommAlg (coordFamily left) Int) ≠ 0 := by
  intro h
  have heval := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => 0)) h
  simp at heval

/-- The structural quotient map has a concrete nonzero kernel element. -/
theorem quotientMap_not_injective :
    ¬ Function.Injective (system.relationFamily left).quotientMap := by
  intro hinjective
  apply relation_polynomial_ne_zero
  exact hinjective (by rw [relation_vanishes, map_zero])

/-- Evaluation at `X = 1`, used to distinguish the two coordinate classes. -/
def oneEval : FreeTypedCommAlg (coordFamily left) Int →+* Int :=
  MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => 1)

private theorem left_JStruct_le_ker_oneEval :
    (relationFamily left).JStruct ≤ RingHom.ker oneEval := by
  rw [StructuralRelationFamily.JStruct]
  apply Ideal.span_le.mpr
  rintro p ⟨r, rfl⟩
  cases r
  simp [relationFamily, oneEval]

/-- Evaluation at `1` descends through the selected structural quotient. -/
def quotientOneEval : system.rawAlgebra left →+* Int :=
  Ideal.Quotient.lift (relationFamily left).JStruct oneEval (by
    intro p hp
    exact left_JStruct_le_ker_oneEval hp)

theorem quotientOneEval_mk (p : FreeTypedCommAlg (coordFamily left) Int) :
    quotientOneEval ((relationFamily left).quotientMap p) = oneEval p :=
  rfl

/-- The relation `X² = 1` does not identify the two sign choices. -/
theorem quotient_X_ne_neg_X :
    (relationFamily left).quotientMap (X ()) ≠
      (relationFamily left).quotientMap (-(X ())) := by
  intro h
  have heval := congrArg quotientOneEval h
  simp [quotientOneEval_mk, oneEval] at heval

/-- The descended left-to-base restriction carries the coordinate to its negative. -/
theorem leftToBase_quotientDesc_X :
    (system.restrictionStable leftToBase).quotientDesc
        ((system.relationFamily AAT.AG.FiniteModel.twoPatchBase).quotientMap (X ())) =
      (system.relationFamily left).quotientMap (-(X ())) := by
  rw [RestrictionStableStructuralRelations.quotientDesc_mk,
    leftToBase_polynomialMap_X, map_neg]

/-- The finite descended restriction is visibly nonidentity on the coordinate. -/
theorem leftToBase_quotientDesc_X_ne_X :
    (system.restrictionStable leftToBase).quotientDesc
        ((system.relationFamily AAT.AG.FiniteModel.twoPatchBase).quotientMap (X ())) ≠
      (system.relationFamily left).quotientMap (X ()) := by
  rw [leftToBase_quotientDesc_X]
  exact Ne.symm quotient_X_ne_neg_X

/-- Coefficients are fixed by the finite descended restriction. -/
theorem leftToBase_quotientDesc_C :
    (system.restrictionStable leftToBase).quotientDesc
        ((system.relationFamily AAT.AG.FiniteModel.twoPatchBase).quotientMap (C (2 : Int))) =
      (system.relationFamily left).quotientMap (C (2 : Int)) :=
  RestrictionStableStructuralRelations.quotientDesc_C _ _

end AAT.AG.LawAlgebra.FiniteExamples.RawPresheaf
