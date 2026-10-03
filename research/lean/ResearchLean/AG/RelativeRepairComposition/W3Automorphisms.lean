import ResearchLean.AG.RelativeRepairComposition.W3ActualArrows
import Mathlib.CategoryTheory.Endomorphism

/-! # Every W3 repair's complete actual automorphism group

The stabilizer is independent of the chosen correction and permission. Its
full labels are constant fixed vectors at the two original vertices. Both
the automorphism and its inverse are constructed in the actual groupoid.
-/
namespace AAT.AG.RelativeRepairComposition.W3Automorphisms
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3AuthoredOperations
open W3ActualRepairs W3GaugeLabels W3GaugeAction W3ActualArrows
attribute [local instance] actualAction

/-- Fixing either full actual repair requires equal original labels fixed by its loop transport. -/
theorem gauge_self_iff (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (b : GlobalLabels sheared S) (R : RealRepairs sheared S) :
    b +ᵥ R = R ↔ b.1 vertexT = b.1 vertexS ∧
      linearAction sheared (b.1 vertexS) = b.1 vertexS := by
  rw [gauge_eq_iff_parameters]
  constructor
  · intro h
    have he : b.1 vertexT - b.1 vertexS = 0 := by
      calc
        b.1 vertexT - b.1 vertexS =
            ((parameters R).1 + b.1 vertexT - b.1 vertexS) - (parameters R).1 := by abel_nf
        _ = 0 := by rw [h.1, sub_self]
    have hb := sub_eq_zero.mp he
    have hf : b.1 vertexS - linearAction sheared (b.1 vertexT) = 0 := by
      calc
        b.1 vertexS - linearAction sheared (b.1 vertexT) =
            ((parameters R).2 + b.1 vertexS - linearAction sheared (b.1 vertexT)) -
              (parameters R).2 := by abel_nf
        _ = 0 := by rw [h.2, sub_self]
    refine ⟨hb, ?_⟩
    rw [hb] at hf
    exact (sub_eq_zero.mp hf).symm
  · rintro ⟨hb,hf⟩
    rw [hb,hf]
    exact ⟨add_sub_cancel_right _ _, add_sub_cancel_right _ _⟩

/-- Every full fixed vector is a permitted constant label at both original vertices for every S. -/
def constantLabel (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (a : FixedVectors sheared) : GlobalLabels sheared S :=
  ⟨fun _ => a.1, by
    constructor
    · intro v hv; exact hv.elim
    · intro e he
      rcases e with ⟨i,j,e,hs,ht⟩
      cases hs
      cases ht
      fin_cases e
      · rfl
      · exact a.2.symm⟩

/-- A constant fixed-vector label fixes every complete independent actual operation. -/
theorem constant_fixes (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (a : FixedVectors sheared) (R : RealRepairs sheared S) :
    constantLabel sheared S a +ᵥ R = R :=
  (gauge_self_iff sheared S _ R).mpr ⟨rfl,a.2⟩

/-- Each original fixed vector constructs a full actual automorphism and its full inverse label. -/
noncomputable def vectorAut {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    (R : ActualCategory sheared S) (a : FixedVectors sheared) : Aut R where
  hom := ⟨Multiplicative.ofAdd (constantLabel sheared S a), constant_fixes sheared S a R.back⟩
  inv := ⟨Multiplicative.ofAdd (constantLabel sheared S (-a)), constant_fixes sheared S (-a) R.back⟩
  hom_inv_id := by
    apply Subtype.ext
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext v
    exact neg_add_cancel a.1
  inv_hom_id := by
    apply Subtype.ext
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext v
    exact add_neg_cancel a.1

/-- Every arbitrary actual automorphism retains a constant full fixed-vector label. -/
theorem aut_labels {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    (R : ActualCategory sheared S) (f : Aut R) (v : geometry.Vertex) :
    f.hom.1.toAdd.1 v = f.hom.1.toAdd.1 vertexS := by
  fin_cases v
  · rfl
  · exact ((gauge_self_iff sheared S f.hom.1.toAdd R.back).mp f.hom.2).1

/-- All actual automorphisms and all original fixed vectors have group inverses in both directions. -/
noncomputable def autFixedEquiv {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    (R : ActualCategory sheared S) : Aut R ≃* Multiplicative (FixedVectors sheared) where
  toFun f := Multiplicative.ofAdd ⟨f.hom.1.toAdd.1 vertexS,
    ((gauge_self_iff sheared S f.hom.1.toAdd R.back).mp f.hom.2).2⟩
  invFun a := vectorAut R a.toAdd
  left_inv f := by
    apply Aut.ext
    apply Subtype.ext
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext v
    exact (aut_labels R f v).symm
  right_inv _ := congrArg Multiplicative.ofAdd (Subtype.ext rfl)
  map_mul' _ _ := congrArg Multiplicative.ofAdd (Subtype.ext rfl)

/-- The forward coordinate retains the complete original vector at every original vertex. -/
theorem autFixedEquiv_label {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    (R : ActualCategory sheared S) (f : Aut R) (v : geometry.Vertex) :
    ((autFixedEquiv R f).toAdd).1 = f.hom.1.toAdd.1 v := (aut_labels R f v).symm

/-- Every actual shear repair's whole automorphism group is the specified full F3. -/
noncomputable def shearAutEquiv {S : Set (EdgeName (K := geometry))}
    (R : ActualCategory true S) : Aut R ≃* Multiplicative (ZMod 3) :=
  (autFixedEquiv R).trans shearFixedEquiv.toMultiplicative

/-- Every actual identity repair's whole automorphism group is the same entire A. -/
noncomputable def identityAutEquiv {S : Set (EdgeName (K := geometry))}
    (R : ActualCategory false S) : Aut R ≃* Multiplicative A :=
  (autFixedEquiv R).trans identityFixedEquiv.toMultiplicative

/-- All shear stabilizers have three distinct full original labels. -/
theorem shear_aut_card {S : Set (EdgeName (K := geometry))} (R : ActualCategory true S) :
    Nat.card (Aut R) = 3 := by
  rw [Nat.card_congr (shearAutEquiv R).toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- All identity stabilizers have nine distinct full original labels. -/
theorem identity_aut_card {S : Set (EdgeName (K := geometry))} (R : ActualCategory false S) :
    Nat.card (Aut R) = 9 := by
  rw [Nat.card_congr (identityAutEquiv R).toEquiv]
  simp [A, Nat.card_eq_fintype_card]

/-- Both unrestricted choices retain all 81 full vertex-label pairs before taking stabilizers. -/
theorem unrestricted_label_card (sheared : Bool) :
    Nat.card (GlobalLabels sheared candidates) = 81 := by
  rw [Nat.card_congr (unrestrictedLabelEquiv sheared).toEquiv]
  simp [A, Nat.card_eq_fintype_card]

end AAT.AG.RelativeRepairComposition.W3Automorphisms
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3Automorphisms
