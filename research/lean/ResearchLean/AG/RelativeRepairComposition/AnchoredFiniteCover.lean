import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.AnchoredLocalEquation
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverAction
import ResearchLean.AG.RelativeRepairComposition.GeneratedRangeInclusion
import ResearchLean.AG.RelativeRepairComposition.StrictFunctorComparison

/-!
# Finite strict raw equations after an actual reference change

## Implementation notes

Local objects are independent raw new-reference affine equations with physical
anchor -a. Strict compatibility compares those raw values on each original
shared edge. Normalization adds the same actual lift difference at each leaf;
all full vertex labels remain unchanged. The original one-time local matrices
and sections therefore generate the normalized interfaces for every range.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uE uB uD vE vB vD uI
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace AnchoredFinite
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (T : OriginalTowerPresentation K p q)
variable (other : ∀ {i j : K.Vertex} (_ : K.Edge i j), FiberAut (p ⋙ q) (T.original.object j))
variable (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
  fiberPushforward p q (T.original.object j) (other e) = T.core e)
variable (P : ClosedRegion K) (U : I → ClosedRegion K)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (candidates allowed : Set (EdgeName (K := K)))
local notation "M" => T.toTower.localCoefficients
local notation "δ" => ActualEquation.defectFamily T P hfixed

/-- Independent raw local new-reference equations strictly agreeing on every shared original edge. -/
def Objects := {h : ∀ i,AnchoredLocal.Objects T other hother P (U i) candidates allowed //
  ∀ i j e (hi : e ∈ (U i).edges) (hj : e ∈ (U j).edges),
    (h i).1 ⟨e,hi⟩ = (h j).1 ⟨e,hj⟩}

/-- Normalize all raw local equations by their actual original lift difference. -/
noncomputable def normalize (h : Objects T other hother P U candidates allowed) :
    StrictSupportedCover.Objects M P U candidates allowed δ :=
  ⟨fun i => AnchoredLocal.normalize T other hother P (U i) hfixed candidates allowed (h.1 i),by
    intro i j e hi hj
    change (h.1 i).1 ⟨e,hi⟩ + T.alternativeCorrection other hother e =
      (h.1 j).1 ⟨e,hj⟩ + T.alternativeCorrection other hother e
    rw [h.2 i j e hi hj]⟩

/-- Recover all independent raw values by subtracting a on the same original edge names. -/
noncomputable def denormalize (h : StrictSupportedCover.Objects M P U candidates allowed δ) :
    Objects T other hother P U candidates allowed :=
  ⟨fun i => AnchoredLocal.denormalize T other hother P (U i) hfixed candidates allowed (h.1 i),by
    intro i j e hi hj
    change (h.1 i).1.1.1 ⟨e,hi⟩ - T.alternativeCorrection other hother e =
      (h.1 j).1.1.1 ⟨e,hj⟩ - T.alternativeCorrection other hother e
    rw [h.2 i j e hi hj]⟩

/-- Raw finite strict equations and normalized original equations retain all inverse object data. -/
noncomputable def objectEquiv : Objects T other hother P U candidates allowed ≃
    StrictSupportedCover.Objects M P U candidates allowed δ where
  toFun := normalize T other hother P U hfixed candidates allowed
  invFun := denormalize T other hother P U hfixed candidates allowed
  left_inv h := by
    apply Subtype.ext
    funext i
    exact (AnchoredLocal.objectEquiv T other hother P (U i) hfixed candidates allowed).symm_apply_apply (h.1 i)
  right_inv h := by
    apply Subtype.ext
    funext i
    exact (AnchoredLocal.objectEquiv T other hother P (U i) hfixed candidates allowed).apply_symm_apply (h.1 i)

/-- Every original permitted strict label acts directly on each independent raw local equation. -/
noncomputable def gauge (b : StrictSupportedCover.Labels M P U candidates allowed)
    (h : Objects T other hother P U candidates allowed) : Objects T other hother P U candidates allowed :=
  ⟨fun i => AnchoredLocal.gauge T other hother P (U i) candidates allowed (b.1 i) (h.1 i),by
    intro i j e hi hj
    have hd := congrArg (RelativeCover.d0 M (ClosedRegion.inter (U i) (U j)) P)
      (StrictSupportedCover.label_overlap M P U candidates allowed b i j)
    rw [← RelativeCover.r_d0,← RelativeCover.r_d0] at hd
    have hv := congrArg (fun c => c.1 ⟨e,⟨hi,hj⟩⟩) hd
    change (h.1 i).1 ⟨e,hi⟩ + (ClosedRegion.d0Hom M (U i) (b.1 i).1.1) ⟨e,hi⟩ =
      (h.1 j).1 ⟨e,hj⟩ + (ClosedRegion.d0Hom M (U j) (b.1 j).1.1) ⟨e,hj⟩
    exact congrArg₂ (· + ·) (h.2 i j e hi hj) hv⟩

/-- Normalization commutes with the full original strict label action. -/
theorem gauge_normalize (b : StrictSupportedCover.Labels M P U candidates allowed)
    (h : Objects T other hother P U candidates allowed) :
    objectEquiv T other hother P U hfixed candidates allowed
      (gauge T other hother P U candidates allowed b h) =
      StrictSupportedCover.gauge M P U candidates allowed δ b
        (objectEquiv T other hother P U hfixed candidates allowed h) := by
  apply Subtype.ext
  funext i
  exact AnchoredLocal.equivariant T other hother P (U i) hfixed candidates allowed
    (Multiplicative.ofAdd (b.1 i)) (h.1 i)

/-- Every raw local action is the original affine gauge, with all original vertex values. -/
theorem gauge_local (b : StrictSupportedCover.Labels M P U candidates allowed)
    (h : Objects T other hother P U candidates allowed) (i : I) :
    (gauge T other hother P U candidates allowed b h).1 i =
      AnchoredLocal.gauge T other hother P (U i) candidates allowed (b.1 i) (h.1 i) := rfl

/-- Full original labels, including stabilizers, act directly on the independent raw finite objects. -/
noncomputable instance addAction : AddAction (StrictSupportedCover.Labels M P U candidates allowed)
    (Objects T other hother P U candidates allowed) where
  vadd := gauge T other hother P U candidates allowed
  zero_vadd h := by
    apply Subtype.ext
    funext i
    exact AnchoredLocal.gauge_zero T other hother P (U i) candidates allowed (h.1 i)
  add_vadd b c h := by
    apply Subtype.ext
    funext i
    exact AnchoredLocal.gauge_add T other hother P (U i) candidates allowed (b.1 i) (c.1 i) (h.1 i)

/-- The native action is exactly the independently constructed raw original local gauge action. -/
theorem vadd_eq (b : StrictSupportedCover.Labels M P U candidates allowed)
    (h : Objects T other hother P U candidates allowed) :
    b +ᵥ h = gauge T other hother P U candidates allowed b h := rfl

/-- The native raw finite groupoid retains every compatible full original label arrow. -/
abbrev Groupoid := ActionCategory (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed))
  (Objects T other hother P U candidates allowed)

/-- The full native raw-reference equivalence preserves all original label values. -/
noncomputable def equivalence : Groupoid T other hother P U candidates allowed ≌
    StrictSupportedCover.Groupoid M P U candidates allowed δ :=
  changedLabelEquivalence (MulEquiv.refl (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)))
    (objectEquiv T other hother P U hfixed candidates allowed)
    (fun b h => gauge_normalize T other hother P U hfixed candidates allowed b.toAdd h)

/-- Both full functor composites recover all raw objects and all transported original arrows. -/
theorem functor_inverse : (equivalence T other hother P U hfixed candidates allowed).functor ⋙
    (equivalence T other hother P U hfixed candidates allowed).inverse =
      𝟭 (Groupoid T other hother P U candidates allowed) :=
  changed_label_functor_inverse (MulEquiv.refl (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)))
    (objectEquiv T other hother P U hfixed candidates allowed)
    (fun b h => gauge_normalize T other hother P U hfixed candidates allowed b.toAdd h)

/-- Both full functor composites recover every normalized tuple and every complete original label. -/
theorem inverse_functor : (equivalence T other hother P U hfixed candidates allowed).inverse ⋙
    (equivalence T other hother P U hfixed candidates allowed).functor =
      𝟭 (StrictSupportedCover.Groupoid M P U candidates allowed δ) :=
  changed_label_inverse_functor (MulEquiv.refl (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)))
    (objectEquiv T other hother P U hfixed candidates allowed)
    (fun b h => gauge_normalize T other hother P U hfixed candidates allowed b.toAdd h)

variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable [Fintype I] [DecidableEq I]
variable [∀ v, Module k ((T.toTower.localCoefficients).A v)]
variable (bases : FiniteFamily.Bases (k := k) (T.toTower.localCoefficients).A)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i,DecidablePred (· ∈ (U i).vertices)] [∀ i,DecidablePred (· ∈ (U i).edges)]
variable [∀ i,DecidablePred (· ∈ (U i).faces)] [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : (T.toTower.localCoefficients).A i),
  (T.toTower.localCoefficients).edge e (t • x) = t • (T.toTower.localCoefficients).edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)

/-- Raw shifted inputs use the same one-time original matrices and generated full sections after h'+a normalization. -/
noncomputable def generatedEquivalence : Groupoid T other hother P U candidates allowed ≌
    GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ ek ee ef allowed :=
  (equivalence T other hother P U hfixed candidates allowed).trans
    (GeneratedCoverAction.equivalence M bases P U candidates hlinear δ ek ee ef allowed)

/-- Every new raw original edge is reconstructed as the normalized generated value minus a. -/
theorem generated_inverse_value
    (y : GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ ek ee ef allowed)
    (i : I) (e : (U i).edges) :
    (((generatedEquivalence (k := k) T other hother P U hfixed candidates allowed bases hlinear ek ee ef).inverse.obj y).back.1 i).1 e =
      ((GeneratedStrictCover.restore M bases P U candidates hlinear δ ek ee ef allowed y.back).1 i).1.1.1 e -
        T.alternativeCorrection other hother e.1 := rfl

/-- Computed raw-reference interfaces have whole inverse functors on every independent raw object and arrow. -/
theorem generated_functor_inverse :
    (generatedEquivalence (k := k) T other hother P U hfixed candidates allowed bases hlinear ek ee ef).functor ⋙
      (generatedEquivalence (k := k) T other hother P U hfixed candidates allowed bases hlinear ek ee ef).inverse =
        𝟭 (Groupoid T other hother P U candidates allowed) :=
  strict_trans_functor_inverse _ _ (functor_inverse T other hother P U hfixed candidates allowed)
    (GeneratedCoverAction.functor_inverse M bases P U candidates hlinear δ ek ee ef allowed)

/-- Computed raw-reference interfaces retain every public value, private freedom and original arrow. -/
theorem generated_inverse_functor :
    (generatedEquivalence (k := k) T other hother P U hfixed candidates allowed bases hlinear ek ee ef).inverse ⋙
      (generatedEquivalence (k := k) T other hother P U hfixed candidates allowed bases hlinear ek ee ef).functor =
        𝟭 (GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ ek ee ef allowed) :=
  strict_trans_inverse_functor _ _ (inverse_functor T other hother P U hfixed candidates allowed)
    (GeneratedCoverAction.inverse_functor M bases P U candidates hlinear δ ek ee ef allowed)

variable {S V : Set (EdgeName (K := K))}
/-- Range relaxation retains the same independent raw values and the same actual shifted defect. -/
def objectsInclusion (h : S ⊆ V) (y : Objects T other hother P U candidates S) :
    Objects T other hother P U candidates V :=
  ⟨fun i => ⟨(y.1 i).1,⟨fun e he => (y.1 i).2.1 e
    (fixedEdgesForRange_antitone P.edges candidates h he),(y.1 i).2.2⟩⟩,y.2⟩

omit [Fintype I] [DecidableEq I] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [∀ i,DecidablePred (· ∈ (U i).vertices)] [∀ i,DecidablePred (· ∈ (U i).edges)]
  [∀ i,DecidablePred (· ∈ (U i).faces)] [DecidablePred (· ∈ candidates)]
  [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Raw range relaxation retains the entire original strict label action. -/
theorem inclusion_equivariant (h : S ⊆ V)
    (b : Multiplicative (StrictSupportedCover.Labels M P U candidates S))
    (y : Objects T other hother P U candidates S) :
    objectsInclusion T other hother P U candidates h (b • y) =
      (GeneratedRangeInclusion.labelsInclusion M P U candidates h).toMultiplicative b •
        objectsInclusion T other hother P U candidates h y := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rfl

/-- The full raw range functor retains all original raw values and every compatible original label. -/
noncomputable def rangeFunctor (h : S ⊆ V) : Groupoid T other hother P U candidates S ⥤
    Groupoid T other hother P U candidates V :=
  actionLabelFunctor (GeneratedRangeInclusion.labelsInclusion M P U candidates h).toMultiplicative
    (objectsInclusion T other hother P U candidates h)
    (inclusion_equivariant T other hother P U candidates h)

/-- The one-time normalized generation commutes with every allowed range inclusion as a whole functor. -/
theorem generated_range (h : S ⊆ V) :
    rangeFunctor T other hother P U candidates h ⋙
      (generatedEquivalence (k := k) T other hother P U hfixed candidates V bases hlinear ek ee ef).functor =
    (generatedEquivalence (k := k) T other hother P U hfixed candidates S bases hlinear ek ee ef).functor ⋙
      GeneratedRangeInclusion.functor M bases P U candidates hlinear δ ek ee ef h := rfl

/-- One-time generated reconstruction commutes with raw range relaxation on every object and arrow. -/
theorem generated_inverse_range (h : S ⊆ V) :
    GeneratedRangeInclusion.functor M bases P U candidates hlinear δ ek ee ef h ⋙
      (generatedEquivalence (k := k) T other hother P U hfixed candidates V bases hlinear ek ee ef).inverse =
    (generatedEquivalence (k := k) T other hother P U hfixed candidates S bases hlinear ek ee ef).inverse ⋙
      rangeFunctor T other hother P U candidates h := rfl

end AnchoredFinite
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
