import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteBinaryTuples
import ResearchLean.AG.RelativeRepairComposition.StrictSupportedCover
import ResearchLean.AG.RelativeRepairComposition.StrictFunctorComparison
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses
import Mathlib.Logic.Equiv.Basic

/-!
# All finite orders and parentheses of strict original assembly

## Implementation notes

The input tree stores actual product parentheses; its leaf bijection stores the
assembly order. Independent objects are nested tuples of original supported
local equations with every shared original edge condition. Flatten/unflatten
retains each full leaf and its full original label. No new intermediate
elimination is performed, so all candidate and unassembled shared edges survive.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA uI
namespace StrictFiniteAssembly
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K) (U : I → ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))
variable (δ : RelativeCover.C2 M ClosedRegion.all P)
variable (t : FiniteBinary.Tree) (σ : FiniteBinary.Leaves t ≃ I)

/-- Nested input tuples keep each independent full supported original leaf equation. -/
abbrev Nested := FiniteBinary.Tuple t (fun l => SupportedEquation.Objects M P (U (σ l)) candidates allowed δ)

/-- Each complete leaf value is read recursively, retaining its original region name. -/
def leafEquiv := FiniteBinary.tupleEquiv t
  (fun l => SupportedEquation.Objects M P (U (σ l)) candidates allowed δ)

/-- Flatten the nested tuple using the input order on the original region indices. -/
def tupleEquiv : Nested M P U candidates allowed δ t σ ≃
    (∀ i,SupportedEquation.Objects M P (U i) candidates allowed δ) :=
  (leafEquiv M P U candidates allowed δ t σ).trans
    (Equiv.piCongrLeft (fun i => SupportedEquation.Objects M P (U i) candidates allowed δ) σ)

/-- Flattening preserves every original leaf as a whole independent affine solution. -/
theorem tuple_leaf (h : Nested M P U candidates allowed δ t σ) (l : FiniteBinary.Leaves t) :
    tupleEquiv M P U candidates allowed δ t σ h (σ l) =
      leafEquiv M P U candidates allowed δ t σ h l :=
  Equiv.piCongrLeft_apply_apply
    (fun i => SupportedEquation.Objects M P (U i) candidates allowed δ) σ
    (leafEquiv M P U candidates allowed δ t σ h) l

/-- Independent nested objects impose equality on every shared original edge. -/
def Objects := {h : Nested M P U candidates allowed δ t σ //
  ∀ l m e (hl : e ∈ (U (σ l)).edges) (hm : e ∈ (U (σ m)).edges),
    (leafEquiv M P U candidates allowed δ t σ h l).1.1.1 ⟨e,hl⟩ =
      (leafEquiv M P U candidates allowed δ t σ h m).1.1.1 ⟨e,hm⟩}

/-- Flatten a compatible nested assembly, using every original shared-edge equality. -/
def flatten (h : Objects M P U candidates allowed δ t σ) :
    StrictSupportedCover.Objects M P U candidates allowed δ :=
  ⟨tupleEquiv M P U candidates allowed δ t σ h.1,by
    intro i j e hi hj
    obtain ⟨l,rfl⟩ := σ.surjective i
    obtain ⟨m,rfl⟩ := σ.surjective j
    rw [tuple_leaf,tuple_leaf]
    exact h.2 l m e hi hj⟩

/-- Reconstruct all original nested child equations and all original cross-child conditions. -/
def unflatten (h : StrictSupportedCover.Objects M P U candidates allowed δ) :
    Objects M P U candidates allowed δ t σ :=
  ⟨(tupleEquiv M P U candidates allowed δ t σ).symm h.1,by
    intro l m e hl hm
    rw [← tuple_leaf,← tuple_leaf,Equiv.apply_symm_apply]
    exact h.2 (σ l) (σ m) e hl hm⟩

/-- Every finite assembly order and parenthesis has full inverse flatten/unflatten algorithms. -/
def objectEquiv : Objects M P U candidates allowed δ t σ ≃
    StrictSupportedCover.Objects M P U candidates allowed δ where
  toFun := flatten M P U candidates allowed δ t σ
  invFun := unflatten M P U candidates allowed δ t σ
  left_inv h := Subtype.ext ((tupleEquiv M P U candidates allowed δ t σ).symm_apply_apply h.1)
  right_inv h := Subtype.ext ((tupleEquiv M P U candidates allowed δ t σ).apply_symm_apply h.1)

/-- An arbitrary full compatible original label acts on every nested original object. -/
noncomputable def gauge (b : StrictSupportedCover.Labels M P U candidates allowed)
    (h : Objects M P U candidates allowed δ t σ) : Objects M P U candidates allowed δ t σ :=
  (objectEquiv M P U candidates allowed δ t σ).symm
    (StrictSupportedCover.gauge M P U candidates allowed δ b
      (objectEquiv M P U candidates allowed δ t σ h))

/-- Flattened gauge action keeps the complete original local action on every leaf. -/
theorem gauge_flatten (b : StrictSupportedCover.Labels M P U candidates allowed)
    (h : Objects M P U candidates allowed δ t σ) :
    objectEquiv M P U candidates allowed δ t σ (gauge M P U candidates allowed δ t σ b h) =
      StrictSupportedCover.gauge M P U candidates allowed δ b
        (objectEquiv M P U candidates allowed δ t σ h) :=
  (objectEquiv M P U candidates allowed δ t σ).apply_symm_apply _

/-- Each nested original leaf is acted on by its full original vertex label. -/
theorem gauge_leaf (b : StrictSupportedCover.Labels M P U candidates allowed)
    (h : Objects M P U candidates allowed δ t σ) (l : FiniteBinary.Leaves t) :
    leafEquiv M P U candidates allowed δ t σ (gauge M P U candidates allowed δ t σ b h).1 l =
      SupportedEquation.gauge M P (U (σ l)) candidates allowed δ (b.1 (σ l))
        (leafEquiv M P U candidates allowed δ t σ h.1 l) := by
  have hv := congrArg (fun x => x.1 (σ l)) (gauge_flatten M P U candidates allowed δ t σ b h)
  change tupleEquiv M P U candidates allowed δ t σ _ (σ l) =
    SupportedEquation.gauge M P (U (σ l)) candidates allowed δ (b.1 (σ l))
      (tupleEquiv M P U candidates allowed δ t σ _ (σ l)) at hv
  simpa only [tuple_leaf] using hv

/-- Zero full label preserves every nested original child object. -/
theorem gauge_zero (h : Objects M P U candidates allowed δ t σ) :
    gauge M P U candidates allowed δ t σ 0 h = h := by
  apply (objectEquiv M P U candidates allowed δ t σ).injective
  rw [gauge_flatten,StrictSupportedCover.gauge_zero]

/-- The full original label sum composes every nested child gauge. -/
theorem gauge_add (b c : StrictSupportedCover.Labels M P U candidates allowed)
    (h : Objects M P U candidates allowed δ t σ) :
    gauge M P U candidates allowed δ t σ (b+c) h =
      gauge M P U candidates allowed δ t σ b (gauge M P U candidates allowed δ t σ c h) := by
  apply (objectEquiv M P U candidates allowed δ t σ).injective
  rw [gauge_flatten,gauge_flatten,gauge_flatten,StrictSupportedCover.gauge_add]

/-- All compatible original leaf labels act, including every original stabilizer. -/
noncomputable instance addAction : AddAction (StrictSupportedCover.Labels M P U candidates allowed)
    (Objects M P U candidates allowed δ t σ) where
  vadd := gauge M P U candidates allowed δ t σ
  zero_vadd := gauge_zero M P U candidates allowed δ t σ
  add_vadd := gauge_add M P U candidates allowed δ t σ

/-- The finite nested native groupoid retains all original full leaf labels as arrows. -/
abbrev Groupoid := ActionCategory (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed))
  (Objects M P U candidates allowed δ t σ)

/-- Whole object flattening is equivariant under the complete original label group. -/
theorem equivariant (b : Multiplicative (StrictSupportedCover.Labels M P U candidates allowed))
    (h : Objects M P U candidates allowed δ t σ) :
    objectEquiv M P U candidates allowed δ t σ (b • h) =
      b • objectEquiv M P U candidates allowed δ t σ h :=
  gauge_flatten M P U candidates allowed δ t σ b.toAdd h

/-- Full finite assembly is equivalent to strict original local equations on every object and arrow. -/
noncomputable def equivalence : Groupoid M P U candidates allowed δ t σ ≌
    StrictSupportedCover.Groupoid M P U candidates allowed δ :=
  changedLabelEquivalence (MulEquiv.refl (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)))
    (objectEquiv M P U candidates allowed δ t σ) (equivariant M P U candidates allowed δ t σ)

/-- Whole flatten-unflatten is the identity, including transported arrow endpoints. -/
theorem functor_inverse : (equivalence M P U candidates allowed δ t σ).functor ⋙
    (equivalence M P U candidates allowed δ t σ).inverse = 𝟭 (Groupoid M P U candidates allowed δ t σ) :=
  changed_label_functor_inverse (MulEquiv.refl (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)))
    (objectEquiv M P U candidates allowed δ t σ) (equivariant M P U candidates allowed δ t σ)

/-- Whole unflatten-flatten is the identity on all strict values and full labels. -/
theorem inverse_functor : (equivalence M P U candidates allowed δ t σ).inverse ⋙
    (equivalence M P U candidates allowed δ t σ).functor =
      𝟭 (StrictSupportedCover.Groupoid M P U candidates allowed δ) :=
  changed_label_inverse_functor (MulEquiv.refl (Multiplicative (StrictSupportedCover.Labels M P U candidates allowed)))
    (objectEquiv M P U candidates allowed δ t σ) (equivariant M P U candidates allowed δ t σ)

variable (t' : FiniteBinary.Tree) (σ' : FiniteBinary.Leaves t' ≃ I)
variable (t'' : FiniteBinary.Tree) (σ'' : FiniteBinary.Leaves t'' ≃ I)

/-- Arbitrary finite reordering and rebracketing is computed by flattening then reconstructing. -/
noncomputable def comparison : Groupoid M P U candidates allowed δ t σ ≌
    Groupoid M P U candidates allowed δ t' σ' :=
  strictComparison (equivalence M P U candidates allowed δ t σ).symm
    (equivalence M P U candidates allowed δ t' σ').symm

/-- All finite order and bracket comparisons restore the identical original local equations and arrows. -/
theorem comparison_rec : (comparison M P U candidates allowed δ t σ t' σ').functor ⋙
    (equivalence M P U candidates allowed δ t' σ').functor =
      (equivalence M P U candidates allowed δ t σ).functor :=
  strict_comparison_rec _ _ (inverse_functor M P U candidates allowed δ t' σ')

/-- All finite order and bracket changes compose as complete native functors. -/
theorem comparison_comp : (comparison M P U candidates allowed δ t σ t' σ').functor ⋙
    (comparison M P U candidates allowed δ t' σ' t'' σ'').functor =
      (comparison M P U candidates allowed δ t σ t'' σ'').functor :=
  strict_comparison_comp _ _ _ (inverse_functor M P U candidates allowed δ t' σ')

end StrictFiniteAssembly
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
