import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.StrictSupportedCover
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses

/-!
# Binary assembly with all original shared edge and vertex conditions

## Implementation notes

Each child retains its original local equations and full compatible label
families. The binary condition compares every edge or vertex shared across
the children. Flattening is a direct finite-tuple operation; no intermediate
edge is eliminated. In particular candidate and unassembled shared values
are retained before the one-time generated coordinate equivalence is applied.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA uI uJ
namespace StrictBinary
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} {J : Type uJ}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K)
variable (U : I → ClosedRegion K) (V : J → ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))

/-- Both children keep the same original zero-through-three cells. -/
def regions : I ⊕ J → ClosedRegion K := Sum.elim U V

/-- The binary full-label condition keeps every cross-child shared vertex value. -/
def Labels : AddSubgroup ((StrictSupportedCover.Labels M P U candidates allowed) ×
    (StrictSupportedCover.Labels M P V candidates allowed)) where
  carrier := {b | ∀ i j v (hi : v ∈ (U i).vertices) (hj : v ∈ (V j).vertices),
    (b.1.1 i).1.1 ⟨v,hi⟩ = (b.2.1 j).1.1 ⟨v,hj⟩}
  zero_mem' := by intro i j v hi hj; rfl
  add_mem' := by
    intro b c hb hc i j v hi hj
    change (b.1.1 i).1.1 ⟨v,hi⟩ + (c.1.1 i).1.1 ⟨v,hi⟩ =
      (b.2.1 j).1.1 ⟨v,hj⟩ + (c.2.1 j).1.1 ⟨v,hj⟩
    rw [hb i j v hi hj,hc i j v hi hj]
  neg_mem' := by
    intro b hb i j v hi hj
    change -(b.1.1 i).1.1 ⟨v,hi⟩ = -(b.2.1 j).1.1 ⟨v,hj⟩
    rw [hb i j v hi hj]

/-- Flatten every full child label; all internal and cross-child equalities are used. -/
def flattenLabels (b : Labels M P U V candidates allowed) :
    StrictSupportedCover.Labels M P (regions U V) candidates allowed :=
  ⟨fun x => match x with | .inl i => b.1.1.1 i | .inr j => b.1.2.1 j,by
    intro x y v hx hy
    cases x with
    | inl i => cases y with
      | inl j => exact b.1.1.2 i j v hx hy
      | inr j => exact b.2 i j v hx hy
    | inr i => cases y with
      | inl j => exact (b.2 j i v hy hx).symm
      | inr j => exact b.1.2.2 i j v hx hy⟩

/-- Split the full strict original label family into its two children. -/
def unflattenLabels (b : StrictSupportedCover.Labels M P (regions U V) candidates allowed) :
    Labels M P U V candidates allowed :=
  ⟨(⟨fun i => b.1 (.inl i),fun i j v hi hj => b.2 (.inl i) (.inl j) v hi hj⟩,
    ⟨fun j => b.1 (.inr j),fun i j v hi hj => b.2 (.inr i) (.inr j) v hi hj⟩),
    fun i j v hi hj => b.2 (.inl i) (.inr j) v hi hj⟩

/-- Binary flattening retains the entire original label group. -/
def labelEquiv : Labels M P U V candidates allowed ≃+
    StrictSupportedCover.Labels M P (regions U V) candidates allowed where
  toFun := flattenLabels M P U V candidates allowed
  invFun := unflattenLabels M P U V candidates allowed
  left_inv b := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv b := by
    apply Subtype.ext
    funext x
    cases x <;> rfl
  map_add' b c := by
    apply Subtype.ext
    funext x
    cases x <;> rfl

variable (δ : RelativeCover.C2 M ClosedRegion.all P)

/-- Binary objects retain both full child tuples and all cross-child shared original edge conditions. -/
def Objects := {h : (StrictSupportedCover.Objects M P U candidates allowed δ) ×
    (StrictSupportedCover.Objects M P V candidates allowed δ) //
  ∀ i j e (hi : e ∈ (U i).edges) (hj : e ∈ (V j).edges),
    (h.1.1 i).1.1.1 ⟨e,hi⟩ = (h.2.1 j).1.1.1 ⟨e,hj⟩}

/-- Flatten the original local equations without changing any original edge or kernel value. -/
def flattenObjects (h : Objects M P U V candidates allowed δ) :
    StrictSupportedCover.Objects M P (regions U V) candidates allowed δ :=
  ⟨fun x => match x with | .inl i => h.1.1.1 i | .inr j => h.1.2.1 j,by
    intro x y e hx hy
    cases x with
    | inl i => cases y with
      | inl j => exact h.1.1.2 i j e hx hy
      | inr j => exact h.2 i j e hx hy
    | inr i => cases y with
      | inl j => exact (h.2 j i e hy hx).symm
      | inr j => exact h.1.2.2 i j e hx hy⟩

/-- Split every original local affine equation while retaining every cross-child constraint. -/
def unflattenObjects (h : StrictSupportedCover.Objects M P (regions U V) candidates allowed δ) :
    Objects M P U V candidates allowed δ :=
  ⟨(⟨fun i => h.1 (.inl i),fun i j e hi hj => h.2 (.inl i) (.inl j) e hi hj⟩,
    ⟨fun j => h.1 (.inr j),fun i j e hi hj => h.2 (.inr i) (.inr j) e hi hj⟩),
    fun i j e hi hj => h.2 (.inl i) (.inr j) e hi hj⟩

/-- Flatten/unflatten are mutually inverse on all original values and all child freedoms. -/
def objectEquiv : Objects M P U V candidates allowed δ ≃
    StrictSupportedCover.Objects M P (regions U V) candidates allowed δ where
  toFun := flattenObjects M P U V candidates allowed δ
  invFun := unflattenObjects M P U V candidates allowed δ
  left_inv h := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv h := by
    apply Subtype.ext
    funext x
    cases x <;> rfl

/-- Binary assembly acts by the full original strict gauge after flattening. -/
noncomputable def gauge (b : Labels M P U V candidates allowed)
    (h : Objects M P U V candidates allowed δ) : Objects M P U V candidates allowed δ :=
  (objectEquiv M P U V candidates allowed δ).symm
    (StrictSupportedCover.gauge M P (regions U V) candidates allowed δ
      (labelEquiv M P U V candidates allowed b) (objectEquiv M P U V candidates allowed δ h))

/-- The left child is acted on by its entire original compatible gauge family. -/
theorem gauge_left (b : Labels M P U V candidates allowed)
    (h : Objects M P U V candidates allowed δ) :
    (gauge M P U V candidates allowed δ b h).1.1 =
      StrictSupportedCover.gauge M P U candidates allowed δ b.1.1 h.1.1 := rfl

/-- The right child is acted on by its entire original compatible gauge family. -/
theorem gauge_right (b : Labels M P U V candidates allowed)
    (h : Objects M P U V candidates allowed δ) :
    (gauge M P U V candidates allowed δ b h).1.2 =
      StrictSupportedCover.gauge M P V candidates allowed δ b.1.2 h.1.2 := rfl

/-- The whole binary object is fixed by the zero full label. -/
theorem gauge_zero (h : Objects M P U V candidates allowed δ) :
    gauge M P U V candidates allowed δ 0 h = h := by
  apply (objectEquiv M P U V candidates allowed δ).injective
  change objectEquiv M P U V candidates allowed δ
    ((objectEquiv M P U V candidates allowed δ).symm _) = _
  rw [Equiv.apply_symm_apply,map_zero,StrictSupportedCover.gauge_zero]

/-- Gauge composition preserves the full sum of both child label families. -/
theorem gauge_add (b c : Labels M P U V candidates allowed)
    (h : Objects M P U V candidates allowed δ) :
    gauge M P U V candidates allowed δ (b+c) h =
      gauge M P U V candidates allowed δ b (gauge M P U V candidates allowed δ c h) := by
  apply (objectEquiv M P U V candidates allowed δ).injective
  simp only [gauge,Equiv.apply_symm_apply,map_add,StrictSupportedCover.gauge_add]

/-- All compatible full binary labels form the action, including every stabilizer. -/
noncomputable instance addAction : AddAction (Labels M P U V candidates allowed)
    (Objects M P U V candidates allowed δ) where
  vadd := gauge M P U V candidates allowed δ
  zero_vadd := gauge_zero M P U V candidates allowed δ
  add_vadd := gauge_add M P U V candidates allowed δ

/-- Binary assembly is the full native groupoid of original child objects and labels. -/
abbrev Groupoid := ActionCategory (Multiplicative (Labels M P U V candidates allowed))
  (Objects M P U V candidates allowed δ)

/-- Flattening commutes with every full original child gauge. -/
theorem equivariant (b : Multiplicative (Labels M P U V candidates allowed))
    (h : Objects M P U V candidates allowed δ) :
    objectEquiv M P U V candidates allowed δ (b • h) =
      (labelEquiv M P U V candidates allowed).toMultiplicative b •
        objectEquiv M P U V candidates allowed δ h :=
  (objectEquiv M P U V candidates allowed δ).apply_symm_apply _

/-- The binary comparison includes every original arrow and both inverse directions. -/
noncomputable def equivalence : Groupoid M P U V candidates allowed δ ≌
    StrictSupportedCover.Groupoid M P (regions U V) candidates allowed δ :=
  changedLabelEquivalence (labelEquiv M P U V candidates allowed).toMultiplicative
    (objectEquiv M P U V candidates allowed δ) (equivariant M P U V candidates allowed δ)

/-- The entire forward-inverse composite preserves original objects and transported arrows. -/
theorem functor_inverse :
    (equivalence M P U V candidates allowed δ).functor ⋙
      (equivalence M P U V candidates allowed δ).inverse = 𝟭 (Groupoid M P U V candidates allowed δ) :=
  changed_label_functor_inverse (labelEquiv M P U V candidates allowed).toMultiplicative
    (objectEquiv M P U V candidates allowed δ) (equivariant M P U V candidates allowed δ)

/-- The entire inverse-forward composite preserves every leaf tuple and full label. -/
theorem inverse_functor :
    (equivalence M P U V candidates allowed δ).inverse ⋙
      (equivalence M P U V candidates allowed δ).functor =
        𝟭 (StrictSupportedCover.Groupoid M P (regions U V) candidates allowed δ) :=
  changed_label_inverse_functor (labelEquiv M P U V candidates allowed).toMultiplicative
    (objectEquiv M P U V candidates allowed δ) (equivariant M P U V candidates allowed δ)

end StrictBinary
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
