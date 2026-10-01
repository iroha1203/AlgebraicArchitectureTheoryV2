import ResearchLean.AG.RelativeRepairComposition.AffinePrimitiveFamily

/-!
# The whole original kernel coefficient system is reused

## Implementation notes

Native coefficient carriers are the entire actual categorical kernels. Equality
of real reference linear parts gives equality of their full edge equivalences,
using the whole-kernel coordinate injection. The generated bundled local system,
including its actual additive structures, is consequently the same at every
parameter. No choice of a parameter's repair enters this identification.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (L R L' R' : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c c' : K.TwoCell → A)
variable (hf : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
variable (hf' : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R' (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R' (K.twoRight f)).linear)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (tower K L R c hf))
local notation "M'" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (tower K L' R' c' hf'))

/-- Every native whole-kernel transport depends on the actual reference linear component alone. -/
theorem same_linear_edge (hR : ∀ {i j : K.Vertex}, ∀ e : K.Edge i j, (R' e).linear = (R e).linear)
    {i j : K.Vertex} (e : K.Edge i j) : (M').edge e = (M).edge e := by
  apply AddEquiv.ext
  intro x
  apply (coefficient K L R c hf j).injective
  calc
    _ = coefficient K L' R' c' hf' j ((M').edge e x) := rfl
    _ = (R' e).linear (coefficient K L' R' c' hf' i x) := edge_coefficient K L' R' c' hf' e x
    _ = (R e).linear (coefficient K L R c hf i x) := by rw [hR e]; rfl
    _ = _ := (edge_coefficient K L R c hf e x).symm

/-- The entire native local system, with its actual full kernel carriers, is the same whenever reference linear parts agree. -/
theorem same_linear_coefficients
    (hR : ∀ {i j : K.Vertex}, ∀ e : K.Edge i j, (R' e).linear = (R e).linear) :
    (M') = (M) := by
  have hinj : Function.Injective (fun m : LocalCoefficients K => m.toEdgeCoefficients) := by
    intro m n h
    cases m
    cases n
    cases h
    rfl
  apply hinj
  change EdgeCoefficients.mk _ _ _ = EdgeCoefficients.mk _ _ _
  congr 1
  funext i j e
  exact same_linear_edge K L R L' R' c c' hf hf' hR e

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Every primitive parameter reuses the same entire original native local system. -/
theorem family_local_coefficients
    (θL θR : V →ₗ[k] (EdgeName (K := K) → A)) (η : V →ₗ[k] (K.TwoCell → A)) (v : V) :
    (familyTower K L R c θL θR η hf v).toTower.localCoefficients =
      (tower K L R c hf).toTower.localCoefficients :=
  same_linear_coefficients K L R (familyOriginal K L θL v) (familyReference K R θR v)
    c (familyComparisons K c η v) hf (family_aligned K R θR hf v)
    (fun e => translated_linear K R (θR v) e)

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
