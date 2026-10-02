import ResearchLean.AG.RelativeRepairComposition.RelativeStrictEquationAction
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses

/-!
# Full native actions on independently generated strict local equations

## Implementation notes

Every full permitted shared vertex label acts on the independent generated
object space. The action is proved to equal the full native generated action
at each region. All actual and generated arrows keep the original label, with
exact inverse functors in both directions.
-/
namespace AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction
open CategoryTheory TransportCoherence AbelianLiftingObstruction
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
universe uk uG uA uI
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable (M : LocalCoefficients.{uG,uA} K) [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ j, DecidablePred (· ∈ (U j).vertices)]
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k) (x : M.A s),
  M.edge e (a • x) = a • M.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)

variable (allowed : Set (EdgeName (K := K)))
local notation "Labels" => StrictSupportedCover.Labels M P U candidates allowed
local notation "Actual" values => RelativeGeneratedStrictCover.EquationObjects M U P values (candidates \ allowed)
local notation "Generated" values => RelativeGeneratedStrictCover.Objects M bases U P candidates hlinear ek ee ef values (candidates \ allowed)
local notation "E" values => RelativeGeneratedStrictCover.objectEquiv M bases U P candidates hlinear ek ee ef (candidates \ allowed) (Set.diff_subset (s := candidates) (t := allowed)) values

/-- All full strict labels act on the independently generated full object family. -/
noncomputable def gauge (values : ∀ j, RelativeCover.C2 M (U j) P)
    (b : Labels) (y : Generated values) : Generated values :=
  ((E values)) (Multiplicative.ofAdd b • ((E values)).symm y)

/-- The whole zero label fixes all public coordinates and all private kernel choices. -/
theorem gauge_zero (values : ∀ j, RelativeCover.C2 M (U j) P) (y : Generated values) :
    gauge M bases U P candidates hlinear ek ee ef allowed values 0 y = y := by
  change ((E values)) ((1 : Multiplicative Labels) • ((E values)).symm y) = y
  rw [one_smul,Equiv.apply_symm_apply]

/-- Composed strict labels preserve the entire original label addition. -/
theorem gauge_add (values : ∀ j, RelativeCover.C2 M (U j) P) (b c : Labels) (y : Generated values) :
    gauge M bases U P candidates hlinear ek ee ef allowed values (b+c) y =
      gauge M bases U P candidates hlinear ek ee ef allowed values b
        (gauge M bases U P candidates hlinear ek ee ef allowed values c y) := by
  change ((E values)) ((Multiplicative.ofAdd b * Multiplicative.ofAdd c) • ((E values)).symm y) =
    ((E values)) (Multiplicative.ofAdd b • ((E values)).symm ((E values) (Multiplicative.ofAdd c • ((E values)).symm y)))
  rw [Equiv.symm_apply_apply,mul_smul]

/-- All full native original labels remain as labels of generated strict arrows. -/
noncomputable instance addAction (values : ∀ j, RelativeCover.C2 M (U j) P) :
    AddAction Labels (Generated values) where
  vadd := gauge M bases U P candidates hlinear ek ee ef allowed values
  zero_vadd := gauge_zero M bases U P candidates hlinear ek ee ef allowed values
  add_vadd := gauge_add M bases U P candidates hlinear ek ee ef allowed values

/-- Every generated component has exactly the full native local label action. -/
theorem action_component (values : ∀ j, RelativeCover.C2 M (U j) P)
    (b : Multiplicative Labels) (y : Generated values) (j : I) :
    (b • y).1 j = Multiplicative.ofAdd (b.toAdd.1 j).1 • (y.1 j) := by
  change FiniteNative.generatedRelativeEquiv M bases (U j) P
      (ClosedRegion.privateAlwaysEdges U P candidates j) hlinear (values j) ek ee ef
      (Multiplicative.ofAdd (b.toAdd.1 j).1 •
        ((FiniteNative.generatedRelativeEquiv M bases (U j) P
          (ClosedRegion.privateAlwaysEdges U P candidates j) hlinear (values j) ek ee ef).symm (y.1 j))) = _
  rw [FiniteNative.generated_relative_equivariant,Equiv.apply_symm_apply]

/-- Full actual extraction commutes with all native strict labels. -/
theorem equivariant (values : ∀ j, RelativeCover.C2 M (U j) P)
    (b : Multiplicative Labels) (h : Actual values) :
    ((E values)) (b • h) = b • ((E values)) h := by
  change ((E values)) (b • h) = ((E values)) (b • ((E values)).symm ((E values) h))
  rw [Equiv.symm_apply_apply]

/-- All independent actual and generated native strict groupoids have label-preserving inverse functors. -/
noncomputable def equivalence (values : ∀ j, RelativeCover.C2 M (U j) P) :
    ActionCategory (Multiplicative Labels) (Actual values) ≌
      ActionCategory (Multiplicative Labels) (Generated values) :=
  changedLabelEquivalence (MulEquiv.refl (Multiplicative Labels)) ((E values))
    (equivariant M bases U P candidates hlinear ek ee ef allowed values)

/-- Forward native arrows retain the entire original strict label, including stabilizers. -/
theorem functor_label (values : ∀ j, RelativeCover.C2 M (U j) P)
    {x y : ActionCategory (Multiplicative Labels) (Actual values)} (f : x ⟶ y) :
    ((equivalence M bases U P candidates hlinear ek ee ef allowed values).functor.map f).1 = f.1 := rfl

/-- Inverse native arrows retain every original strict label value. -/
theorem inverse_label (values : ∀ j, RelativeCover.C2 M (U j) P)
    {x y : ActionCategory (Multiplicative Labels) (Generated values)} (f : x ⟶ y) :
    ((equivalence M bases U P candidates hlinear ek ee ef allowed values).inverse.map f).1 = f.1 := rfl

/-- Reconstructing after extraction restores every full object and native arrow exactly. -/
theorem functor_inverse (values : ∀ j, RelativeCover.C2 M (U j) P) :
    (equivalence M bases U P candidates hlinear ek ee ef allowed values).functor ⋙
      (equivalence M bases U P candidates hlinear ek ee ef allowed values).inverse = 𝟭 _ :=
  changed_label_functor_inverse (MulEquiv.refl (Multiplicative Labels)) ((E values))
    (equivariant M bases U P candidates hlinear ek ee ef allowed values)

/-- Extracting after reconstruction restores every generated full object and native arrow exactly. -/
theorem inverse_functor (values : ∀ j, RelativeCover.C2 M (U j) P) :
    (equivalence M bases U P candidates hlinear ek ee ef allowed values).inverse ⋙
      (equivalence M bases U P candidates hlinear ek ee ef allowed values).functor = 𝟭 _ :=
  changed_label_inverse_functor (MulEquiv.refl (Multiplicative Labels)) ((E values))
    (equivariant M bases U P candidates hlinear ek ee ef allowed values)

end AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.RelativeGeneratedStrictAction
