import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.ReferenceShift
import ResearchLean.AG.RelativeRepairComposition.SupportedNativeEquation
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses

/-!
# Independent raw local equations for actual reference changes

## Implementation notes

The new raw face defect is read from the actual alternative lift. It need not
vanish on P. Raw edge values on every physically fixed original edge are -a.
Adding the actual full-kernel lift difference normalizes the equation to the
original relative complex, with no assumption that a vanishes on P.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace AnchoredLocal
variable (T : OriginalTowerPresentation K p q)
variable (other : ∀ {i j : K.Vertex} (_ : K.Edge i j), FiberAut (p ⋙ q) (T.original.object j))
variable (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
  fiberPushforward p q (T.original.object j) (other e) = T.core e)
variable (P U : ClosedRegion K)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (candidates allowed : Set (EdgeName (K := K)))
local notation "M" => T.toTower.localCoefficients
local notation "δ" => ActualEquation.defectFamily T P hfixed

/-- The original full-kernel lift difference restricted on unchanged original edge names. -/
noncomputable def shift : ClosedRegion.C1 M U :=
  ClosedRegion.r1 M U (T.alternativeCorrection other hother)

/-- The raw local new-reference defect is constructed from actual alternative lift arrows. -/
noncomputable def defect : ClosedRegion.C2 M U :=
  ClosedRegion.r2 M U (T.alternativeDefect other hother)

/-- The actual new defect is the old raw defect plus d1 of the actual lift difference. -/
theorem defect_shift : defect T other hother U =
    (CoverEquation.defect M P δ U).1 + ClosedRegion.d1Hom M U (shift T other hother U) := by
  change ClosedRegion.r2 M U (T.alternativeDefect other hother) = _
  change ClosedRegion.r2 M U (T.toTower.correctedDefect (T.alternativeCorrection other hother)) = _
  rw [T.toTower.correctedDefect_eq,map_add,ClosedRegion.r_d1]
  rfl

/-- Independent raw new-reference solutions keep the physical anchor -a on every fixed named edge. -/
def Objects := {h : ClosedRegion.C1 M U //
  (∀ e : U.edges, e.1 ∈ fixedEdgesForRange P.edges candidates allowed →
    h e = -shift T other hother U e) ∧
  ClosedRegion.d1Hom M U h = -defect T other hother U}

/-- Normalize the independent raw equation by adding a on every original edge. -/
noncomputable def normalize (h : Objects T other hother P U candidates allowed) :
    SupportedEquation.Objects M P U candidates allowed δ := by
  let c : RelativeCover.C1 M U P := ⟨h.1 + shift T other hother U,by
    intro e hp
    change h.1 e + shift T other hother U e = 0
    rw [h.2.1 e (Or.inl hp),neg_add_cancel]⟩
  refine ⟨⟨c,?_⟩,?_⟩
  · apply Subtype.ext
    change ClosedRegion.d1Hom M U (h.1 + shift T other hother U) = -(CoverEquation.defect M P δ U).1
    rw [map_add,h.2.2,defect_shift T other hother P U hfixed]
    abel
  · intro e he
    change h.1 e + shift T other hother U e = 0
    rw [h.2.1 e (Or.inr he),neg_add_cancel]

/-- Recover the independent raw equation by subtracting the actual lift difference. -/
noncomputable def denormalize (h : SupportedEquation.Objects M P U candidates allowed δ) :
    Objects T other hother P U candidates allowed := by
  refine ⟨h.1.1.1 - shift T other hother U,⟨?_,?_⟩⟩
  · intro e he
    change h.1.1.1 e - shift T other hother U e = -shift T other hother U e
    rcases he with hp | hs
    · rw [h.1.1.2 e hp,zero_sub]
    · rw [h.2 e hs,zero_sub]
  · rw [map_sub]
    have hh := congrArg Subtype.val h.1.2
    change ClosedRegion.d1Hom M U h.1.1.1 = -(CoverEquation.defect M P δ U).1 at hh
    rw [hh,defect_shift T other hother P U hfixed]
    abel

/-- Raw shifted equations and the old supported equations are inverse on all original values. -/
noncomputable def objectEquiv : Objects T other hother P U candidates allowed ≃
    SupportedEquation.Objects M P U candidates allowed δ where
  toFun := normalize T other hother P U hfixed candidates allowed
  invFun := denormalize T other hother P U hfixed candidates allowed
  left_inv h := by
    apply Subtype.ext
    change (h.1 + shift T other hother U) - shift T other hother U = h.1
    abel
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (h.1.1.1 - shift T other hother U) + shift T other hother U = h.1.1.1
    abel

/-- Normalization retains each original named-edge value as h'+a. -/
theorem normalize_value (h : Objects T other hother P U candidates allowed) (e : U.edges) :
    (normalize T other hother P U hfixed candidates allowed h).1.1.1 e =
      h.1 e + shift T other hother U e := rfl

/-- Denormalization returns h-a even on the physically fixed original edges. -/
theorem denormalize_value (h : SupportedEquation.Objects M P U candidates allowed δ) (e : U.edges) :
    (denormalize T other hother P U hfixed candidates allowed h).1 e =
      h.1.1.1 e - shift T other hother U e := rfl

/-- Every fixed raw value is the physical anchor -a, including forbidden candidates. -/
theorem fixed_value (h : Objects T other hother P U candidates allowed)
    (e : U.edges) (he : e.1 ∈ fixedEdgesForRange P.edges candidates allowed) :
    h.1 e = -shift T other hother U e := h.2.1 e he

/-- All original permitted labels act on the independent raw equation. -/
noncomputable def gauge (b : SupportedEquation.Labels M P U candidates allowed)
    (h : Objects T other hother P U candidates allowed) : Objects T other hother P U candidates allowed :=
  ⟨h.1 + ClosedRegion.d0Hom M U b.1.1,by
    constructor
    · intro e he
      change h.1 e + (ClosedRegion.d0Hom M U b.1.1) e = -shift T other hother U e
      rw [h.2.1 e he]
      have hz : (ClosedRegion.d0Hom M U b.1.1) e = 0 := by
        rcases he with hp | hs
        · exact (RelativeCover.d0 M U P b.1).2 e hp
        · exact b.2 e hs
      rw [hz,add_zero]
    · rw [map_add,h.2.2,ClosedRegion.d1_d0,add_zero]⟩

/-- The zero full original label fixes each independent raw equation. -/
theorem gauge_zero (h : Objects T other hother P U candidates allowed) :
    gauge T other hother P U candidates allowed 0 h = h := by
  apply Subtype.ext
  change h.1 + ClosedRegion.d0Hom M U 0 = h.1
  rw [map_zero,add_zero]

/-- Raw gauge composition is the sum of the entire original labels. -/
theorem gauge_add (b c : SupportedEquation.Labels M P U candidates allowed)
    (h : Objects T other hother P U candidates allowed) :
    gauge T other hother P U candidates allowed (b+c) h =
      gauge T other hother P U candidates allowed b (gauge T other hother P U candidates allowed c h) := by
  apply Subtype.ext
  change h.1 + ClosedRegion.d0Hom M U (b.1.1+c.1.1) =
    (h.1 + ClosedRegion.d0Hom M U c.1.1) + ClosedRegion.d0Hom M U b.1.1
  rw [map_add]
  abel

/-- The raw anchored action retains all original labels and stabilizers. -/
noncomputable instance addAction : AddAction (SupportedEquation.Labels M P U candidates allowed)
    (Objects T other hother P U candidates allowed) where
  vadd := gauge T other hother P U candidates allowed
  zero_vadd := gauge_zero T other hother P U candidates allowed
  add_vadd := gauge_add T other hother P U candidates allowed

/-- Independent raw anchored equations have every original permitted gauge arrow. -/
abbrev Groupoid := ActionCategory (Multiplicative (SupportedEquation.Labels M P U candidates allowed))
  (Objects T other hother P U candidates allowed)

/-- Normalization commutes with every full original label, without requiring a|P=0. -/
theorem equivariant (b : Multiplicative (SupportedEquation.Labels M P U candidates allowed))
    (h : Objects T other hother P U candidates allowed) :
    objectEquiv T other hother P U hfixed candidates allowed (b • h) =
      b • objectEquiv T other hother P U hfixed candidates allowed h := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change (h.1 + ClosedRegion.d0Hom M U b.toAdd.1.1) + shift T other hother U =
    (h.1 + shift T other hother U) + ClosedRegion.d0Hom M U b.toAdd.1.1
  abel

/-- Full native normalization has every original object and every original label in both directions. -/
noncomputable def equivalence : Groupoid T other hother P U candidates allowed ≌
    SupportedEquation.Groupoid M P U candidates allowed δ :=
  changedLabelEquivalence (MulEquiv.refl (Multiplicative (SupportedEquation.Labels M P U candidates allowed)))
    (objectEquiv T other hother P U hfixed candidates allowed)
    (equivariant T other hother P U hfixed candidates allowed)

/-- Whole forward-inverse normalization is the identity on raw objects and all arrows. -/
theorem functor_inverse :
    (equivalence T other hother P U hfixed candidates allowed).functor ⋙
      (equivalence T other hother P U hfixed candidates allowed).inverse =
        𝟭 (Groupoid T other hother P U candidates allowed) :=
  changed_label_functor_inverse (MulEquiv.refl (Multiplicative (SupportedEquation.Labels M P U candidates allowed)))
    (objectEquiv T other hother P U hfixed candidates allowed)
    (equivariant T other hother P U hfixed candidates allowed)

/-- Whole inverse-forward normalization retains every old supported value and full arrow. -/
theorem inverse_functor :
    (equivalence T other hother P U hfixed candidates allowed).inverse ⋙
      (equivalence T other hother P U hfixed candidates allowed).functor =
        𝟭 (SupportedEquation.Groupoid M P U candidates allowed δ) :=
  changed_label_inverse_functor (MulEquiv.refl (Multiplicative (SupportedEquation.Labels M P U candidates allowed)))
    (objectEquiv T other hother P U hfixed candidates allowed)
    (equivariant T other hother P U hfixed candidates allowed)

end AnchoredLocal
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
