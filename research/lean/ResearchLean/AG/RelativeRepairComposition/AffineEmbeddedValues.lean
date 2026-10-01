import ResearchLean.AG.RelativeRepairComposition.FinitePresentationEmbedding
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCorrection

/-!
# Restriction of independent actual affine repairs along the full shared geometry

Only primitive reference/comparison matching and geometric fixed-edge incidence
are supplied. Real face equalities are derived by evaluation of the complete
mapped words. The old kernel coordinates are the actual affine quotients.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {G H : FiniteTransportPresentation.{uG}}
variable (m : FinitePresentationEmbedding G H)

/-- Read the actual operation at the image of every shared original edge. -/
def embeddedOperation (O : ∀ {i j : H.Vertex}, H.Edge i j → Operations k A) :
    ∀ {i j : G.Vertex}, G.Edge i j → Operations k A := fun e => O (m.edge e)

/-- Every full typed shared word evaluates the same mapped actual operations in temporal order. -/
theorem embedded_word_value (O : ∀ {i j : H.Vertex}, H.Edge i j → Operations k A)
    {i j : G.Vertex} (w : G.Path i j) :
    GroupExtension.pathValue H O (m.path w) =
      GroupExtension.pathValue G (embeddedOperation m O) w := by
  induction w with
  | nil i => rw [m.path_nil]; rfl
  | cons e w ih =>
    rw [m.path_cons]
    change GroupExtension.pathValue H O (m.path w) * O (m.edge e) = _
    rw [ih]
    rfl

/-- Exact heterogeneous typed-word equality retains the same actual affine word value. -/
theorem word_value_heq (O : ∀ {i j : H.Vertex}, H.Edge i j → Operations k A)
    {i j a b : H.Vertex} (w : H.Path i j) (z : H.Path a b)
    (hi : i = a) (hj : j = b) (h : HEq w z) :
    GroupExtension.pathValue H O w = GroupExtension.pathValue H O z := by
  cases hi
  cases hj
  rw [eq_of_heq h]

variable (RG : ∀ {i j : G.Vertex}, G.Edge i j → Operations k A)
variable (RH : ∀ {i j : H.Vertex}, H.Edge i j → Operations k A)
variable (cG : G.TwoCell → A) (cH : H.TwoCell → A)
variable (fixedG : Set (EdgeName (K := G))) (fixedH : Set (EdgeName (K := H)))
variable (href : ∀ {i j : G.Vertex} (e : G.Edge i j), RH (m.edge e) = RG e)
variable (hcomparison : ∀ f : G.TwoCell, cH (m.face f) = cG f)
variable (hfixed : ∀ e ∈ fixedG, m.edgeName e ∈ fixedH)

/-- A real environment repair restricts to a genuine shared repair of the full original W. -/
def restrictEmbeddedRepair (s : Repair H RH cH fixedH) : Repair G RG cG fixedG where
  operation := embeddedOperation m s.operation
  linear e := (s.linear (m.edge e)).trans (congrArg AffineEquiv.linear (href e))
  face f := by
    have hl := word_value_heq s.operation _ _ (m.face_source f).symm (m.face_target f).symm (m.face_left f)
    have hr := word_value_heq s.operation _ _ (m.face_source f).symm (m.face_target f).symm (m.face_right f)
    rw [embedded_word_value] at hl hr
    calc
      translation (k := k) (cG f) * GroupExtension.pathValue G (embeddedOperation m s.operation) (G.twoLeft f) =
          translation (k := k) (cH (m.face f)) * GroupExtension.pathValue H s.operation (H.twoLeft (m.face f)) := by
        rw [hcomparison,hl]
      _ = GroupExtension.pathValue H s.operation (H.twoRight (m.face f)) := s.face (m.face f)
      _ = GroupExtension.pathValue G (embeddedOperation m s.operation) (G.twoRight f) := hr.symm
  fixed_value e he := (s.fixed_value (m.edgeName e) (hfixed e he)).trans (href e.2.2)

/-- The actual shared correction is the same quotient at its original named environment edge. -/
theorem embedded_correction_value (s : Repair H RH cH fixedH) (e : EdgeName (K := G)) :
    realCorrection G RG cG fixedG (restrictEmbeddedRepair m RG RH cG cH fixedG fixedH href hcomparison hfixed s) e =
      realCorrection H RH cH fixedH s (m.edgeName e) := by
  unfold realCorrection
  change (s.operation (m.edge e.2.2) * (RG e.2.2)⁻¹) 0 =
    (s.operation (m.edge e.2.2) * (RH (m.edge e.2.2))⁻¹) 0
  rw [href]

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine
