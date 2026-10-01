import ResearchLean.AG.RelativeRepairComposition.AffineEmbeddedValues

/-!
# Actual authored comparison values on every shared typed route

The geometric maps retain both complete words and all oriented face contexts.
Reference and comparison matching then derive the actual route-value equality;
no syzygy or repair equality is supplied to this transfer theorem.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {G H : FiniteTransportPresentation.{uG}}
variable (m : FinitePresentationEmbedding G H)
variable (RG : ∀ {i j : G.Vertex}, G.Edge i j → Operations k A)
variable (RH : ∀ {i j : H.Vertex}, H.Edge i j → Operations k A)
variable (cG : G.TwoCell → A) (cH : H.TwoCell → A)
variable (href : ∀ {i j : G.Vertex} (e : G.Edge i j), RH (m.edge e) = RG e)
variable (hcomparison : ∀ f : G.TwoCell, cH (m.face f) = cG f)

include href in
/-- Exact sharing identifies the complete reference-operation family at every old edge. -/
theorem embedded_reference_family : @embeddedOperation k _ A _ _ G H m RH = @RG := by
  funext i j e
  exact href e

include href in
/-- Complete shared words evaluate the original primitive references in their original order. -/
theorem embedded_reference_word {i j : G.Vertex} (w : G.Path i j) :
    GroupExtension.pathValue H RH (m.path w) = GroupExtension.pathValue G RG w := by
  rw [embedded_word_value,embedded_reference_family m RG RH href]

include href hcomparison in
/-- Each mapped oriented comparison retains the original complete outgoing context and real comparator. -/
theorem embedded_step_comparison {i j : G.Vertex} {w z : G.Path i j}
    (s : RewriteStep G.toFiniteTransportTwoPresentation w z) :
    faceOperation H RH cH (m.step s).face = faceOperation G RG cG s.face := by
  have hout := word_value_heq RH (m.path s.face.outgoing) (m.step s).face.outgoing
    ((m.face_target s.face.cell).symm.trans (congrArg H.twoTarget (m.step_face s)).symm)
    rfl (m.step_outgoing s)
  rw [embedded_reference_word m RG RH href] at hout
  simp only [faceOperation]
  rw [← hout,m.step_orientation,m.step_face,hcomparison]

include href hcomparison in
/-- Every mapped typed route retains the full ordered primitive comparison product. -/
theorem embedded_pasting_value {i j : G.Vertex} {w z : G.Path i j}
    (p : RewritePasting G.toFiniteTransportTwoPresentation w z) :
    pastingOperation H RH cH (m.route p) = pastingOperation G RG cG p := by
  induction p with
  | nil w => rw [m.route_nil]; rfl
  | cons s p ih =>
    rw [m.route_cons]
    change pastingOperation H RH cH (m.route p) * faceOperation H RH cH (m.step s).face = _
    rw [ih,embedded_step_comparison m RG RH cG cH href hcomparison]
    rfl

/-- Full heterogeneous route equality retains actual values after exact vertex and word matching. -/
theorem pasting_value_heq (O : ∀ {i j : H.Vertex}, H.Edge i j → Operations k A)
    (c : H.TwoCell → A) {i j a b : H.Vertex} {w z : H.Path i j} {u v : H.Path a b}
    (p : RewritePasting H.toFiniteTransportTwoPresentation w z)
    (q : RewritePasting H.toFiniteTransportTwoPresentation u v)
    (hi : i = a) (hj : j = b) (hw : HEq w u) (hz : HEq z v) (hp : HEq p q) :
    pastingOperation H O c p = pastingOperation H O c q := by
  cases hi
  cases hj
  cases eq_of_heq hw
  cases eq_of_heq hz
  rw [eq_of_heq hp]

include href hcomparison in
/-- Whole original three-cell laws restrict from their actual mapped complete routes. -/
theorem embedded_three_law
    (hthree : ∀ f : H.ThreeCell,
      pastingOperation H RH cH (H.threeLeft f) = pastingOperation H RH cH (H.threeRight f)) :
    ∀ f : G.ThreeCell,
      pastingOperation G RG cG (G.threeLeft f) = pastingOperation G RG cG (G.threeRight f) := by
  intro f
  have hl := pasting_value_heq RH cH (m.route (G.threeLeft f)) (H.threeLeft (m.triple f))
    (m.triple_source f).symm (m.triple_target f).symm (m.triple_start f) (m.triple_finish f) (m.triple_left f)
  have hr := pasting_value_heq RH cH (m.route (G.threeRight f)) (H.threeRight (m.triple f))
    (m.triple_source f).symm (m.triple_target f).symm (m.triple_start f) (m.triple_finish f) (m.triple_right f)
  rw [embedded_pasting_value m RG RH cG cH href hcomparison] at hl hr
  exact hl.trans ((hthree (m.triple f)).trans hr.symm)

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine
