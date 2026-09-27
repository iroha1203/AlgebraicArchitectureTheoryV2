import ResearchLean.AG.ProtocolHolonomy.IdentityLiftability
import Formal.Util.AssertStandardAxioms

/-!
# The original identity-operation change group splits over H

The section uses the actual total-state change attached to the identity
fiber lift. It keeps the supplied graph automorphism and each original
named operation, and its state map is `(v,x) ↦ (g v,x)`.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- The original actual change whose visible component is `g` and whose
hidden map is identity on the common fiber. -/
def identityChange
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) (g : H) :
    (identityReversibleData Q K).ChangeGroup H :=
  ⟨(identityLift Q K g.1).toStateChange, g.2⟩

theorem identityChange_state_apply
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) (g : H)
    (v : Q.Vertex) (x : K) :
    (identityChange Q K H g).1.state ⟨v, x⟩ =
      ⟨g.1.vertex v, x⟩ := rfl

/-- Identity hidden changes preserve multiplication of the original H
as actual operation-preserving total-state changes. -/
def identitySection
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    H →* (identityReversibleData Q K).ChangeGroup H where
  toFun := identityChange Q K H
  map_one' := by
    apply Subtype.ext
    apply ReversibleData.StateChange.ext
    · rfl
    · apply Equiv.ext
      rintro ⟨v, x⟩
      rfl
  map_mul' g h := by
    apply Subtype.ext
    apply ReversibleData.StateChange.ext
    · rfl
    · apply Equiv.ext
      rintro ⟨v, x⟩
      rfl

/-- The section is a literal right inverse to the original actual visible
projection, not just to a replacement abstract extension. -/
theorem identitySection_rightInverse
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    Function.RightInverse
      (identitySection Q K H)
      (ReversibleData.ChangeGroup.projection
        (D := identityReversibleData Q K) (H := H)) := by
  intro g
  apply Subtype.ext
  rfl

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityChange
#print axioms AAT.AG.ProtocolHolonomy.identityChange_state_apply
#print axioms AAT.AG.ProtocolHolonomy.identitySection
#print axioms AAT.AG.ProtocolHolonomy.identitySection_rightInverse
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
