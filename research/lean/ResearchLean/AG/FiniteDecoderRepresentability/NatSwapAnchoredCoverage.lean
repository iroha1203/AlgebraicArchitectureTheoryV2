import ResearchLean.AG.FiniteDecoderRepresentability.NatAdjacentSwap
import Formal.Util.AssertStandardAxioms

/-!
# Anchored coverage of the non-representable adjacent swap

This module proves G-121(E)'s required contrast.  The adjacent-swap arrow has no
preimage between the literal fixed code endpoints, but it is covered after the
target endpoint is identified by that same semantic automorphism.  The covering
presentation remains the authored identity presentation.

## Implementation notes

The fixed code occurs literally at both anchors.  The infinite Atom permutation
is placed only in the target endpoint isomorphism, where anchored coverage allows
it, while the displayed code arrow remains `idTypedPresentation`.  Encoding the
permutation in that presentation would contradict the finite-support obstruction
proved in Cycle 16 and would erase the distinction this example must exhibit.
-/

namespace AAT.AG.FiniteDecoderRepresentability

open CategoryTheory AtomFoundation DoctrineFiberProduct

/-- The semantic arrow input whose hom is the adjacent-swap automorphism. -/
def natAdjacentSwapInput : CartSemanticInput natSwapCarrier :=
  cartSemanticInputOfHom natAdjacentSwapSemanticIso.hom

/-- G-121(E) computation API: `simp` exposes the input source as `X_*`. -/
@[simp] theorem natAdjacentSwapInput_source :
    natAdjacentSwapInput.source = natSwapCode.toSemantic := rfl

/-- G-121(E) computation API: `simp` exposes the input target as `X_*`. -/
@[simp] theorem natAdjacentSwapInput_target :
    natAdjacentSwapInput.target = natSwapCode.toSemantic := rfl

/-- G-121(E) computation API: `simp` exposes the input arrow as `u_σ.hom`. -/
@[simp] theorem natAdjacentSwapInput_hom :
    natAdjacentSwapInput.hom = natAdjacentSwapSemanticIso.hom := rfl

/-- G-121(E)'s source endpoint anchor uses the identity isomorphism. -/
def natSwapIdentityAnchor : CoveredObjectWitness natSwapCode.toSemantic where
  code := natSwapCode
  iso := Iso.refl _

/-- G-121(E) computation API: `simp` exposes the identity anchor's code as `P_*`. -/
@[simp] theorem natSwapIdentityAnchor_code :
    natSwapIdentityAnchor.code = natSwapCode := rfl

/-- G-121(E) computation API: `simp` exposes the source endpoint isomorphism as identity. -/
@[simp] theorem natSwapIdentityAnchor_iso :
    natSwapIdentityAnchor.iso = Iso.refl _ := rfl

/-- G-121(E)'s target endpoint anchor uses the adjacent-swap automorphism. -/
def natSwapAdjacentAnchor : CoveredObjectWitness natSwapCode.toSemantic where
  code := natSwapCode
  iso := natAdjacentSwapSemanticIso

/-- G-121(E) computation API: `simp` exposes the adjacent anchor's code as `P_*`. -/
@[simp] theorem natSwapAdjacentAnchor_code :
    natSwapAdjacentAnchor.code = natSwapCode := rfl

/-- G-121(E) computation API: `simp` exposes the target endpoint isomorphism as `u_σ`. -/
@[simp] theorem natSwapAdjacentAnchor_iso :
    natSwapAdjacentAnchor.iso = natAdjacentSwapSemanticIso := rfl

/--
G-121(E)'s anchored coverage witness: identity source anchor, adjacent-swap
target anchor, and the literal identity typed presentation.
-/
def natAdjacentSwapAnchoredCoverage :
    AnchoredCoverageWitness natAdjacentSwapInput where
  sourceAnchor := natSwapIdentityAnchor
  targetAnchor := natSwapAdjacentAnchor
  arrow :=
    { presentation := idTypedPresentation natSwapCode
      square :=
        { sourceIso := Iso.refl _
          targetIso := natAdjacentSwapSemanticIso
          hom_comm := by
            change (𝟙 natSwapCode.toSemantic) ≫
                natAdjacentSwapSemanticIso.hom =
              typedPresentationToSemantic (idTypedPresentation natSwapCode) ≫
                natAdjacentSwapSemanticIso.hom
            rw [typedPresentationToSemantic_id] }
      sourceIso_eq := rfl
      targetIso_eq := rfl }

/-- G-121(E) computation API: `simp` exposes the source anchor as the identity anchor. -/
@[simp] theorem natAdjacentSwapAnchoredCoverage_sourceAnchor :
    natAdjacentSwapAnchoredCoverage.sourceAnchor = natSwapIdentityAnchor := rfl

/-- G-121(E) computation API: `simp` exposes the target anchor as the adjacent-swap anchor. -/
@[simp] theorem natAdjacentSwapAnchoredCoverage_targetAnchor :
    natAdjacentSwapAnchoredCoverage.targetAnchor = natSwapAdjacentAnchor := rfl

/-- G-121(E) computation API: `simp` exposes the covering presentation as the authored identity. -/
@[simp] theorem natAdjacentSwapAnchoredCoverage_presentation :
    natAdjacentSwapAnchoredCoverage.arrow.presentation =
      idTypedPresentation natSwapCode := rfl

/-- G-121(E) computation API: `simp` exposes the square's source endpoint isomorphism as identity. -/
@[simp] theorem natAdjacentSwapAnchoredCoverage_sourceIso :
    natAdjacentSwapAnchoredCoverage.arrow.square.sourceIso = Iso.refl _ := rfl

/-- G-121(E) computation API: `simp` exposes the square's target endpoint isomorphism as `u_σ`. -/
@[simp] theorem natAdjacentSwapAnchoredCoverage_targetIso :
    natAdjacentSwapAnchoredCoverage.arrow.square.targetIso =
      natAdjacentSwapSemanticIso := rfl

/--
G-121(E)'s square evaluation: the identity presentation followed by the target
anchor equals the source identity followed by the fixed semantic arrow.
-/
theorem natAdjacentSwapAnchoredCoverage_square :
    (𝟙 natSwapCode.toSemantic) ≫ natAdjacentSwapSemanticIso.hom =
      typedPresentationToSemantic (idTypedPresentation natSwapCode) ≫
        natAdjacentSwapSemanticIso.hom := by
  rw [typedPresentationToSemantic_id]

/-- The same arrow is covered although no literal-endpoint decoder preimage exists. -/
theorem natAdjacentSwap_covered_and_not_fixed_representable :
    Nonempty (AnchoredCoverageWitness natAdjacentSwapInput) ∧
      ¬ ∃ codeHom : FiniteCodeCartHom natSwapCode natSwapCode,
        finiteCodeCartRealization.map codeHom =
          natAdjacentSwapSemanticIso.hom :=
  ⟨⟨natAdjacentSwapAnchoredCoverage⟩, not_exists_natSwapCodeHom⟩

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
