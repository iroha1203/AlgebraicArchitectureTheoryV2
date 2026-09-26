import ResearchLean.AG.LocalSemanticReconstruction.FinitePermutationReadingCriteria
import ResearchLean.AG.RealizationReconstruction.FixedFSplitExactSequenceAndTorsor
import ResearchLean.AG.RealizationReconstruction.FixedFLensGroupConnection
import ResearchLean.AG.RealizationReconstruction.FixedFProtocolGroupConnection
import ResearchLean.AG.LocalSemanticReconstruction.CSFixedFDetermining
import Formal.Util.AssertStandardAxioms

/-! Design IV-3: the full fixed-visible preserving-change domain of the
common D criterion is identified with the literal all-H lens/protocol
projection fibers. Point readback is proved from each independent state
change, then the same finite determining predicates are transported. -/
namespace AAT.AG.LocalSemanticReconstruction
open RealizationReconstruction
namespace CSFixedFFiberD
universe u
variable {F : FixedFDirectedMultigraph} {K : Type*}
/-- The actual projection fiber over u is the complete fixed-u preserving
change domain used by the common D criterion. -/
noncomputable def projectionFiberEquivPreserving
    (H : Subgroup (FixedFGraphAutomorphism F)) (visible : H) :
    FixedFSplitExactSequenceAndTorsor.ProjectionFiber (K := K) H visible ≃
      PermutationRestriction.PreservingChange F K visible.1 where
  toFun actual := by
    let pair : FixedFPreservingFollowingPair F K := actual.1.1
    have hvisible : pair.automorphism = visible.1 :=
      congrArg Subtype.val actual.2
    refine ⟨{ h := pair.h, observation := ?_ }, ?_⟩
    · intro vertex hidden
      simpa [hvisible] using pair.observation vertex hidden
    · intro namedEdge hidden
      simpa [hvisible] using pair.preserves namedEdge hidden
  invFun change :=
    ⟨⟨{
      automorphism := visible.1
      h := change.1.h
      observation := change.1.observation
      preserves := change.2
    }, visible.property⟩, rfl⟩
  left_inv actual := by
    apply Subtype.ext
    apply Subtype.ext
    apply FixedFPreservingFollowingPair.ext
    · exact (congrArg Subtype.val actual.2).symm
    · rfl
  right_inv change := by
    apply Subtype.ext
    apply FixedFFollowingStateChange.ext
    rfl

private theorem determining_precompose_equiv
    {A B I Value : Type*} (domain : A ≃ B)
    (readB : B → I → Value) (S : Finset I)
    (coherent : ({i // i ∈ S} → Value) → Prop) :
    FiniteReading.Determining (fun a i => readB (domain a) i) S coherent ↔
      FiniteReading.Determining readB S coherent := by
  constructor
  · rintro ⟨hsep, hext⟩
    constructor
    · intro first second hread
      obtain ⟨first, rfl⟩ := domain.surjective first
      obtain ⟨second, rfl⟩ := domain.surjective second
      apply congrArg domain
      apply hsep
      exact hread
    · intro table htable
      obtain ⟨a, ha⟩ := hext table htable
      exact ⟨domain a, ha⟩
  · rintro ⟨hsep, hext⟩
    constructor
    · intro first second hread
      apply domain.injective
      apply hsep
      exact hread
    · intro table htable
      obtain ⟨b, hb⟩ := hext table htable
      refine ⟨domain.symm b, ?_⟩
      funext x
      change readB (domain (domain.symm b)) x.1 = table x
      rw [domain.apply_symm_apply]
      exact congrFun hb x

/-- The independent protocol projection fiber over a fixed visible change
is exactly the full fixed-u D preserving-change domain. -/
noncomputable def protocolFiberEquivPreserving
    {F : FixedFDirectedMultigraph} [Finite F.Vertex] [Finite F.Edge]
    {K : Type*} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) (visible : H) :
    FixedFProtocolGroupConnection.ProtocolChangeGroup.ProjectionFiber
      (K := K) visible ≃
      PermutationRestriction.PreservingChange F K visible.1 :=
  (FixedFProtocolGroupConnection.ProtocolChangeGroup.projectionFiberEquiv
    (K := K) (H := H) visible).trans
    (projectionFiberEquivPreserving H visible)

/-- The independent product-lens projection fiber has the full D domain over
the corresponding complete-update graph visible change. -/
noncomputable def lensFiberEquivPreserving
    {V K : Type u} [Finite K]
    (H : Subgroup (Equiv.Perm V)) (visible : H) :
    FixedFLensGroupConnection.LensChangeGroup.ProjectionFiber
      (K := K) visible ≃
      PermutationRestriction.PreservingChange
        (FixedFFiniteExamples.completeUpdateGraph V) K
        (FixedFFiniteExamples.completeUpdateAutomorphism visible.1) :=
  (FixedFLensGroupConnection.LensChangeGroup.projectionFiberEquiv
    (K := K) (H := H) visible).trans
    (projectionFiberEquivPreserving
      (FixedFLensGroupConnection.completeUpdateGraphSubgroup H)
      (FixedFLensGroupConnection.LensChangeGroup.visibleMulEquivGraphSubgroup (H := H)
        visible))


/-- At every visible product-lens change, the single reference fiber query
is a determining set for the independent CS projection fiber. -/
theorem lens_reference_determining_on_changes
    {V K : Type u} [Finite K] [Nontrivial K]
    (reference : V) (H : Subgroup (Equiv.Perm V)) (visible : H) :
    FiniteReading.Determining
      (fun change vertex => FinitePermutationReadingCriteria.readAt
        (FixedFFiniteExamples.completeUpdateGraph V) K
        (FixedFFiniteExamples.completeUpdateAutomorphism visible.1)
        (lensFiberEquivPreserving (K := K) H visible change) vertex)
      ({reference} : Finset V)
      (FinitePermutationReadingCriteria.EdgeCoherent
        (FixedFFiniteExamples.completeUpdateGraph V) K {reference}) := by
  apply (determining_precompose_equiv (lensFiberEquivPreserving (K := K) H visible)
    (FinitePermutationReadingCriteria.readAt
      (FixedFFiniteExamples.completeUpdateGraph V) K
      (FixedFFiniteExamples.completeUpdateAutomorphism visible.1))
    {reference} _).2
  exact CSFixedFDetermining.lens_reference_determining
    (K := K) reference (FixedFFiniteExamples.completeUpdateAutomorphism visible.1)

/-- At every visible protocol change, one selected vertex per full component
is a determining set for the independent CS projection fiber. -/
theorem protocol_representatives_determining_on_changes
    {F : FixedFDirectedMultigraph} [Finite F.Vertex] [Finite F.Edge]
    {K : Type*} [Finite K] [Nontrivial K]
    (H : Subgroup (FixedFGraphAutomorphism F)) (visible : H) :
    FiniteReading.Determining
      (fun change vertex => FinitePermutationReadingCriteria.readAt F K visible.1
        (protocolFiberEquivPreserving (K := K) H visible change) vertex)
      (CSFixedFDetermining.protocolRepresentativeSet F)
      (FinitePermutationReadingCriteria.EdgeCoherent F K
        (CSFixedFDetermining.protocolRepresentativeSet F)) := by
  apply (determining_precompose_equiv
    (protocolFiberEquivPreserving (K := K) H visible)
    (FinitePermutationReadingCriteria.readAt F K visible.1)
    (CSFixedFDetermining.protocolRepresentativeSet F) _).2
  exact CSFixedFDetermining.protocol_representatives_determining F visible.1


/-- The D reading transported through the protocol fiber equivalence is
the original vertex permutation supplied by the independent change. -/
theorem protocol_fiber_readAt_eq_stateEquiv
    {F : FixedFDirectedMultigraph} [Finite F.Vertex] [Finite F.Edge]
    {K : Type*} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) (visible : H)
    (change : FixedFProtocolGroupConnection.ProtocolChangeGroup.ProjectionFiber
      (K := K) visible) (vertex : F.Vertex) :
    FinitePermutationReadingCriteria.readAt F K visible.1
        (protocolFiberEquivPreserving (K := K) H visible change) vertex =
      change.1.stateEquiv vertex := by
  apply Equiv.ext
  intro state
  rfl


/-- The D reading transported through the product-lens fiber equivalence
is the hidden coordinate of the independent state equivalence. -/
theorem lens_fiber_readAt_eq_hidden
    {V K : Type u} [Finite K]
    (H : Subgroup (Equiv.Perm V)) (visible : H)
    (change : FixedFLensGroupConnection.LensChangeGroup.ProjectionFiber
      (K := K) visible) (vertex : V) (state : K) :
    (FinitePermutationReadingCriteria.readAt
      (FixedFFiniteExamples.completeUpdateGraph V) K
      (FixedFFiniteExamples.completeUpdateAutomorphism visible.1)
      (lensFiberEquivPreserving (K := K) H visible change) vertex) state =
        (change.1.h (vertex,state)).2 := by
  rfl


#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CSFixedFFiberD

end CSFixedFFiberD
end AAT.AG.LocalSemanticReconstruction
