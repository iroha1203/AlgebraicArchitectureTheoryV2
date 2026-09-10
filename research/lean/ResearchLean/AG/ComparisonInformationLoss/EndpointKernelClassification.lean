import Mathlib.Algebra.Group.Graph
import ResearchLean.AG.ComparisonInformationLoss.GeneratedComparisonObservation

/-!
# Endpoint-kernel classification of generated comparison loss

This module identifies the product observation kernel with the product of the
two endpoint observation kernels and the compatible kernel with the graph of
comparison conjugation.  A general group calculation then identifies the
pointed left-coset set of that graph with the target endpoint kernel.

Implementation notes: all quotients below are general left-coset sets.  No
normality assumption is introduced.  The classification map is defined on
representatives and proved invariant under the actual graph relation.
-/

open scoped Pointwise

namespace AAT.AG.ComparisonInformationLoss

universe u v

set_option synthInstance.maxHeartbeats 100000

noncomputable section

namespace PointedLeftCoset

variable {A : Type u} {B : Type v} [Group A] [Group B]

/-- G-120(B2) general helper: a group equivalence carrying one subgroup onto
another induces an equivalence of their left-coset sets.  The subgroup-image
equality is the only premise and supplies both relation-preservation proofs. -/
def equivOfMapEq (L : Subgroup A) (M : Subgroup B) (e : A ≃* B)
    (hmap : Subgroup.map e L = M) : A ⧸ L ≃ B ⧸ M where
  toFun := Quotient.map' e fun a b hab => by
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    rw [← hmap]
    exact ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, rfl⟩
  invFun := Quotient.map' e.symm fun a b hab => by
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    have hm : a⁻¹ * b ∈ Subgroup.map e L := by simpa [hmap] using
      (QuotientGroup.leftRel_apply.mp hab)
    rcases hm with ⟨x, hx, hxe⟩
    simpa [← hxe] using hx
  left_inv x := QuotientGroup.induction_on x fun a => by
    simp only [Quotient.map'_mk'']
    exact congrArg QuotientGroup.mk (e.symm_apply_apply a)
  right_inv x := QuotientGroup.induction_on x fun b => by
    simp only [Quotient.map'_mk'']
    exact congrArg QuotientGroup.mk (e.apply_symm_apply b)

/-- G-120(B2) general main calculation: the left-coset set of the graph of a
group equivalence is equivalent to the target group by
`[(a,b)] ↦ b * T(a)⁻¹`, with inverse `y ↦ [(1,y)]`. -/
def graphQuotientEquiv (T : A ≃* B) :
    (A × B) ⧸ T.toMonoidHom.graph ≃ B where
  toFun := Quotient.lift
    (fun pair : A × B => pair.2 * (T pair.1)⁻¹)
    (fun a b hab => by
      have hgraph : T (a⁻¹ * b).1 = (a⁻¹ * b).2 :=
        MonoidHom.mem_graph.mp (QuotientGroup.leftRel_apply.mp hab)
      change a.2 * (T a.1)⁻¹ = b.2 * (T b.1)⁻¹
      have core : a.2 * (T a.1)⁻¹ * T b.1 = b.2 := by
        calc
          a.2 * (T a.1)⁻¹ * T b.1 = a.2 * T (a.1⁻¹ * b.1) := by
            simp only [map_mul, map_inv, mul_assoc]
          _ = a.2 * (a.2⁻¹ * b.2) := by
            simpa only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv,
              Prod.snd_inv] using congrArg (fun value => a.2 * value) hgraph
          _ = b.2 := by simp
      calc
        a.2 * (T a.1)⁻¹ =
            (a.2 * (T a.1)⁻¹ * T b.1) * (T b.1)⁻¹ := by simp
        _ = b.2 * (T b.1)⁻¹ := by rw [core])
  invFun value := QuotientGroup.mk (1, value)
  left_inv quotient := QuotientGroup.induction_on quotient fun pair => by
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    apply MonoidHom.mem_graph.mpr
    simp
  right_inv value := by simp

/-- G-120(B2) API evaluation of the graph quotient classification. -/
@[simp] theorem graphQuotientEquiv_mk (T : A ≃* B) (pair : A × B) :
    graphQuotientEquiv T (QuotientGroup.mk pair) =
      pair.2 * (T pair.1)⁻¹ :=
  rfl

/-- G-120(B2) API evaluation of the inverse graph classification. -/
@[simp] theorem graphQuotientEquiv_symm_apply (T : A ≃* B) (value : B) :
    (graphQuotientEquiv T).symm value = QuotientGroup.mk (1, value) :=
  rfl

/-- G-120(B2) API: the graph classification sends the distinguished coset to
the identity of the target kernel. -/
@[simp] theorem graphQuotientEquiv_basepoint (T : A ≃* B) :
    graphQuotientEquiv T (QuotientGroup.mk 1) = 1 := by
  change (1 : B) * (T (1 : A))⁻¹ = 1
  simp

end PointedLeftCoset

namespace GeneratedComparison

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence
open AAT.AG.DoctrineFiberProduct

/-- G-120(B2) data: the coefficient-observation kernel at the generated source
endpoint.  It is the source factor used in the product description of `K_c`. -/
abbrev SourceObservationKernelAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  (CompositeFiberAut.coefficientObservation
    (input.generatedBaseRouteGeometryAt i)).ker

/-- G-120(B2) data: the coefficient-observation kernel at the generated target
endpoint.  It is the target factor classified by the pointed quotient. -/
abbrev TargetObservationKernelAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :=
  (CompositeFiberAut.coefficientObservation
    (input.generatedPulledRouteGeometryAt i)).ker

/-- G-120(B2) main identification `K_c = K_X^obs × K_Y^obs`, expressed as a
group equivalence that preserves the underlying endpoint pair.  Membership in
both factors is derived from product-observation kernel membership. -/
def endpointKernelProductEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (SourceObservationKernelAt input i × TargetObservationKernelAt input i) ≃*
      observationKernelAt input i where
  toFun pair := ⟨((pair.1 : CompositeFiberAut
      (input.generatedBaseRouteGeometryAt i)),
    (pair.2 : CompositeFiberAut
      (input.generatedPulledRouteGeometryAt i))), by
        apply MonoidHom.mem_ker.mpr
        apply Prod.ext
        · exact MonoidHom.mem_ker.mp pair.1.2
        · exact MonoidHom.mem_ker.mp pair.2.2⟩
  invFun pair :=
    (⟨pair.1.1, by
      apply MonoidHom.mem_ker.mpr
      exact congrArg Prod.fst (MonoidHom.mem_ker.mp pair.2)⟩,
    ⟨pair.1.2, by
      apply MonoidHom.mem_ker.mpr
      exact congrArg Prod.snd (MonoidHom.mem_ker.mp pair.2)⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- G-120(B2) API evaluation: the product identification preserves the actual
underlying endpoint pair. -/
@[simp] theorem endpointKernelProductEquivAt_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (pair : SourceObservationKernelAt input i ×
      TargetObservationKernelAt input i) :
    (endpointKernelProductEquivAt input i pair : ChangeGroupAt input i) =
      ((pair.1 : CompositeFiberAut (input.generatedBaseRouteGeometryAt i)),
        (pair.2 : CompositeFiberAut
          (input.generatedPulledRouteGeometryAt i))) :=
  rfl

/-- G-120(B2) data: transport `L_c` through the endpoint-product
identification, retaining exactly the same endpoint pair. -/
def compatibleKernelInEndpointProductAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    Subgroup (SourceObservationKernelAt input i ×
      TargetObservationKernelAt input i) :=
  Subgroup.map (endpointKernelProductEquivAt input i).symm
    (compatibleKernelAt input i)

/-- G-120(B2) main graph theorem: after identifying `K_c` with the product of
the endpoint kernels, `L_c` is exactly the graph of comparison conjugation.
The graph equation is derived from actual qualified-comparison membership. -/
theorem compatibleKernelInEndpointProductAt_eq_graph
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    compatibleKernelInEndpointProductAt input i =
      (endpointObservationKernelEquivAt input i).toMonoidHom.graph := by
  ext pair
  constructor
  · rintro ⟨element, helement, rfl⟩
    apply MonoidHom.mem_graph.mpr
    apply Subtype.ext
    have hqualified : (element.1 : ChangeGroupAt input i) ∈
        compatibleSubgroupAt input i :=
      (mem_compatibleKernel_iff (observationAt input i)
        (compatibleSubgroupAt input i) element).mp helement
    let qualified : qualifiedComparisonSubgroup
        (input.generatedCompatibleUpperGeometryMateAt i) :=
      ⟨element.1, hqualified⟩
    have htarget := qualifiedComparisonIsoTargetProjectionMulEquiv_apply
      (comparisonIsoAt input i) qualified
    change endpointChangeEquivAt input i element.1.1 = element.1.2 at htarget
    exact htarget
  · intro hgraph
    have htarget : endpointChangeEquivAt input i pair.1 = pair.2 := by
      exact congrArg Subtype.val (MonoidHom.mem_graph.mp hgraph)
    refine ⟨endpointKernelProductEquivAt input i pair, ?_, by rfl⟩
    apply (mem_compatibleKernel_iff (observationAt input i)
      (compatibleSubgroupAt input i) _).mpr
    change ((pair.1 : CompositeFiberAut
        (input.generatedBaseRouteGeometryAt i)),
      (pair.2 : CompositeFiberAut
        (input.generatedPulledRouteGeometryAt i))) ∈
        qualifiedComparisonSubgroup
          (input.generatedCompatibleUpperGeometryMateAt i)
    have hqualified :=
      (qualifiedComparisonIsoGraphMulEquiv (comparisonIsoAt input i)
        (pair.1 : CompositeFiberAut
          (input.generatedBaseRouteGeometryAt i))).2
    have hqualified' :
        ((pair.1 : CompositeFiberAut
            (input.generatedBaseRouteGeometryAt i)),
          endpointChangeEquivAt input i pair.1) ∈
            qualifiedComparisonSubgroup
              (input.generatedCompatibleUpperGeometryMateAt i) := by
      change
        ((pair.1 : CompositeFiberAut
            (input.generatedBaseRouteGeometryAt i)),
          endpointChangeEquivAt input i pair.1) ∈
            qualifiedComparisonSubgroup (comparisonIsoAt input i).hom
      exact hqualified
    rw [htarget] at hqualified'
    exact hqualified'

/-- G-120(B2) construction: transport the actual observation-loss coset set
through `K_c ≃ K_X^obs × K_Y^obs`; the compatible kernel becomes the graph
of endpoint comparison conjugation by the preceding theorem. -/
noncomputable def observationLossToProductQuotientAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    observationLossAt input i ≃
      (SourceObservationKernelAt input i ×
        TargetObservationKernelAt input i) ⧸
          (endpointObservationKernelEquivAt input i).toMonoidHom.graph :=
  PointedLeftCoset.equivOfMapEq
    (compatibleKernelAt input i)
    ((endpointObservationKernelEquivAt input i).toMonoidHom.graph)
    (endpointKernelProductEquivAt input i).symm
    (compatibleKernelInEndpointProductAt_eq_graph input i)

/-- G-120(B2) target classification `Psi`: the actual pointed observation-loss
set is equivalent to the target endpoint observation kernel. -/
noncomputable def observationLossEquivTargetKernelAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    observationLossAt input i ≃ TargetObservationKernelAt input i :=
  (observationLossToProductQuotientAt input i).trans
    (PointedLeftCoset.graphQuotientEquiv
      (endpointObservationKernelEquivAt input i))

/-- G-120(B2) representative formula for `Psi`: after writing an actual
observation-kernel change as `(a,b)`, its loss class maps to
`b * T(a)⁻¹`. -/
@[simp] theorem observationLossEquivTargetKernelAt_mk
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (change : observationKernelAt input i) :
    observationLossEquivTargetKernelAt input i (QuotientGroup.mk change) =
      ((endpointKernelProductEquivAt input i).symm change).2 *
        (endpointObservationKernelEquivAt input i
          ((endpointKernelProductEquivAt input i).symm change).1)⁻¹ :=
  rfl

/-- G-120(B2) inverse formula for `Psi`: a target-kernel element `value` is
represented by the loss class of the endpoint pair `(1,value)`. -/
@[simp] theorem observationLossEquivTargetKernelAt_symm_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (value : TargetObservationKernelAt input i) :
    (observationLossEquivTargetKernelAt input i).symm value =
      QuotientGroup.mk
        (endpointKernelProductEquivAt input i (1, value)) :=
  rfl

/-- G-120(B2) pointedness: `Psi` sends the distinguished loss class to the
identity of the target endpoint observation kernel. -/
@[simp] theorem observationLossEquivTargetKernelAt_basepoint
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    observationLossEquivTargetKernelAt input i (QuotientGroup.mk 1) = 1 := by
  rw [observationLossEquivTargetKernelAt_mk]
  simp

/-- G-120(B2) consequence: the actual observation-loss set is a singleton
exactly when the target endpoint observation kernel is a singleton. -/
theorem subsingleton_observationLoss_iff_targetKernel
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    Subsingleton (observationLossAt input i) ↔
      Subsingleton (TargetObservationKernelAt input i) :=
  (observationLossEquivTargetKernelAt input i).subsingleton_congr

/-- G-120(B2) elementary target-kernel form: singleton means every target
observation-kernel element is the identity. -/
theorem subsingleton_targetKernel_iff_eq_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    Subsingleton (TargetObservationKernelAt input i) ↔
      ∀ value : TargetObservationKernelAt input i, value = 1 := by
  constructor
  · intro h value
    exact @Subsingleton.elim _ h value 1
  · intro h
    exact ⟨fun a b => (h a).trans (h b).symm⟩

/-- G-120(B2) exact observation-only criterion: an actual compatible-change
predicate depending only on the observed comparison exists exactly when every
target endpoint observation-kernel element is the identity. -/
theorem exists_observation_predicate_iff_targetKernel_eq_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (∃ predicate : ObservationGroupAt input i → Prop,
        ∀ change : ChangeGroupAt input i,
          change ∈ compatibleSubgroupAt input i ↔
            predicate (observationAt input i change)) ↔
      ∀ value : TargetObservationKernelAt input i, value = 1 := by
  calc
    _ ↔ observationKernelAt input i ≤ compatibleSubgroupAt input i :=
      exists_observation_predicate_iff_kernel_leAt input i
    _ ↔ Subsingleton (observationLossAt input i) :=
      (subsingleton_kernel_quotient_iff_ker_le
        (observationAt input i) (compatibleSubgroupAt input i)).symm
    _ ↔ Subsingleton (TargetObservationKernelAt input i) :=
      subsingleton_observationLoss_iff_targetKernel input i
    _ ↔ _ := subsingleton_targetKernel_iff_eq_one input i

end GeneratedComparison

end

end AAT.AG.ComparisonInformationLoss

#assert_standard_axioms_only AAT.AG.ComparisonInformationLoss.PointedLeftCoset
#assert_standard_axioms_only AAT.AG.ComparisonInformationLoss.GeneratedComparison
