import ResearchLean.AG.AbelianLiftingObstruction.KernelTransport
import ResearchLean.AG.CrossStageCoherence.PastingObstruction

/-!
# The same kernel and transport in the geometry-to-core tower

G-129 D: the arbitrary-functor groups and the existing Chapter 4 groups retain
the same full automorphisms, projection, inclusion, and path transport.
This connects the general kernel construction to `InnerFiberAut` without
replacing either the original geometry arrow or the core projection.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence TransportCoherence.Arbitrary

universe u v

/-- G-129 D: the composite fiber comparison retains every original automorphism. -/
def compositeFiberEquiv {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    CompositeFiberAut G ≃* FiberAut (geometryProjection U ⋙ packageProjection U) G where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- API: the composite fiber comparison preserves the full forward arrow. -/
@[simp] theorem compositeFiberEquiv_hom {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) (a : CompositeFiberAut G) :
    FiberAut.hom (compositeFiberEquiv G a) = CompositeFiberAut.hom a := rfl

/-- API: the composite fiber comparison preserves the full inverse arrow. -/
@[simp] theorem compositeFiberEquiv_inv {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) (a : CompositeFiberAut G) :
    FiberAut.inv (compositeFiberEquiv G a) = CompositeFiberAut.inv a := rfl

/-- G-129 D: the comparison square uses exactly `compositeFiberPushforward`. -/
theorem compositeFiberEquiv_pushforward {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) (a : CompositeFiberAut G) :
    fiberPushforward (geometryProjection U) (packageProjection U) G (compositeFiberEquiv G a) =
      packageFiberAutMulEquiv G.core (compositeFiberPushforward G a) := rfl

/-- G-129 D: the actual kernel is exactly the same Chapter 4 `InnerFiberAut`. -/
def innerKernelEquiv {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    InnerFiberAut G ≃* Kernel (geometryProjection U) (packageProjection U) G where
  toFun a := ⟨compositeFiberEquiv G a.1,
    (fiberPushforward_eq_one_iff (geometryProjection U) (packageProjection U) G _).mpr a.2⟩
  invFun a := ⟨(compositeFiberEquiv G).symm a.1,
    (fiberPushforward_eq_one_iff (geometryProjection U) (packageProjection U) G _).mp a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- G-129 D: the kernel comparison preserves the original inclusion. -/
@[simp] theorem innerKernelEquiv_inclusion {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) (a : InnerFiberAut G) :
    kernelInclusion (geometryProjection U) (packageProjection U) G (innerKernelEquiv G a) =
      compositeFiberEquiv G (innerFiberInclusion G a) := rfl

/-- API: the kernel comparison retains the original forward geometry morphism. -/
@[simp] theorem innerKernelEquiv_hom {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) (a : InnerFiberAut G) :
    FiberAut.hom (kernelInclusion (geometryProjection U) (packageProjection U) G
      (innerKernelEquiv G a)) = a.1.1.hom := rfl

/-- API: the kernel comparison retains the original inverse geometry morphism. -/
@[simp] theorem innerKernelEquiv_inv {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) (a : InnerFiberAut G) :
    FiberAut.inv (kernelInclusion (geometryProjection U) (packageProjection U) G
      (innerKernelEquiv G a)) = a.1.1.inv := rfl

/-- G-129 D: general kernel transport recovers the existing actual path whisker. -/
theorem innerKernelEquiv_transport
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U) (current : UpperEdgeReselection data)
    {i j : P.Vertex} (path : P.Path i j) (a : InnerFiberAut (data.geometry i)) :
    kernelInclusion (geometryProjection U) (packageProjection U) (data.geometry j)
      (kernelTransportHom (geometryProjection U) (packageProjection U)
        (upperReselectedPathLift data current path)
        ((upperReselectLiftData data current).pathLift_compositeStrong path)
        ((upperReselectLiftData data current).pathLift_coreStrong path)
        (innerKernelEquiv (data.geometry i) a)) =
      compositeFiberEquiv (data.geometry j)
        (upperWhiskerCompositeFiberAut data current (innerFiberInclusion (data.geometry i) a) path) := by
  apply FiberAut.ext_of_strong_fac (upperReselectedPathLift data current path)
    ((upperReselectLiftData data current).pathLift_compositeStrong path)
  rw [kernelTransportHom_fac, compositeFiberEquiv_hom]
  exact (upperWhiskerCompositeFiberAut_fac data current
    (innerFiberInclusion (data.geometry i) a) path).symm

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
