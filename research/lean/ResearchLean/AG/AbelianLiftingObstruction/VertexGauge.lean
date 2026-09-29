import ResearchLean.AG.AbelianLiftingObstruction.SolutionTorsor

/-!
# Vertex reidentification of actual coherent lifts

A zero-cochain acts through the coboundary in the same local coefficients. The
main arrow formula identifies that action with conjugation at the source and
target vertices of each original edge.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory TransportCoherence TransportCoherence.Arbitrary

universe uG uE uB uD vE vB vD

namespace OriginalTowerPresentation

variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)

/-- The vertex cochain acts on actual coherent original edge choices. -/
noncomputable def vertexGauge (b : C0 T.toTower.localCoefficients)
    (S : Solution T) : Solution T :=
  T.solutionAction (d0ToZ1 T.toTower.localCoefficients b) S

/-- Vertex reidentification is addition of the actual coboundary on corrections. -/
theorem vertexGauge_correction (b : C0 T.toTower.localCoefficients)
    (S : Solution T) :
    T.solutionCorrection (T.vertexGauge b S) =
      T.solutionCorrection S + d0 T.toTower.localCoefficients b :=
  T.solutionAction_correction _ S

/-- Transport across any chosen actual edge is the same map of the fixed core. -/
theorem selectedEdge_kernel_fac (S : Solution T)
    {i j : K.Vertex} (e : K.Edge i j)
    (a : Kernel p q (T.original.object i)) :
    (selectedUpper K p q T.original S.choice).edgeLift e ≫
      FiberAut.hom (kernelInclusion p q (T.original.object j)
        (Additive.toMul (T.toTower.localCoefficients.edge e (Additive.ofMul a)) :
          Kernel p q (T.original.object j))) =
      FiberAut.hom (kernelInclusion p q (T.original.object i) a) ≫
        (selectedUpper K p q T.original S.choice).edgeLift e := by
  have hfac := kernelTransportHom_fac p q
    ((selectedUpper K p q T.original S.choice).edgeLift e)
    ((selectedUpper K p q T.original S.choice).edgeStrong e)
    (selectedLowerStrong K p q T.original T.originalLowerStrong S.choice e) a
  rw [← T.edgeTransport_independent_lift S.choice S.choice_core e] at hfac
  exact hfac

/-- G-129 (C1): vertex reidentification acts by the original edge's two endpoint automorphisms. -/
theorem vertexGauge_edge_arrow (b : C0 T.toTower.localCoefficients)
    (S : Solution T) {i j : K.Vertex} (e : K.Edge i j) :
    (selectedUpper K p q T.original (T.vertexGauge b S).choice).edgeLift e =
      (FiberAut.hom (kernelInclusion p q (T.original.object i)
        (Additive.toMul (-(b i)) : Kernel p q (T.original.object i))) ≫
        (selectedUpper K p q T.original S.choice).edgeLift e) ≫
      FiberAut.hom (kernelInclusion p q (T.original.object j)
        (Additive.toMul (b j) : Kernel p q (T.original.object j))) := by
  let a : Kernel p q (T.original.object i) := Additive.toMul (b i)
  let c : Kernel p q (T.original.object j) := Additive.toMul (b j)
  let t : Kernel p q (T.original.object j) :=
    Additive.toMul (T.toTower.localCoefficients.edge e (b i))
  have hchoice := T.solutionAction_edge
    (d0ToZ1 T.toTower.localCoefficients b) S e
  change (T.vertexGauge b S).choice e =
    kernelInclusion p q (T.original.object j)
      (Additive.toMul (d0 T.toTower.localCoefficients b ⟨i, j, e⟩) :
        Kernel p q (T.original.object j)) * S.choice e at hchoice
  have hselected :
      (selectedUpper K p q T.original (T.vertexGauge b S).choice).edgeLift e =
        (selectedUpper K p q T.original S.choice).edgeLift e ≫
          FiberAut.hom (kernelInclusion p q (T.original.object j)
            (Additive.toMul (d0 T.toTower.localCoefficients b ⟨i, j, e⟩) :
              Kernel p q (T.original.object j))) := by
    change T.original.edgeLift e ≫ FiberAut.hom ((T.vertexGauge b S).choice e) =
      (T.original.edgeLift e ≫ FiberAut.hom (S.choice e)) ≫
        FiberAut.hom (kernelInclusion p q (T.original.object j)
          (Additive.toMul (d0 T.toTower.localCoefficients b ⟨i, j, e⟩) :
            Kernel p q (T.original.object j)))
    rw [hchoice]
    exact (Category.assoc _ _ _).symm
  have hfac := T.selectedEdge_kernel_fac S e
    (Additive.toMul (-(b i)) : Kernel p q (T.original.object i))
  have htransport : Additive.toMul
      (T.toTower.localCoefficients.edge e (-(b i))) = t⁻¹ := by
    rw [map_neg]
    rfl
  change (selectedUpper K p q T.original S.choice).edgeLift e ≫
      FiberAut.hom (kernelInclusion p q (T.original.object j)
        (Additive.toMul (T.toTower.localCoefficients.edge e (-(b i))) :
          Kernel p q (T.original.object j))) =
      FiberAut.hom (kernelInclusion p q (T.original.object i)
        (Additive.toMul (-(b i)) : Kernel p q (T.original.object i))) ≫
        (selectedUpper K p q T.original S.choice).edgeLift e at hfac
  have hfac' : (selectedUpper K p q T.original S.choice).edgeLift e ≫
      FiberAut.hom (kernelInclusion p q (T.original.object j) t⁻¹) =
      FiberAut.hom (kernelInclusion p q (T.original.object i)
        (Additive.toMul (-(b i)) : Kernel p q (T.original.object i))) ≫
        (selectedUpper K p q T.original S.choice).edgeLift e := by
    rw [← htransport]
    exact hfac
  rw [hselected]
  calc
    (selectedUpper K p q T.original S.choice).edgeLift e ≫
        FiberAut.hom (kernelInclusion p q (T.original.object j)
          (Additive.toMul (d0 T.toTower.localCoefficients b ⟨i, j, e⟩) :
            Kernel p q (T.original.object j))) =
      ((selectedUpper K p q T.original S.choice).edgeLift e ≫
        FiberAut.hom (kernelInclusion p q (T.original.object j) t⁻¹)) ≫
        FiberAut.hom (kernelInclusion p q (T.original.object j) c) := by
          rw [Category.assoc]
          congr 1
    _ = _ := by rw [hfac']

/-- The zero vertex reidentification is the identity on actual solutions. -/
theorem vertexGauge_zero (S : Solution T) :
    T.vertexGauge 0 S = S := by
  change T.solutionAction (d0ToZ1 T.toTower.localCoefficients 0) S = S
  rw [map_zero]
  exact T.solutionAction_zero S

/-- Consecutive vertex reidentifications add in the same zero-cochain group. -/
theorem vertexGauge_add (b c : C0 T.toTower.localCoefficients)
    (S : Solution T) :
    T.vertexGauge (b + c) S = T.vertexGauge b (T.vertexGauge c S) := by
  change T.solutionAction (d0ToZ1 T.toTower.localCoefficients (b + c)) S =
    T.solutionAction (d0ToZ1 T.toTower.localCoefficients b)
      (T.solutionAction (d0ToZ1 T.toTower.localCoefficients c) S)
  rw [map_add]
  exact T.solutionAction_add _ _ S

end OriginalTowerPresentation

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
