import ResearchLean.AG.ObstructionDiagnosticBridge.LocallyConstantCoefficient
import Formal.AG.Cohomology.ObstructionSheaf
import Mathlib.CategoryTheory.Sites.Continuous
import Formal.Util.AssertStandardAxioms

/-!
# Pulling locally constant presentation coefficients back to an AAT site

This module records the geometric part of the selected G-125 input: every AAT
context has an open support, readable refinement induces inclusion of supports,
and the support functor is continuous for the AAT and open-set topologies.
Continuity is Mathlib's generic site-theoretic condition, not a certificate for
the presentation coefficient sheaf.

The locally constant `M_R`-valued sheaf constructed previously is then pulled
back along the support functor.  Its sheaf condition follows from the generic
topology compatibility and the proved topological sheaf theorem, and the
result is packaged by the existing `ObstructionSheaf.ofAddCommGrpValued`.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AAT.AG.ObstructionDiagnosticBridge

open CanonicalResolution ResolutionInvariance

universe u

/--
The context-to-open-support part of the selected G-125 input.

`continuous` says that the selected AAT topology is compatible with the
open-support functor in Mathlib's standard site-theoretic sense: pulling back
any sheaf on the open-set site gives an AAT sheaf.
-/
structure ContextOpenSupport {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A) where
  space : TopCat.{u}
  support : S.category ⥤ Opens space
  continuous : Functor.IsContinuous.{u} support S.topology
    (Opens.grothendieckTopology space)

namespace GeneratorPresentation

variable {Source : Type u} {laws : FiniteLawFamily Source}
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}

/-- The locally constant presentation coefficients pulled back to AAT contexts. -/
def aatLocallyConstantAddCommGrpPresheaf (P : GeneratorPresentation laws)
    (G : ContextOpenSupport S) : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u} :=
  G.support.op ⋙ P.locallyConstantAddCommGrpPresheaf G.space

/-- The underlying Type-valued functor is the pullback of the topological sheaf. -/
theorem aatLocallyConstant_forget (P : GeneratorPresentation laws)
    (G : ContextOpenSupport S) :
    P.aatLocallyConstantAddCommGrpPresheaf G ⋙ forget AddCommGrpCat.{u} =
      G.support.op ⋙
        (P.locallyConstantAddCommGrpPresheaf G.space ⋙ forget AddCommGrpCat.{u}) := by
  rfl

/-- Topology compatibility transports the proved locally constant sheaf condition. -/
theorem aatLocallyConstantAddCommGrpPresheaf_isSheaf
    (P : GeneratorPresentation laws) (G : ContextOpenSupport S) :
    Site.AATSheafCondition S
      (P.aatLocallyConstantAddCommGrpPresheaf G ⋙ forget AddCommGrpCat.{u}) := by
  rw [Site.AATSheafCondition.iff_presieve_isSheaf]
  letI : Functor.IsContinuous.{u} G.support S.topology
      (Opens.grothendieckTopology G.space) := G.continuous
  exact G.support.op_comp_isSheaf_of_types S.topology
    (Opens.grothendieckTopology G.space)
    ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2
      (P.locallyConstantAddCommGrpPresheaf_isSheaf G.space)⟩

/-- The actual G-125 obstruction sheaf on the selected AAT site. -/
def aatLocallyConstantObstructionSheaf (P : GeneratorPresentation laws)
    (G : ContextOpenSupport S) : Cohomology.ObstructionSheaf S :=
  Cohomology.ObstructionSheaf.ofAddCommGrpValued
    (P.aatLocallyConstantAddCommGrpPresheaf G)
    (P.aatLocallyConstantAddCommGrpPresheaf_isSheaf G)

/-- Sections of the obstruction sheaf are locally constant functions on context support. -/
theorem aatLocallyConstantObstructionSheaf_obj
    (P : GeneratorPresentation laws) (G : ContextOpenSupport S)
    (W : S.category) :
    (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.obj (op W) =
      P.LocallyConstantSection G.space (G.support.obj W) := by
  rfl

/--
On a nonempty preconnected support, the actual obstruction-sheaf section group
is additively equivalent to the presentation group `M_R`.
-/
def aatLocallyConstantObstructionSectionEquiv
    (P : GeneratorPresentation laws) (G : ContextOpenSupport S)
    (W : S.category) [Nonempty (G.support.obj W)]
    [PreconnectedSpace (G.support.obj W)] :
    (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.obj (op W) ≃+
      P.PresentationGroup :=
  P.locallyConstantSectionEquiv G.space (G.support.obj W)

/--
Restriction in the actual obstruction sheaf is the identity after evaluating
sections on nonempty preconnected supports.
-/
theorem aatLocallyConstantObstructionSectionEquiv_restriction
    (P : GeneratorPresentation laws) (G : ContextOpenSupport S)
    (source target : S.category)
    [Nonempty (G.support.obj source)] [PreconnectedSpace (G.support.obj source)]
    [Nonempty (G.support.obj target)] [PreconnectedSpace (G.support.obj target)]
    (f : source ⟶ target)
    (localValue :
      (P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.obj (op target)) :
    P.aatLocallyConstantObstructionSectionEquiv G source
        ((P.aatLocallyConstantObstructionSheaf G).carrier.toPresheaf.map f.op localValue) =
      P.aatLocallyConstantObstructionSectionEquiv G target localValue := by
  exact P.locallyConstantSectionEquiv_restriction G.space
    (G.support.obj target) (G.support.obj source)
    ((Opens.toTopCat G.space).map (G.support.map f)).hom localValue

end GeneratorPresentation

#assert_standard_axioms_only AAT.AG.ObstructionDiagnosticBridge

end AAT.AG.ObstructionDiagnosticBridge
