import ResearchLean.AG.QualitySurface.LawGeneratedIdealPowerSequence
import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Short exact law-generated ideal-power sequence

The raw law-generated conormal sequence is packaged as a categorical short
exact sequence of `AddCommGrpCat`-valued presheaves.  Exactness is constructed
from the explicit objectwise kernel equivalence of Cycle 6.  No exactness,
kernel, sheaf, or effectivity field is accepted.

When Mathlib's `HasSheafify` instance is available for the selected topology
and `AddCommGrpCat`, the short exact sequence is sent through the canonical
sheafification functor.
-/

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace LawGeneratedIdealPowerSequence
namespace Raw

universe u

open CategoryTheory Limits Opposite
open AAT.AG AAT.AG.LawAlgebra

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable (G : ArchitecturalEquationSystem S.contextPreorder)

/-- The ambient category of additive presheaves used by the raw sequence. -/
abbrev PresheafCategory := S.categoryᵒᵖ ⥤ AddCommGrpCat.{u}

/-- The categorical raw conormal sequence `I/I² → O/I² → O/I`. -/
def shortComplex : ShortComplex (PresheafCategory (S := S)) :=
  ShortComplex.mk (conormalInclusion G) (projection G) (projection_comp_inclusion G)

/-- The raw conormal inclusion is a monomorphism of presheaves. -/
instance conormalInclusion_mono : Mono (conormalInclusion G) := by
  rw [NatTrans.mono_iff_mono_app]
  intro W
  rw [AddCommGrpCat.mono_iff_injective]
  exact conormalInclusionAt_injective G W.unop

/-- The raw quotient projection is an epimorphism of presheaves. -/
instance projection_epi : Epi (projection G) := by
  rw [NatTrans.epi_iff_epi_app]
  intro W
  rw [AddCommGrpCat.epi_iff_surjective]
  exact projectionAt_surjective G W.unop

/-- Applying the objectwise kernel equivalence and its inverse recovers the kernel element. -/
theorem conormalInclusionAt_equiv_symm (W : S.category)
    (y : AddMonoidHom.ker (projectionAt G W).toAddMonoidHom) :
    conormalInclusionAt G W ((conormalKernelEquiv G W).symm y) = y.1 := by
  have h := conormalKernelEquiv_apply G W ((conormalKernelEquiv G W).symm y)
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

/-- A pointwise kernel witness obtained from a morphism killed by the projection. -/
def kernelElement {Z : PresheafCategory (S := S)}
    (k : Z ⟶ q1Coefficient G) (hk : k ≫ projection G = 0)
    (W : S.categoryᵒᵖ) (z : Z.obj W) :
    AddMonoidHom.ker (projectionAt G W.unop).toAddMonoidHom :=
  ⟨k.app W z, by
    have hz := congrArg (fun η => η.app W z) hk
    change projectionAt G W.unop (k.app W z) = 0
    simpa [projection] using hz⟩

/-- The objectwise kernel lift is natural and therefore a presheaf morphism. -/
noncomputable def kernelLift {Z : PresheafCategory (S := S)}
    (k : Z ⟶ q1Coefficient G) (hk : k ≫ projection G = 0) :
    Z ⟶ conormalCoefficient G where
  app W := AddCommGrpCat.ofHom
    ((conormalKernelEquiv G W.unop).symm.toAddMonoidHom.comp
      { toFun := fun z => kernelElement G k hk W z
        map_zero' := by
          apply Subtype.ext
          exact map_zero (k.app W).hom
        map_add' := by
          intro x y
          apply Subtype.ext
          exact map_add (k.app W).hom x y })
  naturality {X Y} φ := by
    ext z
    change (conormalKernelEquiv G Y.unop).symm
        (kernelElement G k hk Y (Z.map φ z)) =
      (conormalCoefficient G).map φ
        ((conormalKernelEquiv G X.unop).symm (kernelElement G k hk X z))
    apply conormalInclusionAt_injective G Y.unop
    calc
      conormalInclusionAt G Y.unop
          ((conormalKernelEquiv G Y.unop).symm
            (kernelElement G k hk Y (Z.map φ z))) =
          k.app Y (Z.map φ z) := by
            rw [conormalInclusionAt_equiv_symm]
            rfl
      _ = (q1Coefficient G).map φ (k.app X z) := k.naturality_apply φ z
      _ = (q1Coefficient G).map φ
          (conormalInclusionAt G X.unop
            ((conormalKernelEquiv G X.unop).symm (kernelElement G k hk X z))) := by
            rw [conormalInclusionAt_equiv_symm]
            rfl
      _ = conormalInclusionAt G Y.unop
          ((conormalCoefficient G).map φ
            ((conormalKernelEquiv G X.unop).symm (kernelElement G k hk X z))) := by
            exact ((conormalInclusion G).naturality_apply φ _).symm

/-- The explicit kernel lift factors the original morphism. -/
theorem kernelLift_fac {Z : PresheafCategory (S := S)}
    (k : Z ⟶ q1Coefficient G) (hk : k ≫ projection G = 0) :
    kernelLift G k hk ≫ conormalInclusion G = k := by
  ext W z
  exact conormalInclusionAt_equiv_symm G W.unop (kernelElement G k hk W z)

/-- The law-generated conormal inclusion is the categorical kernel of the projection. -/
noncomputable def conormalInclusionIsKernel :
    IsLimit (KernelFork.ofι (conormalInclusion G) (projection_comp_inclusion G)) :=
  KernelFork.IsLimit.ofι' (conormalInclusion G) (projection_comp_inclusion G)
    (fun k hk => ⟨kernelLift G k hk, kernelLift_fac G k hk⟩)

/-- The raw categorical conormal sequence is exact. -/
theorem shortComplex_exact : (shortComplex G).Exact :=
  (shortComplex G).exact_of_f_is_kernel (conormalInclusionIsKernel G)

/-- The first map of the displayed short complex is mono. -/
instance shortComplex_mono_f : Mono (shortComplex G).f := by
  change Mono (conormalInclusion G)
  infer_instance

/-- The second map of the displayed short complex is epi. -/
instance shortComplex_epi_g : Epi (shortComplex G).g := by
  change Epi (projection G)
  infer_instance

/-- The raw categorical conormal sequence is short exact. -/
theorem shortComplex_shortExact : (shortComplex G).ShortExact :=
  ShortComplex.ShortExact.mk' (shortComplex_exact G)
    (inferInstance : Mono (shortComplex G).f)
    (inferInstance : Epi (shortComplex G).g)

/-! ## Canonical sheafification -/

variable [HasSheafify S.topology AddCommGrpCat.{u}]

/-- The raw short complex mapped through canonical additive sheafification. -/
noncomputable def sheafifiedShortComplex :
    ShortComplex (Sheaf S.topology AddCommGrpCat.{u}) :=
  (shortComplex G).map (presheafToSheaf S.topology AddCommGrpCat.{u})

/-- Canonical sheafification preserves the generated short exact sequence. -/
theorem sheafifiedShortComplex_shortExact :
    (sheafifiedShortComplex G).ShortExact :=
  (shortComplex_shortExact G).map_of_exact
    (presheafToSheaf S.topology AddCommGrpCat.{u})

end Raw
end LawGeneratedIdealPowerSequence
end ResearchLean.AG.QualitySurface

#assert_standard_axioms_only ResearchLean.AG.QualitySurface.LawGeneratedIdealPowerSequence.Raw
