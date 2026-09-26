import ResearchLean.AG.RealizationReconstruction.FixedFLensGroupConnection
import ResearchLean.AG.LocalSemanticReconstruction.FiniteApplicationHomDecoders
import ResearchLean.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction
import Formal.Util.AssertStandardAxioms

/-! Design IV-3: identify the literal all-H product-lens visible kernel
with automorphisms of the fixed semantic lens, transport it through the
common main reader, and evaluate its original state map at a local graph
point. -/
namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
universe u
attribute [local instance] uliftCategory
namespace CSLensKernelLocal
variable {V K : Type u} {reference : V} [Finite K]
  (H : Subgroup (Equiv.Perm V))
private abbrev X : LensRealization V reference :=
  LensRealization.product V K reference
private abbrev LensKernel := MonoidHom.ker
  (FixedFLensGroupConnection.LensChangeGroup.projection (K := K) (H := H))
/-- A visible-identity independent lens change acts as a semantic lens
automorphism, with inverse inherited from the actual state equivalence. -/
noncomputable def kernelToAut (element : LensKernel (K := K) H) : Aut (LensRealization.product V K reference) := by
  let change := element.1
  have hv : change.visible = 1 := MonoidHom.mem_ker.mp element.property
  let forward : LensRealization.product V K reference ⟶ LensRealization.product V K reference := {
    toFun := change.h
    get_naturality := by
      intro state
      simpa [X, hv] using change.get_naturality state
    put_naturality := by
      intro state requested
      simpa [X, hv] using change.put_naturality state requested
  }
  let backward : LensRealization.product V K reference ⟶ LensRealization.product V K reference := {
    toFun := change.h.symm
    get_naturality := by
      intro state
      have h := change.get_naturality (change.h.symm state)
      simpa [X, hv] using h.symm
    put_naturality := by
      intro state requested
      apply change.h.injective
      have h := change.put_naturality (change.h.symm state) requested
      simpa [X, hv] using h.symm
  }
  exact {
    hom := forward
    inv := backward
    hom_inv_id := by
      apply LensRealization.Hom.ext
      funext state
      exact change.h.symm_apply_apply state
    inv_hom_id := by
      apply LensRealization.Hom.ext
      funext state
      exact change.h.apply_symm_apply state
  }

/-- A semantic automorphism has the corresponding visible-identity
independent product-lens change. -/
noncomputable def autToKernel
    (aut : Aut (LensRealization.product V K reference)) :
    LensKernel (K := K) H := by
  let stateEquiv : Equiv.Perm (V × K) := {
    toFun := aut.hom.toFun
    invFun := aut.inv.toFun
    left_inv := by
      intro state
      have h := congrArg (fun f : LensRealization.product V K reference ⟶
        LensRealization.product V K reference => f.toFun state) aut.hom_inv_id
      exact h
    right_inv := by
      intro state
      have h := congrArg (fun f : LensRealization.product V K reference ⟶
        LensRealization.product V K reference => f.toFun state) aut.inv_hom_id
      exact h
  }
  refine ⟨{
    visible := 1
    h := stateEquiv
    get_naturality := by
      intro state
      simpa [stateEquiv] using aut.hom.get_naturality state
    put_naturality := by
      intro state requested
      simpa [stateEquiv] using aut.hom.put_naturality state requested
  }, ?_⟩
  rfl


/-- The literal visible-identity kernel is the automorphism group of the
fixed product lens, before applying the common main reader. -/
noncomputable def kernelAutMulEquiv :
    LensKernel (K := K) H ≃* Aut (LensRealization.product V K reference) where
  toFun := kernelToAut H
  invFun := autToKernel H
  left_inv element := by
    apply Subtype.ext
    apply FixedFLensGroupConnection.LensChangeGroup.ext
    · exact (MonoidHom.mem_ker.mp element.property).symm
    · apply Equiv.ext
      intro state
      rfl
  right_inv aut := by
    apply Aut.ext
    apply LensRealization.Hom.ext
    funext state
    rfl
  map_mul' first second := by
    apply Aut.ext
    apply LensRealization.Hom.ext
    funext state
    rfl


/-- Transport the literal product-lens kernel through the one main local
reader, preserving all automorphism Hom and inverse data. -/
noncomputable def kernelLocalAutMulEquiv
    (input : LensFamilyInput.{u}) {K : Type u} [Finite K]
    (H : Subgroup (Equiv.Perm input.View)) :
    MonoidHom.ker
      (FixedFLensGroupConnection.LensChangeGroup.projection (K := K) (H := H)) ≃*
      Aut ((reading (Parameter.lens input : Parameter.{u, u})).obj
        (ULiftHom.objUp
          (LensRealization.product input.View K input.reference))) := by
  let upEquiv := CategoryTheory.ULiftHom.equiv
    (C := LensRealization input.View input.reference)
  let mainEquiv := equivalence (Parameter.lens input : Parameter.{u, u})
  exact (kernelAutMulEquiv (reference := input.reference) (K := K) H).trans
    ((upEquiv.fullyFaithfulFunctor.autMulEquivOfFullyFaithful
      (LensRealization.product input.View K input.reference)).trans
      (mainEquiv.fullyFaithfulFunctor.autMulEquivOfFullyFaithful
        (ULiftHom.objUp
          (LensRealization.product input.View K input.reference))))


/-- The transported kernel automorphism is evaluated by the same main local
Hom graph point as its original product-lens state permutation. -/
theorem kernelLocalAut_point
    (input : LensFamilyInput.{u}) {K : Type u} [Finite K]
    (H : Subgroup (Equiv.Perm input.View))
    (element : MonoidHom.ker
      (FixedFLensGroupConnection.LensChangeGroup.projection (K := K) (H := H)))
    (state output : input.View × K) :
    FiniteApplicationHomDecoders.decodeLensPoint input
      (ULiftHom.objUp
        (LensRealization.product input.View K input.reference))
      (ULiftHom.objUp
        (LensRealization.product input.View K input.reference))
      state output
      (localHomTable (.lens input)
        (kernelLocalAutMulEquiv input H element).hom) = true ↔
      element.1.h state = output := by
  change FiniteApplicationHomDecoders.decodeLensPoint input
      (ULiftHom.objUp (LensRealization.product input.View K input.reference))
      (ULiftHom.objUp (LensRealization.product input.View K input.reference))
      state output
      (localHomTable (.lens input)
        ((reading (.lens input)).map
          (ULift.up ((kernelToAut (reference := input.reference) (K := K) H element).hom))))
        = true ↔ _
  exact FiniteApplicationHomDecoders.lensPoint_decode input
    (ULift.up ((kernelToAut (reference := input.reference) (K := K) H element).hom))
      state output


#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CSLensKernelLocal

end CSLensKernelLocal
end AAT.AG.LocalSemanticReconstruction
