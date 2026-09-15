import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualLocalFiberProjection
import Formal.Util.AssertStandardAxioms

/-!
# Doctrine-source rigidity at the finite-axis-fold normalized endpoint

The residual analysis must retain the lower exact-doctrine map independently
of the Atom and upper-reading components.  This file extracts the actual action
of every normalized endpoint automorphism on the complete doctrine-source
carrier.  The inverse automorphism supplies the inverse function.  The pointed
source law then fixes the selected source; because the fixed source carrier has
exactly two elements, the whole permutation is forced to be the identity.

No source map, inverse, finite table, or rigidity certificate is accepted as
an input.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization

noncomputable section

private noncomputable abbrev FiniteAxisFoldResidualSourceCore :=
  finiteAxisFoldActualDirectAdmissibleGeometry.obj.core

/-- The complete doctrine-source carrier of the actual normalized endpoint. -/
abbrev FiniteAxisFoldResidualDoctrineSource :=
  FiniteAxisFoldResidualSourceCore.reading.doctrine.Source

/-- The actual source-map action of a normalized endpoint automorphism. -/
noncomputable def finiteAxisFoldNormalizedDoctrineSourceEquiv
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    Equiv.Perm FiniteAxisFoldResidualDoctrineSource where
  toFun := automorphism.hom.f.hom.base.base.doctrineHom.sourceMap
  invFun := automorphism.inv.f.hom.base.base.doctrineHom.sourceMap
  left_inv source := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        hom.f.hom.base.base.doctrineHom.sourceMap source)
      automorphism.hom_inv_id
    exact equality
  right_inv source := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        hom.f.hom.base.base.doctrineHom.sourceMap source)
      automorphism.inv_hom_id
    exact equality

/-- The source action is multiplicative on the full normalized automorphism
group. -/
noncomputable def finiteAxisFoldNormalizedDoctrineSourceProjection :
    Aut FiniteAxisFoldNormalizedDirectGeometry →*
      Equiv.Perm FiniteAxisFoldResidualDoctrineSource where
  toFun := finiteAxisFoldNormalizedDoctrineSourceEquiv
  map_one' := by
    apply Equiv.ext
    intro source
    rfl
  map_mul' first second := by
    apply Equiv.ext
    intro source
    rfl

/-- Every normalized automorphism fixes the pointed source selected by the
actual endpoint package. -/
theorem finiteAxisFoldNormalizedDoctrineSourceEquiv_selected
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    finiteAxisFoldNormalizedDoctrineSourceEquiv automorphism
        FiniteAxisFoldResidualSourceCore.reading.source =
      FiniteAxisFoldResidualSourceCore.reading.source :=
  automorphism.hom.f.hom.base.base.source_eq

/-- The fixed endpoint doctrine has two sources.  Fixing its selected source
therefore forces the complete source permutation to be the identity. -/
theorem finiteAxisFoldNormalizedDoctrineSourceEquiv_eq_refl
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    finiteAxisFoldNormalizedDoctrineSourceEquiv automorphism = Equiv.refl _ := by
  apply Equiv.ext
  intro source
  unfold FiniteAxisFoldResidualDoctrineSource FiniteAxisFoldResidualSourceCore at source ⊢
  unfold finiteAxisFoldActualDirectAdmissibleGeometry at source ⊢
  unfold authoredExactDirectAdmissibleGeometryAt authoredExactDirectGeometryAt at source ⊢
  change ULift (Fin 2) at source
  have selected :=
    finiteAxisFoldNormalizedDoctrineSourceEquiv_selected automorphism
  change finiteAxisFoldNormalizedDoctrineSourceEquiv automorphism
      (ULift.up (1 : Fin 2)) = ULift.up (1 : Fin 2) at selected
  rcases source with ⟨source⟩
  fin_cases source
  · cases image_eq : finiteAxisFoldNormalizedDoctrineSourceEquiv automorphism
        (ULift.up (0 : Fin 2)) with
    | up image =>
        fin_cases image
        · exact image_eq
        · exfalso
          apply Fin.zero_ne_one
          apply ULift.up_injective
          apply (finiteAxisFoldNormalizedDoctrineSourceEquiv automorphism).injective
          exact image_eq.trans selected.symm
  · exact selected

/-- The full source projection is the trivial homomorphism; this conclusion is
derived for every normalized automorphism, not merely for the residual kernel. -/
theorem finiteAxisFoldNormalizedDoctrineSourceProjection_apply
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    finiteAxisFoldNormalizedDoctrineSourceProjection automorphism = 1 :=
  finiteAxisFoldNormalizedDoctrineSourceEquiv_eq_refl automorphism

/-- Function-level rigidity of the lower exact-doctrine source map for every
normalized endpoint automorphism. -/
theorem finiteAxisFoldNormalizedDoctrineSourceMap_eq_id
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    automorphism.hom.f.hom.base.base.doctrineHom.sourceMap = _root_.id := by
  funext source
  have evaluated := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldResidualDoctrineSource =>
      permutation source)
    (finiteAxisFoldNormalizedDoctrineSourceEquiv_eq_refl automorphism)
  exact evaluated

/-- In particular, every element of the full residual axis--signature kernel
has identity lower doctrine-source map.  Kernel membership is not needed for
the proof; the stronger full-automorphism theorem is applied. -/
theorem finiteAxisFoldResidual_doctrineSourceMap_eq_id
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel) :
    remainder.1.1.hom.f.hom.base.base.doctrineHom.sourceMap = _root_.id :=
  finiteAxisFoldNormalizedDoctrineSourceMap_eq_id remainder.1.1

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end


end AAT.AG.RealizationReconstruction
