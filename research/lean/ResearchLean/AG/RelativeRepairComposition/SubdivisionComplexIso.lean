import ResearchLean.AG.RelativeRepairComposition.SubdivisionSupportedCochains
import ResearchLean.AG.RelativeRepairComposition.NativeIdentityComplex
import Mathlib.Algebra.Group.ULift

/-!
# The actual supported relative subdivision complex splits natively

For every permission range, the same original complex is paired with the
contractible entire kernel at the fresh object. The actual original d0, d1 and
d2 agree in these coordinates, including both full three-cell routes.

## Implementation notes

ULift places the whole fresh kernel in the same universe as the cochain
families; its down map retains every actual value. The comparison is assembled
from the already proved original differentials and then the native biproduct.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory Limits TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable (P : ClosedRegion K) (candidates allowed : Set (EdgeName (K := K)))
variable (hp : chosen ∉ P.edges) (hc : chosen ∉ candidates)

/-- The native identity summand uses the entire actual new-object kernel in the cochain universe. -/
noncomputable def freshComplex : CochainComplex AddCommGrpCat.{max uG vE} ℕ :=
  NativeIdentityComplex.complex (ULift.{uG} ((originalTower T chosen F).toTower.localCoefficients.A (.inr ())))

/-- The whole actual full-kernel summand is natively contractible. -/
noncomputable def freshContraction : Homotopy (𝟙 (freshComplex T chosen F)) 0 :=
  NativeIdentityComplex.contraction _

/-- The original permission complex paired with the full fresh identity summand. -/
noncomputable def splitComplex : CochainComplex AddCommGrpCat.{max uG vE} ℕ :=
  NativeProductComplex.complex
    (RelativeComplex.cochainComplex T.toTower.localCoefficients P candidates allowed)
    (freshComplex T chosen F)

/-- A zero second group retains precisely the original first value. -/
def zeroProductEquiv (G : Type*) [AddCommGroup G] : G ≃+ G × PUnit where
  toFun x := ⟨x,⟨⟩⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  map_add' _ _ := rfl

/-- The actual subdivision has the original supported groups plus the full fresh group in degrees zero and one. -/
noncomputable def relativeComponentIso : ∀ n,
    (RelativeComplex.cochainComplex (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)).X n ≅
    (splitComplex T chosen F P candidates allowed).X n
  | 0 => ((relative0Equiv T chosen F P candidates allowed hp hc).trans
      (AddEquiv.prodCongr (AddEquiv.refl _) (AddEquiv.ulift.symm))).toAddCommGrpIso
  | 1 => ((relative1Equiv T chosen F P candidates allowed hp hc).trans
      (AddEquiv.prodCongr (AddEquiv.refl _) (AddEquiv.ulift.symm))).toAddCommGrpIso
  | 2 => (zeroProductEquiv (RelativeComplex.relativeC2 T.toTower.localCoefficients P)).toAddCommGrpIso
  | 3 => (zeroProductEquiv (RelativeComplex.relativeC3 T.toTower.localCoefficients P)).toAddCommGrpIso
  | _ + 4 => (zeroProductEquiv PUnit).toAddCommGrpIso

/-- Every degree comparison commutes with the same original supported relative differential. -/
theorem relative_component_comm (n : ℕ) :
    (relativeComponentIso T chosen F P candidates allowed hp hc n).hom ≫
      (splitComplex T chosen F P candidates allowed).d n (n+1) =
    (RelativeComplex.cochainComplex (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)).d n (n+1) ≫
      (relativeComponentIso T chosen F P candidates allowed hp hc (n+1)).hom := by
  simp only [splitComplex,NativeProductComplex.complex_d,RelativeComplex.cochainComplex,CochainComplex.of_d]
  rcases n with _ | _ | _ | n
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro b
    apply Prod.ext
    · exact (congrArg Prod.fst (relative_d0 T chosen F P candidates allowed hp hc b)).symm
    · exact congrArg ULift.up
        (congrArg Prod.snd (relative_d0 T chosen F P candidates allowed hp hc b)).symm
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro h
    apply Prod.ext
    · exact (relative_d1 T chosen F P candidates allowed hp hc h).symm
    · rfl
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro c
    apply Prod.ext
    · exact (relative_d2 T chosen F P hp c).symm
    · rfl
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change (PUnit.unit,PUnit.unit) = _
    exact Subsingleton.elim _ _

/-- The actual entire supported relative subdivision complex splits by its original cochain maps. -/
noncomputable def relativeProductIso :
    RelativeComplex.cochainComplex (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed) ≅
    splitComplex T chosen F P candidates allowed :=
  HomologicalComplex.Hom.isoOfComponents (relativeComponentIso T chosen F P candidates allowed hp hc) (by
    intro i j hij
    change i+1=j at hij
    subst j
    exact relative_component_comm T chosen F P candidates allowed hp hc i)

/-- The same actual supported complex is the native biproduct of the original complex and its full contractible kernel summand. -/
noncomputable def relativeBiprodIso :
    RelativeComplex.cochainComplex (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed) ≅
    RelativeComplex.cochainComplex T.toTower.localCoefficients P candidates allowed ⊞
      freshComplex T chosen F :=
  (relativeProductIso T chosen F P candidates allowed hp hc).trans
    (NativeProductComplex.iso _ _)

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
