import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteNativeCoordinates

/-!
# Full original-cell basis comparisons

## Implementation notes

A change of basis is generated at each original cell from the two full input
coordinate maps. It retains the original cell name and every coefficient.
Naturality is applied to the original relative differentials, including d2;
no new differential or vanishing law is supplied as a certificate.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
namespace FiniteFamily
universe uk ui ua
variable {k : Type uk} [Field k]
variable {I : Type ui} (A : I → Type ua)
variable [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
variable (B B' B'' : Bases (k := k) A) (s p : Set I)
variable [DecidablePred (· ∈ p)]

/-- Full linear basis change through the same independently defined original family. -/
def basisComparison : (Index A B s p → k) ≃ₗ[k] (Index A B' s p → k) :=
  (equivalence A B s p).symm.trans (equivalence A B' s p)

/-- Changing bases preserves every complete original coefficient value. -/
theorem restore_basis_comparison (x : Index A B s p → k) :
    (equivalence A B' s p).symm (basisComparison A B B' s p x) =
      (equivalence A B s p).symm x :=
  (equivalence A B' s p).symm_apply_apply _

/-- Every new coordinate uses its same original cell and the two full kernel bases. -/
theorem basis_comparison_value (x : Index A B s p → k) (j : Index A B' s p) :
    basisComparison A B B' s p x j = B'.coordinate j.1.1
      ((B.coordinate j.1.1).symm (fun l => x ⟨j.1,l⟩)) j.2 := by
  change B'.coordinate j.1.1
    (((equivalence A B s p).symm x).1 ⟨j.1.1,j.1.2.1⟩) j.2 = _
  rw [restore_value A B s p x ⟨j.1.1,j.1.2.1⟩ j.1.2.2]

/-- The reverse basis change restores all coordinate components. -/
theorem basis_comparison_inverse (x : Index A B s p → k) :
    basisComparison A B' B s p (basisComparison A B B' s p x) = x := by
  change equivalence A B s p ((equivalence A B' s p).symm
    (equivalence A B' s p ((equivalence A B s p).symm x))) = x
  rw [LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]

/-- Three full basis changes compose without altering any original coefficient. -/
theorem basis_comparison_comp (x : Index A B s p → k) :
    basisComparison A B' B'' s p (basisComparison A B B' s p x) =
      basisComparison A B B'' s p x := by
  change equivalence A B'' s p ((equivalence A B' s p).symm
    (equivalence A B' s p ((equivalence A B s p).symm x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- An unchanged full basis gives the identity on all original coordinates. -/
theorem basis_comparison_self (x : Index A B s p → k) :
    basisComparison A B B s p x = x := (equivalence A B s p).apply_symm_apply x

end FiniteFamily
namespace FiniteNative
universe uk uG uA
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (B B' : FiniteFamily.Bases (k := k) M.A) (U P : ClosedRegion K)
variable [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)]
variable [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ P.triples)]

/-- All original vertex coordinates change linearly through the full relative family. -/
def basisComparison0 := (coordinate0 M B U P).symm.trans (coordinate0 M B' U P)
/-- All original named edge coordinates retain their complete target kernel. -/
def basisComparison1 := (coordinate1 M B U P).symm.trans (coordinate1 M B' U P)
/-- All original face coordinates retain their authored target kernel. -/
def basisComparison2 := (coordinate2 M B U P).symm.trans (coordinate2 M B' U P)
/-- All original triple coordinates retain their authored target kernel. -/
def basisComparison3 := (coordinate3 M B U P).symm.trans (coordinate3 M B' U P)

omit [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ P.triples)] in
/-- The same full original vertex family is restored after changing bases. -/
theorem restore_basis0 (x : Index0 M B U P → k) :
    (coordinate0 M B' U P).symm (basisComparison0 M B B' U P x) =
      (coordinate0 M B U P).symm x := (coordinate0 M B' U P).symm_apply_apply _
omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ P.triples)] in
/-- The same full original edge family is restored after changing bases. -/
theorem restore_basis1 (x : Index1 M B U P → k) :
    (coordinate1 M B' U P).symm (basisComparison1 M B B' U P x) =
      (coordinate1 M B U P).symm x := (coordinate1 M B' U P).symm_apply_apply _
omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.triples)] in
/-- The same full original face family is restored after changing bases. -/
theorem restore_basis2 (x : Index2 M B U P → k) :
    (coordinate2 M B' U P).symm (basisComparison2 M B B' U P x) =
      (coordinate2 M B U P).symm x := (coordinate2 M B' U P).symm_apply_apply _
omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)] in
/-- The same full original triple family is restored after changing bases. -/
theorem restore_basis3 (x : Index3 M B U P → k) :
    (coordinate3 M B' U P).symm (basisComparison3 M B B' U P x) =
      (coordinate3 M B U P).symm x := (coordinate3 M B' U P).symm_apply_apply _

omit [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ P.triples)] in
/-- The original d0 is conjugated by the full vertex and edge basis changes. -/
theorem basis_comparison_d0 (x : Index0 M B U P → k) :
    coordinate1 M B' U P (RelativeCover.d0 M U P
      ((coordinate0 M B' U P).symm (basisComparison0 M B B' U P x))) =
    basisComparison1 M B B' U P
      (coordinate1 M B U P (RelativeCover.d0 M U P ((coordinate0 M B U P).symm x))) := by
  rw [restore_basis0]
  change _ = coordinate1 M B' U P ((coordinate1 M B U P).symm (coordinate1 M B U P _))
  rw [LinearEquiv.symm_apply_apply]

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.triples)] in
/-- The original d1 is conjugated by the full edge and face basis changes. -/
theorem basis_comparison_d1 (x : Index1 M B U P → k) :
    coordinate2 M B' U P (RelativeCover.d1 M U P
      ((coordinate1 M B' U P).symm (basisComparison1 M B B' U P x))) =
    basisComparison2 M B B' U P
      (coordinate2 M B U P (RelativeCover.d1 M U P ((coordinate1 M B U P).symm x))) := by
  rw [restore_basis1]
  change _ = coordinate2 M B' U P ((coordinate2 M B U P).symm (coordinate2 M B U P _))
  rw [LinearEquiv.symm_apply_apply]

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)] in
/-- The original d2 is conjugated by the full face and triple basis changes. -/
theorem basis_comparison_d2 (x : Index2 M B U P → k) :
    coordinate3 M B' U P (RelativeCover.d2 M U P
      ((coordinate2 M B' U P).symm (basisComparison2 M B B' U P x))) =
    basisComparison3 M B B' U P
      (coordinate3 M B U P (RelativeCover.d2 M U P ((coordinate2 M B U P).symm x))) := by
  rw [restore_basis2]
  change _ = coordinate3 M B' U P ((coordinate3 M B U P).symm (coordinate3 M B U P _))
  rw [LinearEquiv.symm_apply_apply]

variable (internalEdges : Set (EdgeName (K := K))) [DecidablePred (· ∈ internalEdges)]
/-- Full basis comparison preserves the original private/public edge partition. -/
def splitBasisComparison := (edgeSplit M B U P internalEdges).symm.trans
  (edgeSplit M B' U P internalEdges)

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ P.triples)] in
/-- The entire original edge family is reconstructed after changing private/public bases. -/
theorem restore_split_basis (xz : (XIndex M B U P internalEdges → k) ×
    (ZIndex M B U P internalEdges → k)) :
    (edgeSplit M B' U P internalEdges).symm (splitBasisComparison M B B' U P internalEdges xz) =
      (edgeSplit M B U P internalEdges).symm xz :=
  (edgeSplit M B' U P internalEdges).symm_apply_apply _

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ P.triples)] in
/-- New public coordinates use the same original edge and depend only on its old complete public value. -/
theorem split_basis_public (xz : (XIndex M B U P internalEdges → k) ×
    (ZIndex M B U P internalEdges → k)) (j : ZIndex M B' U P internalEdges) :
    (splitBasisComparison M B B' U P internalEdges xz).2 j =
      B'.coordinate j.1.1.1.2.1
        ((B.coordinate j.1.1.1.2.1).symm (fun l => xz.2 ⟨⟨j.1.1,l⟩,j.2⟩)) j.1.2 := by
  change B'.coordinate j.1.1.1.2.1
    (((edgeSplit M B U P internalEdges).symm xz).1 ⟨j.1.1.1,j.1.1.2.1⟩) j.1.2 = _
  rw [public_edge_value M B U P internalEdges xz.1 xz.2
    ⟨j.1.1.1,j.1.1.2.1⟩ j.1.1.2.2 j.2]

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ P.triples)] in
/-- New private coordinates use the same original edge and every old internal kernel basis component. -/
theorem split_basis_private (xz : (XIndex M B U P internalEdges → k) ×
    (ZIndex M B U P internalEdges → k)) (j : XIndex M B' U P internalEdges) :
    (splitBasisComparison M B B' U P internalEdges xz).1 j =
      B'.coordinate j.1.1.1.2.1
        ((B.coordinate j.1.1.1.2.1).symm (fun l => xz.1 ⟨⟨j.1.1,l⟩,j.2⟩)) j.1.2 := by
  change B'.coordinate j.1.1.1.2.1
    (((edgeSplit M B U P internalEdges).symm xz).1 ⟨j.1.1.1,j.1.1.2.1⟩) j.1.2 = _
  rw [private_edge_value M B U P internalEdges xz.1 xz.2
    ⟨j.1.1.1,j.1.1.2.1⟩ j.1.1.2.2 j.2]

end FiniteNative
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
