import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteNativeMatrices
import ResearchLean.AG.RelativeRepairComposition.NativeEquationBridge

/-!
# Complete local interfaces of independent original repairs

## Implementation notes

The original affine equation remains independently defined. The matrix and
section generators are applied to the same full original differential. Both
coordinate directions retain every actual edge choice and full gauge label.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction FiniteCoefficients
universe uk uG uA
namespace FiniteNative
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (B : FiniteFamily.Bases (k := k) M.A) (U P : ClosedRegion K)
variable [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [DecidablePred (· ∈ U.vertices)] [DecidablePred (· ∈ U.edges)]
variable (internalEdges : Set (EdgeName (K := K))) [DecidablePred (· ∈ internalEdges)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable (δ : RelativeCover.C2 M ClosedRegion.all P)

/-- The affine right-hand side is the same actual defect in full original face coordinates. -/
def rhs : Index2 M B U P → k := coordinate2 M B U P (-CoverEquation.defect M P δ U)

/-- Coordinate solutions use the generated original label and differential components. -/
abbrev CoordinateEquation := LinearInterface.EquationObjects
  (D M B U P internalEdges hlinear) (F M B U P internalEdges hlinear)
  (a M B U P internalEdges hlinear) (c M B U P internalEdges hlinear)
  (D_a_add_F_c M B U P internalEdges hlinear) (rhs M B U P δ)

/-- The original independently defined local affine equation has full mutually inverse coordinates. -/
def solutionCoordinateEquiv : CoverEquation.Solution M P δ U ≃
    CoordinateEquation M B U P internalEdges hlinear δ where
  toFun h := ⟨edgeSplit M B U P internalEdges h.1,by
    change D M B U P internalEdges hlinear _ + F M B U P internalEdges hlinear _ = _
    rw [D_add_F,faceMap_apply]
    simp only [LinearMap.fst_apply,LinearMap.snd_apply,Prod.mk.eta]
    rw [LinearEquiv.symm_apply_apply,differential1_eq,h.2]
    rfl⟩
  invFun h := ⟨(edgeSplit M B U P internalEdges).symm h.1,by
    apply (coordinate2 M B U P).injective
    rw [← differential1_eq M hlinear U P]
    rw [← faceMap_apply,← D_add_F]
    exact h.2⟩
  left_inv h := Subtype.ext ((edgeSplit M B U P internalEdges).symm_apply_apply h.1)
  right_inv h := Subtype.ext ((edgeSplit M B U P internalEdges).apply_symm_apply h.1)

omit [DecidablePred (· ∈ P.vertices)] in
/-- The complete original relative zero-cochain acts by the same label in both coordinates. -/
theorem solution_coordinate_equivariant (b : Multiplicative (RelativeCover.C0 M U P))
    (h : CoverEquation.Solution M P δ U) :
    solutionCoordinateEquiv M B U P internalEdges hlinear δ (b • h) =
      b • solutionCoordinateEquiv M B U P internalEdges hlinear δ h := by
  apply Subtype.ext
  change edgeSplit M B U P internalEdges (h.1 + RelativeCover.d0 M U P b.toAdd) =
    edgeSplit M B U P internalEdges h.1 +
      (a M B U P internalEdges hlinear b.toAdd,c M B U P internalEdges hlinear b.toAdd)
  rw [map_add,← differential0_eq M hlinear U P,a_c_eq_edgeSplit_differential0]

/-- Full local equation coordinates preserve every original gauge arrow. -/
def coordinateEquationEquivalence : CoverEquation.Groupoid M P δ U ≌
    Equation.Groupoid (LinearInterface.coboundary (a M B U P internalEdges hlinear)
      (c M B U P internalEdges hlinear)).toAddMonoidHom
      (LinearInterface.differential (D M B U P internalEdges hlinear)
        (F M B U P internalEdges hlinear)).toAddMonoidHom
      (LinearInterface.differential_coboundary (D M B U P internalEdges hlinear)
        (F M B U P internalEdges hlinear) (a M B U P internalEdges hlinear)
        (c M B U P internalEdges hlinear) (D_a_add_F_c M B U P internalEdges hlinear))
      (rhs M B U P δ) :=
  changedLabelEquivalence (MulEquiv.refl (Multiplicative (RelativeCover.C0 M U P)))
    (solutionCoordinateEquiv M B U P internalEdges hlinear δ)
    (solution_coordinate_equivariant M B U P internalEdges hlinear δ)

/-- Public restriction reads every original overlap edge from the public coordinates alone. -/
def publicRestriction (W : ClosedRegion K) (inc : ClosedRegion.Inclusion W U)
    (z : ZIndex M B U P internalEdges → k) :
    ∀ e : W.edges, M.A e.1.2.1 :=
  fun e => ((edgeSplit M B U P internalEdges).symm (0,z)).1 ⟨e.1,inc.edges e.2⟩

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ U.vertices)] [DecidablePred (· ∈ U.edges)] in
/-- Original restriction is independent of every private value whenever the overlap is public. -/
theorem restriction_public_only (W : ClosedRegion K) (inc : ClosedRegion.Inclusion W U)
    (hw : ∀ e ∈ W.edges, e ∉ internalEdges)
    (x : XIndex M B U P internalEdges → k) (z : ZIndex M B U P internalEdges → k) :
    (fun e : W.edges => ((edgeSplit M B U P internalEdges).symm (x,z)).1 ⟨e.1,inc.edges e.2⟩) =
      publicRestriction M B U P internalEdges W inc z := by
  funext e
  by_cases hp : e.1 ∈ P.edges
  · exact (((edgeSplit M B U P internalEdges).symm (x,z)).2 _ hp).trans
      (((edgeSplit M B U P internalEdges).symm (0,z)).2 _ hp).symm
  · exact public_edge_private_independent M B U P internalEdges x 0 z
      ⟨e.1,inc.edges e.2⟩ hp (hw e.1 e.2)

variable [Fintype k] [DecidableEq k]
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable [DecidablePred (· ∈ U.faces)]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)

/-- All interface objects use the section generated once from the original private matrix. -/
abbrev GeneratedObjects := LinearInterface.Objects
  (D M B U P internalEdges hlinear) (F M B U P internalEdges hlinear)
  (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces)
  (generatedSection_regular M B U P internalEdges hlinear enumK enumEdges enumFaces)
  (a M B U P internalEdges hlinear) (c M B U P internalEdges hlinear)
  (D_a_add_F_c M B U P internalEdges hlinear) (rhs M B U P δ)

/-- Generated coordinates and the independent original equation are inverse on all values. -/
def generatedSolutionEquiv : CoverEquation.Solution M P δ U ≃
    GeneratedObjects M B U P internalEdges hlinear δ enumK enumEdges enumFaces :=
  (solutionCoordinateEquiv M B U P internalEdges hlinear δ).trans
    (LinearInterface.equationCoordinateEquiv
      (D M B U P internalEdges hlinear) (F M B U P internalEdges hlinear)
      (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces)
      (generatedSection_regular M B U P internalEdges hlinear enumK enumEdges enumFaces)
      (a M B U P internalEdges hlinear) (c M B U P internalEdges hlinear)
      (D_a_add_F_c M B U P internalEdges hlinear) (rhs M B U P δ))

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every full original gauge label acts on the same generated interface. -/
theorem generated_solution_equivariant (b : Multiplicative (RelativeCover.C0 M U P))
    (h : CoverEquation.Solution M P δ U) :
    generatedSolutionEquiv M B U P internalEdges hlinear δ enumK enumEdges enumFaces (b • h) =
      b • generatedSolutionEquiv M B U P internalEdges hlinear δ enumK enumEdges enumFaces h := by
  exact (congrArg (LinearInterface.equationCoordinateEquiv
    (D M B U P internalEdges hlinear) (F M B U P internalEdges hlinear)
    (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces)
    (generatedSection_regular M B U P internalEdges hlinear enumK enumEdges enumFaces)
    (a M B U P internalEdges hlinear) (c M B U P internalEdges hlinear) (D_a_add_F_c M B U P internalEdges hlinear) (rhs M B U P δ))
    (solution_coordinate_equivariant M B U P internalEdges hlinear δ b h)).trans
      (LinearInterface.equation_coordinate_equivariant
        (D M B U P internalEdges hlinear) (F M B U P internalEdges hlinear)
        (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces)
        (generatedSection_regular M B U P internalEdges hlinear enumK enumEdges enumFaces)
        (a M B U P internalEdges hlinear) (c M B U P internalEdges hlinear) (D_a_add_F_c M B U P internalEdges hlinear) (rhs M B U P δ) b
        (solutionCoordinateEquiv M B U P internalEdges hlinear δ h))

/-- The generated native interface keeps every original full label as an arrow. -/
abbrev GeneratedGroupoid := ActionCategory (Multiplicative (RelativeCover.C0 M U P))
  (GeneratedObjects M B U P internalEdges hlinear δ enumK enumEdges enumFaces)

/-- Full mutually inverse native groupoid coordinates for the generated local interface. -/
def generatedEquationEquivalence : CoverEquation.Groupoid M P δ U ≌
    GeneratedGroupoid M B U P internalEdges hlinear δ enumK enumEdges enumFaces :=
  changedLabelEquivalence (MulEquiv.refl (Multiplicative (RelativeCover.C0 M U P)))
    (generatedSolutionEquiv M B U P internalEdges hlinear δ enumK enumEdges enumFaces)
    (generated_solution_equivariant M B U P internalEdges hlinear δ enumK enumEdges enumFaces)

omit [DecidablePred (· ∈ P.vertices)] in
/-- Forward interface arrows retain precisely their original full label. -/
theorem generated_functor_label {h h' : CoverEquation.Groupoid M P δ U} (f : h ⟶ h') :
    ((generatedEquationEquivalence M B U P internalEdges hlinear δ enumK enumEdges enumFaces).functor.map f).1 = f.1 := rfl

omit [DecidablePred (· ∈ P.vertices)] in
/-- Inverse interface arrows retain precisely their original full label. -/
theorem generated_inverse_label
    {y y' : GeneratedGroupoid M B U P internalEdges hlinear δ enumK enumEdges enumFaces} (f : y ⟶ y') :
    ((generatedEquationEquivalence M B U P internalEdges hlinear δ enumK enumEdges enumFaces).inverse.map f).1 = f.1 := rfl

omit [DecidablePred (· ∈ P.vertices)] in
/-- Both object compositions restore the independent original solution exactly. -/
theorem generated_left_obj (h : CoverEquation.Groupoid M P δ U) :
    (generatedEquationEquivalence M B U P internalEdges hlinear δ enumK enumEdges enumFaces).inverse.obj
      ((generatedEquationEquivalence M B U P internalEdges hlinear δ enumK enumEdges enumFaces).functor.obj h) = h :=
  changed_label_left_obj _ _
    (generated_solution_equivariant M B U P internalEdges hlinear δ enumK enumEdges enumFaces) h

omit [DecidablePred (· ∈ P.vertices)] in
/-- Both object compositions restore all generated coordinates exactly. -/
theorem generated_right_obj
    (y : GeneratedGroupoid M B U P internalEdges hlinear δ enumK enumEdges enumFaces) :
    (generatedEquationEquivalence M B U P internalEdges hlinear δ enumK enumEdges enumFaces).functor.obj
      ((generatedEquationEquivalence M B U P internalEdges hlinear δ enumK enumEdges enumFaces).inverse.obj y) = y :=
  changed_label_right_obj _ _
    (generated_solution_equivariant M B U P internalEdges hlinear δ enumK enumEdges enumFaces) y

end FiniteNative
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
