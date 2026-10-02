import ResearchLean.AG.RelativeRepairComposition.FiniteNativeMatrices

/-!
# Independent finite interfaces for every full local right-hand side

## Implementation notes

The matrix, elimination and section use only the full original differential.
An arbitrary relative face value is then supplied as the right-hand side. This
keeps the same generator available for both sides of an actual subdivision,
even when their independently generated sections differ. Actual signed defects
are particular inputs to this construction, not supplied comparison laws.
-/
namespace AAT.AG.RelativeRepairComposition.FiniteNative
open CategoryTheory TransportCoherence AbelianLiftingObstruction FiniteCoefficients
universe uk uG uA
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (U P : ClosedRegion K)
variable [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)]
variable [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ U.vertices)]
variable [DecidablePred (· ∈ U.edges)]
variable (internalEdges : Set (EdgeName (K := K))) [DecidablePred (· ∈ internalEdges)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable (rhs : RelativeCover.C2 M U P)

/-- The independent relative equation keeps every original local correction and label. -/
abbrev RelativeEquation := Equation.Solution (RelativeCover.d0 M U P)
  (RelativeCover.d1 M U P) (RelativeCover.d1_d0 M U P) rhs

/-- The split matrix equation is independently computed from the same full differential. -/
abbrev ArbitraryMatrixEquation := LinearInterface.EquationObjects
  (D M bases U P internalEdges hlinear) (F M bases U P internalEdges hlinear)
  (a M bases U P internalEdges hlinear) (c M bases U P internalEdges hlinear)
  (D_a_add_F_c M bases U P internalEdges hlinear) (coordinate2 M bases U P rhs)

/-- Full relative solutions and full private/public matrix solutions have both inverse maps. -/
def relativeEquationCoordinates : RelativeEquation M U P rhs ≃
    ArbitraryMatrixEquation M bases U P internalEdges hlinear rhs where
  toFun h := ⟨edgeSplit M bases U P internalEdges h.1,by
    change D M bases U P internalEdges hlinear _ + F M bases U P internalEdges hlinear _ = _
    rw [D_add_F,faceMap_apply]
    simp only [LinearMap.fst_apply,LinearMap.snd_apply,Prod.mk.eta]
    rw [LinearEquiv.symm_apply_apply,differential1_eq,h.2]⟩
  invFun h := ⟨(edgeSplit M bases U P internalEdges).symm h.1,by
    apply (coordinate2 M bases U P).injective
    rw [← differential1_eq M hlinear U P]
    rw [← faceMap_apply,← D_add_F]
    exact h.2⟩
  left_inv h := Subtype.ext ((edgeSplit M bases U P internalEdges).symm_apply_apply h.1)
  right_inv h := Subtype.ext ((edgeSplit M bases U P internalEdges).apply_symm_apply h.1)

omit [DecidablePred (· ∈ P.vertices)] in
/-- The whole relative solution reads both full original edge coordinate components. -/
theorem relativeEquationCoordinates_value (h : RelativeEquation M U P rhs) :
    (relativeEquationCoordinates M bases U P internalEdges hlinear rhs h).1 =
      edgeSplit M bases U P internalEdges h.1 := rfl

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every original vertex label acts by its two full computed coboundary components. -/
theorem relative_equation_coordinates_equivariant
    (b : Multiplicative (RelativeCover.C0 M U P)) (h : RelativeEquation M U P rhs) :
    relativeEquationCoordinates M bases U P internalEdges hlinear rhs (b • h) =
      b • relativeEquationCoordinates M bases U P internalEdges hlinear rhs h := by
  apply Subtype.ext
  change edgeSplit M bases U P internalEdges (h.1 + RelativeCover.d0 M U P b.toAdd) =
    edgeSplit M bases U P internalEdges h.1 +
      (a M bases U P internalEdges hlinear b.toAdd,c M bases U P internalEdges hlinear b.toAdd)
  rw [map_add,← differential0_eq M hlinear U P,a_c_eq_edgeSplit_differential0]

variable [Fintype k] [DecidableEq k]
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable [DecidablePred (· ∈ U.faces)]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)

/-- The generated interface retains the whole public relation and whole private kernel. -/
abbrev GeneratedRelativeObjects := LinearInterface.Objects
  (D M bases U P internalEdges hlinear) (F M bases U P internalEdges hlinear)
  (generatedSection M bases U P internalEdges hlinear enumK enumEdges enumFaces)
  (generatedSection_regular M bases U P internalEdges hlinear enumK enumEdges enumFaces)
  (a M bases U P internalEdges hlinear) (c M bases U P internalEdges hlinear)
  (D_a_add_F_c M bases U P internalEdges hlinear) (coordinate2 M bases U P rhs)

/-- Independent generation gives complete mutually inverse coordinates for every relative rhs. -/
def generatedRelativeEquiv : RelativeEquation M U P rhs ≃
    GeneratedRelativeObjects M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces :=
  (relativeEquationCoordinates M bases U P internalEdges hlinear rhs).trans
    (LinearInterface.equationCoordinateEquiv
      (D M bases U P internalEdges hlinear) (F M bases U P internalEdges hlinear)
      (generatedSection M bases U P internalEdges hlinear enumK enumEdges enumFaces)
      (generatedSection_regular M bases U P internalEdges hlinear enumK enumEdges enumFaces)
      (a M bases U P internalEdges hlinear) (c M bases U P internalEdges hlinear)
      (D_a_add_F_c M bases U P internalEdges hlinear) (coordinate2 M bases U P rhs))

omit [DecidablePred (· ∈ P.vertices)] in
/-- Extraction preserves every complete original public basis value. -/
theorem generatedRelativeEquiv_public (h : RelativeEquation M U P rhs) :
    (generatedRelativeEquiv M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces h).1.1 =
      (edgeSplit M bases U P internalEdges h.1).2 := rfl

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every generated public value survives full restoration to the original local equation. -/
theorem generatedRelativeEquiv_inverse_public
    (y : GeneratedRelativeObjects M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces) :
    (edgeSplit M bases U P internalEdges
      ((generatedRelativeEquiv M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces).symm y).1).2 =
      y.1.1 := by
  rw [← generatedRelativeEquiv_public]
  exact congrArg (fun y => y.1.1)
    ((generatedRelativeEquiv M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces).apply_symm_apply y)

omit [DecidablePred (· ∈ P.vertices)] in
/-- The independently generated interface action retains every full original label. -/
theorem generated_relative_equivariant (b : Multiplicative (RelativeCover.C0 M U P))
    (h : RelativeEquation M U P rhs) :
    generatedRelativeEquiv M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces (b • h) =
      b • generatedRelativeEquiv M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces h :=
  (congrArg (LinearInterface.equationCoordinateEquiv
    (D M bases U P internalEdges hlinear) (F M bases U P internalEdges hlinear)
    (generatedSection M bases U P internalEdges hlinear enumK enumEdges enumFaces)
    (generatedSection_regular M bases U P internalEdges hlinear enumK enumEdges enumFaces)
    (a M bases U P internalEdges hlinear) (c M bases U P internalEdges hlinear)
    (D_a_add_F_c M bases U P internalEdges hlinear) (coordinate2 M bases U P rhs))
    (relative_equation_coordinates_equivariant M bases U P internalEdges hlinear rhs b h)).trans
      (LinearInterface.equation_coordinate_equivariant _ _ _ _ _ _ _ _ b _)

/-- Independently generated public relations use the same original D and its computed section. -/
def generatedRelation : Set (ZIndex M bases U P internalEdges → k) :=
  LinearInterface.Relation (D M bases U P internalEdges hlinear)
    (F M bases U P internalEdges hlinear)
    (generatedSection M bases U P internalEdges hlinear enumK enumEdges enumFaces)
    (coordinate2 M bases U P rhs)

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every generated public value is allowed exactly when a full original local solution reads it. -/
theorem generated_relation_iff_relative (z : ZIndex M bases U P internalEdges → k) :
    z ∈ generatedRelation M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces ↔
      ∃ h : RelativeEquation M U P rhs, (edgeSplit M bases U P internalEdges h.1).2 = z := by
  constructor
  · intro hz
    let y : GeneratedRelativeObjects M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces :=
      (⟨z,hz⟩,0)
    refine ⟨(generatedRelativeEquiv M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces).symm y,?_⟩
    exact generatedRelativeEquiv_inverse_public M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces y
  · rintro ⟨h,hh⟩
    have hy := (generatedRelativeEquiv M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces h).1.2
    rw [generatedRelativeEquiv_public,hh] at hy
    exact hy

/-- The generated native groupoid uses the independent whole relative labels. -/
abbrev GeneratedRelativeGroupoid := ActionCategory (Multiplicative (RelativeCover.C0 M U P))
  (GeneratedRelativeObjects M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces)

/-- Full native coordinates preserve all objects, all original label arrows and both inverses. -/
def generatedRelativeEquationEquivalence :
    Equation.Groupoid (RelativeCover.d0 M U P) (RelativeCover.d1 M U P)
      (RelativeCover.d1_d0 M U P) rhs ≌
    GeneratedRelativeGroupoid M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces :=
  changedLabelEquivalence (MulEquiv.refl (Multiplicative (RelativeCover.C0 M U P)))
    (generatedRelativeEquiv M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces)
    (generated_relative_equivariant M bases U P internalEdges hlinear rhs enumK enumEdges enumFaces)

end AAT.AG.RelativeRepairComposition.FiniteNative
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.FiniteNative
