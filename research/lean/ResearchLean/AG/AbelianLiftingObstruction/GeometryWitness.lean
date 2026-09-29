import ResearchLean.AG.AbelianLiftingObstruction.CrossStage
import ResearchLean.AG.AbelianLiftingObstruction.GeometryKernelTransport
import ResearchLean.AG.AbelianLiftingObstruction.SquarePresentation

/-! # The same concrete geometry package on the three-cell square

Every hypothesis is proved from the original full kernel and identity edges.
The nonidentity coefficient swap is the authored comparison, and its same
actual-kernel class obstructs coherent lifts.
-/

namespace AAT.AG.AbelianLiftingObstruction.GeometryWitness

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence TransportCoherence.Arbitrary
open GeometryInput GeometryKernelTransport

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
The shared square receives the same geometry package and identity arrows. -/
noncomputable abbrev liftData : TwoLayerLiftData squarePresentation FiniteModel.carrier where
  geometry _ := package
  edgeLift _ := 𝟙 package
  edgeGeometryStrong _ := identityStrong _ _
  edgeCoreStrong _ := identityStrong _ _

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
Every path is evaluated using the original identity edges. -/
theorem path_identity {i j : squarePresentation.Vertex} (w : squarePresentation.Path i j) :
    liftData.pathLift w = 𝟙 package := by
  induction w with
  | nil _ => rfl
  | cons _ _ ih =>
    change (𝟙 package) ≫ liftData.pathLift _ = 𝟙 package
    rw [ih, Category.id_comp]

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
The sole authored comparison is the original nonidentity inner swap. -/
noncomputable abbrev data : TwoLayerTransportData squarePresentation FiniteModel.carrier where
  lift := liftData
  twoCellBase f := by rw [path_identity, path_identity]
  comparator _ := innerFiberInclusion package innerSwap

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
Both the fixed core selection and its chosen edge lifts are identities. -/
noncomputable abbrev sectionFamily : EdgeSectionFamily data := identityEdgeSection data

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
Reselection by this section preserves each original identity arrow. -/
theorem selected_path_identity {i j : squarePresentation.Vertex}
    (w : squarePresentation.Path i j) :
    upperReselectedPathLift liftData sectionFamily.lift w = 𝟙 package := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change (𝟙 package ≫ 𝟙 package) ≫
      upperReselectedPathLift liftData sectionFamily.lift w = 𝟙 package
    rw [ih, Category.id_comp, Category.id_comp]


/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
A2 holds on the same original core arrows because the comparator is in the kernel. -/
theorem alignment : CoreAlignmentAt data sectionFamily := by
  intro f
  have h := kernelInclusion_map (geometryProjection FiniteModel.carrier)
    (packageProjection FiniteModel.carrier) package authoredKernelElement
  change (TransportCoherence.reselectedPathLift data.coreData.lift sectionFamily.core
      (squarePresentation.twoLeft f)).comp (data.comparator f).1.hom.base = _
  rw [← CrossStage.selected_path_core data sectionFamily,
    ← CrossStage.selected_path_core data sectionFamily]
  rw [selected_path_identity, selected_path_identity]
  simpa using h

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
Conditions 1–3 use the same actual kernel on every vertex and selected edge. -/
theorem kernel_comm (_v : squarePresentation.Vertex) (a b : ActualKernel) : a * b = b * a :=
  mul_comm a b

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
The generated map along the same selected identity edge is identity. -/
theorem transport_identity {i j : squarePresentation.Vertex}
    (e : squarePresentation.Edge i j) :
    kernelTransportHom (geometryProjection FiniteModel.carrier) (packageProjection FiniteModel.carrier)
      (upperReselectedEdgeLift liftData sectionFamily.lift e)
      (CrossStage.selectedStrong liftData sectionFamily.lift e)
      (CrossStage.selectedCoreStrong liftData sectionFamily.lift e) =
        MonoidHom.id ActualKernel := by
  simpa only [upperReselectedEdgeLift, liftData, sectionFamily,
    identityEdgeSection, CompositeFiberAut.hom, Category.comp_id] using
      kernelTransport_identity (geometryProjection FiniteModel.carrier)
        (packageProjection FiniteModel.carrier) package

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
A2's generated kernel transport is bijective without an extra input premise. -/
theorem transport_bijective {i j : squarePresentation.Vertex}
    (e : squarePresentation.Edge i j) :
    Function.Bijective (kernelTransportHom (geometryProjection FiniteModel.carrier)
      (packageProjection FiniteModel.carrier) (upperReselectedEdgeLift liftData sectionFamily.lift e)
      (CrossStage.selectedStrong liftData sectionFamily.lift e)
      (CrossStage.selectedCoreStrong liftData sectionFamily.lift e)) := by
  rw [transport_identity]
  exact Function.bijective_id

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
The same nonidentity authored comparator centralizes the full kernel. -/
theorem comparator_central (f : squarePresentation.TwoCell) (a : ActualKernel) :
    compositeFiberEquiv package (data.comparator f) * kernelInclusion _ _ package a =
      kernelInclusion _ _ package a * compositeFiberEquiv package (data.comparator f) :=
  authored_centralizes a

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
Apply the Chapter 4 adapter to this fully constructed original input. -/
noncomputable abbrev input := CrossStage.presentation data sectionFamily alignment
  kernel_comm transport_bijective comparator_central

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
The actual kernel's coefficient transport on the square is identity. -/
theorem edge_transport (a : input.toTower.localCoefficients.A ()) :
    input.toTower.localCoefficients.edge (() : squarePresentation.Edge () ()) a = a := by
  change Additive.ofMul
    (kernelTransportHom _ _ (upperReselectedEdgeLift liftData sectionFamily.lift ())
      (CrossStage.selectedStrong _ _ _) (CrossStage.selectedCoreStrong _ _ _)
      (Additive.toMul a)) = a
  rw [transport_identity]
  rfl

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
The sole generated comparison equals identity by strong uniqueness. -/
theorem canonical_one (f : squarePresentation.TwoCell) :
    sectionCellComparator data sectionFamily f = 1 := by
  apply (compositeFiberEquiv package).injective
  have hc := CrossStage.canonicalFace_eq data sectionFamily alignment
    kernel_comm transport_bijective comparator_central f
  change input.toTower.canonicalFace f =
    compositeFiberEquiv package (sectionCellComparator data sectionFamily f) at hc
  rw [← hc]
  apply FiberAut.ext_of_strong_fac _
    (input.toTower.upper.pathLift_isStronglyCocartesian (squarePresentation.twoLeft f))
  change _ ≫ FiberAut.hom (Arbitrary.canonicalFiberComparator _ _ _ _ _ _) = _
  rw [Arbitrary.canonicalFiberComparator_fac]
  change input.toTower.upper.pathLift (squarePresentation.twoRight f) =
    input.toTower.upper.pathLift (squarePresentation.twoLeft f) ≫ 𝟙 package
  have hh := Category.comp_id (input.toTower.upper.pathLift (squarePresentation.twoLeft f))
  change input.toTower.upper.pathLift (squarePresentation.twoLeft f) ≫ 𝟙 package =
    input.toTower.upper.pathLift (squarePresentation.twoLeft f) at hh
  rw [hh]
  have hp {i j : squarePresentation.Vertex} (w : squarePresentation.Path i j) :
      input.toTower.upper.pathLift w = 𝟙 package := by
    change (selectedUpper squarePresentation _ _ (CrossStage.originalLift liftData)
      (fun {i j} e => compositeFiberEquiv package (sectionFamily.lift i j e))).pathLift w = _
    rw [CrossStage.selected_path]
    exact selected_path_identity w
  rw [hp, hp]

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
B1 is the same nonidentity Chapter 4 section obstruction. -/
theorem section_defect (f : squarePresentation.TwoCell) :
    sectionInnerObstruction data sectionFamily alignment f = innerSwap := by
  apply innerFiberInclusion_injective package
  have hh := sectionInnerObstruction_inclusion data sectionFamily alignment f
  change innerFiberInclusion package (sectionInnerObstruction data sectionFamily alignment f) = _ at hh
  rw [hh]
  change data.comparator f * (sectionCellComparator data sectionFamily f)⁻¹ = _
  rw [canonical_one, inv_one, mul_one]

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
The actual additive defect is the authored swap, not an assumed cochain. -/
theorem defect_value (f : squarePresentation.TwoCell) :
    input.toTower.defect f = Additive.ofMul authoredKernelElement := by
  change Additive.ofMul (input.toTower.faceDefect f) = _
  rw [CrossStage.faceDefect_eq, section_defect]
  rfl

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
Transporting any authored automorphism along any path leaves it unchanged. -/
theorem whisker_identity {i j : squarePresentation.Vertex}
    (a : CompositeFiberAut package) (w : squarePresentation.Path i j) :
    upperWhiskerCompositeFiberAut liftData sectionFamily.lift a w = a := by
  apply (compositeFiberEquiv package).injective
  apply FiberAut.ext_of_strong_fac (𝟙 package) upper_identity_strong
  have hf := upperWhiskerCompositeFiberAut_fac liftData sectionFamily.lift a w
  rw [selected_path_identity] at hf
  simpa only [upperFiberAutThenPath, selected_path_identity, Category.id_comp,
    Category.comp_id] using hf

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
A4 compares the original two distinct deletions of e² inside e³. -/
theorem authored_syzygy : UpperSyzygyCompatible data sectionFamily.lift := by
  intro cell
  cases cell
  change 1 * upperWhiskerCompositeFiberAut liftData sectionFamily.lift
      (innerFiberInclusion package innerSwap) squareEdge =
    1 * upperWhiskerCompositeFiberAut liftData sectionFamily.lift
      (innerFiberInclusion package innerSwap) (.nil ())
  rw [whisker_identity, whisker_identity]

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
The same actual input supplies the general 3-cell condition. -/
theorem syzygy : ∀ cell : squarePresentation.ThreeCell,
    AuthoredSyzygy input.toTower.toTransportData 1
      (squarePresentation.threeLeft cell) (squarePresentation.threeRight cell) := CrossStage.syzygy data sectionFamily alignment
  kernel_comm transport_bijective comparator_central authored_syzygy

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
Each kernel element has order at most two, including its full geometry arrow. -/
theorem coefficient_double (a : input.toTower.localCoefficients.A ()) : a + a = 0 := by
  apply Additive.toMul.injective
  apply (innerKernelEquiv package).symm.injective
  change (innerKernelEquiv package).symm
    ((Additive.toMul a : ActualKernel) * (Additive.toMul a : ActualKernel)) = _
  rw [map_mul, GeometryKernel.inner_square]
  rfl

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
d0 is zero on the same vertex coefficients. -/
theorem d0_zero (b : C0 input.toTower.localCoefficients) :
    d0 input.toTower.localCoefficients b = 0 := by
  funext ⟨i, j, e⟩
  cases i; cases j; cases e
  rw [square_d0, edge_transport, sub_self]
  rfl

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
d1 counts both occurrences, whose sum is zero on this full actual kernel. -/
theorem d1_zero (h : C1 input.toTower.localCoefficients) :
    d1 input.toTower.localCoefficients h = 0 := by
  funext f
  cases f
  rw [square_d1, edge_transport, coefficient_double]
  rfl

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
d2 is zero because the two suffix transports are identity. -/
theorem d2_zero (c : C2 input.toTower.localCoefficients) :
    d2 input.toTower.localCoefficients c = 0 := by
  funext cell
  cases cell
  rw [square_d2]
  change input.toTower.localCoefficients.edge (() : squarePresentation.Edge () ())
    (c ()) - c () = 0
  exact sub_eq_zero.mpr (edge_transport (c ()))

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
The original authored swap gives a nonzero cochain. -/
theorem defect_nonzero : input.toTower.defect ≠ 0 := by
  intro h
  have hx := congrFun h ()
  rw [defect_value] at hx
  apply authoredKernelElement_ne_one
  exact congrArg Additive.toMul hx

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
The 3-cell cocycle condition is evaluated in this same complex. -/
theorem defect_cocycle : d2 input.toTower.localCoefficients input.toTower.defect = 0 :=
  d2_zero _

/-- G-129 completion criterion 4 main consequence, using the computed same complex:
The computed swap represents a nonzero H2 obstruction. -/
theorem obstruction_nonzero : input.toTower.obstructionClass syzygy ≠ 0 := by
  intro h
  rcases (input.obstructionClass_eq_zero_iff_correction syzygy).mp h with ⟨x, hx⟩
  rw [d1_zero] at hx
  exact defect_nonzero (neg_eq_zero.mp hx.symm)

/-- G-129 completion criterion 4 API, derived from the explicit GeometryInput package:
B3 proves absence of the same original coherent geometry lifts. -/
theorem no_solution : ¬ Nonempty (Solution input) := by
  intro h
  exact obstruction_nonzero ((input.obstructionClass_eq_zero_iff_solution syzygy).mpr h)

/-- G-129 completion criterion 4 main consequence, using the computed obstruction and D:
D returns the same obstruction decision to Chapter 4's original predicate. -/
theorem not_coherentizable : ¬ SectionRelativeCoherentizable data sectionFamily := by
  intro h
  exact obstruction_nonzero ((CrossStage.obstructionClass_zero_iff data sectionFamily alignment
    kernel_comm transport_bijective comparator_central authored_syzygy).mpr h)

end AAT.AG.AbelianLiftingObstruction.GeometryWitness

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction.GeometryWitness
