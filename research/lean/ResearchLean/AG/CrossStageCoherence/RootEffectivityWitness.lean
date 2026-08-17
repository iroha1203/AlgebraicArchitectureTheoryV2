import ResearchLean.AG.CrossStageCoherence.IdentityEdgeLiftSpecialization

/-!
# G-109 root-effectivity obstruction witness

This module realizes witness (w4) from the fixed G-109 target.  Its active
two-cell compares the empty path with the repeated edge `a · a`.  A formal
comparison section and compatible core/edge/strict local datum both exist,
but any edge realization would make the active path coordinate a square.
The authored comparator has no square root, so effectivity and joint
vanishing fail outside the edge-level presentation class.

## Implementation notes

The fixture uses the reviewed selected-triple geometry after diagonal base
change to `Int × Int`.  Two liftable transpositions produce a three-cycle
`root`; its square is nonidentity in the core, which keeps the active cell out
of the strict sector while retaining an explicit edge section.  An independent
coefficient-factor swap supplies the square-root obstruction: every ring
automorphism of `Int × Int` has square fixing `(1, 0)`, whereas the authored
comparator sends `(1, 0)` to `(0, 1)`.

The older repeated-edge negative fixture was rejected because its
`CompatiblePairs` type is empty.  A comparator lying wholly in the inner
fiber was also rejected because it would make the active cell strict and move
the same impossible square root into the strict trivializer.  The local
heartbeat bound covers concrete dependent-record normalization only; no
aggregate Research build is required.
-/

namespace AAT.AG.CrossStageCoherence

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 6000000

namespace RootEffectivityWitness

/-- Existing pair coefficient ring reused by the fixed w4 concrete package. -/
abbrev Coefficient := GeometryTransport.NegativeGeometryWitness.PairCoefficient

/-- The reviewed factor-swap endomorphism, exposed at the w4 coefficient type. -/
def coefficientSwap : Coefficient →+* Coefficient :=
  GeometryTransport.NegativeGeometryWitness.pairSwap

/-- API connection to the existing involutivity theorem for coefficient swap. -/
theorem coefficient_swap_comp :
    coefficientSwap.comp coefficientSwap = RingHom.id Coefficient := by
  exact GeometryTransport.NegativeGeometryWitness.pairSwap_comp

/-- Diagonal base change used to make the selected-triple raw system swap-stable. -/
def diagonalCoefficient : Int →+* Coefficient :=
  FiniteCrossStageWitness.diagonalCoefficient

/-- Coefficient swap fixes the diagonal map, by the reviewed base-change API. -/
theorem coefficient_swap_comp_diagonal :
    coefficientSwap.comp diagonalCoefficient = diagonalCoefficient := by
  exact FiniteCrossStageWitness.pairSwap_comp_diagonal

/-- Selected-triple raw system after diagonal extension to the pair ring. -/
noncomputable def raw :
    LawAlgebra.RawAmbientRestrictionSystem NoncentralTwistWitness.geometry.toAATSite
      Coefficient :=
  NoncentralTwistWitness.raw.baseChange diagonalCoefficient

/-- The pair-swap coefficient action preserves the concrete raw system. -/
theorem raw_swap : raw.baseChange coefficientSwap = raw := by
  unfold raw
  rw [← LawAlgebra.RawAmbientRestrictionSystem.baseChange_comp]
  rw [coefficient_swap_comp_diagonal]

/-- Geometry package on which the liftable three-cycle and inner swap coexist. -/
noncomputable def package : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := FiniteCrossStageWitness.core
  geometry := NoncentralTwistWitness.geometry
  Coefficient := Coefficient
  coefficientCommRing := inferInstance
  raw := raw

/-- Core-axis permutation leaves this context-independent raw system unchanged. -/
theorem raw_reindex_core_permutation (permutation : Equiv.Perm (Fin 4))
    (system : LawAlgebra.RawAmbientRestrictionSystem package.site
      package.Coefficient) :
    rawReindex (G := package) (H := package)
      (FiniteCrossStageWitness.corePermutationTotal permutation) system = system := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext
  · rfl
  · rfl
  · rfl

/-- Dependent extensionality helper for the concrete geometry automorphisms. -/
theorem geometry_hom_heq_of_base_eq
    {f g : PackageTotalHom package.core package.core}
    (F : GeomReadHom package package f)
    (T : GeomReadHom package package g)
    (baseEquality : f = g)
    (coefficientEquality : F.coefficientHom = T.coefficientHom)
    (supportEquality : HEq F.supportComp T.supportComp)
    (axisEquality : HEq F.axisComp T.axisComp)
    (observableEquality : HEq F.observableComp T.observableComp) :
    HEq F T := by
  cases baseEquality
  exact heq_of_eq (GeomReadHom.ext coefficientEquality supportEquality
    axisEquality observableEquality)

/-- Lift a selected-axis-preserving core permutation to the w4 geometry package. -/
noncomputable def geometryPermutationHom
    (permutation : Equiv.Perm (Fin 4))
    (preservesSelected : ∀ axis, NoncentralTwistWitness.SelectedAxis axis →
      NoncentralTwistWitness.SelectedAxis (permutation axis)) :
    GeomReadHom package package
      (FiniteCrossStageWitness.corePermutationTotal permutation) where
  coverage := {
    requiredSupport := fun _ h => False.elim h
    requiredEquationCoordinate := fun _ h => False.elim h
    selectedViolationWitness := fun _ h => False.elim h
    requiredAxis := preservesSelected
    supportVisibleOn := fun _ _ _ => trivial
    equationCoordinateVisibleOn := fun _ _ _ => trivial
    violationWitnessVisibleOn := fun _ _ _ => trivial
    axisReadableOn := fun _ axis readable => preservesSelected axis readable
    boundaryVisibleOn := fun _ _ _ => trivial }
  overlap := { overlapIso := fun _ _ _ => Iso.refl _ }
  coefficientHom := RingHom.id package.Coefficient
  raw_eq := by
    unfold rawTransport
    rw [LawAlgebra.RawAmbientRestrictionSystem.baseChange_id]
    exact (raw_reindex_core_permutation permutation package.raw).symm
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ h := h
  axisReads _ _ h := h
  observableReads _ _ h := h
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- First adjacent selected-axis transposition as a total geometry morphism. -/
noncomputable def swap01Total : GeometryTotalHom package package where
  base := FiniteCrossStageWitness.corePermutationTotal
    NoncentralTwistWitness.swap01
  geometry := geometryPermutationHom NoncentralTwistWitness.swap01
    NoncentralTwistWitness.swap01_preserves

/-- Second adjacent selected-axis transposition as a total geometry morphism. -/
noncomputable def swap12Total : GeometryTotalHom package package where
  base := FiniteCrossStageWitness.corePermutationTotal
    NoncentralTwistWitness.swap12
  geometry := geometryPermutationHom NoncentralTwistWitness.swap12
    NoncentralTwistWitness.swap12_preserves

/-- The first adjacent total transposition is involutive. -/
theorem swap01_total_square :
    swap01Total.comp swap01Total = GeometryTotalHom.id package := by
  have baseSquare :
      (swap01Total.comp swap01Total).base =
        (GeometryTotalHom.id package).base := by
    change (FiniteCrossStageWitness.corePermutationTotal
      NoncentralTwistWitness.swap01).comp
        (FiniteCrossStageWitness.corePermutationTotal
          NoncentralTwistWitness.swap01) =
      PackageTotalHom.id FiniteCrossStageWitness.core
    rw [FiniteCrossStageWitness.corePermutationTotal_comp,
      NoncentralTwistWitness.swap01_square]
    exact FiniteCrossStageWitness.corePermutationTotal_refl
  apply GeometryTotalHom.ext
  · exact baseSquare
  · apply geometry_hom_heq_of_base_eq _ _ baseSquare
    · exact RingHom.id_comp _
    · rfl
    · rfl
    · rfl

/-- The second adjacent total transposition is involutive. -/
theorem swap12_total_square :
    swap12Total.comp swap12Total = GeometryTotalHom.id package := by
  have baseSquare :
      (swap12Total.comp swap12Total).base =
        (GeometryTotalHom.id package).base := by
    change (FiniteCrossStageWitness.corePermutationTotal
      NoncentralTwistWitness.swap12).comp
        (FiniteCrossStageWitness.corePermutationTotal
          NoncentralTwistWitness.swap12) =
      PackageTotalHom.id FiniteCrossStageWitness.core
    rw [FiniteCrossStageWitness.corePermutationTotal_comp,
      NoncentralTwistWitness.swap12_square]
    exact FiniteCrossStageWitness.corePermutationTotal_refl
  apply GeometryTotalHom.ext
  · exact baseSquare
  · apply geometry_hom_heq_of_base_eq _ _ baseSquare
    · exact RingHom.id_comp _
    · rfl
    · rfl
    · rfl

/-- Geometry automorphism induced by the first adjacent transposition. -/
noncomputable def swap01Iso : Aut package where
  hom := swap01Total
  inv := swap01Total
  hom_inv_id := swap01_total_square
  inv_hom_id := swap01_total_square

/-- Geometry automorphism induced by the second adjacent transposition. -/
noncomputable def swap12Iso : Aut package where
  hom := swap12Total
  inv := swap12Total
  hom_inv_id := swap12_total_square
  inv_hom_id := swap12_total_square

/-- First transposition in the composite-fiber kernel object used by w4. -/
noncomputable def compositeSwap01 : CompositeFiberAut package :=
  ⟨swap01Iso, rfl⟩

/-- Second transposition in the composite-fiber kernel object used by w4. -/
noncomputable def compositeSwap12 : CompositeFiberAut package :=
  ⟨swap12Iso, rfl⟩

/-- Liftable three-cycle serving as the active core edge gauge. -/
noncomputable def root : CompositeFiberAut package :=
  compositeSwap01 * compositeSwap12

/-- Geometry hom whose only nonidentity component swaps coefficient factors. -/
noncomputable def coefficientSwapGeometryHom :
    GeomReadHom package package (PackageTotalHom.id package.core) where
  coverage := CoverageTransport.id package
  overlap := OverlapTransport.id package
  coefficientHom := coefficientSwap
  raw_eq := by
    unfold rawTransport
    calc
      package.raw = package.raw.baseChange coefficientSwap := raw_swap.symm
      _ = rawReindex (G := package) (H := package)
          (PackageTotalHom.id package.core)
          (package.raw.baseChange coefficientSwap) :=
        (rawReindex_id package _).symm
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- Total geometry endomorphism underlying the inner coefficient swap. -/
noncomputable def coefficientSwapTotal : GeometryTotalHom package package where
  base := PackageTotalHom.id package.core
  geometry := coefficientSwapGeometryHom

/-- The total coefficient-swap morphism is involutive. -/
theorem coefficient_swap_total_square :
    coefficientSwapTotal.comp coefficientSwapTotal =
      GeometryTotalHom.id package := by
  have baseSquare :
      (coefficientSwapTotal.comp coefficientSwapTotal).base =
        (GeometryTotalHom.id package).base := by
    change (PackageTotalHom.id package.core).comp
        (PackageTotalHom.id package.core) = PackageTotalHom.id package.core
    exact Category.comp_id
      (self := PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      (PackageTotalHom.id package.core)
  apply GeometryTotalHom.ext
  · exact baseSquare
  · apply geometry_hom_heq_of_base_eq _ _ baseSquare
    · exact coefficient_swap_comp
    · rfl
    · rfl
    · rfl

/-- Geometry automorphism generated by coefficient-factor exchange. -/
noncomputable def coefficientSwapIso : Aut package where
  hom := coefficientSwapTotal
  inv := coefficientSwapTotal
  hom_inv_id := coefficient_swap_total_square
  inv_hom_id := coefficient_swap_total_square

/-- Nonidentity strict-sector gauge lying in the inner fiber. -/
noncomputable def innerSwap : InnerFiberAut package :=
  ⟨⟨coefficientSwapIso, rfl⟩, rfl⟩

/-- Active authored comparator: the root square followed by coefficient swap. -/
noncomputable def authored : CompositeFiberAut package :=
  root * root * innerFiberInclusion package innerSwap

/-- Ring equivalence induced by an arbitrary composite-fiber automorphism. -/
noncomputable def coefficientEquiv (automorphism : CompositeFiberAut package) :
    Coefficient ≃+* Coefficient where
  toFun := automorphism.1.hom.geometry.coefficientHom
  invFun := automorphism.1.inv.geometry.coefficientHom
  left_inv x := by
    have h := congrArg
      (fun k : package ⟶ package =>
        (show GeometryTotalHom package package from k).geometry.coefficientHom x)
      automorphism.1.hom_inv_id
    exact h
  right_inv x := by
    have h := congrArg
      (fun k : package ⟶ package =>
        (show GeometryTotalHom package package from k).geometry.coefficientHom x)
      automorphism.1.inv_hom_id
    exact h
  map_mul' x y := automorphism.1.hom.geometry.coefficientHom.map_mul x y
  map_add' x y := automorphism.1.hom.geometry.coefficientHom.map_add x y

/-- Distinguished idempotent used to detect the coefficient swap. -/
def distinguished : Coefficient := (1, 0)

/-- Complementary idempotent obtained by swapping the pair factors. -/
def complementary : Coefficient := (0, 1)

/-- Every coefficient automorphism sends the distinguished idempotent to one
of the two primitive pair idempotents. -/
theorem coefficient_image_cases (automorphism : CompositeFiberAut package) :
    coefficientEquiv automorphism distinguished = distinguished ∨
      coefficientEquiv automorphism distinguished = complementary := by
  let f := coefficientEquiv automorphism
  have image_ne_zero : f distinguished ≠ 0 := by
    intro equality
    apply (by decide : distinguished ≠ (0 : Coefficient))
    apply f.injective
    simpa using equality
  have image_ne_one : f distinguished ≠ 1 := by
    intro equality
    apply (by decide : distinguished ≠ (1 : Coefficient))
    apply f.injective
    simpa using equality
  have image_idempotent :
      f distinguished * f distinguished = f distinguished := by
    calc
      f distinguished * f distinguished = f (distinguished * distinguished) :=
        (map_mul f distinguished distinguished).symm
      _ = f distinguished := by norm_num [distinguished]
  rcases image : f distinguished with ⟨x, y⟩
  have x_idempotent : x * x = x := by
    simpa [image] using congrArg Prod.fst image_idempotent
  have y_idempotent : y * y = y := by
    simpa [image] using congrArg Prod.snd image_idempotent
  have x_cases : x = 0 ∨ x = 1 := by
    have factor_zero : x * (x - 1) = 0 := by nlinarith [x_idempotent]
    rcases mul_eq_zero.mp factor_zero with factor_zero | factor_zero
    · exact Or.inl factor_zero
    · exact Or.inr (sub_eq_zero.mp factor_zero)
  have y_cases : y = 0 ∨ y = 1 := by
    have factor_zero : y * (y - 1) = 0 := by nlinarith [y_idempotent]
    rcases mul_eq_zero.mp factor_zero with factor_zero | factor_zero
    · exact Or.inl factor_zero
    · exact Or.inr (sub_eq_zero.mp factor_zero)
  rcases x_cases with rfl | rfl <;> rcases y_cases with rfl | rfl
  · exact False.elim (image_ne_zero image)
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact False.elim (image_ne_one image)

/-- Squaring any induced coefficient automorphism fixes the distinguished idempotent. -/
theorem coefficient_square_fixes_distinguished
    (automorphism : CompositeFiberAut package) :
    coefficientEquiv automorphism
        (coefficientEquiv automorphism distinguished) = distinguished := by
  rcases coefficient_image_cases automorphism with image | image
  · rw [image]
    exact image
  · rw [image]
    calc
      coefficientEquiv automorphism complementary =
          coefficientEquiv automorphism (1 - distinguished) := by
            rfl
      _ = 1 - coefficientEquiv automorphism distinguished := by
        rw [map_sub, map_one]
      _ = distinguished := by rw [image]; decide

/-- The authored comparator actually swaps the two distinguished idempotents. -/
theorem authored_coefficient_fires :
    authored.1.hom.geometry.coefficientHom distinguished = complementary := by
  rfl

/-- The coefficient action proves that the active comparator has no square root. -/
theorem authored_has_no_square_root
    (automorphism : CompositeFiberAut package) :
    automorphism * automorphism ≠ authored := by
  intro equality
  have coefficientEquality := congrArg
    (fun element : CompositeFiberAut package =>
      element.1.hom.geometry.coefficientHom distinguished) equality
  change coefficientEquiv automorphism
      (coefficientEquiv automorphism distinguished) =
    authored.1.hom.geometry.coefficientHom distinguished at coefficientEquality
  rw [authored_coefficient_fires] at coefficientEquality
  rw [coefficient_square_fixes_distinguished] at coefficientEquality
  exact (by decide : distinguished ≠ complementary) coefficientEquality

/-- Concrete base context inhabiting the selected-triple site. -/
theorem site_nonempty : Nonempty package.site.category :=
  ⟨⟨FiniteCrossStageWitness.baseContext⟩⟩

/-- The coefficient detector is nonzero, excluding the zero-ring escape. -/
theorem coefficient_nontrivial : distinguished ≠ 0 := by
  decide

/-- The diagonal base-changed `X²-X` relation remains a nonzero polynomial. -/
theorem raw_relation_nonzero :
    ((package.raw.relationFamily
      (⟨FiniteCrossStageWitness.baseContext⟩ : package.site.category)).polynomial ()) ≠
        0 := by
  change MvPolynomial.map diagonalCoefficient
      (MvPolynomial.X () ^ 2 - MvPolynomial.X ()) ≠ 0
  intro equality
  have coefficientEquality := congrArg
    (MvPolynomial.coeff (Finsupp.single () 2)) equality
  simp [MvPolynomial.coeff_X_pow, diagonalCoefficient] at coefficientEquality

/-- Distinct active repeated edge and strict local edge of the w4 presentation. -/
inductive Edge
  | active | strict
  deriving DecidableEq, Fintype

/-- Active root-obstructed cell and independently strict cell. -/
inductive Cell
  | active | strict
  deriving DecidableEq, Fintype

/-- Empty boundary path shared by both w4 cells. -/
def nilPath : PresentedPath (fun _ _ : PUnit => Edge)
    PUnit.unit PUnit.unit :=
  .nil PUnit.unit

/-- Repeated active edge `a · a` that forces an induced square coordinate. -/
def activeDoublePath : PresentedPath (fun _ _ : PUnit => Edge)
    PUnit.unit PUnit.unit :=
  @PresentedPath.cons PUnit (fun _ _ : PUnit => Edge)
    PUnit.unit PUnit.unit PUnit.unit .active
    (@PresentedPath.cons PUnit (fun _ _ : PUnit => Edge)
      PUnit.unit PUnit.unit PUnit.unit .active nilPath)

/-- Single strict edge carrying the independent inner-fiber trivialization. -/
def strictPath : PresentedPath (fun _ _ : PUnit => Edge)
    PUnit.unit PUnit.unit :=
  .cons .strict nilPath

/-- Finite one-vertex, two-edge presentation for the fixed w4 witness. -/
noncomputable abbrev presentation : FiniteTransportPresentation where
  Vertex := PUnit
  vertexFintype := inferInstance
  Edge := fun _ _ => Edge
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Cell
  twoCellFintype := inferInstance
  twoSource := fun _ => PUnit.unit
  twoTarget := fun _ => PUnit.unit
  twoLeft := fun _ => nilPath
  twoRight
    | .active => activeDoublePath
    | .strict => strictPath
  ThreeCell := PEmpty
  threeCellFintype := inferInstance
  threeSource := fun cell => nomatch cell
  threeTarget := fun cell => nomatch cell
  threeStart := fun cell => nomatch cell
  threeFinish := fun cell => nomatch cell
  threeLeft := fun cell => nomatch cell
  threeRight := fun cell => nomatch cell

/-- Authored comparator family for the active and strict cells. -/
noncomputable def comparator : Cell → CompositeFiberAut package
  | .active => authored
  | .strict => innerFiberInclusion package innerSwap

/-- Identity-edge-lift two-layer datum generated from the w4 presentation. -/
noncomputable abbrev data :
    TwoLayerTransportData presentation FiniteModel.carrier :=
  IdentityEdgeLiftSpecialization.data presentation package comparator

/-- Core projection of the liftable three-cycle root. -/
noncomputable def coreRoot : PackageFiberAut package.core :=
  compositeFiberPushforward package root

/-- The coefficient swap lies in the kernel of composite-fiber pushforward. -/
theorem inner_swap_pushforward :
    compositeFiberPushforward package
        (innerFiberInclusion package innerSwap) = 1 :=
  (compositeFiberPushforward_eq_one_iff _).2 innerSwap.2

/-- The active comparator projects to the square of the core root. -/
theorem authored_pushforward :
    compositeFiberPushforward package authored = coreRoot * coreRoot := by
  simp [authored, coreRoot, inner_swap_pushforward]

/-- The root square acts as a nonidentity three-cycle square on the core axes. -/
theorem core_root_square_ne_one : coreRoot * coreRoot ≠ 1 := by
  intro equality
  have axisEquality := congrArg
    (fun automorphism : PackageFiberAut package.core =>
      (PackageFiberAut.hom automorphism).upper.axisMap (0 : Fin 4)) equality
  change (2 : Fin 4) = 0 at axisEquality
  exact (by decide : (2 : Fin 4) ≠ 0) axisEquality

/-- The active cell is excluded from the strict sector by its nontrivial core image. -/
theorem active_not_qualified :
    ¬ StrictCellQualified data .active := by
  intro qualified
  have pushed := qualified.2
  change compositeFiberPushforward package authored = 1 at pushed
  rw [authored_pushforward] at pushed
  exact core_root_square_ne_one pushed

/-- The single-edge inner-swap cell concretely inhabits the strict sector. -/
theorem strict_qualified : StrictCellQualified data .strict := by
  constructor
  · have pathEquality :=
      (IdentityEdgeLiftSpecialization.path_lift_eq_id presentation package
        (presentation.twoLeft Cell.strict)).trans
      (IdentityEdgeLiftSpecialization.path_lift_eq_id presentation package
        (presentation.twoRight Cell.strict)).symm
    exact congrArg GeometryTotalHom.base pathEquality
  · change compositeFiberPushforward package
      (innerFiberInclusion package innerSwap) = 1
    exact inner_swap_pushforward

/-- Core gauge selecting the liftable root on the repeated active edge. -/
noncomputable def coreReselection : EdgeReselection data.coreData.lift :=
  fun _ _ edge =>
    match edge with
    | .active => coreRoot
    | .strict => 1

/-- The explicit core gauge trivializes both authored core comparators. -/
theorem core_reselection_coherent :
    CoherentAt data.coreData coreReselection := by
  intro cell
  cases cell
  · simp only [presentation, nilPath, activeDoublePath,
      reselectedPathLift, reselectLiftData, AdmissibleLiftData.pathLift,
      reselectedEdgeLift, IdentityEdgeLiftSpecialization.data,
      TwoLayerTransportData.coreData, TwoLayerLiftData.coreLiftData,
      IdentityEdgeLiftSpecialization.liftData, coreReselection, comparator,
      authored_pushforward]
    rfl
  · simp only [presentation, nilPath, strictPath,
      reselectedPathLift, reselectLiftData, AdmissibleLiftData.pathLift,
      reselectedEdgeLift, IdentityEdgeLiftSpecialization.data,
      TwoLayerTransportData.coreData, TwoLayerLiftData.coreLiftData,
      IdentityEdgeLiftSpecialization.liftData, coreReselection, comparator,
      inner_swap_pushforward]
    exact Category.comp_id
      (self := PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      (PackageTotalHom.id package.core)

/-- Core trivializer built from the generated coherence theorem. -/
noncomputable def coreTrivializer : CoreTrivializer data where
  reselection := coreReselection
  coherent := core_reselection_coherent

/-- Actual composite-fiber edge section lifting the core reselection. -/
noncomputable def edgeSection : EdgeSectionFamily data where
  core := coreReselection
  lift := fun _ _ edge =>
    match edge with
    | .active => root
    | .strict => 1
  projects := by
    intro _ _ edge
    cases edge
    · rfl
    · exact map_one _

/-- The edge section inherits the proved core alignment. -/
theorem edge_section_alignment : CoreAlignmentAt data edgeSection :=
  core_reselection_coherent

/-- Strict gauge using the inner swap only on the strict edge. -/
noncomputable def strictReselection : StrictEdgeReselection data.lift :=
  fun _ _ edge =>
    match edge with
    | .active => 1
    | .strict => innerSwap

/-- On the unique qualified cell the strict authored comparator is the inner swap. -/
theorem strict_authored_eq_inner_swap
    (qualified : StrictCellQualified data .strict) :
    strictAuthoredComparator data ⟨.strict, qualified⟩ = innerSwap := by
  apply Subtype.ext
  rfl

/-- The explicit strict gauge trivializes every qualified strict cell. -/
theorem strict_reselection_coherent :
    StrictCoherentAt data strictReselection := by
  intro cell
  rcases cell with ⟨cell, qualified⟩
  cases cell
  · exact False.elim (active_not_qualified qualified)
  · rw [strict_authored_eq_inner_swap qualified]
    simp only [presentation, nilPath, strictPath,
      upperReselectedPathLift, upperReselectLiftData,
      TwoLayerLiftData.pathLift, upperReselectedEdgeLift,
      strictToUpperReselection, strictReselection,
      IdentityEdgeLiftSpecialization.data,
      IdentityEdgeLiftSpecialization.liftData]
    exact Category.comp_id
      (self := geometryTotalCategory FiniteModel.carrier)
      (CompositeFiberAut.hom (innerFiberInclusion package innerSwap))

/-- Strict trivializer generated from the concrete qualified-cell proof. -/
noncomputable def strictTrivializer : StrictTrivializer data where
  reselection := strictReselection
  coherent := strict_reselection_coherent

/-- Core-lifted and strict gauges agree on the actual qualified cell boundary. -/
theorem shared_restriction :
    SharedBoundaryCompatible edgeSection strictTrivializer := by
  intro cell
  rcases cell with ⟨cell, qualified⟩
  cases cell
  · exact False.elim (active_not_qualified qualified)
  · change (upperReselectedPathLift data.lift
        (relativeUpperReselection edgeSection strictReselection)
        nilPath).comp
        (CompositeFiberAut.hom (innerFiberInclusion package innerSwap)) =
      upperReselectedPathLift data.lift
        (relativeUpperReselection edgeSection strictReselection)
        strictPath
    simp only [upperReselectedPathLift, upperReselectLiftData,
      TwoLayerLiftData.pathLift, upperReselectedEdgeLift,
      relativeUpperReselection, edgeSection,
      nilPath, strictPath, IdentityEdgeLiftSpecialization.data,
      IdentityEdgeLiftSpecialization.liftData]
    exact Category.comp_id
      (self := geometryTotalCategory FiniteModel.carrier)
      (CompositeFiberAut.hom (innerFiberInclusion package innerSwap))

/-- Explicit nonempty compatible core/edge/strict local datum for w4. -/
noncomputable def compatiblePair : CompatiblePairs data where
  coreTrivializer := coreTrivializer
  edgeSection := edgeSection
  core_restriction := rfl
  alignment := edge_section_alignment
  strictTrivializer := strictTrivializer
  restriction := shared_restriction

/-- The constructed compatible datum discharges the pairwise-vanishing conjunct. -/
theorem compatible_pairwise_vanishes : CompatiblePairwiseVanishes data :=
  ⟨compatiblePair⟩

/-- The repeated active path places the fixture outside the edge-level class. -/
theorem not_edge_level : ¬ EdgeLevelPresentation presentation := by
  intro edgeLevel
  have tooLong := (edgeLevel Cell.active).2
  change PresentedPath.length activeDoublePath ≤ 1 at tooLong
  norm_num [activeDoublePath, nilPath, PresentedPath.length] at tooLong

/-- Identity edge lifts make every baseline canonical cell comparator trivial. -/
theorem upper_canonical_eq_one (cell : Cell) :
    upperCanonicalTwoCellComparator data 1 cell = 1 :=
  IdentityEdgeLiftSpecialization.upper_canonical_eq_one
    presentation package comparator cell

/-- Explicit formal comparison value on every supported w4 node. -/
noncomputable def nodeValue
    {source target : presentation.Vertex}
    (node : CellChainNode presentation source target) :
    CompositeFiberAut (data.lift.geometry target) := by
  cases source
  cases target
  exact match node.path with
    | .nil _ => 1
    | .cons edge _ =>
        match edge with
        | .active => authored
        | .strict => innerFiberInclusion package innerSwap

/-- Formal descent section existing independently of any edge gauge. -/
noncomputable def comparisonSection : CellComparisonSection data where
  value := nodeValue
  nil_normalization := by
    intro vertex
    cases vertex
    rfl
  naturality := by
    intro cell
    cases cell
    all_goals rw [upper_canonical_eq_one]
    all_goals
      simp [nodeValue, CellChainNode.right, CellChainNode.left,
        presentation, nilPath, activeDoublePath, strictPath,
        IdentityEdgeLiftSpecialization.data, comparator]

/-- The explicit formal comparison section prevents universal-quantifier vacuity. -/
theorem comparison_section_nonempty :
    Nonempty (CellComparisonSection data) :=
  ⟨comparisonSection⟩

/-- Theorem (C) converts the explicit section into cell-chain coherence. -/
theorem cell_chain_coherent : CellChainCoherent data :=
  (cellChainCoherent_iff_nonempty_comparisonSection data).2
    comparison_section_nonempty

/-- The canonical coordinate of the repeated active path is the square of one
edge gauge, by coordinate uniqueness and path concatenation. -/
theorem path_gauge_coordinate_active_double
    (gauge : UpperEdgeReselection data.lift) :
    PathGaugeCoordinate data.lift gauge activeDoublePath =
      gauge PUnit.unit PUnit.unit Edge.active *
        gauge PUnit.unit PUnit.unit Edge.active := by
  symm
  apply pathGaugeCoordinate_unique data.lift gauge activeDoublePath
    (gauge PUnit.unit PUnit.unit Edge.active *
      gauge PUnit.unit PUnit.unit Edge.active)
  change ((IdentityEdgeLiftSpecialization.liftData presentation package).pathLift
      activeDoublePath).comp
        (CompositeFiberAut.hom
          (gauge PUnit.unit PUnit.unit Edge.active *
            gauge PUnit.unit PUnit.unit Edge.active)) =
    upperReselectedPathLift
      (IdentityEdgeLiftSpecialization.liftData presentation package)
      gauge activeDoublePath
  rw [IdentityEdgeLiftSpecialization.path_lift_eq_id]
  rw [compositeFiberAut_hom_mul]
  let activePath : PresentedPath (fun _ _ : PUnit => Edge)
      PUnit.unit PUnit.unit := .cons Edge.active nilPath
  rw [show activeDoublePath =
      activePath.append activePath by rfl,
    upperReselectedPathLift_append]
  simp only [activePath, nilPath, upperReselectedPathLift,
    upperReselectLiftData,
    TwoLayerLiftData.pathLift, upperReselectedEdgeLift,
    IdentityEdgeLiftSpecialization.liftData]
  change (𝟙 package) ≫
      ((CompositeFiberAut.hom (gauge PUnit.unit PUnit.unit Edge.active)) ≫
        (CompositeFiberAut.hom (gauge PUnit.unit PUnit.unit Edge.active))) =
    ((((𝟙 package) ≫
          (CompositeFiberAut.hom (gauge PUnit.unit PUnit.unit Edge.active))) ≫
        (𝟙 package)) ≫
      (((𝟙 package) ≫
          (CompositeFiberAut.hom (gauge PUnit.unit PUnit.unit Edge.active))) ≫
        (𝟙 package)))
  simp only [Category.id_comp, Category.comp_id]

/-- Any realizable formal section therefore supplies a square root of `authored`. -/
theorem realizable_forces_active_square
    (realizable : EdgeRealizableCellComparisonSection data) :
    realizable.gauge PUnit.unit PUnit.unit Edge.active *
        realizable.gauge PUnit.unit PUnit.unit Edge.active = authored := by
  have naturality := realizable.comparison.naturality Cell.active
  have rightValue :
      realizable.comparison.value
          (CellChainNode.right presentation Cell.active) = authored := by
    rw [show CellChainNode.left presentation Cell.active =
        CellChainNode.nil presentation PUnit.unit by
          apply CellChainNode.ext
          rfl,
      realizable.comparison.nil_normalization,
      upper_canonical_eq_one] at naturality
    simpa [IdentityEdgeLiftSpecialization.data, comparator] using naturality
  rw [← rightValue, ← realizable.realizes
    (CellChainNode.right presentation Cell.active)]
  change realizable.gauge PUnit.unit PUnit.unit Edge.active *
      realizable.gauge PUnit.unit PUnit.unit Edge.active =
    PathGaugeCoordinate data.lift realizable.gauge activeDoublePath
  exact (path_gauge_coordinate_active_double realizable.gauge).symm

/-- API-level cross-check: all-cell coherence yields the same active square equation. -/
theorem coherent_active_square
    (gauge : UpperEdgeReselection data.lift)
    (coherent : CrossStageCoherentAt data gauge) :
    gauge PUnit.unit PUnit.unit Edge.active *
        gauge PUnit.unit PUnit.unit Edge.active = authored := by
  exact realizable_forces_active_square
    (edgeRealizableSectionOfCoherentAt data gauge coherent)

/-- The active square-root obstruction refutes joint vanishing. -/
theorem not_joint : ¬ JointVanishes data := by
  intro joint
  obtain ⟨gauge, coherent⟩ :=
    (jointVanishes_iff_crossStageCoherentizable data).1 joint
  exact authored_has_no_square_root
    (gauge PUnit.unit PUnit.unit Edge.active)
    (coherent_active_square gauge coherent)

/-- No actual upper edge gauge realizes even the explicit formal section. -/
theorem no_edge_realizable_section :
    ¬ Nonempty (EdgeRealizableCellComparisonSection data) := by
  rintro ⟨realizable⟩
  exact authored_has_no_square_root
    (realizable.gauge PUnit.unit PUnit.unit Edge.active)
    (realizable_forces_active_square realizable)

/-- The explicit comparison section witnesses failure of universal effectivity. -/
theorem not_path_gauge_effective : ¬ PathGaugeEffective data := by
  intro effective
  obtain ⟨gauge, realizes⟩ := effective comparisonSection
  apply no_edge_realizable_section
  exact ⟨{ comparison := comparisonSection
           gauge := gauge
           realizes := realizes }⟩

/-- The strict sector is concretely inhabited, so its compatibility is nonvacuous. -/
theorem strict_sector_nonempty : Nonempty (StrictTwoCell data) :=
  ⟨⟨.strict, strict_qualified⟩⟩

/-- The strict gauge is genuinely nonidentity on the pair coefficient ring. -/
theorem inner_swap_ne_one : innerSwap ≠ 1 := by
  intro equality
  have coefficientEquality := congrArg
    (fun automorphism : InnerFiberAut package =>
      automorphism.1.1.hom.geometry.coefficientHom distinguished) equality
  change complementary = distinguished at coefficientEquality
  exact (by decide : complementary ≠ distinguished) coefficientEquality

/-- The nonidentity strict gauge is actually used on the strict presentation edge. -/
theorem strict_reselection_nonidentity :
    strictReselection PUnit.unit PUnit.unit Edge.strict ≠ 1 :=
  inner_swap_ne_one

/-- Active and strict edges are distinct constructors. -/
theorem edges_distinct : Edge.active ≠ Edge.strict := by
  decide

/-- Root-obstructed and strict cells are distinct constructors. -/
theorem cells_distinct : Cell.active ≠ Cell.strict := by
  decide

/-- The obstructed boundary really contains two occurrences of one edge. -/
theorem active_double_path_length :
    PresentedPath.length activeDoublePath = 2 := by
  rfl

/-- Nonemptiness and nondegeneracy checks for every layer used by w4. -/
theorem fixture_nonempty :
    Nonempty package.site.category ∧
      distinguished ≠ 0 ∧
      ((package.raw.relationFamily
        (⟨FiniteCrossStageWitness.baseContext⟩ : package.site.category)).polynomial ()) ≠
          0 ∧
      Nonempty presentation.Vertex ∧
      Nonempty (presentation.Edge PUnit.unit PUnit.unit) ∧
      Nonempty presentation.TwoCell ∧
      Nonempty (StrictTwoCell data) ∧
      Nonempty (CellComparisonSection data) :=
  ⟨site_nonempty, coefficient_nontrivial, raw_relation_nonzero,
    ⟨PUnit.unit⟩, ⟨Edge.active⟩, ⟨Cell.active⟩,
    strict_sector_nonempty, comparison_section_nonempty⟩

/-- Fixed G-109 witness (w4): compatible formal descent exists outside the
edge-level class, but its repeated-edge root equation is not effectivizable. -/
theorem w4_root_effectivity_obstruction :
    (Nonempty package.site.category ∧
      distinguished ≠ 0 ∧
      ((package.raw.relationFamily
        (⟨FiniteCrossStageWitness.baseContext⟩ : package.site.category)).polynomial ()) ≠
          0 ∧
      Nonempty presentation.Vertex ∧
      Nonempty (presentation.Edge PUnit.unit PUnit.unit) ∧
      Nonempty presentation.TwoCell ∧
      Nonempty (StrictTwoCell data) ∧
      Nonempty (CellComparisonSection data)) ∧
      Edge.active ≠ Edge.strict ∧
      Cell.active ≠ Cell.strict ∧
      PresentedPath.length activeDoublePath = 2 ∧
      ¬ EdgeLevelPresentation presentation ∧
      strictReselection PUnit.unit PUnit.unit Edge.strict ≠ 1 ∧
      CompatiblePairwiseVanishes data ∧
      Nonempty (CellComparisonSection data) ∧
      CellChainCoherent data ∧
      ¬ Nonempty (EdgeRealizableCellComparisonSection data) ∧
      ¬ PathGaugeEffective data ∧
      ¬ JointVanishes data ∧
      (∀ automorphism : CompositeFiberAut package,
        automorphism * automorphism ≠ authored) :=
  ⟨fixture_nonempty, edges_distinct, cells_distinct,
    active_double_path_length, not_edge_level, strict_reselection_nonidentity,
    compatible_pairwise_vanishes,
    comparison_section_nonempty, cell_chain_coherent,
    no_edge_realizable_section, not_path_gauge_effective, not_joint,
    authored_has_no_square_root⟩

end RootEffectivityWitness

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
