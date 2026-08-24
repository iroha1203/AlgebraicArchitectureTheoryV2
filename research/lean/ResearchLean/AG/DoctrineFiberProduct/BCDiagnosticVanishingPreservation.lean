import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticQualifiedBaseChange
import ResearchLean.AG.TransportCoherence.VanishingCoherence

/-!
# Unconditional preservation of diagnostic obstruction vanishing

The fixed `(d1)`--`(d3)` transport maps a source-fiber interpretation by an
actual core-fiber functor.  Every coherent edge reselection maps to a coherent
target reselection, so obstruction vanishing is preserved without an `H_bc`
hypothesis.  Specializing to the direct and via-base Beck--Chevalley routes
proves that the negative conjunct required by the pre-2026-08-24 G-110(D)
cannot occur on the source-fiber-incidence domain.  The revised card takes
these declarations as candidates for its unconditional covariance layer.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- The endpoint group homomorphism is the underlying action of the
core-fiber functor on automorphisms. -/
@[simp]
theorem coreFiberFunctorPackageAutHom_hom
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (F : CategoryTheory.Functor (CoreFiber X) (CoreFiber Y))
    (P : CoreFiber X)
    (automorphism : PackageFiberAut P.1) :
    (packageFiberAutCoreFiberEquiv (F.obj P)
      (coreFiberFunctorPackageAutHom F P automorphism)).hom =
      F.map (packageFiberAutCoreFiberEquiv P automorphism).hom := by
  change
    ((packageFiberAutCoreFiberEquiv (F.obj P))
      ((packageFiberAutCoreFiberEquiv (F.obj P)).symm
        ((F.mapAut P) ((packageFiberAutCoreFiberEquiv P) automorphism)))).hom =
      F.map ((packageFiberAutCoreFiberEquiv P) automorphism).hom
  have equality := (packageFiberAutCoreFiberEquiv (F.obj P)).apply_symm_apply
    ((F.mapAut P) ((packageFiberAutCoreFiberEquiv P) automorphism))
  exact congrArg Iso.hom equality

/-- Forgetting the fiber tag recovers the authored package-fiber
automorphism. -/
@[simp]
theorem packageFiberAutCoreFiberEquiv_hom_val
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : CoreFiber X) (automorphism : PackageFiberAut P.1) :
    ((packageFiberAutCoreFiberEquiv P) automorphism).hom.1 =
      PackageFiberAut.hom automorphism := by
  rcases P with ⟨P, rfl⟩
  rfl

@[simp]
theorem fiberwise_toLiftData_edgeLift
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {i j : G.Vertex} (edge : G.Edge i j) :
    data.toLiftData.edgeLift edge = (data.edgeIso edge).hom.1 := rfl

/-- Map a source edge reselection through one core-fiber functor. -/
noncomputable def mapEdgeReselection
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CategoryTheory.Functor (CoreFiber X) (CoreFiber Y))
    (reselection : EdgeReselection data.toLiftData) :
    EdgeReselection (data.map F).toLiftData :=
  fun _ j edge => coreFiberFunctorPackageAutHom F (data.package j)
    (reselection _ j edge)

/-- One reselected edge represented inside the categorical core fiber. -/
noncomputable def fiberReselectedEdge
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (reselection : EdgeReselection data.toLiftData)
    {i j : G.Vertex} (edge : G.Edge i j) :
    data.package i ⟶ data.package j :=
  (data.edgeIso edge).hom ≫
    (packageFiberAutCoreFiberEquiv (data.package j)
      (reselection i j edge)).hom

/-- A reselected path represented inside the categorical core fiber. -/
noncomputable def fiberReselectedPath
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (reselection : EdgeReselection data.toLiftData) {i j : G.Vertex} :
    (path : G.Path i j) → (data.package i ⟶ data.package j)
  | .nil _ => 𝟙 _
  | .cons edge tail =>
      fiberReselectedEdge data reselection edge ≫
        fiberReselectedPath data reselection tail

/-- Forgetting the fiber tag recovers G-106 reselected path evaluation. -/
@[simp]
theorem fiberReselectedPath_val
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (reselection : EdgeReselection data.toLiftData) {i j : G.Vertex}
    (path : G.Path i j) :
    (fiberReselectedPath data reselection path).1 =
      reselectedPathLift data.toLiftData reselection path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [fiberReselectedPath, fiberReselectedEdge,
        reselectedPathLift, reselectLiftData, AdmissibleLiftData.pathLift,
        reselectedEdgeLift]
      change
        (data.edgeIso edge).hom.1 ≫
            (packageFiberAutCoreFiberEquiv (data.package _) _).hom.1 ≫
              (fiberReselectedPath data reselection tail).1 =
          data.toLiftData.edgeLift edge ≫
            PackageFiberAut.hom (reselection _ _ edge) ≫
              reselectedPathLift data.toLiftData reselection tail
      rw [inductionHypothesis, packageFiberAutCoreFiberEquiv_hom_val,
        fiberwise_toLiftData_edgeLift]

/-- A mapped reselected edge is the functorial image of the source edge. -/
@[simp]
theorem fiberReselectedEdge_map
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CategoryTheory.Functor (CoreFiber X) (CoreFiber Y))
    (reselection : EdgeReselection data.toLiftData)
    {i j : G.Vertex} (edge : G.Edge i j) :
    fiberReselectedEdge (data.map F)
        (mapEdgeReselection data F reselection) edge =
      F.map (fiberReselectedEdge data reselection edge) := by
  simp only [fiberReselectedEdge, mapEdgeReselection,
    FiberwiseAdmissibleTransportData.map,
    coreFiberFunctorPackageAutHom_hom,
    Functor.mapIso_hom, F.map_comp]

/-- A mapped reselected path is the functorial image of the source path. -/
theorem fiberReselectedPath_map
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CategoryTheory.Functor (CoreFiber X) (CoreFiber Y))
    (reselection : EdgeReselection data.toLiftData) {i j : G.Vertex}
    (path : G.Path i j) :
    fiberReselectedPath (data.map F)
        (mapEdgeReselection data F reselection) path =
      F.map (fiberReselectedPath data reselection path) := by
  induction path with
  | nil vertex =>
      simpa only [fiberReselectedPath] using
        (F.map_id (data.package vertex)).symm
  | cons edge tail inductionHypothesis =>
      simp only [fiberReselectedPath]
      rw [fiberReselectedEdge_map, inductionHypothesis, F.map_comp]

/-- Functorial transport sends every coherent reselection to a coherent
target reselection. -/
theorem coherentAt_map
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CategoryTheory.Functor (CoreFiber X) (CoreFiber Y))
    (reselection : EdgeReselection data.toLiftData)
    (coherent : CoherentAt data.toTransportData reselection) :
    CoherentAt (data.transported F)
      (mapEdgeReselection data F reselection) := by
  intro cell
  have sourceFiberEquality :
      fiberReselectedPath data reselection (G.twoLeft cell) ≫
          (packageFiberAutCoreFiberEquiv
            (data.package (G.twoTarget cell)) (data.comparator cell)).hom =
        fiberReselectedPath data reselection (G.twoRight cell) := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    change
      (fiberReselectedPath data reselection (G.twoLeft cell)).1 ≫
          (packageFiberAutCoreFiberEquiv
            (data.package (G.twoTarget cell)) (data.comparator cell)).hom.1 =
        (fiberReselectedPath data reselection (G.twoRight cell)).1
    rw [packageFiberAutCoreFiberEquiv_hom_val]
    simpa only [fiberReselectedPath_val] using coherent cell
  have mappedEquality := congrArg F.map sourceFiberEquality
  have mappedFiberEquality :
      F.map (fiberReselectedPath data reselection (G.twoLeft cell)) ≫
          F.map ((packageFiberAutCoreFiberEquiv
            (data.package (G.twoTarget cell)) (data.comparator cell)).hom) =
        F.map (fiberReselectedPath data reselection (G.twoRight cell)) := by
    simpa only [F.map_comp] using mappedEquality
  have targetFiberEquality :
      fiberReselectedPath (data.map F)
          (mapEdgeReselection data F reselection) (G.twoLeft cell) ≫
            (packageFiberAutCoreFiberEquiv
              ((data.map F).package (G.twoTarget cell))
              ((data.transported F).comparator cell)).hom =
        fiberReselectedPath (data.map F)
          (mapEdgeReselection data F reselection) (G.twoRight cell) := by
    rw [fiberReselectedPath_map, fiberReselectedPath_map]
    simpa only [FiberwiseAdmissibleTransportData.transported,
      FiberwiseAdmissibleTransportData.toTransportData,
      FiberwiseAdmissibleTransportData.map,
      coreFiberFunctorPackageAutHom_hom] using mappedFiberEquality
  have targetTotalEquality := congrArg (fun morphism => morphism.1)
    targetFiberEquality
  change
    (fiberReselectedPath (data.map F)
        (mapEdgeReselection data F reselection) (G.twoLeft cell)).1 ≫
        (packageFiberAutCoreFiberEquiv
          ((data.map F).package (G.twoTarget cell))
          ((data.map F).comparator cell)).hom.1 =
      (fiberReselectedPath (data.map F)
        (mapEdgeReselection data F reselection) (G.twoRight cell)).1
    at targetTotalEquality
  simpa only [FiberwiseAdmissibleTransportData.transported,
    FiberwiseAdmissibleTransportData.toTransportData,
    fiberReselectedPath_val,
    packageFiberAutCoreFiberEquiv_hom_val] using targetTotalEquality

/-- Obstruction vanishing is preserved by every functorial fiberwise
transport.  No condition on the functor or square is required. -/
theorem transportObstructionVanishes_map
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CategoryTheory.Functor (CoreFiber X) (CoreFiber Y))
    (vanishes : TransportObstructionVanishes data.toTransportData) :
    TransportObstructionVanishes (data.transported F) := by
  rw [transportObstructionVanishes_iff_coherentizable] at vanishes ⊢
  rcases vanishes with ⟨reselection, coherent⟩
  exact ⟨mapEdgeReselection data F reselection,
    coherentAt_map data F reselection coherent⟩

/-- Extensionality for admissible lift data, including its dependent edge
family. -/
theorem admissibleLiftData_ext
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (left right : AdmissibleLiftData G U)
    (package_eq : left.package = right.package)
    (edgeLift_eq : HEq
      (@AdmissibleLiftData.edgeLift G U left)
      (@AdmissibleLiftData.edgeLift G U right)) : left = right := by
  cases left with
  | mk leftPackage leftEdge leftStrong =>
      cases right with
      | mk rightPackage rightEdge rightStrong =>
          cases package_eq
          cases edgeLift_eq
          rfl

/-- Extensionality for admissible transport data after identifying its
dependent lift layer. -/
theorem admissibleTransportData_ext
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (left right : AdmissibleTransportData G U)
    (lift_eq : left.lift = right.lift)
    (comparator_eq : HEq left.comparator right.comparator) : left = right := by
  cases left with
  | mk leftLift leftBase leftComparator =>
      cases right with
      | mk rightLift rightBase rightComparator =>
          cases lift_eq
          cases comparator_eq
          rfl

/-- Rebuilding an ordinary qualified source datum through its core-fiber
incidence changes none of its G-106 data. -/
theorem toFiberwise_toTransportData_eq
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : AdmissibleTransportData G U} {X : ExtractionInstance U}
    (incidence : DiagnosticSourceFiberIncidence U data X) :
    incidence.toFiberwise.toTransportData = data := by
  have liftEquality : incidence.toFiberwise.toTransportData.lift = data.lift := by
    apply admissibleLiftData_ext
    · funext vertex
      exact incidence.toFiberwise_package vertex
    · have packageEquality :
          incidence.toFiberwise.toTransportData.lift.package =
            data.lift.package := by
        funext vertex
        exact incidence.toFiberwise_package vertex
      cases packageEquality
      apply heq_of_eq
      funext i j edge
      exact incidence.toFiberwise_edgeLift edge
  apply admissibleTransportData_ext _ _ liftEquality
  cases liftEquality
  apply heq_of_eq
  funext cell
  exact incidence.toFiberwise_comparator cell

/-- The actual direct Beck--Chevalley route preserves obstruction vanishing
on every source-fiber-qualified ordinary interpretation. -/
theorem bcDiagnosticDirectTransportObstructionVanishes
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    (vanishes : TransportObstructionVanishes interpretation.data) :
    TransportObstructionVanishes
      (bcDiagnosticDirectTransportedInterpretationData presentation
        interpretation incidence) := by
  rw [← toFiberwise_toTransportData_eq incidence] at vanishes
  exact transportObstructionVanishes_map incidence.toFiberwise
    (bcDiagnosticDirectFunctor presentation) vanishes

/-- The actual via-base Beck--Chevalley route also preserves obstruction
vanishing unconditionally. -/
theorem bcDiagnosticViaBaseTransportObstructionVanishes
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC presentation))
    (incidence : BCDiagnosticSourceFiberIncidence presentation interpretation)
    (vanishes : TransportObstructionVanishes interpretation.data) :
    TransportObstructionVanishes
      (bcDiagnosticViaBaseTransportedInterpretationData presentation
        interpretation incidence) := by
  rw [← toFiberwise_toTransportData_eq incidence] at vanishes
  exact transportObstructionVanishes_map incidence.toFiberwise
    (bcDiagnosticViaBaseFunctor presentation) vanishes

/-- There is no qualified witness whose source obstruction vanishes and whose
transported obstruction fails to vanish along either actual route.  This
refutes the negative conjunct of the pre-2026-08-24 G-110(D) on its fixed input
domain and supports the revised unconditional covariance statement. -/
theorem no_bcDiagnosticQualifiedVanishingCounterexample
    {U : AtomCarrier.{u}} [DecidableEq U.Atom] :
    ¬ ∃ (presentation : BCPresentation U)
        (interpretation : BCDiagnosticInterpretation U
          (toSemanticBC presentation))
        (incidence : BCDiagnosticSourceFiberIncidence presentation
          interpretation),
      TransportObstructionVanishes interpretation.data ∧
        (¬ TransportObstructionVanishes
          (bcDiagnosticDirectTransportedInterpretationData presentation
            interpretation incidence) ∨
         ¬ TransportObstructionVanishes
          (bcDiagnosticViaBaseTransportedInterpretationData presentation
            interpretation incidence)) := by
  rintro ⟨presentation, interpretation, incidence, sourceVanishes,
    directFails | viaBaseFails⟩
  · exact directFails
      (bcDiagnosticDirectTransportObstructionVanishes presentation
        interpretation incidence sourceVanishes)
  · exact viaBaseFails
      (bcDiagnosticViaBaseTransportObstructionVanishes presentation
        interpretation incidence sourceVanishes)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
