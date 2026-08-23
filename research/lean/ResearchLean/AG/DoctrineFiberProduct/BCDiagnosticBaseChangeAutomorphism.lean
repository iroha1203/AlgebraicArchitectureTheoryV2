import ResearchLean.AG.DoctrineFiberProduct.PackageProjectionBeckChevalleyExactness
import ResearchLean.AG.TransportCoherence.FinitePresentation

/-!
# Endpoint automorphism action for diagnostic base change

This module constructs the unconditional group-homomorphism layer of G-110
K3.  A generated core-fiber functor sends each G-106 endpoint
`PackageFiberAut` to the corresponding target endpoint group, hence acts
pointwise on defect cochains and preserves the identity cochain.  For the two
generated Beck--Chevalley routes, the exact canonical mate supplies the
endpoint comparison isomorphism and its naturality identifies the two images.

No transported diagnostic datum, comparator, raw-defect preservation law,
orbit theorem, or `H_bc` certificate is accepted here.  Constructing the
transported datum is the next unconditional layer; raw-defect and orbit
preservation remain explicitly conditional downstream obligations.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- Identify G-106 package-fiber automorphisms with automorphisms of the
corresponding object in the categorical core fiber. -/
noncomputable def packageFiberAutCoreFiberEquiv
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : CoreFiber X) : PackageFiberAut P.1 ≃* Aut P := by
  rcases P with ⟨P, rfl⟩
  refine {
  toFun automorphism := {
    hom := ⟨PackageFiberAut.hom automorphism, by
      apply CategoryTheory.IsHomLift.of_commsq
        (packageProjection U) (𝟙 (packagePoint P))
        (PackageFiberAut.hom automorphism) rfl rfl
      rw [packageProjection_map, PackageFiberAut.hom_base_eq]
      exact Category.id_comp _⟩
    inv := ⟨PackageFiberAut.inv automorphism, by
      apply CategoryTheory.IsHomLift.of_commsq
        (packageProjection U) (𝟙 (packagePoint P))
        (PackageFiberAut.inv automorphism) rfl rfl
      rw [packageProjection_map, PackageFiberAut.inv_base_eq]
      exact Category.id_comp _⟩
    hom_inv_id := by
      apply CategoryTheory.Functor.Fiber.hom_ext
      exact automorphism.1.hom_inv_id
    inv_hom_id := by
      apply CategoryTheory.Functor.Fiber.hom_ext
      exact automorphism.1.inv_hom_id }
  invFun automorphism := ⟨{
    hom := automorphism.hom.1
    inv := automorphism.inv.1
    hom_inv_id := congrArg Subtype.val automorphism.hom_inv_id
    inv_hom_id := congrArg Subtype.val automorphism.inv_hom_id }, by
      letI : (packageProjection U).IsHomLift
          (𝟙 (packagePoint P)) automorphism.hom.1 := automorphism.hom.2
      have fac := CategoryTheory.IsHomLift.fac
        (packageProjection U) (𝟙 (packagePoint P)) automorphism.hom.1
      simpa using fac.symm⟩
  left_inv automorphism := by
    apply Subtype.ext
    apply Iso.ext
    rfl
  right_inv automorphism := by
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    rfl
  map_mul' left right := by
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    rfl }

/-- Every core-fiber functor induces the endpoint group homomorphism required
by diagnostic base change. -/
noncomputable def coreFiberFunctorPackageAutHom
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (F : CoreFiber X ⥤ CoreFiber Y) (P : CoreFiber X) :
    PackageFiberAut P.1 →* PackageFiberAut (F.obj P).1 :=
  (packageFiberAutCoreFiberEquiv (F.obj P)).symm.toMonoidHom.comp
    ((F.mapAut P).comp (packageFiberAutCoreFiberEquiv P).toMonoidHom)

@[simp]
theorem coreFiberFunctorPackageAutHom_one
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (F : CoreFiber X ⥤ CoreFiber Y) (P : CoreFiber X) :
    coreFiberFunctorPackageAutHom F P 1 = 1 := by
  exact map_one _

@[simp]
theorem coreFiberFunctorPackageAutHom_mul
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (F : CoreFiber X ⥤ CoreFiber Y) (P : CoreFiber X)
    (left right : PackageFiberAut P.1) :
    coreFiberFunctorPackageAutHom F P (left * right) =
      coreFiberFunctorPackageAutHom F P left *
        coreFiberFunctorPackageAutHom F P right := by
  exact map_mul _ _ _

/-- A core-fiber isomorphism identifies the corresponding endpoint
automorphism groups. -/
noncomputable def packageFiberAutMulEquivOfCoreFiberIso
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {P Q : CoreFiber X} (iso : P ≅ Q) :
    PackageFiberAut P.1 ≃* PackageFiberAut Q.1 :=
  (packageFiberAutCoreFiberEquiv P).trans
    ((Aut.autMulEquivOfIso iso).trans
      (packageFiberAutCoreFiberEquiv Q).symm)

/-- The generated direct BC route on the core fiber. -/
noncomputable def bcDiagnosticDirectFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcLeftPresentation presentation)) ⋙
    coreFiberTransportFunctor
      (typedPresentationToSemantic (bcTopPresentation presentation))

/-- The generated via-base BC route on the core fiber. -/
noncomputable def bcDiagnosticViaBaseFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  coreFiberTransportFunctor
      (typedPresentationToSemantic (bcBottomPresentation presentation)) ⋙
    selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcRightPresentation presentation))

/-- The exact canonical BC mate as an endpoint package isomorphism. -/
noncomputable def bcDiagnosticComparisonIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (P : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    (bcDiagnosticDirectFunctor presentation).obj P ≅
      (bcDiagnosticViaBaseFunctor presentation).obj P := by
  letI : IsIso (coreBeckChevalleyMate presentation) :=
    coreBeckChevalleyMate_isIso presentation
  exact asIso ((coreBeckChevalleyMate presentation).app P)

/-- The endpoint automorphism comparison generated by the exact BC mate. -/
noncomputable def bcDiagnosticEndpointComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (P : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    PackageFiberAut (bcDiagnosticDirectFunctor presentation |>.obj P).1 ≃*
      PackageFiberAut (bcDiagnosticViaBaseFunctor presentation |>.obj P).1 :=
  packageFiberAutMulEquivOfCoreFiberIso
    (bcDiagnosticComparisonIso presentation P)

/-- Naturality of the generated mate identifies the direct and via-base
images of every core-fiber automorphism. -/
theorem bcDiagnosticCoreFiberAutComparison_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (P : CoreFiber presentation.1.cospan.firstSource.toSemantic)
    (automorphism : Aut P) :
    Aut.autMulEquivOfIso (bcDiagnosticComparisonIso presentation P)
        ((bcDiagnosticDirectFunctor presentation).mapAut P automorphism) =
      (bcDiagnosticViaBaseFunctor presentation).mapAut P automorphism := by
  apply Iso.ext
  letI : IsIso (coreBeckChevalleyMate presentation) :=
    coreBeckChevalleyMate_isIso presentation
  change inv ((coreBeckChevalleyMate presentation).app P) ≫
        (bcDiagnosticDirectFunctor presentation).map automorphism.hom ≫
        (coreBeckChevalleyMate presentation).app P =
      (bcDiagnosticViaBaseFunctor presentation).map automorphism.hom
  have naturality :
      (bcDiagnosticDirectFunctor presentation).map automorphism.hom ≫
          (coreBeckChevalleyMate presentation).app P =
        (coreBeckChevalleyMate presentation).app P ≫
          (bcDiagnosticViaBaseFunctor presentation).map automorphism.hom := by
    exact (coreBeckChevalleyMate presentation).naturality automorphism.hom
  calc
    _ = inv ((coreBeckChevalleyMate presentation).app P) ≫
        ((coreBeckChevalleyMate presentation).app P ≫
          (bcDiagnosticViaBaseFunctor presentation).map automorphism.hom) := by
      rw [naturality]
    _ = _ := by simp

/-- Naturality of the generated mate identifies the direct and via-base
images of every source endpoint automorphism. -/
theorem bcDiagnosticEndpointComparison_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (P : CoreFiber presentation.1.cospan.firstSource.toSemantic)
    (automorphism : PackageFiberAut P.1) :
    bcDiagnosticEndpointComparison presentation P
        (coreFiberFunctorPackageAutHom
          (bcDiagnosticDirectFunctor presentation) P automorphism) =
      coreFiberFunctorPackageAutHom
        (bcDiagnosticViaBaseFunctor presentation) P automorphism := by
  apply (packageFiberAutCoreFiberEquiv
    ((bcDiagnosticViaBaseFunctor presentation).obj P)).injective
  simpa [bcDiagnosticEndpointComparison,
    packageFiberAutMulEquivOfCoreFiberIso,
    coreFiberFunctorPackageAutHom] using
      (bcDiagnosticCoreFiberAutComparison_naturality
        presentation P (packageFiberAutCoreFiberEquiv P automorphism))

/-! ## Pointwise action on a fixed combinatorial cochain -/

/-- Packages obtained by applying one generated core-fiber functor at every
vertex while retaining the original finite combinatorial presentation. -/
noncomputable def coreFiberFunctorEndpointPackage
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (targetBase : G.Vertex → ExtractionInstance U)
    (action : ∀ vertex,
      CoreFiber (packagePoint (data.lift.package vertex)) ⥤
        CoreFiber (targetBase vertex))
    (vertex : G.Vertex) : AATCorePackage U :=
  (action vertex).obj ⟨data.lift.package vertex, rfl⟩ |>.1

/-- Endpoint-automorphism cochains on the packages generated by a vertexwise
core-fiber action. -/
abbrev CoreFiberFunctorDefectCochain
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (targetBase : G.Vertex → ExtractionInstance U)
    (action : ∀ vertex,
      CoreFiber (packagePoint (data.lift.package vertex)) ⥤
        CoreFiber (targetBase vertex)) :=
  (cell : G.TwoCell) → PackageFiberAut
    (coreFiberFunctorEndpointPackage data targetBase action (G.twoTarget cell))

/-- Map a G-106 defect cochain pointwise through the generated endpoint group
homomorphisms. -/
noncomputable def coreFiberFunctorDefectCochainMap
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (targetBase : G.Vertex → ExtractionInstance U)
    (action : ∀ vertex,
      CoreFiber (packagePoint (data.lift.package vertex)) ⥤
        CoreFiber (targetBase vertex))
    (cochain : DefectCochain data) :
    CoreFiberFunctorDefectCochain data targetBase action :=
  fun cell => coreFiberFunctorPackageAutHom
    (action (G.twoTarget cell))
    ⟨data.lift.package (G.twoTarget cell), rfl⟩ (cochain cell)

/-- The pointwise diagnostic action preserves the identity cochain. -/
theorem coreFiberFunctorDefectCochainMap_identity
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (targetBase : G.Vertex → ExtractionInstance U)
    (action : ∀ vertex,
      CoreFiber (packagePoint (data.lift.package vertex)) ⥤
        CoreFiber (targetBase vertex)) :
    coreFiberFunctorDefectCochainMap data targetBase action
        (identityDefectCochain data) =
      (fun _ => 1) := by
  funext cell
  exact coreFiberFunctorPackageAutHom_one
    (action (G.twoTarget cell))
    ⟨data.lift.package (G.twoTarget cell), rfl⟩

/-- The pointwise diagnostic action preserves cochain multiplication. -/
theorem coreFiberFunctorDefectCochainMap_mul
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U)
    (targetBase : G.Vertex → ExtractionInstance U)
    (action : ∀ vertex,
      CoreFiber (packagePoint (data.lift.package vertex)) ⥤
        CoreFiber (targetBase vertex))
    (left right : DefectCochain data) :
    coreFiberFunctorDefectCochainMap data targetBase action
        (fun cell => left cell * right cell) =
      (fun cell =>
        coreFiberFunctorDefectCochainMap data targetBase action left cell *
          coreFiberFunctorDefectCochainMap data targetBase action right cell) := by
  funext cell
  exact coreFiberFunctorPackageAutHom_mul
    (action (G.twoTarget cell))
    ⟨data.lift.package (G.twoTarget cell), rfl⟩ (left cell) (right cell)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
