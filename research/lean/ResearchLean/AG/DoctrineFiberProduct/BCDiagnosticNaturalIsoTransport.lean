import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticNaturalIsoCompatibility

/-!
# Diagnostic transport along a core-fiber natural isomorphism

This module transports an already selected target diagnostic coordinate across
a natural isomorphism.  Unlike the paired forward conclusions, the resulting
edge/path equations and coherence equivalence compare the two target
diagnostics directly.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- Conjugation of package-fiber automorphisms respects composition of the
underlying core-fiber isomorphisms. -/
theorem packageFiberAutMulEquivOfCoreFiberIso_trans
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {P Q R : CoreFiber X} (first : P ≅ Q) (second : Q ≅ R)
    (automorphism : PackageFiberAut P.1) :
    packageFiberAutMulEquivOfCoreFiberIso (first ≪≫ second) automorphism =
      packageFiberAutMulEquivOfCoreFiberIso second
        (packageFiberAutMulEquivOfCoreFiberIso first automorphism) := by
  apply (packageFiberAutCoreFiberEquiv R).injective
  apply Iso.ext
  dsimp [packageFiberAutMulEquivOfCoreFiberIso,
    CategoryTheory.Aut.autMulEquivOfIso]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  simp

/-- Underlying conjugation formula for transported package-fiber
automorphisms. -/
theorem packageFiberAutMulEquivOfCoreFiberIso_hom
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {P Q : CoreFiber X} (iso : P ≅ Q)
    (automorphism : PackageFiberAut P.1) :
    (packageFiberAutCoreFiberEquiv Q
      (packageFiberAutMulEquivOfCoreFiberIso iso automorphism)).hom =
      iso.inv ≫
        (packageFiberAutCoreFiberEquiv P automorphism).hom ≫ iso.hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  simp [packageFiberAutMulEquivOfCoreFiberIso,
    packageFiberAutCoreFiberEquiv, CategoryTheory.Aut.autMulEquivOfIso]

/-- Transport an arbitrary target edge reselection through a natural
isomorphism. -/
noncomputable def transportEdgeReselectionAlongNaturalIso
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {F H : CoreFiber X ⥤ CoreFiber Y} (comparison : F ≅ H)
    (reselection : EdgeReselection (data.map F).toLiftData) :
    EdgeReselection (data.map H).toLiftData :=
  fun _ j edge =>
    packageFiberAutMulEquivOfCoreFiberIso
      (comparison.app (data.package j)) (reselection _ j edge)

/-- Reselection transport respects vertical composition of natural
isomorphisms. -/
theorem transportEdgeReselectionAlongNaturalIso_trans
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {F H K : CoreFiber X ⥤ CoreFiber Y}
    (first : F ≅ H) (second : H ≅ K)
    (reselection : EdgeReselection (data.map F).toLiftData) :
    transportEdgeReselectionAlongNaturalIso data (first ≪≫ second) reselection =
      transportEdgeReselectionAlongNaturalIso data second
        (transportEdgeReselectionAlongNaturalIso data first reselection) := by
  funext i j edge
  exact packageFiberAutMulEquivOfCoreFiberIso_trans
    (first.app (data.package j)) (second.app (data.package j))
    (reselection i j edge)

/-- The identity natural isomorphism fixes every target reselection. -/
@[simp]
theorem transportEdgeReselectionAlongNaturalIso_refl
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    (F : CoreFiber X ⥤ CoreFiber Y)
    (reselection : EdgeReselection (data.map F).toLiftData) :
    transportEdgeReselectionAlongNaturalIso data (Iso.refl F) reselection =
      reselection := by
  funext i j edge
  apply (packageFiberAutCoreFiberEquiv ((data.map F).package j)).injective
  apply Iso.ext
  simp [transportEdgeReselectionAlongNaturalIso,
    packageFiberAutMulEquivOfCoreFiberIso,
    CategoryTheory.Aut.autMulEquivOfIso,
    FiberwiseAdmissibleTransportData.map]

/-- Transport through an isomorphism and then its inverse returns the original
target reselection. -/
@[simp]
theorem transportEdgeReselectionAlongNaturalIso_symm_apply
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {F H : CoreFiber X ⥤ CoreFiber Y} (comparison : F ≅ H)
    (reselection : EdgeReselection (data.map F).toLiftData) :
    transportEdgeReselectionAlongNaturalIso data comparison.symm
        (transportEdgeReselectionAlongNaturalIso data comparison reselection) =
      reselection := by
  rw [← transportEdgeReselectionAlongNaturalIso_trans]
  have hcomparison : comparison ≪≫ comparison.symm = Iso.refl F := by
    ext
    simp
  rw [hcomparison]
  exact transportEdgeReselectionAlongNaturalIso_refl data F reselection

/-- Transporting a canonically mapped source reselection across a comparison
recovers the canonical map for the other endpoint functor. -/
theorem transportEdgeReselectionAlongNaturalIso_map
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {F H : CoreFiber X ⥤ CoreFiber Y} (comparison : F ≅ H)
    (reselection : EdgeReselection data.toLiftData) :
    transportEdgeReselectionAlongNaturalIso data comparison
        (mapEdgeReselection data F reselection) =
      mapEdgeReselection data H reselection := by
  funext i j edge
  exact coreFiberFunctorPackageAutHom_iso_naturality comparison
    (data.package j) (reselection i j edge)

/-- A reselected target edge commutes with the pointwise comparison. -/
theorem fiberReselectedEdge_naturality_iso
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {F H : CoreFiber X ⥤ CoreFiber Y} (comparison : F ≅ H)
    (reselection : EdgeReselection (data.map F).toLiftData)
    {i j : G.Vertex} (edge : G.Edge i j) :
    fiberReselectedEdge (data.map F) reselection edge ≫
        (comparison.app (data.package j)).hom =
      (comparison.app (data.package i)).hom ≫
        fiberReselectedEdge (data.map H)
          (transportEdgeReselectionAlongNaturalIso data comparison reselection)
          edge := by
  simp only [fiberReselectedEdge,
    transportEdgeReselectionAlongNaturalIso,
    FiberwiseAdmissibleTransportData.map, Functor.mapIso_hom]
  rw [packageFiberAutMulEquivOfCoreFiberIso_hom]
  have hedge := comparison.hom.naturality (data.edgeIso edge).hom
  calc
    _ = F.map (data.edgeIso edge).hom ≫
        (comparison.app (data.package j)).hom ≫
          ((comparison.app (data.package j)).inv ≫
            (packageFiberAutCoreFiberEquiv ((data.map F).package j)
              (reselection i j edge)).hom ≫
            (comparison.app (data.package j)).hom) := by
          simp [FiberwiseAdmissibleTransportData.map]
    _ = (comparison.app (data.package i)).hom ≫
        H.map (data.edgeIso edge).hom ≫
          ((comparison.app (data.package j)).inv ≫
            (packageFiberAutCoreFiberEquiv ((data.map F).package j)
              (reselection i j edge)).hom ≫
            (comparison.app (data.package j)).hom) := by
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ (comparison.app (data.package j)).inv ≫
              (packageFiberAutCoreFiberEquiv ((data.map F).package j)
                (reselection i j edge)).hom ≫
              (comparison.app (data.package j)).hom) hedge
    _ = _ := rfl

/-- The complete reselected target path commutes with the pointwise
comparison. -/
theorem fiberReselectedPath_naturality_iso
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {F H : CoreFiber X ⥤ CoreFiber Y} (comparison : F ≅ H)
    (reselection : EdgeReselection (data.map F).toLiftData)
    {i j : G.Vertex} (path : G.Path i j) :
    fiberReselectedPath (data.map F) reselection path ≫
        (comparison.app (data.package j)).hom =
      (comparison.app (data.package i)).hom ≫
        fiberReselectedPath (data.map H)
          (transportEdgeReselectionAlongNaturalIso data comparison reselection)
          path := by
  induction path with
  | nil vertex =>
      simp only [fiberReselectedPath, Category.id_comp]
      exact (Category.comp_id _).symm
  | cons edge tail inductionHypothesis =>
      simp only [fiberReselectedPath]
      rw [Category.assoc, inductionHypothesis, ← Category.assoc,
        fiberReselectedEdge_naturality_iso data comparison reselection edge,
        Category.assoc]

/-- Coherence is invariant under direct transport of an arbitrary target
reselection across a natural isomorphism. -/
theorem coherentAt_naturalIso
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {F H : CoreFiber X ⥤ CoreFiber Y} (comparison : F ≅ H)
    (reselection : EdgeReselection (data.map F).toLiftData)
    (coherent : CoherentAt (data.transported F) reselection) :
    CoherentAt (data.transported H)
      (transportEdgeReselectionAlongNaturalIso data comparison reselection) := by
  intro cell
  let target := G.twoTarget cell
  let source := G.twoSource cell
  let left := G.twoLeft cell
  let right := G.twoRight cell
  let cSource := (comparison.app (data.package source)).hom
  let cTarget := (comparison.app (data.package target)).hom
  have hleft := fiberReselectedPath_naturality_iso data comparison reselection left
  have hright := fiberReselectedPath_naturality_iso data comparison reselection right
  have hcomparator :
      cTarget ≫
        (packageFiberAutCoreFiberEquiv ((data.map H).package target)
          ((data.map H).comparator cell)).hom =
      (packageFiberAutCoreFiberEquiv ((data.map F).package target)
          ((data.map F).comparator cell)).hom ≫ cTarget := by
    have naturality := comparison.hom.naturality
      (packageFiberAutCoreFiberEquiv (data.package target)
        (data.comparator cell)).hom
    simpa [cTarget, target, FiberwiseAdmissibleTransportData.map,
      coreFiberFunctorPackageAutHom_hom] using naturality
  have hcoherentFiber :
      fiberReselectedPath (data.map F) reselection left ≫
          (packageFiberAutCoreFiberEquiv ((data.map F).package target)
            ((data.map F).comparator cell)).hom =
        fiberReselectedPath (data.map F) reselection right := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    change
      (fiberReselectedPath (data.map F) reselection left).1 ≫
          (packageFiberAutCoreFiberEquiv ((data.map F).package target)
            ((data.map F).comparator cell)).hom.1 =
        (fiberReselectedPath (data.map F) reselection right).1
    simpa only [left, right, target, fiberReselectedPath_val,
      packageFiberAutCoreFiberEquiv_hom_val] using coherent cell
  have htargetFiber :
      fiberReselectedPath (data.map H)
          (transportEdgeReselectionAlongNaturalIso data comparison reselection)
          left ≫
        (packageFiberAutCoreFiberEquiv ((data.map H).package target)
          ((data.map H).comparator cell)).hom =
      fiberReselectedPath (data.map H)
        (transportEdgeReselectionAlongNaturalIso data comparison reselection)
        right := by
    apply (cancel_epi cSource).1
    calc
      cSource ≫
          (fiberReselectedPath (data.map H)
            (transportEdgeReselectionAlongNaturalIso data comparison reselection)
            left ≫
          (packageFiberAutCoreFiberEquiv ((data.map H).package target)
            ((data.map H).comparator cell)).hom) =
        (fiberReselectedPath (data.map F) reselection left ≫ cTarget) ≫
          (packageFiberAutCoreFiberEquiv ((data.map H).package target)
            ((data.map H).comparator cell)).hom := by
              simpa only [Category.assoc] using congrArg
                (fun q => q ≫
                  (packageFiberAutCoreFiberEquiv ((data.map H).package target)
                    ((data.map H).comparator cell)).hom) hleft.symm
      _ = fiberReselectedPath (data.map F) reselection left ≫
          ((packageFiberAutCoreFiberEquiv ((data.map F).package target)
            ((data.map F).comparator cell)).hom ≫ cTarget) := by
              simp only [Category.assoc]
              rw [hcomparator]
      _ = fiberReselectedPath (data.map F) reselection right ≫ cTarget := by
              rw [← Category.assoc, hcoherentFiber]
      _ = cSource ≫
          fiberReselectedPath (data.map H)
            (transportEdgeReselectionAlongNaturalIso data comparison reselection)
            right := hright
  have htotal := congrArg (fun morphism => morphism.1) htargetFiber
  change
    (fiberReselectedPath (data.map H)
        (transportEdgeReselectionAlongNaturalIso data comparison reselection)
        left).1 ≫
      (packageFiberAutCoreFiberEquiv ((data.map H).package target)
        ((data.map H).comparator cell)).hom.1 =
    (fiberReselectedPath (data.map H)
      (transportEdgeReselectionAlongNaturalIso data comparison reselection)
      right).1 at htotal
  simpa only [left, right, target,
    FiberwiseAdmissibleTransportData.transported,
    FiberwiseAdmissibleTransportData.toTransportData,
    fiberReselectedPath_val, packageFiberAutCoreFiberEquiv_hom_val] using htotal

/-- Coherence is equivalent at naturally isomorphic target diagnostics. -/
theorem coherentAt_naturalIso_iff
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {F H : CoreFiber X ⥤ CoreFiber Y} (comparison : F ≅ H)
    (reselection : EdgeReselection (data.map F).toLiftData) :
    CoherentAt (data.transported F) reselection ↔
      CoherentAt (data.transported H)
        (transportEdgeReselectionAlongNaturalIso data comparison reselection) := by
  constructor
  · exact coherentAt_naturalIso data comparison reselection
  · intro coherent
    have back := coherentAt_naturalIso data comparison.symm
      (transportEdgeReselectionAlongNaturalIso data comparison reselection)
      coherent
    simpa using back

/-- Obstruction vanishing is invariant under a natural isomorphism of target
diagnostic functors. -/
theorem transportObstructionVanishes_naturalIso_iff
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {F H : CoreFiber X ⥤ CoreFiber Y} (comparison : F ≅ H) :
    TransportObstructionVanishes (data.transported F) ↔
      TransportObstructionVanishes (data.transported H) := by
  rw [transportObstructionVanishes_iff_coherentizable,
    transportObstructionVanishes_iff_coherentizable]
  constructor
  · rintro ⟨reselection, coherent⟩
    exact ⟨transportEdgeReselectionAlongNaturalIso data comparison reselection,
      coherentAt_naturalIso data comparison reselection coherent⟩
  · rintro ⟨reselection, coherent⟩
    exact ⟨transportEdgeReselectionAlongNaturalIso data comparison.symm reselection,
      coherentAt_naturalIso data comparison.symm reselection coherent⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
