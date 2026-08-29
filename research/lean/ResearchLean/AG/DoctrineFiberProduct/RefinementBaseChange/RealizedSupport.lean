import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Projection

/-!
# Realized-support reflection and authored package transport

The condition below speaks only about extraction at a selected source, and only
when the target point carries an actual core package.  It is converted here to
the selected-family equality consumed by the complete package constructor.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-- Reverse extraction on package-realized targets of a pointed refinement. -/
def RealizedLocusExtractionReflecting {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (r : PointedRefinementHom X Y) : Prop :=
  Nonempty (CoreFiber Y) → ∀ atom : U.Atom,
    Y.doctrine.extracts Y.source (r.doctrineHom.atomMap atom) →
      X.doctrine.extracts X.source atom

/-- Realized support at one compatible source of a raw configuration. -/
def RealizedAt {U : AtomCarrier.{u}} (C : RefinementBCConfiguration U)
    (p : C.CompatibleSource) : Prop :=
  Nonempty (CoreFiber (C.targetPointAt p))

/-- The card-fixed condition holds at every compatible source. -/
def ConfigurationRealizedLocusExtractionReflecting {U : AtomCarrier.{u}}
    (C : RefinementBCConfiguration U) : Prop :=
  ∀ p : C.CompatibleSource,
    RealizedLocusExtractionReflecting (C.baseRefinementAt p)

/-- Reflection at an actual target package is exactly the selected family equality. -/
theorem selected_family_eq_of_realized_reflection
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (target : CoreFiber Y) :
    target.1.family =
      (X.doctrine.atomize X.source).transport r.doctrineHom.atomEquiv := by
  rcases target with ⟨Q, hQ⟩
  subst Y
  have hrealized : Nonempty (CoreFiber (packagePoint Q)) := ⟨⟨Q, rfl⟩⟩
  apply AtomFamily.ext
  intro targetAtom
  constructor
  · intro hmem
    have htarget := (Q.family_mem_iff_extracts targetAtom).mp hmem
    let sourceAtom := r.doctrineHom.atomEquiv.symm targetAtom
    have hsource : X.doctrine.extracts X.source sourceAtom :=
      condition hrealized sourceAtom (by
        have heq : r.doctrineHom.atomMap sourceAtom = targetAtom := by
          rw [← r.doctrineHom.atomEquiv_apply]
          exact r.doctrineHom.atomEquiv.apply_symm_apply targetAtom
        rw [heq]
        exact htarget)
    exact ⟨sourceAtom, hsource,
      r.doctrineHom.atomEquiv.apply_symm_apply targetAtom⟩
  · rintro ⟨sourceAtom, hsource, rfl⟩
    have htarget := r.doctrineHom.extraction_forward X.source sourceAtom hsource
    rw [r.source_eq] at htarget
    apply (Q.family_mem_iff_extracts _).mpr
    exact htarget

/-- The selected-family datum used to author the source package. -/
noncomputable def selectedTransportDataOfRealizedReflection
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (target : CoreFiber Y) :
    SelectedRefinementTransport.SelectedTransportData X target.1 where
  atomEquiv := r.doctrineHom.atomEquiv
  family_eq := selected_family_eq_of_realized_reflection r condition target

/-- Construct the authored source package and its complete refinement lift. -/
noncomputable def refinementLiftOfRealizedReflection
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (target : CoreFiber Y) : RefinementCartesianLift r target := by
  rcases target with ⟨Q, hQ⟩
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition ⟨Q, rfl⟩
  let P := SelectedRefinementTransport.inverseCorePackage Q data
  let φ : RefinementPackageHom ⟨P⟩ ⟨Q⟩ := {
    base := r
    upper := SelectedRefinementTransport.inverseCorePackageForwardUpper Q data
    atomEquiv_eq := rfl
  }
  exact {
    domain := P
    hom := φ
    isStronglyCartesian :=
      refinementPackageHom_isStronglyCartesian_of_upper_inverse φ
        (SelectedRefinementTransport.inverseCorePackageBackwardUpper Q data)
        (SelectedRefinementTransport.inverseCorePackageForward_comp_backward Q data)
        (SelectedRefinementTransport.inverseCorePackageBackward_comp_forward Q data)
  }

/-- The fixed geometric condition constructs an objectwise refinement cleavage. -/
noncomputable def refinementCleavageOfRealizedReflection
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r) :
    RefinementCartesianCleavage r where
  lift target := refinementLiftOfRealizedReflection r condition target

/-- A refinement cartesian cleavage forces reverse extraction on realized targets. -/
theorem realizedReflectionOfRefinementCleavage
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y)
    (cleavage : RefinementCartesianCleavage r) :
    RealizedLocusExtractionReflecting r := by
  intro hrealized atom htarget
  rcases hrealized with ⟨target⟩
  let lift := cleavage.lift target
  rcases target with ⟨Q, hQ⟩
  have hupper := lift.hom.upper.extraction_eq
  have hmemQ : Q.family.mem (r.doctrineHom.atomEquiv atom) := by
    apply (Q.family_mem_iff_extracts _).mpr
    subst Y
    simpa [RefinementDoctrineHom.atomEquiv_apply] using htarget
  have hmemP : lift.domain.family.mem atom := by
    rw [hupper] at hmemQ
    rcases hmemQ with ⟨sourceAtom, hsourceAtom, heq⟩
    letI := lift.isStronglyCartesian
    have hfac := CategoryTheory.IsHomLift.fac'
      (refinementPackageProjection U) r lift.hom
    have hbaseAtom := congrArg
      (fun base => base.doctrineHom.atomMap atom) hfac
    have hbaseAtom' : lift.hom.base.doctrineHom.atomMap atom =
        r.doctrineHom.atomMap atom := by
      simpa [refinementPackageProjection, pointedRefinementCategory,
        PointedRefinementHom.comp, refinementHomComp] using hbaseAtom
    have hatom : lift.hom.upper.atomEquiv atom =
        r.doctrineHom.atomEquiv atom := by
      rw [lift.hom.atomEquiv_eq]
      rw [lift.hom.base.doctrineHom.atomEquiv_apply,
        r.doctrineHom.atomEquiv_apply]
      exact hbaseAtom'
    have : sourceAtom = atom := by
      apply lift.hom.upper.atomEquiv.injective
      rw [heq, hatom]
    exact this ▸ hsourceAtom
  have hsource := (lift.domain.family_mem_iff_extracts atom).mp hmemP
  letI := lift.isStronglyCartesian
  have hdomainWrapper := CategoryTheory.IsHomLift.domain_eq
    (refinementPackageProjection U) r lift.hom
  have hdomain : packagePoint lift.domain = X :=
    congrArg PointedRefinementObject.pointed hdomainWrapper
  rw [← hdomain]
  exact hsource

/-- Local support classification for one pointed refinement. -/
theorem refinementCartesianCleavage_iff_realizedReflection
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y) :
    Nonempty (RefinementCartesianCleavage r) ↔
      RealizedLocusExtractionReflecting r := by
  constructor
  · rintro ⟨cleavage⟩
    exact realizedReflectionOfRefinementCleavage r cleavage
  · intro condition
    exact ⟨refinementCleavageOfRealizedReflection r condition⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
