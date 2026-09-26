import ResearchLean.AG.LocalSemanticReconstruction.G124ComparisonObservationTransport
import ResearchLean.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition
import Formal.Util.AssertStandardAxioms

/-! Local comparison normalization and primitive kernel conditions for
design G-124 Part III-3. -/

namespace AAT.AG.LocalSemanticReconstruction.G124PrimitiveKernel

open CategoryTheory CategoryTheory.Idempotents
open AtomFoundation DoctrineFiberProduct GeometryTransport TransportCoherence
open AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition
open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel
open IndependentAATPrimitiveReconstruction
open IndependentGeometryCategoryReconstruction
open RealizationReconstruction
open RealizationComparisonIdempotents
open FullGeometryNormalization
open G124PrimitiveNormalization

universe u v

/-- A functor maps comparison-preserving endpoint pairs to the comparison
group of the mapped arrow; fullness is needed only to invert this map. -/
noncomputable def comparisonHomOfFunctor
    {C : Type u} {D : Type v} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c →*
      GeneratedArrowComparisonSubgroup (F.map c) where
  toFun pair :=
    ⟨(functorAutomorphismHom F X pair.1.1,
      functorAutomorphismHom F Y pair.1.2), by
      change F.map pair.1.1.hom ≫ F.map c =
        F.map c ≫ F.map pair.1.2.hom
      rw [← F.map_comp, ← F.map_comp, pair.2]⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_one (functorAutomorphismHom F X)
    · exact map_one (functorAutomorphismHom F Y)
  map_mul' first second := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul (functorAutomorphismHom F X) first.1.1 second.1.1
    · exact map_mul (functorAutomorphismHom F Y) first.1.2 second.1.2

/-- A proved equality of comparison arrows changes only the square
predicate; the two endpoint automorphisms are retained verbatim. -/
noncomputable def comparisonArrowEqMulEquiv
    {C : Type u} [Category C] {X Y : C} {c d : X ⟶ Y} (h : c = d) :
    GeneratedArrowComparisonSubgroup c ≃*
      GeneratedArrowComparisonSubgroup d := by
  cases h
  exact MulEquiv.refl _

theorem comparisonArrowEqMulEquiv_val
    {C : Type u} [Category C] {X Y : C} {c d : X ⟶ Y}
    (h : c = d) (pair : GeneratedArrowComparisonSubgroup c) :
    (comparisonArrowEqMulEquiv h pair).1 = pair.1 := by
  cases h
  rfl

/-- The accepted representative Hom equivalence restricts to the two
object-admissible full subcategories without a new condition on morphisms. -/
noncomputable def admissibleReadingFullyFaithful (U : AtomCarrier.{u}) :
    (representativeAdmissibleReading.{u, v} U).FullyFaithful where
  preimage {X Y} f := ObjectProperty.homMk
    ((representativeReadingHomEquiv X.obj Y.obj).symm f.hom)
  map_preimage {X Y} f := by
    apply ObjectProperty.hom_ext
    exact (representativeReadingHomEquiv X.obj Y.obj).apply_symm_apply f.hom
  preimage_map {X Y} f := by
    apply ObjectProperty.hom_ext
    exact (representativeReadingHomEquiv X.obj Y.obj).symm_apply_apply f.hom

/-- The reverse primitive assembly is fully faithful on every lawful local
Hom.  Its preimage is the complete original Hom reader on the same primitive
source and target data. -/
noncomputable def admissibleAssemblyFullyFaithful (U : AtomCarrier.{u}) :
    (representativeAdmissibleAssembly.{u, v} U).FullyFaithful where
  preimage {X Y} f := ObjectProperty.homMk
    (IndependentGeometryHomPrimitive.NativeReader.representativeHomReadingEquiv
      (s := objectData X.obj.localObject) (t := objectData Y.obj.localObject) f.hom)
  map_preimage {X Y} f := by
    apply ObjectProperty.hom_ext
    exact (IndependentGeometryHomPrimitive.NativeReader.representativeHomReadingEquiv
      (s := objectData X.obj.localObject)
      (t := objectData Y.obj.localObject)).symm_apply_apply f.hom
  preimage_map {X Y} f := by
    apply ObjectProperty.hom_ext
    exact (IndependentGeometryHomPrimitive.NativeReader.representativeHomReadingEquiv
      (s := objectData X.obj.localObject)
      (t := objectData Y.obj.localObject)).apply_symm_apply f.hom

/-- Full raw comparison groups on admissible native and primitive objects
are equivalent for every comparison arrow. -/
noncomputable def admissibleRawComparisonEquiv {U : AtomCarrier.{u}}
    {X Y : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c ≃*
      GeneratedArrowComparisonSubgroup
        ((representativeAdmissibleReading U).map c) :=
  generatedArrowComparisonMulEquivOfFullyFaithful
    (representativeAdmissibleReading U)
    (admissibleReadingFullyFaithful U) c

/-- The G-122 raw comparison carrier and the general displayed-arrow
comparison carrier have the same endpoint square and group law. -/
noncomputable def nativeRawGeneratedEquiv {U : AtomCarrier.{u}}
    {X Y : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : X ⟶ Y) :
    rawGeometryNormalizationComparisonSubgroup c ≃*
      GeneratedArrowComparisonSubgroup c :=
  MulEquiv.refl _

noncomputable def nativeNormalizedGeneratedEquiv {U : AtomCarrier.{u}}
    {X Y : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : X ⟶ Y) :
    normalizedGeometryComparisonSubgroup c ≃*
      GeneratedArrowComparisonSubgroup ((geometryNormalizationFunctor U).map c) :=
  MulEquiv.refl _

/-- Normalize a comparison-preserving pair by the locally constructed
projectors.  Both endpoints are mapped by the actual local normalization
functor, so the square is obtained by functoriality. -/
noncomputable def localComparisonNormalization {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c →*
      GeneratedArrowComparisonSubgroup ((localNormalizationFunctor U).map c) where
  toFun pair :=
    ⟨(functorAutomorphismHom (localNormalizationFunctor U) X pair.1.1,
      functorAutomorphismHom (localNormalizationFunctor U) Y pair.1.2), by
      change (localNormalizationFunctor U).map pair.1.1.hom ≫
          (localNormalizationFunctor U).map c =
        (localNormalizationFunctor U).map c ≫
          (localNormalizationFunctor U).map pair.1.2.hom
      rw [← Functor.map_comp, ← Functor.map_comp, pair.2]⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_one (functorAutomorphismHom (localNormalizationFunctor U) X)
    · exact map_one (functorAutomorphismHom (localNormalizationFunctor U) Y)
  map_mul' first second := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul (functorAutomorphismHom (localNormalizationFunctor U) X)
        first.1.1 second.1.1
    · exact map_mul (functorAutomorphismHom (localNormalizationFunctor U) Y)
        first.1.2 second.1.2

/-- Normalize all endpoint automorphism pairs, including those that do not
preserve a selected comparison square. -/
noncomputable def localEndpointNormalization {U : AtomCarrier.{u}}
    (X Y : RepresentativeAdmissibleLocal.{u, v} U) :
    (Aut X × Aut Y) →*
      (Aut ((localNormalizationFunctor U).obj X) ×
        Aut ((localNormalizationFunctor U).obj Y)) :=
  MonoidHom.prodMap
    (functorAutomorphismHom (localNormalizationFunctor U) X)
    (functorAutomorphismHom (localNormalizationFunctor U) Y)

/-- The two native paths have literally the same normalized comparison
arrow after assembling its primitive local source. -/
theorem normalizationAssemblyArrowEq {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    (normalizedRepresentativeAssembly U).map
        ((localNormalizationFunctor U).map c) =
      (geometryNormalizationFunctor U).map
        ((representativeAdmissibleAssembly U).map c) := by
  apply Karoubi.Hom.ext
  exact normalization_assembly_map U c

/-- Full faithfulness of primitive assembly persists on the normalized
Karoubi Hom types; the local sandwich law is reflected by its Hom injection. -/
noncomputable def normalizedAssemblyFullyFaithful (U : AtomCarrier.{u}) :
    (normalizedRepresentativeAssembly.{u, v} U).FullyFaithful where
  preimage {X Y} f :=
    { f := (admissibleAssemblyFullyFaithful U).preimage f.f
      comm := by
        apply (admissibleAssemblyFullyFaithful U).map_injective
        simpa only [normalizedRepresentativeKaroubiObject,
          normalizedGeometryKaroubiObject, Functor.map_comp,
          representativeAdmissibleAssembly_map_projector,
          (admissibleAssemblyFullyFaithful U).map_preimage] using f.comm }
  map_preimage {X Y} f := by
    apply Karoubi.Hom.ext
    exact (admissibleAssemblyFullyFaithful U).map_preimage f.f
  preimage_map {X Y} f := by
    apply Karoubi.Hom.ext
    exact (admissibleAssemblyFullyFaithful U).preimage_map f.f

noncomputable def rawComparisonAssemblyEquiv {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c ≃*
      GeneratedArrowComparisonSubgroup
        ((representativeAdmissibleAssembly U).map c) :=
  generatedArrowComparisonMulEquivOfFullyFaithful
    (representativeAdmissibleAssembly U)
    (admissibleAssemblyFullyFaithful U) c

theorem rawComparisonAssemblyEquiv_val {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    (rawComparisonAssemblyEquiv c pair).1 =
      (comparisonHomOfFunctor (representativeAdmissibleAssembly U) c pair).1 := by
  rfl

noncomputable def normalizedComparisonAssemblyEquiv {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup ((localNormalizationFunctor U).map c) ≃*
      GeneratedArrowComparisonSubgroup
        ((normalizedRepresentativeAssembly U).map
          ((localNormalizationFunctor U).map c)) :=
  generatedArrowComparisonMulEquivOfFullyFaithful
    (normalizedRepresentativeAssembly U)
    (normalizedAssemblyFullyFaithful U)
    ((localNormalizationFunctor U).map c)

theorem normalizedComparisonAssemblyEquiv_val {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup ((localNormalizationFunctor U).map c)) :
    (normalizedComparisonAssemblyEquiv c pair).1 =
      (comparisonHomOfFunctor (normalizedRepresentativeAssembly U)
        ((localNormalizationFunctor U).map c) pair).1 := by
  rfl

/-- Identify the normalized comparison after local assembly with the native
normalized comparison at the exact arrow proved in the assembly square. -/
noncomputable def normalizedComparisonAssemblyEquivNative
    {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup ((localNormalizationFunctor U).map c) ≃*
      GeneratedArrowComparisonSubgroup
        ((geometryNormalizationFunctor U).map
          ((representativeAdmissibleAssembly U).map c)) :=
  (normalizedComparisonAssemblyEquiv c).trans
    (comparisonArrowEqMulEquiv (normalizationAssemblyArrowEq (U := U) c))

/-- Native normalization on the ordinary displayed comparison group, with
the accepted G-122 raw and normalized subgroup carriers identified exactly. -/
noncomputable def nativeComparisonNormalization {U : AtomCarrier.{u}}
    {X Y : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c →*
      GeneratedArrowComparisonSubgroup ((geometryNormalizationFunctor U).map c) :=
  (nativeNormalizedGeneratedEquiv c).toMonoidHom.comp
    ((geometryNormalizationComparisonSubgroupHom c).comp
      (nativeRawGeneratedEquiv c).symm.toMonoidHom)

theorem nativeComparisonNormalization_val {U : AtomCarrier.{u}}
    {X Y : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    (nativeComparisonNormalization c pair).1 =
      (comparisonHomOfFunctor (geometryNormalizationFunctor U) c pair).1 := by
  rfl

/-- Normalizing a primitive comparison and assembling it gives the same
complete endpoint automorphisms as assembling the raw comparison and then
applying native normalization.  The arrows themselves agree by the preceding
normalization square. -/
theorem normalizationComparisonSquare {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    (comparisonHomOfFunctor (normalizedRepresentativeAssembly U)
      ((localNormalizationFunctor U).map c)
      (localComparisonNormalization c pair)).1 =
    (comparisonHomOfFunctor (geometryNormalizationFunctor U)
      ((representativeAdmissibleAssembly U).map c)
      (comparisonHomOfFunctor (representativeAdmissibleAssembly U) c pair)).1 := by
  apply Prod.ext
  · apply Iso.ext
    apply Karoubi.Hom.ext
    exact normalization_assembly_map U pair.1.1.hom
  · apply Iso.ext
    apply Karoubi.Hom.ext
    exact normalization_assembly_map U pair.1.2.hom

theorem normalizationComparison_commutes {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    normalizedComparisonAssemblyEquivNative c
        (localComparisonNormalization c pair) =
      nativeComparisonNormalization
        ((representativeAdmissibleAssembly U).map c)
        (rawComparisonAssemblyEquiv c pair) := by
  have hraw :
      comparisonHomOfFunctor (representativeAdmissibleAssembly U) c pair =
        rawComparisonAssemblyEquiv c pair :=
    Subtype.ext (rawComparisonAssemblyEquiv_val c pair).symm
  apply Subtype.ext
  calc
    (normalizedComparisonAssemblyEquivNative c
        (localComparisonNormalization c pair)).1 =
        (comparisonHomOfFunctor (normalizedRepresentativeAssembly U)
          ((localNormalizationFunctor U).map c)
          (localComparisonNormalization c pair)).1 := by
            exact (comparisonArrowEqMulEquiv_val
              (normalizationAssemblyArrowEq (U := U) c)
              (normalizedComparisonAssemblyEquiv c
                (localComparisonNormalization c pair))).trans
              (normalizedComparisonAssemblyEquiv_val c _)
    _ = (comparisonHomOfFunctor (geometryNormalizationFunctor U)
      ((representativeAdmissibleAssembly U).map c)
      (comparisonHomOfFunctor (representativeAdmissibleAssembly U) c pair)).1 :=
        normalizationComparisonSquare c pair
    _ = (nativeComparisonNormalization
      ((representativeAdmissibleAssembly U).map c)
      (rawComparisonAssemblyEquiv c pair)).1 := by
        rw [hraw]
        exact (nativeComparisonNormalization_val _ _).symm

/-- The restricted normalization kernel is transported through the actual
raw and normalized comparison equivalences. -/
noncomputable def localNativeRestrictedKernelEquiv {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    (localComparisonNormalization c).ker ≃*
      (nativeComparisonNormalization
        ((representativeAdmissibleAssembly U).map c)).ker :=
  RestrictionKernelFiberTransport.kernelMulEquiv
    (localComparisonNormalization c)
    (nativeComparisonNormalization
      ((representativeAdmissibleAssembly U).map c))
    (rawComparisonAssemblyEquiv c)
    (normalizedComparisonAssemblyEquivNative c)
    (fun pair => (normalizationComparison_commutes c pair).symm)

/-- Every local normalization lift fiber is equivalent to its assembled
native lift fiber, with no surjectivity assumed for a general arrow. -/
noncomputable def localNativeRestrictedFiberEquiv {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y)
    (normalized : GeneratedArrowComparisonSubgroup
      ((localNormalizationFunctor U).map c)) :
    RestrictionKernelFiberTransport.Fiber
        (localComparisonNormalization c) normalized ≃
      RestrictionKernelFiberTransport.Fiber
        (nativeComparisonNormalization
          ((representativeAdmissibleAssembly U).map c))
        (normalizedComparisonAssemblyEquivNative c normalized) :=
  RestrictionKernelFiberTransport.fiberEquiv
    (localComparisonNormalization c)
    (nativeComparisonNormalization
      ((representativeAdmissibleAssembly U).map c))
    (rawComparisonAssemblyEquiv c)
    (normalizedComparisonAssemblyEquivNative c)
    (fun pair => (normalizationComparison_commutes c pair).symm)
    normalized

theorem localNativeRestrictedFiberEquiv_smul {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y)
    (normalized : GeneratedArrowComparisonSubgroup
      ((localNormalizationFunctor U).map c))
    (kernelElement : ((localComparisonNormalization c).ker)ᵐᵒᵖ)
    (point : RestrictionKernelFiberTransport.Fiber
      (localComparisonNormalization c) normalized) :
    localNativeRestrictedFiberEquiv c normalized
        (RestrictionKernelFiberTransport.rightKernelAction
          (localComparisonNormalization c) normalized kernelElement point) =
      RestrictionKernelFiberTransport.rightKernelAction
        (nativeComparisonNormalization
          ((representativeAdmissibleAssembly U).map c))
        (normalizedComparisonAssemblyEquivNative c normalized)
        (MulOpposite.op
          (localNativeRestrictedKernelEquiv c
            (MulOpposite.unop kernelElement)))
        (localNativeRestrictedFiberEquiv c normalized point) :=
  RestrictionKernelFiberTransport.fiberEquiv_smul
    (localComparisonNormalization c)
    (nativeComparisonNormalization
      ((representativeAdmissibleAssembly U).map c))
    (rawComparisonAssemblyEquiv c)
    (normalizedComparisonAssemblyEquivNative c)
    (fun pair => (normalizationComparison_commutes c pair).symm)
    normalized kernelElement point

/-- A comparison-preserving local normalization-kernel element is also in
the ambient endpoint kernel.  The reverse need not hold. -/
noncomputable def localRestrictedToAmbient {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    (localComparisonNormalization c).ker →*
      (localEndpointNormalization X Y).ker where
  toFun pair := ⟨pair.1.1, by
    have h := MonoidHom.mem_ker.mp pair.property
    apply MonoidHom.mem_ker.mpr
    exact congrArg Subtype.val h⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' first second := by
    apply Subtype.ext
    rfl

theorem localRestrictedToAmbient_injective {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    Function.Injective (localRestrictedToAmbient c) := by
  intro first second h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun k : (localEndpointNormalization X Y).ker => k.1) h

theorem localRestrictedToAmbient_mem_range_iff {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y)
    (ambient : (localEndpointNormalization X Y).ker) :
    ambient ∈ (localRestrictedToAmbient c).range ↔
      ambient.1 ∈ GeneratedArrowComparisonSubgroup c := by
  constructor
  · rintro ⟨restricted, equality⟩
    have h := congrArg (fun k : (localEndpointNormalization X Y).ker => k.1) equality
    change restricted.1.1 = ambient.1 at h
    rw [← h]
    exact restricted.1.property
  · intro h
    let restricted : (localComparisonNormalization c).ker :=
      ⟨⟨ambient.1, h⟩, by
        apply MonoidHom.mem_ker.mpr
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp ambient.property⟩
    refine ⟨restricted, ?_⟩
    apply Subtype.ext
    rfl

/-- Point-level kernel condition on four local arrows.  The inverse laws and
comparison square are checked before normalization.  The final two fields
compare every normalized primitive query with the Karoubi identities, whose
underlying arrows are the locally constructed projectors. -/
structure PrimitiveKernelPoints {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y)
    (sourceForward sourceBackward : X ⟶ X)
    (targetForward targetBackward : Y ⟶ Y) : Prop where
  source_forward_backward : sourceForward ≫ sourceBackward = 𝟙 X
  source_backward_forward : sourceBackward ≫ sourceForward = 𝟙 X
  target_forward_backward : targetForward ≫ targetBackward = 𝟙 Y
  target_backward_forward : targetBackward ≫ targetForward = 𝟙 Y
  comparison_square : sourceForward ≫ c = c ≫ targetForward
  normalized_source_point :
    ∀ query : IndependentGeometryHomPrimitive.Query.{u, v} U .representative,
      IndependentGeometryHomPrimitive.InvariantWitness.point _ _
          (((localNormalizationFunctor U).map sourceForward).f).hom.val query =
        IndependentGeometryHomPrimitive.InvariantWitness.point _ _
          (admissibleRepresentativeProjector X).hom.val query
  normalized_target_point :
    ∀ query : IndependentGeometryHomPrimitive.Query.{u, v} U .representative,
      IndependentGeometryHomPrimitive.InvariantWitness.point _ _
          (((localNormalizationFunctor U).map targetForward).f).hom.val query =
        IndependentGeometryHomPrimitive.InvariantWitness.point _ _
          (admissibleRepresentativeProjector Y).hom.val query

/-- The independently stated primitive conditions classify every element of
the restricted local normalization kernel, using point extensionality in
both directions. -/
theorem primitiveKernelPoints_iff {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    PrimitiveKernelPoints c pair.1.1.hom pair.1.1.inv
      pair.1.2.hom pair.1.2.inv ↔
      pair ∈ (localComparisonNormalization c).ker := by
  constructor
  · intro h
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply Prod.ext
    · apply Iso.ext
      apply Karoubi.Hom.ext
      apply ObjectProperty.hom_ext
      apply Subtype.ext
      apply IndependentGeometryHomPrimitive.InvariantWitness.point_ext
      exact h.normalized_source_point
    · apply Iso.ext
      apply Karoubi.Hom.ext
      apply ObjectProperty.hom_ext
      apply Subtype.ext
      apply IndependentGeometryHomPrimitive.InvariantWitness.point_ext
      exact h.normalized_target_point
  · intro h
    rw [MonoidHom.mem_ker] at h
    constructor
    · exact pair.1.1.hom_inv_id
    · exact pair.1.1.inv_hom_id
    · exact pair.1.2.hom_inv_id
    · exact pair.1.2.inv_hom_id
    · exact pair.property
    · intro query
      have hs := congrArg
        (fun p : GeneratedArrowComparisonSubgroup
          ((localNormalizationFunctor U).map c) => p.1.1.hom.f.hom.val) h
      simpa only [localComparisonNormalization, localNormalizationFunctor,
        normalizedRepresentativeKaroubiObject, admissibleRepresentativeProjector]
        using congrArg (fun f => IndependentGeometryHomPrimitive.InvariantWitness.point
          _ _ f query) hs
    · intro query
      have ht := congrArg
        (fun p : GeneratedArrowComparisonSubgroup
          ((localNormalizationFunctor U).map c) => p.1.2.hom.f.hom.val) h
      simpa only [localComparisonNormalization, localNormalizationFunctor,
        normalizedRepresentativeKaroubiObject, admissibleRepresentativeProjector]
        using congrArg (fun f => IndependentGeometryHomPrimitive.InvariantWitness.point
          _ _ f query) ht

/-- A local kernel presentation retains the four primitive local arrows and
the displayed inverse, comparison, and normalized-point equations.  No
native endpoint automorphism or completed kernel element is a field. -/
structure PrimitiveKernelCode {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) where
  sourceForward : X ⟶ X
  sourceBackward : X ⟶ X
  targetForward : Y ⟶ Y
  targetBackward : Y ⟶ Y
  valid : PrimitiveKernelPoints c sourceForward sourceBackward
    targetForward targetBackward

noncomputable def PrimitiveKernelCode.toLocalKernel {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} {c : X ⟶ Y}
    (code : PrimitiveKernelCode c) : (localComparisonNormalization c).ker := by
  let source : Aut X :=
    { hom := code.sourceForward
      inv := code.sourceBackward
      hom_inv_id := code.valid.source_forward_backward
      inv_hom_id := code.valid.source_backward_forward }
  let target : Aut Y :=
    { hom := code.targetForward
      inv := code.targetBackward
      hom_inv_id := code.valid.target_forward_backward
      inv_hom_id := code.valid.target_backward_forward }
  let pair : GeneratedArrowComparisonSubgroup c :=
    ⟨(source, target), code.valid.comparison_square⟩
  exact ⟨pair, (primitiveKernelPoints_iff c pair).mp code.valid⟩

noncomputable def PrimitiveKernelCode.ofLocalKernel {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} {c : X ⟶ Y}
    (kernel : (localComparisonNormalization c).ker) : PrimitiveKernelCode c where
  sourceForward := kernel.1.1.1.hom
  sourceBackward := kernel.1.1.1.inv
  targetForward := kernel.1.1.2.hom
  targetBackward := kernel.1.1.2.inv
  valid := (primitiveKernelPoints_iff c kernel.1).mpr kernel.2

/-- Both inverse laws hold on all local restricted-kernel elements, and
assembly of the four local arrows reconstructs every such element. -/
noncomputable def primitiveKernelEquiv {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    PrimitiveKernelCode c ≃ (localComparisonNormalization c).ker where
  toFun := PrimitiveKernelCode.toLocalKernel
  invFun := PrimitiveKernelCode.ofLocalKernel
  left_inv code := by
    cases code
    rfl
  right_inv kernel := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Iso.ext <;> rfl

noncomputable instance primitiveKernelGroup {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    Group (PrimitiveKernelCode c) :=
  (primitiveKernelEquiv c).group

/-- The primitive four-arrow code is multiplicatively equivalent to every
element of the locally normalized restricted comparison kernel. -/
noncomputable def primitiveKernelMulEquiv {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    PrimitiveKernelCode c ≃* (localComparisonNormalization c).ker where
  toEquiv := primitiveKernelEquiv c
  map_mul' _ _ := rfl

/-- The transported group law is the original automorphism composition on
the four local arrows; in categorical order the second forward arrow is
applied first. -/
theorem primitiveKernel_mul_sourceForward {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} {c : X ⟶ Y}
    (first second : PrimitiveKernelCode c) :
    (first * second).sourceForward =
      second.sourceForward ≫ first.sourceForward := rfl

theorem primitiveKernel_mul_targetForward {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} {c : X ⟶ Y}
    (first second : PrimitiveKernelCode c) :
    (first * second).targetForward =
      second.targetForward ≫ first.targetForward := rfl

/-- The ambient endpoint kernel has its own primitive presentation.  It
contains no comparison square, so it can have elements absent from the
restricted comparison kernel. -/
structure PrimitiveEndpointKernelCode {U : AtomCarrier.{u}}
    (X : RepresentativeAdmissibleLocal.{u, v} U) where
  forward : X ⟶ X
  backward : X ⟶ X
  forward_backward : forward ≫ backward = 𝟙 X
  backward_forward : backward ≫ forward = 𝟙 X
  normalized_point :
    ∀ query : IndependentGeometryHomPrimitive.Query.{u, v} U .representative,
      IndependentGeometryHomPrimitive.InvariantWitness.point _ _
          (((localNormalizationFunctor U).map forward).f).hom.val query =
        IndependentGeometryHomPrimitive.InvariantWitness.point _ _
          (admissibleRepresentativeProjector X).hom.val query

noncomputable def PrimitiveEndpointKernelCode.toKernel {U : AtomCarrier.{u}}
    {X : RepresentativeAdmissibleLocal.{u, v} U}
    (code : PrimitiveEndpointKernelCode X) :
    (functorAutomorphismHom (localNormalizationFunctor U) X).ker := by
  let aut : Aut X :=
    { hom := code.forward
      inv := code.backward
      hom_inv_id := code.forward_backward
      inv_hom_id := code.backward_forward }
  refine ⟨aut, ?_⟩
  apply MonoidHom.mem_ker.mpr
  apply Iso.ext
  apply Karoubi.Hom.ext
  apply ObjectProperty.hom_ext
  apply Subtype.ext
  apply IndependentGeometryHomPrimitive.InvariantWitness.point_ext
  exact code.normalized_point

noncomputable def PrimitiveEndpointKernelCode.ofKernel {U : AtomCarrier.{u}}
    {X : RepresentativeAdmissibleLocal.{u, v} U}
    (kernel : (functorAutomorphismHom (localNormalizationFunctor U) X).ker) :
    PrimitiveEndpointKernelCode X where
  forward := kernel.1.hom
  backward := kernel.1.inv
  forward_backward := kernel.1.hom_inv_id
  backward_forward := kernel.1.inv_hom_id
  normalized_point := by
    intro query
    have h := MonoidHom.mem_ker.mp kernel.property
    have hh := congrArg
      (fun aut : Aut ((localNormalizationFunctor U).obj X) => aut.hom.f.hom.val) h
    simpa only [localNormalizationFunctor, normalizedRepresentativeKaroubiObject,
      admissibleRepresentativeProjector] using
      congrArg (fun f => IndependentGeometryHomPrimitive.InvariantWitness.point
        _ _ f query) hh

noncomputable def primitiveEndpointKernelEquiv {U : AtomCarrier.{u}}
    (X : RepresentativeAdmissibleLocal.{u, v} U) :
    PrimitiveEndpointKernelCode X ≃
      (functorAutomorphismHom (localNormalizationFunctor U) X).ker where
  toFun := PrimitiveEndpointKernelCode.toKernel
  invFun := PrimitiveEndpointKernelCode.ofKernel
  left_inv code := by
    cases code
    rfl
  right_inv kernel := by
    apply Subtype.ext
    apply Iso.ext
    rfl

noncomputable instance primitiveEndpointKernelGroup {U : AtomCarrier.{u}}
    (X : RepresentativeAdmissibleLocal.{u, v} U) :
    Group (PrimitiveEndpointKernelCode X) :=
  (primitiveEndpointKernelEquiv X).group

noncomputable def primitiveEndpointKernelMulEquiv {U : AtomCarrier.{u}}
    (X : RepresentativeAdmissibleLocal.{u, v} U) :
    PrimitiveEndpointKernelCode X ≃*
      (functorAutomorphismHom (localNormalizationFunctor U) X).ker where
  toEquiv := primitiveEndpointKernelEquiv X
  map_mul' _ _ := rfl

/-- The ambient product kernel separates into its two endpoint kernels. -/
noncomputable def ambientKernelPairMulEquiv {U : AtomCarrier.{u}}
    (X Y : RepresentativeAdmissibleLocal.{u, v} U) :
    (functorAutomorphismHom (localNormalizationFunctor U) X).ker ×
      (functorAutomorphismHom (localNormalizationFunctor U) Y).ker ≃*
        (localEndpointNormalization X Y).ker where
  toFun pair := ⟨(pair.1.1, pair.2.1), by
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext
    · exact MonoidHom.mem_ker.mp pair.1.property
    · exact MonoidHom.mem_ker.mp pair.2.property⟩
  invFun ambient :=
    (⟨ambient.1.1, by
      have h := MonoidHom.mem_ker.mp ambient.property
      exact MonoidHom.mem_ker.mpr (congrArg Prod.fst h)⟩,
     ⟨ambient.1.2, by
      have h := MonoidHom.mem_ker.mp ambient.property
      exact MonoidHom.mem_ker.mpr (congrArg Prod.snd h)⟩)
  left_inv pair := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv ambient := by
    apply Subtype.ext
    rfl
  map_mul' first second := by
    apply Subtype.ext
    rfl

/-- Both ambient endpoint kernels are presented by local forward/backward
Homs and normalized primitive point equations. -/
noncomputable def primitiveAmbientKernelMulEquiv {U : AtomCarrier.{u}}
    (X Y : RepresentativeAdmissibleLocal.{u, v} U) :
    (PrimitiveEndpointKernelCode X × PrimitiveEndpointKernelCode Y) ≃*
      (localEndpointNormalization X Y).ker :=
  ((primitiveEndpointKernelMulEquiv X).prodCongr
    (primitiveEndpointKernelMulEquiv Y)).trans
      (ambientKernelPairMulEquiv X Y)

/-- Forget only the comparison square, keeping the two local endpoint
kernel codes and every primitive normalized point equation. -/
noncomputable def primitiveRestrictedToAmbient {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y) :
    PrimitiveKernelCode c →*
      (PrimitiveEndpointKernelCode X × PrimitiveEndpointKernelCode Y) where
  toFun code :=
    (⟨code.sourceForward, code.sourceBackward,
      code.valid.source_forward_backward, code.valid.source_backward_forward,
      code.valid.normalized_source_point⟩,
     ⟨code.targetForward, code.targetBackward,
      code.valid.target_forward_backward, code.valid.target_backward_forward,
      code.valid.normalized_target_point⟩)
  map_one' := by
    apply Prod.ext <;> rfl
  map_mul' first second := by
    apply Prod.ext <;> rfl

theorem primitiveRestrictedToAmbient_square {U : AtomCarrier.{u}}
    {X Y : RepresentativeAdmissibleLocal.{u, v} U} (c : X ⟶ Y)
    (code : PrimitiveKernelCode c) :
    primitiveAmbientKernelMulEquiv X Y (primitiveRestrictedToAmbient c code) =
      localRestrictedToAmbient c (primitiveKernelMulEquiv c code) := by
  apply Subtype.ext
  rfl

/-! The fixed finite-axis-fold input of G-122 is now read into the same
primitive local comparison category used above. -/

noncomputable abbrev fixedG122Carrier : AtomCarrier :=
  finiteAxisFoldG122FamilyInput.Carrier

local instance fixedG122AtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

noncomputable def fixedG122NativeArrow :=
  (authoredExactBarAlphaAdmissibleIsoAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible).hom

noncomputable def fixedG122LocalArrow :=
  (representativeAdmissibleReading fixedG122Carrier).map fixedG122NativeArrow

noncomputable abbrev fixedG122Source :=
  authoredExactDirectAdmissibleGeometryAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

noncomputable abbrev fixedG122Target :=
  authoredExactViaBaseAdmissibleGeometryAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

theorem admissibleAssembly_read_obj {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    (representativeAdmissibleAssembly U).obj
      ((representativeAdmissibleReading U).obj G) = G := by
  cases G with
  | mk geometry admissible =>
    change (⟨IndependentGeometryTableAssembly.assemble
      (objectData (representativeReadObject geometry).localObject),
      _⟩ : CanonicalNormalizationAdmissibleGeometry U) = ⟨geometry, admissible⟩
    have hobj : IndependentGeometryTableAssembly.assemble
        (objectData (representativeReadObject geometry).localObject) = geometry :=
      assemble_objectData_readFragments geometry
    exact ObjectProperty.FullSubcategory.ext hobj

theorem fullSubcategory_eqToHom_hom {C : Type u} [Category C]
    {P : ObjectProperty C} {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  cases h
  rfl

theorem admissibleAssembly_read_map {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ⟶ H) :
    (representativeAdmissibleAssembly U).map
        ((representativeAdmissibleReading U).map c) ≫
          eqToHom (admissibleAssembly_read_obj H) =
      eqToHom (admissibleAssembly_read_obj G) ≫ c := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    fullSubcategory_eqToHom_hom]
  have hmap := G124ProjectionObservationComponents.representativeAssembly_read_map
    (U := U) c.hom
  have hident :
      ((representativeAdmissibleAssembly U).map
        ((representativeAdmissibleReading U).map c)).hom =
      (representativeAssemblyFunctor U).map
        ((representativeReadingFunctor U).map c.hom) := rfl
  rw [hident, hmap]
  simp [representativeEndpointHomEquiv, representativeObjectIso,
    Iso.homCongr, Category.assoc]

theorem fixedG122AssemblyReadArrow :
    (representativeAdmissibleAssembly fixedG122Carrier).map
        fixedG122LocalArrow ≫
          eqToHom (admissibleAssembly_read_obj fixedG122Target) =
      eqToHom (admissibleAssembly_read_obj fixedG122Source) ≫
        fixedG122NativeArrow :=
  admissibleAssembly_read_map fixedG122NativeArrow


noncomputable def fixedG122RawComparisonEquiv :
    RawComparison ≃*
      GeneratedArrowComparisonSubgroup fixedG122LocalArrow :=
  (nativeRawGeneratedEquiv fixedG122NativeArrow).trans
    (admissibleRawComparisonEquiv fixedG122NativeArrow)

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124PrimitiveKernel

end AAT.AG.LocalSemanticReconstruction.G124PrimitiveKernel
