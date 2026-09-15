import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldNormalizedAxisProjection
import Formal.Util.AssertStandardAxioms

/-!
# A finite signature-fiber quotient of the normalized axis kernel

Besides permuting the three global signature axes, an endpoint automorphism
acts on the three coordinates over each axis.  On the axis kernel this joint
action preserves each fiber of `Fin 3 × Fin 3`; the coordinate law also fixes
the distinguished diagonal point `(i, i)`.

Every such finite table is constructed below from the primitive southwest
core, identity local geometry data, the fixed exact pull/top-transport route,
and canonical normalization.  No completed semantic automorphism or coverage
certificate is accepted as input.  The final decomposition leaves a smaller
signature-trivial kernel explicit: no coverage, finiteness, or triviality of
that remaining kernel is asserted here.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

set_option maxHeartbeats 1200000

local instance finiteAxisFoldNormalizedSignatureFiberAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The joint global-axis and coordinate action of a normalized endpoint
automorphism. -/
noncomputable def finiteAxisFoldNormalizedSignatureEquiv
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    Equiv.Perm (Fin 3 × Fin 3) where
  toFun value :=
    (automorphism.hom.f.hom.base.upper.axisMap value.1,
      automorphism.hom.f.hom.base.upper.coordinateEquiv value.1 value.2)
  invFun value :=
    (automorphism.inv.f.hom.base.upper.axisMap value.1,
      automorphism.inv.f.hom.base.upper.coordinateEquiv value.1 value.2)
  left_inv value := by
    apply Prod.ext
    · exact (finiteAxisFoldNormalizedAxisEquiv automorphism).left_inv value.1
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        (hom.f.hom.base.upper.coordinateEquiv value.1 value.2 : Fin 3))
      automorphism.hom_inv_id
    change automorphism.inv.f.hom.base.upper.coordinateEquiv
        (automorphism.hom.f.hom.base.upper.axisMap value.1)
        (automorphism.hom.f.hom.base.upper.coordinateEquiv value.1 value.2) =
      value.2 at equality
    exact equality
  right_inv value := by
    apply Prod.ext
    · exact (finiteAxisFoldNormalizedAxisEquiv automorphism).right_inv value.1
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        (hom.f.hom.base.upper.coordinateEquiv value.1 value.2 : Fin 3))
      automorphism.inv_hom_id
    change automorphism.hom.f.hom.base.upper.coordinateEquiv
        (automorphism.inv.f.hom.base.upper.axisMap value.1)
        (automorphism.inv.f.hom.base.upper.coordinateEquiv value.1 value.2) =
      value.2 at equality
    exact equality

/-- Projection from the full normalized endpoint automorphism group to its
finite joint signature action. -/
noncomputable def finiteAxisFoldNormalizedSignatureProjection :
    Aut FiniteAxisFoldNormalizedDirectGeometry →* Equiv.Perm (Fin 3 × Fin 3) where
  toFun := finiteAxisFoldNormalizedSignatureEquiv
  map_one' := by
    apply Equiv.ext
    intro value
    rfl
  map_mul' first second := by
    apply Equiv.ext
    intro value
    rfl

/-- Axis-preserving total-signature permutations fixing the coordinate selected
on each axis. -/
def finiteAxisFoldSignatureFiberPermutationSubgroup :
    Subgroup (Equiv.Perm (Fin 3 × Fin 3)) where
  carrier permutation :=
    (∀ value, (permutation value).1 = value.1) ∧
      ∀ axis, permutation (axis, axis) = (axis, axis)
  one_mem' := by
    constructor <;> intro <;> rfl
  mul_mem' := by
    intro first second first_mem second_mem
    constructor
    · intro value
      change (first (second value)).1 = value.1
      rw [first_mem.1, second_mem.1]
    · intro axis
      change first (second (axis, axis)) = (axis, axis)
      rw [second_mem.2, first_mem.2]
  inv_mem' := by
    intro permutation permutation_mem
    constructor
    · intro value
      have equality := permutation_mem.1 (permutation.symm value)
      rw [permutation.apply_symm_apply] at equality
      exact equality.symm
    · intro axis
      change permutation.symm (axis, axis) = (axis, axis)
      apply permutation.injective
      simpa using (permutation_mem.2 axis).symm

/-- The finite group of fiberwise, diagonal-fixing signature tables. -/
abbrev FiniteAxisFoldSignatureFiberPermutation :=
  finiteAxisFoldSignatureFiberPermutationSubgroup

/-- Axis-kernel membership makes the complete global axis map identity. -/
theorem finiteAxisFoldNormalizedAxisKernel_axisMap
    (remainder : FiniteAxisFoldNormalizedAxisKernel) :
    remainder.1.hom.f.hom.base.upper.axisMap = _root_.id := by
  apply funext
  intro axis
  have equality := congrArg
    (fun permutation : Equiv.Perm (Fin 3) => permutation axis)
    (MonoidHom.mem_ker.mp remainder.2)
  exact equality

/-- The joint signature action of every axis-kernel element belongs to the
finite fiberwise subgroup. -/
theorem finiteAxisFoldNormalizedAxisKernel_signature_mem
    (remainder : FiniteAxisFoldNormalizedAxisKernel) :
    finiteAxisFoldNormalizedSignatureProjection remainder.1 ∈
      finiteAxisFoldSignatureFiberPermutationSubgroup := by
  have axisMap_eq := finiteAxisFoldNormalizedAxisKernel_axisMap remainder
  constructor
  · intro value
    exact congrFun axisMap_eq value.1
  · intro axis
    have coordinateEquality :=
      remainder.1.hom.f.hom.base.upper.coordinate_eq FiniteModel.object axis
    change remainder.1.hom.f.hom.base.upper.coordinateEquiv axis axis =
      remainder.1.hom.f.hom.base.upper.axisMap axis at coordinateEquality
    apply Prod.ext
    · exact congrFun axisMap_eq axis
    · simpa [axisMap_eq] using coordinateEquality

/-- Restriction of the finite joint-signature projection to the complete axis
kernel. -/
noncomputable def finiteAxisFoldNormalizedAxisKernelSignatureProjection :
    FiniteAxisFoldNormalizedAxisKernel →*
      FiniteAxisFoldSignatureFiberPermutation where
  toFun remainder :=
    ⟨finiteAxisFoldNormalizedSignatureProjection remainder.1,
      finiteAxisFoldNormalizedAxisKernel_signature_mem remainder⟩
  map_one' := by
    apply Subtype.ext
    exact map_one finiteAxisFoldNormalizedSignatureProjection
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul finiteAxisFoldNormalizedSignatureProjection first.1 second.1

/-- Inverses of fiber-preserving tables preserve first coordinates too. -/
theorem finiteAxisFoldSignatureFiberPermutation_inv_first
    (permutation : FiniteAxisFoldSignatureFiberPermutation)
    (value : Fin 3 × Fin 3) :
    (permutation.1.symm value).1 = value.1 := by
  have equality := permutation.2.1 (permutation.1.symm value)
  rw [permutation.1.apply_symm_apply] at equality
  exact equality.symm

/-- Coordinate permutation on one fixed axis fiber. -/
noncomputable def finiteAxisFoldSignatureFiberEquiv
    (permutation : FiniteAxisFoldSignatureFiberPermutation)
    (axis : Fin 3) : Equiv.Perm (Fin 3) where
  toFun coordinate := (permutation.1 (axis, coordinate)).2
  invFun coordinate := (permutation.1.symm (axis, coordinate)).2
  left_inv coordinate := by
    have forwardPair : permutation.1 (axis, coordinate) =
        (axis, (permutation.1 (axis, coordinate)).2) := by
      apply Prod.ext
      · exact permutation.2.1 (axis, coordinate)
      · rfl
    have equality := permutation.1.symm_apply_apply (axis, coordinate)
    rw [forwardPair] at equality
    exact congrArg Prod.snd equality
  right_inv coordinate := by
    have inversePair : permutation.1.symm (axis, coordinate) =
        (axis, (permutation.1.symm (axis, coordinate)).2) := by
      apply Prod.ext
      · exact finiteAxisFoldSignatureFiberPermutation_inv_first
          permutation (axis, coordinate)
      · rfl
    have equality := permutation.1.apply_symm_apply (axis, coordinate)
    rw [inversePair] at equality
    exact congrArg Prod.snd equality

/-- Primitive exact-core action of a finite signature-fiber table.  All other
computational fields are retained from the identity exact change. -/
noncomputable def finiteAxisFoldSignatureFiberUpper
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage :=
  { SignedExactCoreReadingHom.refl finiteAxisFoldSupportPackage with
    coordinateEquiv := finiteAxisFoldSignatureFiberEquiv permutation
    coordinate_eq := by
      intro object axis
      change finiteAxisFoldSignatureFiberEquiv permutation axis axis = axis
      exact congrArg Prod.snd (permutation.2.2 axis) }

/-- Primitive signature-fiber table as a total package endomorphism over the
fixed pointed-doctrine identity. -/
noncomputable def finiteAxisFoldSignatureFiberTotal
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    PackageTotalHom finiteAxisFoldSupportPackage finiteAxisFoldSupportPackage where
  base := ExtInstHom.id (packagePoint finiteAxisFoldSupportPackage)
  upper := finiteAxisFoldSignatureFiberUpper permutation
  atomEquiv_eq := rfl

/-- Internal package composition applies `first` and then `second`; this is the
opposite argument order from multiplication in `Equiv.Perm`. -/
theorem finiteAxisFoldSignatureFiberTotal_comp
    (first second : FiniteAxisFoldSignatureFiberPermutation) :
    (finiteAxisFoldSignatureFiberTotal first).comp
        (finiteAxisFoldSignatureFiberTotal second) =
      finiteAxisFoldSignatureFiberTotal (second * first) := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  · apply SignedExactCoreReadingHom.ext
    · apply Equiv.ext
      intro atom
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · apply Function.hfunext rfl
      intro axis axis' axis_eq
      cases axis_eq
      apply heq_of_eq
      apply Equiv.ext
      intro coordinate
      change
        (second.1 (axis, (first.1 (axis, coordinate)).2)).2 =
          (second.1 (first.1 (axis, coordinate))).2
      have firstPair : first.1 (axis, coordinate) =
          (axis, (first.1 (axis, coordinate)).2) := by
        apply Prod.ext
        · exact first.2.1 (axis, coordinate)
        · rfl
      rw [← firstPair]

/-- The identity table gives the package identity. -/
theorem finiteAxisFoldSignatureFiberTotal_one :
    finiteAxisFoldSignatureFiberTotal 1 =
      PackageTotalHom.id finiteAxisFoldSupportPackage := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  · apply SignedExactCoreReadingHom.ext
    · apply Equiv.ext
      intro atom
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · apply Function.hfunext rfl
      intro axis axis' axis_eq
      cases axis_eq
      apply heq_of_eq
      apply Equiv.ext
      intro coordinate
      rfl

/-- Primitive coordinate-fiber changes do not alter the fixed raw restriction
system. -/
theorem finiteAxisFoldSignatureFiber_rawReindex
    (permutation : FiniteAxisFoldSignatureFiberPermutation)
    (system : LawAlgebra.RawAmbientRestrictionSystem
      finiteAxisFoldGeometryPackage.site finiteAxisFoldGeometryPackage.Coefficient) :
    rawReindex (G := finiteAxisFoldGeometryPackage)
      (H := finiteAxisFoldGeometryPackage)
      (finiteAxisFoldSignatureFiberTotal permutation) system = system := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

/-- Identity local geometry data over one primitive signature-fiber table. -/
noncomputable def finiteAxisFoldSignatureFiberGeometryReadHom
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    GeomReadHom finiteAxisFoldGeometryPackage finiteAxisFoldGeometryPackage
      (finiteAxisFoldSignatureFiberTotal permutation) where
  coverage := by
    constructor
    · intros
      assumption
    · intros
      assumption
    · intros
      assumption
    · intros
      assumption
    · intros
      assumption
    · intros
      assumption
    · intros
      assumption
    · intros
      assumption
    · intros
      assumption
  overlap := by
    constructor
    intro base left right
    exact Iso.refl _
  coefficientHom := RingHom.id Int
  raw_eq := by
    change finiteAxisFoldGeometryPackage.raw =
      rawReindex (finiteAxisFoldSignatureFiberTotal permutation)
        (finiteAxisFoldGeometryPackage.raw.baseChange (RingHom.id Int))
    have baseChange :
        finiteAxisFoldGeometryPackage.raw.baseChange (RingHom.id Int) =
          finiteAxisFoldGeometryPackage.raw := by
      simpa only using
        (LawAlgebra.RawAmbientRestrictionSystem.baseChange_id
          finiteAxisFoldGeometryPackage.raw)
    rw [baseChange]
    exact (finiteAxisFoldSignatureFiber_rawReindex permutation
      finiteAxisFoldGeometryPackage.raw).symm
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- Complete southwest geometry action of a primitive finite table. -/
noncomputable def finiteAxisFoldSignatureFiberGeometry
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    GeometryTotalHom finiteAxisFoldGeometryPackage finiteAxisFoldGeometryPackage where
  base := finiteAxisFoldSignatureFiberTotal permutation
  geometry := finiteAxisFoldSignatureFiberGeometryReadHom permutation

@[simp] theorem finiteAxisFoldSignatureFiberGeometry_packageBase
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    (finiteAxisFoldSignatureFiberGeometry permutation).base.base =
      ExtInstHom.id (packagePoint finiteAxisFoldGeometryPackage.core) := by
  rfl

private theorem finiteAxisFoldSignatureFiberGeometryReadHom_heq_of_base_eq
    {firstBase secondBase : PackageTotalHom
      finiteAxisFoldGeometryPackage.core finiteAxisFoldGeometryPackage.core}
    (first : GeomReadHom finiteAxisFoldGeometryPackage
      finiteAxisFoldGeometryPackage firstBase)
    (second : GeomReadHom finiteAxisFoldGeometryPackage
      finiteAxisFoldGeometryPackage secondBase)
    (base_eq : firstBase = secondBase)
    (coefficient_eq : first.coefficientHom = second.coefficientHom)
    (support_eq : HEq first.supportComp second.supportComp)
    (axis_eq : HEq first.axisComp second.axisComp)
    (observable_eq : HEq first.observableComp second.observableComp) :
    HEq first second := by
  cases base_eq
  exact heq_of_eq
    (GeomReadHom.ext coefficient_eq support_eq axis_eq observable_eq)

/-- Complete-geometry composition has the same internal order as package
composition. -/
theorem finiteAxisFoldSignatureFiberGeometry_comp
    (first second : FiniteAxisFoldSignatureFiberPermutation) :
    (finiteAxisFoldSignatureFiberGeometry first).comp
        (finiteAxisFoldSignatureFiberGeometry second) =
      finiteAxisFoldSignatureFiberGeometry (second * first) := by
  have base_eq := finiteAxisFoldSignatureFiberTotal_comp first second
  apply GeometryTotalHom.ext base_eq
  apply finiteAxisFoldSignatureFiberGeometryReadHom_heq_of_base_eq _ _ base_eq rfl
  · rfl
  · rfl
  · rfl

/-- The identity table gives the complete southwest geometry identity. -/
theorem finiteAxisFoldSignatureFiberGeometry_one :
    finiteAxisFoldSignatureFiberGeometry 1 =
      GeometryTotalHom.id finiteAxisFoldGeometryPackage := by
  have base_eq := finiteAxisFoldSignatureFiberTotal_one
  apply GeometryTotalHom.ext base_eq
  apply finiteAxisFoldSignatureFiberGeometryReadHom_heq_of_base_eq _ _ base_eq rfl
  · rfl
  · rfl
  · rfl

/-- Primitive table as a complete-geometry automorphism. -/
noncomputable def finiteAxisFoldSignatureFiberGeometryAut
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    Aut finiteAxisFoldGeometryPackage where
  hom := finiteAxisFoldSignatureFiberGeometry permutation
  inv := finiteAxisFoldSignatureFiberGeometry permutation⁻¹
  hom_inv_id := by
    change (finiteAxisFoldSignatureFiberGeometry permutation).comp
      (finiteAxisFoldSignatureFiberGeometry permutation⁻¹) = _
    rw [finiteAxisFoldSignatureFiberGeometry_comp]
    simpa using finiteAxisFoldSignatureFiberGeometry_one
  inv_hom_id := by
    change (finiteAxisFoldSignatureFiberGeometry permutation⁻¹).comp
      (finiteAxisFoldSignatureFiberGeometry permutation) = _
    rw [finiteAxisFoldSignatureFiberGeometry_comp]
    simpa using finiteAxisFoldSignatureFiberGeometry_one

/-- Primitive table as a southwest-fiber endomorphism. -/
noncomputable def finiteAxisFoldSouthwestSignatureFiberHom
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    finiteAxisFoldSouthwestGeometryFiber ⟶ finiteAxisFoldSouthwestGeometryFiber := by
  refine ⟨finiteAxisFoldSignatureFiberGeometry permutation, ?_⟩
  apply CategoryTheory.IsHomLift.of_commsq
    (crossStageProjection.{0, 0} FiniteModel.carrier)
    (𝟙 finiteAxisFoldBCDatumSquare.context.square.semantic.square.southwest)
    (finiteAxisFoldSignatureFiberGeometry permutation)
    finiteAxisFoldSouthwestGeometryFiber.2
    finiteAxisFoldSouthwestGeometryFiber.2
  change (finiteAxisFoldSignatureFiberGeometry permutation).base.base ≫
      eqToHom finiteAxisFoldSouthwestGeometryFiber.2 =
    eqToHom finiteAxisFoldSouthwestGeometryFiber.2 ≫ 𝟙 _
  rw [finiteAxisFoldSignatureFiberGeometry_packageBase]
  change ExtInstHom.id (packagePoint finiteAxisFoldGeometryPackage.core) =
    ExtInstHom.id (packagePoint finiteAxisFoldGeometryPackage.core)
  rfl

/-- Primitive table as a southwest-fiber automorphism. -/
noncomputable def finiteAxisFoldSouthwestSignatureFiberAut
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    Aut finiteAxisFoldSouthwestGeometryFiber where
  hom := finiteAxisFoldSouthwestSignatureFiberHom permutation
  inv := finiteAxisFoldSouthwestSignatureFiberHom permutation⁻¹
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    change (finiteAxisFoldSignatureFiberGeometry permutation).comp
      (finiteAxisFoldSignatureFiberGeometry permutation⁻¹) = _
    rw [finiteAxisFoldSignatureFiberGeometry_comp]
    simpa using finiteAxisFoldSignatureFiberGeometry_one
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    change (finiteAxisFoldSignatureFiberGeometry permutation⁻¹).comp
      (finiteAxisFoldSignatureFiberGeometry permutation) = _
    rw [finiteAxisFoldSignatureFiberGeometry_comp]
    simpa using finiteAxisFoldSignatureFiberGeometry_one

/-- Southwest primitive tables form a group homomorphism. -/
noncomputable def finiteAxisFoldSouthwestSignatureFiberSectionHom :
    FiniteAxisFoldSignatureFiberPermutation →*
      Aut finiteAxisFoldSouthwestGeometryFiber where
  toFun := finiteAxisFoldSouthwestSignatureFiberAut
  map_one' := by
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact finiteAxisFoldSignatureFiberGeometry_one
  map_mul' first second := by
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (finiteAxisFoldSignatureFiberGeometry_comp second first).symm

/-- The fixed exact pull and top transport carry the primitive southwest
action to the actual direct endpoint. -/
noncomputable def finiteAxisFoldActualDirectSignatureFiberSectionHom :
    FiniteAxisFoldSignatureFiberPermutation →*
      Aut (authoredExactDirectGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))) :=
  ((geomFiberTransportFunctor
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top).mapAut _).comp
    (((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapAut _).comp
      finiteAxisFoldSouthwestSignatureFiberSectionHom)

/-- Exact pull and top transport preserve the identity global-axis action of
the fiberwise signature table. -/
theorem finiteAxisFoldActualDirectSignatureFiber_axisMap
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    (finiteAxisFoldActualDirectSignatureFiberSectionHom permutation).hom.1.base.upper.axisMap =
      _root_.id := by
  calc
    _ = ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapIso
        (finiteAxisFoldSouthwestSignatureFiberAut permutation)).hom.1.base.upper.axisMap :=
      geomFiberTransportMap_axisMap
        finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapIso
            (finiteAxisFoldSouthwestSignatureFiberAut permutation)).hom
    _ = (finiteAxisFoldSouthwestSignatureFiberAut
          permutation).hom.1.base.upper.axisMap :=
      exactGeometryPullMap_axisMap
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
        (finiteAxisFoldSouthwestSignatureFiberAut permutation).hom
    _ = _ := rfl

/-- Admissible packaging and normalization of the actual direct finite action. -/
noncomputable def finiteAxisFoldNormalizedSignatureFiberSectionHom :
    FiniteAxisFoldSignatureFiberPermutation →*
      Aut FiniteAxisFoldNormalizedDirectGeometry :=
  ((geometryNormalizationFunctor.{0, 0} FiniteModel.carrier).mapAut _).comp
    (finiteAxisFoldActualDirectAdmissibleAutomorphismHom.comp
      finiteAxisFoldActualDirectSignatureFiberSectionHom)

/-- Exact pullback preserves coordinate values of the primitive fiberwise
action. -/
theorem exactGeometryPullMap_signatureFiber_coordinate
    (permutation : FiniteAxisFoldSignatureFiberPermutation)
    (axis coordinate : Fin 3) :
    (((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
        (finiteAxisFoldSouthwestSignatureFiberAut permutation).hom).1.base.upper.coordinateEquiv
          axis coordinate) =
      finiteAxisFoldSignatureFiberEquiv permutation axis coordinate := by
  have factorization := congrArg
    (fun total => total.base.upper.coordinateEquiv axis coordinate)
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      (finiteAxisFoldSouthwestSignatureFiberAut permutation).hom)
  simpa [GeometryTotalHom.comp, PackageTotalHom.comp,
    SignedExactCoreReadingHom.comp, exactGeometryPullLift,
    UpperGeometryCleavage.generatedExactGeometryHom,
    UpperGeometryCleavage.exactBaseHom, inverseCorePackageHom,
    inverseCorePackageForwardUpper,
    finiteAxisFoldSouthwestSignatureFiberAut,
    finiteAxisFoldSouthwestSignatureFiberHom,
    finiteAxisFoldSignatureFiberGeometry,
    finiteAxisFoldSignatureFiberTotal,
    finiteAxisFoldSignatureFiberUpper] using factorization

/-- Top transport also preserves primitive coordinate values. -/
theorem finiteAxisFoldActualDirectSignatureFiber_coordinate
    (permutation : FiniteAxisFoldSignatureFiberPermutation)
    (axis coordinate : Fin 3) :
    (finiteAxisFoldActualDirectSignatureFiberSectionHom permutation).hom.1.base.upper.coordinateEquiv
        axis coordinate =
      finiteAxisFoldSignatureFiberEquiv permutation axis coordinate := by
  have factorization := congrArg
    (fun total => total.base.upper.coordinateEquiv axis coordinate)
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          (finiteAxisFoldSouthwestSignatureFiberAut permutation).hom))
  have pulled := exactGeometryPullMap_signatureFiber_coordinate
    permutation axis coordinate
  have transported :
      (finiteAxisFoldActualDirectSignatureFiberSectionHom permutation).hom.1.base.upper.coordinateEquiv
          axis coordinate =
        (((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (finiteAxisFoldSouthwestSignatureFiberAut permutation).hom).1.base.upper.coordinateEquiv
              axis coordinate) := by
    simpa [finiteAxisFoldActualDirectSignatureFiberSectionHom,
      GeometryTotalHom.comp, PackageTotalHom.comp,
      SignedExactCoreReadingHom.comp, geomFiberLift, geomTransportAlongHom,
      geomTransportAlongGeometryHom, transportAlongHom, transportAlongUpper] using
        factorization
  exact transported.trans pulled

/-- Reading the joint signature action after the primitive construction gives
back the complete finite input table. -/
theorem finiteAxisFoldNormalizedSignatureProjection_section
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    finiteAxisFoldNormalizedSignatureProjection
        (finiteAxisFoldNormalizedSignatureFiberSectionHom permutation) =
      permutation.1 := by
  apply Equiv.ext
  intro value
  apply Prod.ext
  · have axisEquality :
        (finiteAxisFoldActualDirectSignatureFiberSectionHom permutation).hom.1.base.upper.axisMap
            value.1 = value.1 :=
      congrFun (finiteAxisFoldActualDirectSignatureFiber_axisMap permutation) value.1
    calc
      _ = value.1 := by
        simpa [finiteAxisFoldNormalizedSignatureProjection,
          finiteAxisFoldNormalizedSignatureEquiv,
          finiteAxisFoldNormalizedSignatureFiberSectionHom,
          finiteAxisFoldActualDirectAdmissibleAutomorphismHom] using axisEquality
      _ = (permutation.1 value).1 := (permutation.2.1 value).symm
  · change
      (finiteAxisFoldActualDirectSignatureFiberSectionHom permutation).hom.1.base.upper.coordinateEquiv
          value.1 value.2 =
        (permutation.1 value).2
    rw [finiteAxisFoldActualDirectSignatureFiber_coordinate]
    rfl

/-- The finite signature construction lies in the complete axis kernel. -/
theorem finiteAxisFoldNormalizedSignatureFiberSection_mem_axisKernel
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    finiteAxisFoldNormalizedSignatureFiberSectionHom permutation ∈
      MonoidHom.ker finiteAxisFoldNormalizedAxisProjection := by
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro axis
  change
    (finiteAxisFoldNormalizedSignatureFiberSectionHom permutation).hom.f.hom.base.upper.axisMap
      axis = axis
  have pairEquality := congrArg
    (fun table : Equiv.Perm (Fin 3 × Fin 3) => table (axis, axis))
    (finiteAxisFoldNormalizedSignatureProjection_section permutation)
  exact (congrArg Prod.fst pairEquality).trans
    (permutation.2.1 (axis, axis))

/-- Primitive finite signature tables as a group homomorphism into the axis
kernel. -/
noncomputable def finiteAxisFoldNormalizedAxisKernelSignatureSectionHom :
    FiniteAxisFoldSignatureFiberPermutation →*
      FiniteAxisFoldNormalizedAxisKernel where
  toFun permutation :=
    ⟨finiteAxisFoldNormalizedSignatureFiberSectionHom permutation,
      finiteAxisFoldNormalizedSignatureFiberSection_mem_axisKernel permutation⟩
  map_one' := by
    apply Subtype.ext
    exact map_one finiteAxisFoldNormalizedSignatureFiberSectionHom
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul finiteAxisFoldNormalizedSignatureFiberSectionHom first second

/-- The primitive construction is a right inverse of the restricted finite
signature projection. -/
theorem finiteAxisFoldNormalizedAxisKernelSignatureProjection_section
    (permutation : FiniteAxisFoldSignatureFiberPermutation) :
    finiteAxisFoldNormalizedAxisKernelSignatureProjection
        (finiteAxisFoldNormalizedAxisKernelSignatureSectionHom permutation) =
      permutation := by
  apply Subtype.ext
  exact finiteAxisFoldNormalizedSignatureProjection_section permutation

/-- Axis-kernel elements invisible to the complete finite signature table. -/
noncomputable abbrev FiniteAxisFoldNormalizedAxisSignatureKernel :=
  MonoidHom.ker finiteAxisFoldNormalizedAxisKernelSignatureProjection

/-- Remove the explicitly constructed finite signature component of an
arbitrary axis-kernel element. -/
noncomputable def finiteAxisFoldNormalizedAxisSignatureKernelRemainder
    (remainder : FiniteAxisFoldNormalizedAxisKernel) :
    FiniteAxisFoldNormalizedAxisSignatureKernel :=
  ⟨remainder *
      (finiteAxisFoldNormalizedAxisKernelSignatureSectionHom
        (finiteAxisFoldNormalizedAxisKernelSignatureProjection remainder))⁻¹,
    by
      simp [finiteAxisFoldNormalizedAxisKernelSignatureProjection_section]⟩

/-- Exact decomposition into a signature-trivial remainder and the finite
signature component. -/
theorem finiteAxisFoldNormalizedAxisSignatureKernelRemainder_mul_section
    (remainder : FiniteAxisFoldNormalizedAxisKernel) :
    (finiteAxisFoldNormalizedAxisSignatureKernelRemainder remainder).1 *
        finiteAxisFoldNormalizedAxisKernelSignatureSectionHom
          (finiteAxisFoldNormalizedAxisKernelSignatureProjection remainder) =
      remainder := by
  simp [finiteAxisFoldNormalizedAxisSignatureKernelRemainder]

/-- A concrete nonidentity off-diagonal action that fixes all global axes and
all distinguished diagonal coordinates. -/
def finiteAxisFoldOffDiagonalSwap : Equiv.Perm (Fin 3 × Fin 3) :=
  Equiv.swap ((0 : Fin 3), (1 : Fin 3)) ((0 : Fin 3), (2 : Fin 3))

theorem finiteAxisFoldOffDiagonalSwap_mem :
    finiteAxisFoldOffDiagonalSwap ∈
      finiteAxisFoldSignatureFiberPermutationSubgroup := by
  constructor
  · intro value
    rcases value with ⟨axis, coordinate⟩
    fin_cases axis <;> fin_cases coordinate <;> rfl
  · intro axis
    fin_cases axis <;> rfl

theorem finiteAxisFoldOffDiagonalSwap_ne_one :
    (⟨finiteAxisFoldOffDiagonalSwap, finiteAxisFoldOffDiagonalSwap_mem⟩ :
      FiniteAxisFoldSignatureFiberPermutation) ≠ 1 := by
  intro equality
  have moved := congrArg
    (fun permutation : FiniteAxisFoldSignatureFiberPermutation =>
      permutation.1 ((0 : Fin 3), (1 : Fin 3))) equality
  change ((0 : Fin 3), (2 : Fin 3)) = ((0 : Fin 3), (1 : Fin 3)) at moved
  have coordinateEquality := congrArg (fun value : Fin 3 × Fin 3 => value.2) moved
  have valueEquality := congrArg Fin.val coordinateEquality
  norm_num at valueEquality

/-- The fixed construction therefore exhibits a nonidentity normalized
automorphism whose global axis action is identity. -/
theorem finiteAxisFoldNormalizedAxisKernel_coordinateAction_ne_one :
    finiteAxisFoldNormalizedAxisKernelSignatureSectionHom
      ⟨finiteAxisFoldOffDiagonalSwap, finiteAxisFoldOffDiagonalSwap_mem⟩ ≠ 1 := by
  intro equality
  apply finiteAxisFoldOffDiagonalSwap_ne_one
  have mapped := congrArg
    finiteAxisFoldNormalizedAxisKernelSignatureProjection equality
  simpa [finiteAxisFoldNormalizedAxisKernelSignatureProjection_section] using mapped

end


end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
