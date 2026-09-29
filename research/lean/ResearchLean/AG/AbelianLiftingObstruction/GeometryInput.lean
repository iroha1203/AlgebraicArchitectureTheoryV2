import ResearchLean.AG.AbelianLiftingObstruction.PointedContexts
import ResearchLean.AG.CrossStageCoherence.FiniteWitnesses

/-!
# A point-detecting geometry input with a nontrivial coefficient kernel

G-129 completion condition 4: a finite Atom carrier, a nonempty site with a
cover, and a nonzero raw equation coexist with a nonidentity inner automorphism.

## Implementation notes

The existing finite Atom model is instantiated using `coreReadingFor` with
point-detecting selected restrictions. Its context objects and readable
relation are unchanged. The diagonal raw system and coefficient swap use the
same constructions as `FiniteCrossStageWitness`. The full geometry morphism
contract is retained, including all three realization comparison families.
-/

namespace AAT.AG.AbelianLiftingObstruction.GeometryInput

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence

/-- The finite reading with explicit point-detecting context maps. -/
noncomputable def reading : CoreReading FiniteModel.carrier :=
  { FiniteModel.coreReadingFor (PointedContexts.contextPreorder FiniteModel.object) with
    signatureReading := FiniteCrossStageWitness.signature }

/-- The core is generated from the existing finite AAT axioms and this reading. -/
noncomputable def core : AATCorePackage FiniteModel.carrier :=
  AATCorePackage.generate FiniteModel.axiomSystem reading

/-- Coverage selects exactly axes `0` and `1`. -/
def requirements : Site.CoverageRequirements core.object
    core.equationSystem core.algebra.signatureReading where
  requiredSupport := fun _ => False
  requiredEquationCoordinate := fun _ => False
  selectedViolationWitness := fun _ => False
  requiredAxis := fun axis => axis = (0 : Fin 4) ∨ axis = (1 : Fin 4)
  supportVisibleOn := fun _ _ => True
  equationCoordinateVisibleOn := fun _ _ => True
  violationWitnessVisibleOn := fun _ _ => True
  axisReadableOn := fun _ axis => axis = (0 : Fin 4) ∨ axis = (1 : Fin 4)
  boundaryVisibleOn := fun _ _ => True

/-- Geometry on the finite Atom carrier, with the full context preorder and product meets. -/
noncomputable def selectedGeometry : Site.SelectedGeometryReading core where
  requirements := requirements
  overlap := Site.meetOverlapPullback core.contextPreorder
    (PointedContexts.finiteMeet FiniteModel.object)

/-- One explicit context witnessing that the selected site is inhabited. -/
def baseContext : Site.ArchCtx core.object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ _ => False
    supportReads_objectFamily := fun h => False.elim h
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/-- Diagonal coefficient map into the symmetric pair ring. -/
def diagonalCoefficient : Int →+*
    GeometryTransport.NegativeGeometryWitness.PairCoefficient :=
  Int.castRingHom _

/-- Swapping the pair factors fixes the diagonal coefficient map. -/
theorem pairSwap_comp_diagonal :
    GeometryTransport.NegativeGeometryWitness.pairSwap.comp diagonalCoefficient =
      diagonalCoefficient := by
  ext value <;> rfl

/-- One semantic coordinate on every selected context. -/
def coordFamily (W : selectedGeometry.toAATSite.category) :
    LawAlgebra.CoordinateFamily W.ctx where
  Coord := Unit
  label := fun _ => LawAlgebra.CoordinateLabel.semantic
  LocalData := fun _ => Unit

/-- The nonzero integral relation used before diagonal coefficient extension. -/
noncomputable def relationFamily (W : selectedGeometry.toAATSite.category) :
    LawAlgebra.StructuralRelationFamily (coordFamily W) Int where
  Relation := Unit
  polynomial := fun _ => MvPolynomial.X () ^ 2 - MvPolynomial.X ()

/-- Every context restriction fixes the selected coordinate. -/
noncomputable def coordinateRestriction
    {X Y : selectedGeometry.toAATSite.category} (w : X ⟶ Y) :
    LawAlgebra.TypedCoordinateRestriction (coordFamily X) (coordFamily Y) Int
      (selectedGeometry.toAATSite.contextPreorder.morphism (leOfHom w)) where
  variableImage := fun _ => MvPolynomial.X ()

/-- Fixture API: coordinate restriction commutes with the polynomial structure map. -/
theorem coordinateRestriction_polynomialMap
    {X Y : selectedGeometry.toAATSite.category} (w : X ⟶ Y) :
    (coordinateRestriction w).polynomialMap =
      RingHom.id (LawAlgebra.FreeTypedCommAlg (coordFamily X) Int) := by
  apply MvPolynomial.ringHom_ext
  · intro value
    change (coordinateRestriction w).polynomialMap (MvPolynomial.C value) =
      MvPolynomial.C value
    exact LawAlgebra.TypedCoordinateRestriction.polynomialMap_C _ _
  · intro coordinate
    cases coordinate
    rw [LawAlgebra.TypedCoordinateRestriction.polynomialMap_X]
    rfl

/-- The relation is stable under the identity coordinate restriction. -/
noncomputable def restrictionStable
    {X Y : selectedGeometry.toAATSite.category} (w : X ⟶ Y) :
    LawAlgebra.RestrictionStableStructuralRelations
      (relationFamily X) (relationFamily Y)
      (selectedGeometry.toAATSite.contextPreorder.morphism (leOfHom w)) where
  restriction := coordinateRestriction w
  maps_JStruct := by
    intro polynomial hpolynomial
    have identity : (coordinateRestriction w).polynomialMap polynomial =
        polynomial := by
      rw [coordinateRestriction_polynomialMap]
      rfl
    rw [identity]
    exact hpolynomial

/-- Coherent integral raw system on the selected site. -/
noncomputable def integralRaw :
    LawAlgebra.RawAmbientRestrictionSystem selectedGeometry.toAATSite Int where
  coordFamily := coordFamily
  relationFamily := relationFamily
  restrictionStable := restrictionStable
  identity_polynomialMap W := coordinateRestriction_polynomialMap (𝟙 W)
  composition_polynomialMap f g := by
    change (coordinateRestriction (f ≫ g)).polynomialMap =
      ((coordinateRestriction f).polynomialMap).comp
        ((coordinateRestriction g).polynomialMap)
    rw [coordinateRestriction_polynomialMap,
      coordinateRestriction_polynomialMap,
      coordinateRestriction_polynomialMap]
    exact (RingHom.id_comp _).symm

/-- The actual finite raw system after diagonal coefficient extension. -/
noncomputable def symmetricRaw :
    LawAlgebra.RawAmbientRestrictionSystem selectedGeometry.toAATSite
      GeometryTransport.NegativeGeometryWitness.PairCoefficient :=
  integralRaw.baseChange diagonalCoefficient

/-- The raw system is fixed by the nonidentity coefficient swap. -/
theorem symmetricRaw_swap :
    symmetricRaw.baseChange
        GeometryTransport.NegativeGeometryWitness.pairSwap = symmetricRaw := by
  unfold symmetricRaw
  rw [← LawAlgebra.RawAmbientRestrictionSystem.baseChange_comp]
  rw [pairSwap_comp_diagonal]

/-- The finite geometry package used by both witness directions. -/
noncomputable def package :
    GeometryPackage.{0, 0} FiniteModel.carrier where
  core := core
  geometry := selectedGeometry
  Coefficient := GeometryTransport.NegativeGeometryWitness.PairCoefficient
  coefficientCommRing := inferInstance
  raw := symmetricRaw

/-- The fixture has an actual selected finite context. -/
theorem site_nonempty : Nonempty package.site.category :=
  ⟨⟨baseContext⟩⟩

/-- The top sieve is an actual cover in the selected generated topology. -/
theorem has_actual_cover :
    (⊤ : Sieve (⟨baseContext⟩ : package.site.category)) ∈
      package.site.topology ⟨baseContext⟩ :=
  package.site.top_mem _

/-- The pair coefficient ring is nonzero. -/
theorem coefficient_nontrivial :
    (((2 : Int), (2 : Int)) : package.Coefficient) ≠ 0 := by
  norm_num

/-- The inherited finite raw relation remains genuinely nonzero. -/
theorem raw_relation_nonzero :
    ((package.raw.relationFamily
      (⟨baseContext⟩ : package.site.category)).polynomial ()) ≠ 0 := by
  intro equality
  change MvPolynomial.map diagonalCoefficient
      (MvPolynomial.X () ^ 2 - MvPolynomial.X ()) = 0 at equality
  have evaluated := congrArg
    (MvPolynomial.eval₂Hom (RingHom.fst Int Int)
      (fun _ : Unit => (2 : Int))) equality
  norm_num [diagonalCoefficient] at evaluated

/-- Coefficient swap is a geometry self-map over the identity core morphism. -/
noncomputable def coefficientSwapGeometryHom :
    GeomReadHom package package (PackageTotalHom.id core) where
  coverage := CoverageTransport.id package
  overlap := OverlapTransport.id package
  coefficientHom := GeometryTransport.NegativeGeometryWitness.pairSwap
  raw_eq := by
    unfold rawTransport
    calc
      package.raw = package.raw.baseChange
          GeometryTransport.NegativeGeometryWitness.pairSwap :=
        symmetricRaw_swap.symm
      _ = rawReindex (G := package) (H := package)
          (PackageTotalHom.id package.core)
          (package.raw.baseChange
            GeometryTransport.NegativeGeometryWitness.pairSwap) :=
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

/-- Lift the coefficient swap to a total geometry endomorphism over the identity core map. -/
noncomputable def coefficientSwapTotal : GeometryTotalHom package package where
  base := PackageTotalHom.id core
  geometry := coefficientSwapGeometryHom

/-- The total coefficient swap is involutive. -/
theorem coefficientSwapTotal_square :
    coefficientSwapTotal.comp coefficientSwapTotal = GeometryTotalHom.id package := by
  have baseSquare :
      (coefficientSwapTotal.comp coefficientSwapTotal).base =
        (GeometryTotalHom.id package).base := by
    change (PackageTotalHom.id core).comp (PackageTotalHom.id core) =
      PackageTotalHom.id core
    exact Category.comp_id
      (self := AAT.AG.AtomFoundation.PackageTotalHom.packageTotalCategory
        FiniteModel.carrier)
      (PackageTotalHom.id core)
  apply GeometryTotalHom.ext
  · exact baseSquare
  · exact heq_of_eq (GeomReadHom.ext
      GeometryTransport.NegativeGeometryWitness.pairSwap_comp
      HEq.rfl HEq.rfl HEq.rfl)

/-- Package the involutive coefficient swap as a geometry automorphism. -/
noncomputable def coefficientSwapIso : Aut package where
  hom := coefficientSwapTotal
  inv := coefficientSwapTotal
  hom_inv_id := coefficientSwapTotal_square
  inv_hom_id := coefficientSwapTotal_square

/-- The concrete nonidentity element of the strict subgroup `H_G`. -/
noncomputable def innerSwap : InnerFiberAut package :=
  ⟨⟨coefficientSwapIso, rfl⟩, rfl⟩

/-- The coefficient swap supplies a nonidentity element of the inner kernel. -/
theorem innerSwap_ne_one : innerSwap ≠ 1 := by
  intro equality
  have coefficientEquality := congrArg
    (fun automorphism : InnerFiberAut package =>
      automorphism.1.1.hom.geometry.coefficientHom
        (((1 : Int), (0 : Int)) : package.Coefficient)) equality
  change (((0 : Int), (1 : Int)) : package.Coefficient) = ((1, 0) : package.Coefficient)
    at coefficientEquality
  norm_num at coefficientEquality


end AAT.AG.AbelianLiftingObstruction.GeometryInput

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction.GeometryInput
