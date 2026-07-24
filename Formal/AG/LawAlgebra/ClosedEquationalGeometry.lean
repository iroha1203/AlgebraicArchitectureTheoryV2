import Formal.AG.LawAlgebra.LawEquation
import Formal.AG.LawAlgebra.AffineChart
import Formal.AG.LawAlgebra.StandardScheme
import Formal.AG.Atom.Signature
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Algebra

noncomputable section

namespace AAT.AG.LawAlgebra

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

/-! ## Implementation notes

The obstruction construction uses actual `Scheme.IdealSheafData` assembled from the
law-by-law coordinate spans selected on each affine context. It does not accept an arbitrary
ideal family as primary input. Semantic cores enter the construction through a raw-presentation
equivalence followed by the canonical sheafification unit, so presentation provenance and
restriction naturality remain explicit proof obligations.

The equation-system standard route is the represented specialization of
Definition 5.2B.  A single representing scheme carries the universal
evaluation for every context, and `GeneratorIndex` retains the context
coordinate explicitly.  Thus residual regularity comes from the universal
represented point, residual representability from the generated equalizer,
and witness ideals from `E.witnessIdeal`; independently supplied section maps,
residual functions, lawfulness predicates, or conclusion certificates are
not inputs.  The selected atlas supplies actual affine chart rings and
pair-context transition maps.  A named localization property for those maps
generates the tensor comparison, overlap equality, and quasi-coherent chart
package used by the final equation correspondence.

Required and all-selected laws produce separate ideal sheaves and separate closed subschemes.
For a general Scheme the public geometry is Mathlib's subscheme together with its quotient affine
cover; it is not replaced by a single global affine quotient. These choices keep the semantic,
witness, ideal, and actual-factorization layers independently testable by the characterization
and comparison theorems below.
-/

universe u v w

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable (raw : RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (AATCommAlgCat k)]
variable (X : StandardArchitectureScheme raw)
variable {E F H : ArchitecturalEquationSystem S.contextPreorder}

/--
A localization is transported across equivalences of both its source and
target rings.  The transported algebra map is the conjugate of the original
one, and the selected multiplicative subset is carried along the source
equivalence.
-/
theorem IsLocalization.transportRingEquiv
    {R : Type u} {T : Type v} {R' : Type w} {T' : Type*}
    [CommRing R] [CommRing T] [CommRing R'] [CommRing T']
    [Algebra R T] (M : Submonoid R) [IsLocalization M T]
    (eR : R ≃+* R') (eT : T ≃+* T') :
    letI := (eT.toRingHom.comp
      ((algebraMap R T).comp eR.symm.toRingHom)).toAlgebra
    IsLocalization (M.map eR.toMonoidHom) T' := by
  letI : Algebra R T' :=
    (eT.toRingHom.comp (algebraMap R T)).toAlgebra
  letI : IsLocalization M T' :=
    (IsLocalization.isLocalization_iff_of_ringEquiv M eT).mp
      (inferInstance : IsLocalization M T)
  exact IsLocalization.isLocalization_of_base_ringEquiv M T' eR

/--
Version of `IsLocalization.transportRingEquiv` whose target algebra map is
identified with a named ring homomorphism.
-/
theorem IsLocalization.transportRingEquivOfEq
    {R : Type u} {T : Type v} {R' : Type w} {T' : Type*}
    [CommRing R] [CommRing T] [CommRing R'] [CommRing T']
    [Algebra R T] (M : Submonoid R) [IsLocalization M T]
    (eR : R ≃+* R') (eT : T ≃+* T') (f : R' →+* T')
    (h : eT.toRingHom.comp
      ((algebraMap R T).comp eR.symm.toRingHom) = f) :
    letI := f.toAlgebra
    IsLocalization (M.map eR.toMonoidHom) T' := by
  rw [← h]
  exact IsLocalization.transportRingEquiv M eR eT

/-! ## Closed-equational readings -/

/-- A semantic reading of each equation on sections of test Schemes. -/
structure GeometricLawReading
    (E : ArchitecturalEquationSystem S.contextPreorder) where
  /-- The semantic law predicate on a section of a test Scheme. -/
  HoldsOn : ∀ {T : AlgebraicGeometry.Scheme},
    (T ⟶ X.underlying) → E.Index → Prop

/-- Geometric readings are determined by their section predicate. -/
@[ext] theorem GeometricLawReading.ext
    (R Q : GeometricLawReading raw X E)
    (h : @R.HoldsOn = @Q.HoldsOn) : R = Q := by
  cases R
  cases Q
  cases h
  rfl

/-- Stability of a geometric reading under base change of a test section. -/
def IsGeometricLawReading (R : GeometricLawReading raw X E) : Prop :=
  ∀ {T T' : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) (f : T' ⟶ T) (i : E.Index),
    R.HoldsOn s i → R.HoldsOn (f ≫ s) i

/-- Atom-indexed violation coordinates for one law on every affine open. -/
structure ClosedEquationalLawWitness
    (E : ArchitecturalEquationSystem S.contextPreorder) (i : E.Index) where
  /-- The violation coordinate of each atom on an affine open. -/
  coordinate : ∀ V : X.underlying.affineOpens,
    U.Atom → Γ(X.underlying, V)

/-- Closed-equational witnesses are determined by their coordinates. -/
@[ext] theorem ClosedEquationalLawWitness.ext
    {i : E.Index}
    (W Z : ClosedEquationalLawWitness raw X E i)
    (h : W.coordinate = Z.coordinate) : W = Z := by
  cases W
  cases Z
  cases h
  rfl

/-- Exact compatibility of witness coordinates with basic-open restriction. -/
def IsClosedEquationalLawWitness
    {i : E.Index}
    (W : ClosedEquationalLawWitness raw X E i) : Prop :=
  ∀ (V : X.underlying.affineOpens) (f : Γ(X.underlying, V)) (a : U.Atom),
    X.underlying.presheaf.map
        (homOfLE (X.underlying.basicOpen_le f)).op (W.coordinate V a) =
      W.coordinate (X.underlying.affineBasicOpen f) a

/-- The local ideal spanned by the atom-indexed coordinates of one law. -/
def localLawWitnessIdeal
    {i : E.Index}
    (W : ClosedEquationalLawWitness raw X E i)
    (V : X.underlying.affineOpens) : Ideal Γ(X.underlying, V) :=
  Ideal.span (Set.range (W.coordinate V))

/-- Coordinate compatibility induces exact basic-open compatibility of the spanned ideal. -/
theorem localLawWitnessIdeal_map_basicOpen
    {i : E.Index}
    (W : ClosedEquationalLawWitness raw X E i)
    (hW : IsClosedEquationalLawWitness raw X W)
    (V : X.underlying.affineOpens) (f : Γ(X.underlying, V)) :
    Ideal.map
        (X.underlying.presheaf.map
          (homOfLE (X.underlying.basicOpen_le f)).op).hom
        (localLawWitnessIdeal raw X W V) =
      localLawWitnessIdeal raw X W (X.underlying.affineBasicOpen f) := by
  rw [localLawWitnessIdeal, localLawWitnessIdeal, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (hW V f a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨W.coordinate V a, ⟨a, rfl⟩, hW V f a⟩

/-- Restrict a family of global equations to every affine open. -/
noncomputable def ClosedEquationalLawWitness.ofGlobalSections
    (i : E.Index)
    (equation : U.Atom → Γ(X.underlying, ⊤)) :
    ClosedEquationalLawWitness raw X E i where
  coordinate V a :=
    X.underlying.presheaf.map (homOfLE le_top).op (equation a)

/-- The global-section constructor satisfies basic-open compatibility. -/
theorem ClosedEquationalLawWitness.ofGlobalSections_valid
    (i : E.Index)
    (equation : U.Atom → Γ(X.underlying, ⊤)) :
    IsClosedEquationalLawWitness raw X
      (ClosedEquationalLawWitness.ofGlobalSections raw X i equation) := by
  intro V f a
  simp only [ClosedEquationalLawWitness.ofGlobalSections,
    ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  rfl

/-- Coordinates of the global-section constructor are canonical restrictions. -/
@[simp] theorem ClosedEquationalLawWitness.ofGlobalSections_coordinate
    (i : E.Index)
    (equation : U.Atom → Γ(X.underlying, ⊤))
    (V : X.underlying.affineOpens) (a : U.Atom) :
    (ClosedEquationalLawWitness.ofGlobalSections raw X i equation).coordinate V a =
      X.underlying.presheaf.map (homOfLE le_top).op (equation a) :=
  rfl

/-- An objectwise raw-presentation identification for an existing semantic equation core. -/
structure SemanticLawEquationSchemeBridge
    (E : ArchitecturalEquationSystem S.contextPreorder) where
  /-- The raw-presentation equivalence for each context. -/
  toRawPresentation : ∀ W : S.category,
    E.Observable W ≃+* raw.rawAlgebra W

/-- The bridge map followed by the canonical sheafification unit. -/
noncomputable def SemanticLawEquationSchemeBridge.toSheafifiedSection
    {raw : RawAmbientRestrictionSystem S k}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (B : SemanticLawEquationSchemeBridge raw E)
    (W : S.category) : E.Observable W →+* SheafifiedSectionRing raw W :=
  (sheafificationUnitAlgHom raw W).toRingHom.comp
    (B.toRawPresentation W).toRingHom

/-- Scheme bridges are determined by their presentation equivalences. -/
@[ext, nolint unusedArguments] theorem SemanticLawEquationSchemeBridge.ext
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B C : SemanticLawEquationSchemeBridge raw E)
    (h : B.toRawPresentation = C.toRawPresentation) : B = C := by
  cases B
  cases C
  cases h
  rfl

/-- Naturality and canonical presentation stability of a scheme bridge. -/
structure IsSemanticLawEquationSchemeBridge
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E) : Prop where
  restriction_natural :
    ∀ {source target : S.category} (f : source ⟶ target)
      (x : E.Observable target),
      B.toSheafifiedSection source (E.restrict f x) =
        sheafifiedRestriction raw f (B.toSheafifiedSection target x)
  presentation_stable :
    ∀ W : S.category,
      AffineChart.AffineAATChart.SheafifiedChartPresentation raw W

/-- A valid bridge is bijective on every canonical sheafified section ring. -/
theorem SemanticLawEquationSchemeBridge.toSheafifiedSection_bijective
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (hB : IsSemanticLawEquationSchemeBridge raw E B)
    (W : S.category) :
    Function.Bijective (B.toSheafifiedSection W) := by
  letI : IsIso (raw.toRingedSite.canonical.app (op W)) :=
    (hB.presentation_stable W).canonical_isIso
  exact (CategoryTheory.ConcreteCategory.bijective_of_isIso
    (raw.toRingedSite.canonical.app (op W)).right).comp
      (B.toRawPresentation W).bijective

/-- Send a core violation witness to an actual global equation. -/
noncomputable def semanticCoreGlobalEquation
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (i : E.Index) (a : U.Atom) : Γ(X.underlying, ⊤) :=
  X.decoration.interpretation
    (B.toSheafifiedSection X.decoration.context
      (E.violationCoordinate X.decoration.context i a))

/-- Vanishing of a family of global equations along a Scheme section. -/
def GlobalEquationsVanishAlong
    (equation : U.Atom → Γ(X.underlying, ⊤))
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  ∀ a, s.appTop (equation a) = 0

/-- The canonical geometric reading induced by a semantic equation core. -/
noncomputable def GeometricLawReading.ofSemanticCore
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E) :
    GeometricLawReading raw X E where
  HoldsOn s i :=
    GlobalEquationsVanishAlong raw X
      (semanticCoreGlobalEquation raw X E B i) s

/-- Core equation vanishing is stable under base change. -/
theorem GeometricLawReading.ofSemanticCore_valid
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E) :
    IsGeometricLawReading raw X
      (GeometricLawReading.ofSemanticCore raw X E B) := by
  intro T T' s f i hs a
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hs a, map_zero]

/-- The core reading unfolds to generatorwise equation vanishing. -/
@[simp] theorem GeometricLawReading.ofSemanticCore_holdsOn
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (i : E.Index) :
    (GeometricLawReading.ofSemanticCore raw X E B).HoldsOn s i ↔
      ∀ a, s.appTop (semanticCoreGlobalEquation raw X E B i a) = 0 :=
  Iff.rfl

/-- Bridge naturality sends restricted core witnesses to restricted canonical sections. -/
theorem semanticCoreWitness_restrict
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (hB : IsSemanticLawEquationSchemeBridge raw E B)
    {source target : S.category} (f : source ⟶ target)
    (i : E.Index) (a : U.Atom) :
    B.toSheafifiedSection source (E.violationCoordinate source i a) =
      sheafifiedRestriction raw f
        (B.toSheafifiedSection target (E.violationCoordinate target i a)) := by
  rw [← E.violationCoordinate_restrict f i a]
  exact hB.restriction_natural f _

/-- The image of a core witness ideal is the span of the transported coordinates. -/
theorem semanticCoreLawWitnessIdeal_map
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (W : S.category) (i : E.Index) :
    Ideal.map (B.toSheafifiedSection W) (E.witnessIdeal W i) =
      Ideal.span (Set.range (fun a =>
        B.toSheafifiedSection W (E.violationCoordinate W i a))) := by
  rw [ArchitecturalEquationSystem.witnessIdeal, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, rfl⟩

/-- A valid bridge reflects its core witness ideal through map and comap. -/
theorem semanticCoreLawWitnessIdeal_comap_map
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (hB : IsSemanticLawEquationSchemeBridge raw E B)
    (W : S.category) (i : E.Index) :
    Ideal.comap (B.toSheafifiedSection W)
        (Ideal.map (B.toSheafifiedSection W) (E.witnessIdeal W i)) =
      E.witnessIdeal W i := by
  exact (E.witnessIdeal W i).comap_map_of_bijective _
    (B.toSheafifiedSection_bijective raw E hB W)

/-- On an atlas chart, the pulled global equation is the corresponding local core witness. -/
theorem semanticCoreGlobalEquation_on_chart
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (hB : IsSemanticLawEquationSchemeBridge raw E B)
    (j : X.atlas.Index) (i : E.Index) (a : U.Atom) :
    ((X.atlas.chart j).map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw (X.atlas.chart j).context)).hom)
        (semanticCoreGlobalEquation raw X E B i a) =
      B.toSheafifiedSection (X.atlas.chart j).context
        (E.violationCoordinate (X.atlas.chart j).context i a) := by
  rw [semanticCoreGlobalEquation]
  let x := B.toSheafifiedSection X.decoration.context
    (E.violationCoordinate X.decoration.context i a)
  calc
    ((X.atlas.chart j).map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw (X.atlas.chart j).context)).hom)
        (X.decoration.interpretation x) =
      sheafifiedRestriction raw (X.atlas.chart j).contextHom x := by
        simpa only [Category.assoc, CommRingCat.comp_apply] using
          (congrArg (fun q => q x)
            (X.atlasValid.chart_valid j).interpretation_compatible).symm
    _ = B.toSheafifiedSection (X.atlas.chart j).context
        (E.violationCoordinate (X.atlas.chart j).context i a) :=
      (semanticCoreWitness_restrict raw E B hB
        (X.atlas.chart j).contextHom i a).symm

/-- The canonical closed-equational witness induced by the existing semantic core. -/
noncomputable def ClosedEquationalLawWitness.ofSemanticCore
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (i : E.Index) : ClosedEquationalLawWitness raw X E i :=
  ClosedEquationalLawWitness.ofGlobalSections raw X i
    (semanticCoreGlobalEquation raw X E B i)

/-- Core-induced closed-equational witnesses satisfy exact restriction compatibility. -/
theorem ClosedEquationalLawWitness.ofSemanticCore_valid
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (i : E.Index) :
    IsClosedEquationalLawWitness raw X
      (ClosedEquationalLawWitness.ofSemanticCore raw X E B i) :=
  ClosedEquationalLawWitness.ofGlobalSections_valid raw X i _

/-! ## Closed-equational recognition and selection -/

/-- A semantic reading together with closed laws, context selection, and their witnesses. -/
structure ClosedEquationalLawReading
    (E : ArchitecturalEquationSystem S.contextPreorder) where
  /-- The semantic reading carried by this closed-equational package. -/
  geometric : GeometricLawReading raw X E
  /-- The laws certified as closed equations. -/
  closed : Set E.Index
  /-- The closed laws selected on each affine context. -/
  selected : X.underlying.affineOpens → Set E.Index
  /-- The atom-indexed equation witness for each closed law. -/
  witness : ∀ i, closed i → ClosedEquationalLawWitness raw X E i

/-- Closed-equational readings are determined by their four data components. -/
@[ext] theorem ClosedEquationalLawReading.ext
    (R Q : ClosedEquationalLawReading raw X E)
    (hgeometric : R.geometric = Q.geometric)
    (hclosed : R.closed = Q.closed)
    (hselected : R.selected = Q.selected)
    (hwitness : HEq R.witness Q.witness) : R = Q := by
  cases R
  cases Q
  cases hgeometric
  cases hclosed
  cases hselected
  cases hwitness
  rfl

/-- Compatibility required to construct the law witness ideal sheaves. -/
def IsClosedEquationalWitnessReading
    (R : ClosedEquationalLawReading raw X E) : Prop :=
  ∀ i (hi : R.closed i),
    IsClosedEquationalLawWitness raw X (R.witness i hi)

/-- Full recognition of semantic stability, witnesses, and context selection. -/
structure IsClosedEquationalLawReading
    (R : ClosedEquationalLawReading raw X E) : Prop where
  geometric_stable : IsGeometricLawReading raw X R.geometric
  witness_compatible : IsClosedEquationalWitnessReading raw X R
  selected_closed :
    ∀ V i, R.selected V i → R.closed i
  selected_basicOpen :
    ∀ (V : X.underlying.affineOpens)
      (f : Γ(X.underlying, V)) (i : E.Index),
      R.selected V i ↔
        R.selected (X.underlying.affineBasicOpen f) i

/-- Every required law is closed-equational and selected on every affine context. -/
structure RequiredClosed (R : ClosedEquationalLawReading raw X E) : Prop where
  closed : ∀ i, E.Required i → R.closed i
  selected :
    ∀ V i, E.Required i → R.selected V i

/-- Required-law semantic truth along a section. -/
def SemanticLawfulAlong
    (R : ClosedEquationalLawReading raw X E)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  ∀ i, E.Required i → R.geometric.HoldsOn s i

/-- Semantic truth of every law index along a section. -/
def FullySemanticLawfulAlong
    (R : ClosedEquationalLawReading raw X E)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  ∀ i, R.geometric.HoldsOn s i

/-- Every law is closed-equational and selected on every affine context. -/
structure AllLawsSelected
    (R : ClosedEquationalLawReading raw X E) : Prop where
  closed : ∀ i, R.closed i
  selected : ∀ V i, R.selected V i

/-- The canonical closed-equational reading induced by a semantic equation core. -/
noncomputable def ClosedEquationalLawReading.ofSemanticCore
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E) :
    ClosedEquationalLawReading raw X E where
  geometric := GeometricLawReading.ofSemanticCore raw X E B
  closed := Set.univ
  selected := fun _ => Set.univ
  witness i _ := ClosedEquationalLawWitness.ofSemanticCore raw X E B i

/-- The canonical core reading uses the canonical core witness. -/
@[simp] theorem ClosedEquationalLawReading.ofSemanticCore_witness
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (i : E.Index)
    (hi : (ClosedEquationalLawReading.ofSemanticCore raw X E B).closed i) :
    (ClosedEquationalLawReading.ofSemanticCore raw X E B).witness i hi =
      ClosedEquationalLawWitness.ofSemanticCore raw X E B i :=
  rfl

/-- The canonical core reading has compatible witnesses. -/
theorem ClosedEquationalLawReading.ofSemanticCore_witnessCompatible
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E) :
    IsClosedEquationalWitnessReading raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X E B) := by
  intro i hi
  exact ClosedEquationalLawWitness.ofSemanticCore_valid raw X E B i

/-- The canonical core reading satisfies full recognition. -/
theorem ClosedEquationalLawReading.ofSemanticCore_valid
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E) :
    IsClosedEquationalLawReading raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X E B) where
  geometric_stable := GeometricLawReading.ofSemanticCore_valid raw X E B
  witness_compatible :=
    ClosedEquationalLawReading.ofSemanticCore_witnessCompatible raw X E B
  selected_closed := fun _ i _ => Set.mem_univ i
  selected_basicOpen := fun _ _ i =>
    iff_of_true (Set.mem_univ i) (Set.mem_univ i)

/-- The canonical core reading contains every required law. -/
theorem ClosedEquationalLawReading.ofSemanticCore_requiredClosed
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E) :
    RequiredClosed raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X E B) where
  closed := fun i _ => Set.mem_univ i
  selected := fun _ i _ => Set.mem_univ i

/-- Every law is selected by the canonical core reading. -/
theorem ClosedEquationalLawReading.ofSemanticCore_selected
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (V : X.underlying.affineOpens) (i : E.Index) :
    (ClosedEquationalLawReading.ofSemanticCore raw X E B).selected V i :=
  Set.mem_univ i

/-- The canonical core reading selects every law. -/
theorem ClosedEquationalLawReading.ofSemanticCore_allLawsSelected
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E) :
    AllLawsSelected raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X E B) where
  closed := fun i => Set.mem_univ i
  selected := fun _ i => Set.mem_univ i

/-! ## Actual ideal sheaves -/

/-- The actual Mathlib ideal sheaf spanned by one law witness. -/
noncomputable def lawWitnessIdealSheaf
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : E.Index) (hi : R.closed i) :
    X.underlying.IdealSheafData where
  ideal := localLawWitnessIdeal raw X (R.witness i hi)
  map_ideal_basicOpen :=
    localLawWitnessIdeal_map_basicOpen raw X (R.witness i hi) (hR i hi)

/-- The component of a law witness ideal sheaf is its local span. -/
@[simp] theorem lawWitnessIdealSheaf_ideal
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : E.Index) (hi : R.closed i)
    (V : X.underlying.affineOpens) :
    (lawWitnessIdealSheaf raw X R hR i hi).ideal V =
      localLawWitnessIdeal raw X (R.witness i hi) V :=
  rfl

/-- A global-section witness gives Mathlib's ideal sheaf induced from the top open. -/
theorem lawWitnessIdealSheaf_ofGlobalSections
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : E.Index) (hi : R.closed i)
    (equation : U.Atom → Γ(X.underlying, ⊤))
    (hw : R.witness i hi =
      ClosedEquationalLawWitness.ofGlobalSections raw X i equation) :
    lawWitnessIdealSheaf raw X R hR i hi =
      Scheme.IdealSheafData.ofIdealTop (X := X.underlying)
        (Ideal.span (Set.range equation)) := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [lawWitnessIdealSheaf_ideal, hw, localLawWitnessIdeal]
  simp only [ClosedEquationalLawWitness.ofGlobalSections_coordinate,
    Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨equation a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

/--
An ideal generated in global sections is contained in the scheme-theoretic
kernel exactly when all of its global sections vanish along the morphism.
-/
theorem ofIdealTop_le_schemeKernel_iff
    (I : Ideal Γ(X.underlying, ⊤))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) :
    Scheme.IdealSheafData.ofIdealTop (X := X.underlying) I ≤ s.ker ↔
      I ≤ RingHom.ker s.appTop.hom := by
  constructor
  · intro h f hf
    change s.appTop f = 0
    apply T.IsSheaf.section_ext
    rintro x -
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.underlying.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (s x)) isOpen_univ
    let Vaff : X.underlying.affineOpens := ⟨V, hV⟩
    refine ⟨s ⁻¹ᵁ V, le_top, hxV, ?_⟩
    simp only [homOfLE_leOfHom, map_zero]
    have hmem :
        X.underlying.presheaf.map
            (homOfLE (le_top : V ≤ ⊤)).op f ∈
          (Scheme.IdealSheafData.ofIdealTop
            (X := X.underlying) I).ideal Vaff := by
      rw [Scheme.IdealSheafData.ofIdealTop_ideal]
      exact Ideal.mem_map_of_mem _ hf
    have hzero :
        s.app V
            (X.underlying.presheaf.map
              (homOfLE (le_top : V ≤ ⊤)).op f) = 0 :=
      RingHom.mem_ker.mp
        (s.ideal_ker_le Vaff (h Vaff hmem))
    have hnat :
        s.app V
            (X.underlying.presheaf.map
              (homOfLE (le_top : V ≤ ⊤)).op f) =
          T.presheaf.map
              (homOfLE (le_top : s ⁻¹ᵁ V ≤ ⊤)).op
            (s.appTop f) := by
      simpa only [CommRingCat.comp_apply,
        TopologicalSpace.Opens.map_homOfLE] using
        congr($(s.naturality
          (homOfLE (le_top : V ≤ ⊤)).op).hom f)
    exact hnat.symm.trans hzero
  · intro h
    change Scheme.IdealSheafData.ofIdealTop
        (X := X.underlying) I ≤
      Scheme.IdealSheafData.ofIdeals
        (fun V => RingHom.ker (s.app V).hom)
    apply Scheme.IdealSheafData.le_ofIdeals_iff.mpr
    intro V
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal,
      homOfLE_leOfHom, Ideal.map_le_iff_le_comap,
      RingHom.comap_ker, ← CommRingCat.hom_comp, s.naturality]
    intro f hf
    rw [RingHom.mem_ker, CommRingCat.comp_apply]
    have hzero : s.app ⊤ f = 0 := h hf
    rw [hzero, map_zero]

/--
On any scheme, vanishing of a family of global equations is equivalent to
vanishing of the Mathlib ideal sheaf generated by their span.
-/
theorem globalEquationsVanishAlong_iff_ofIdealTop_span_comap_eq_bot
    (equation : U.Atom → Γ(X.underlying, ⊤))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) :
    GlobalEquationsVanishAlong raw X equation s ↔
      (Scheme.IdealSheafData.ofIdealTop
        (X := X.underlying)
        (Ideal.span (Set.range equation))).comap s = ⊥ := by
  constructor
  · intro h
    apply le_antisymm
    · apply (Scheme.IdealSheafData.map_gc s _ _).mpr
      change Scheme.IdealSheafData.ofIdealTop
        (X := X.underlying)
        (Ideal.span (Set.range equation)) ≤
          (⊥ : T.IdealSheafData).map s
      rw [Scheme.IdealSheafData.map_bot]
      apply (ofIdealTop_le_schemeKernel_iff raw X _ s).mpr
      apply Ideal.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact h a
    · exact bot_le
  · intro h a
    have hcomap :
        (Scheme.IdealSheafData.ofIdealTop
          (X := X.underlying)
          (Ideal.span (Set.range equation))).comap s ≤ ⊥ :=
      h.le
    have hle := (Scheme.IdealSheafData.map_gc s _ _).mp hcomap
    change Scheme.IdealSheafData.ofIdealTop
      (X := X.underlying)
      (Ideal.span (Set.range equation)) ≤
        (⊥ : T.IdealSheafData).map s at hle
    rw [Scheme.IdealSheafData.map_bot] at hle
    have hideal :
        Ideal.span (Set.range equation) ≤
          RingHom.ker s.appTop.hom :=
      (ofIdealTop_le_schemeKernel_iff raw X _ s).mp hle
    exact hideal (Ideal.subset_span ⟨a, rfl⟩)

/-- `ofIdealTop` carries arbitrary suprema of global ideals to ideal-sheaf suprema. -/
theorem ofIdealTop_iSup
    {ι : Type*}
    (I : ι → Ideal Γ(X.underlying, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (X := X.underlying) (⨆ i, I i) =
      ⨆ i, Scheme.IdealSheafData.ofIdealTop (X := X.underlying) (I i) := by
  apply Scheme.IdealSheafData.ext
  funext V
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal,
    Scheme.IdealSheafData.ideal_iSup, iSup_apply, Ideal.map_iSup]

/-! ## Equation-generated scheme realization -/

namespace EquationObservableRealization

variable {raw : RawAmbientRestrictionSystem S k}
variable {X : StandardArchitectureScheme raw}
variable {E : ArchitecturalEquationSystem S.contextPreorder}
variable
  (R : AAT.AG.LawAlgebra.EquationObservableRealization raw X E)

/-- Indices for all context-owned equalizer equations. -/
abbrev GeneratorIndex
    (E : ArchitecturalEquationSystem S.contextPreorder) :=
  Σ W : S.category, E.Index × U.Atom

/-- Indices for all contextual generators of one equation. -/
abbrev WitnessIndex (S : Site.AATSite A) :=
  S.category × U.Atom

/-- Representing equivalence commutes with test-scheme pullback. -/
theorem pointAt_comp
    (hR : IsEquationObservableRealization R)
    {T T' : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) (f : T' ⟶ T) :
    R.pointAt (f ≫ s) =
      EquationArchitecturePoint.pullback f (R.pointAt s) :=
  hR.representingEquiv_natural s f

/-- The represented relative reading is generated by test-scheme pullback. -/
theorem architectureReadingAt_comp
    (hR : IsEquationObservableRealization R)
    {T T' : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) (f : T' ⟶ T) :
    (R.pointAt (f ≫ s)).reading =
      R.reading.pullback f (R.pointAt s).reading := by
  rw [R.pointAt_comp hR s f]
  rfl

/--
Evaluation of an object-dependent residual is generated by pulling back both
the relative architecture reading and the observable point.
-/
theorem residualEvaluation_comp
    (hR : IsEquationObservableRealization R)
    {T T' : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) (f : T' ⟶ T)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    R.evaluation (f ≫ s) W
        (E.equationResidual W (R.architectureAt (f ≫ s)) i a) =
      f.appTop
        (R.evaluation s W
          (E.equationResidual W (R.architectureAt s) i a)) := by
  rw [EquationObservableRealization.evaluation,
    EquationObservableRealization.evaluation,
    EquationObservableRealization.architectureAt,
    EquationObservableRealization.architectureAt,
    R.pointAt_comp hR s f]
  exact R.reading.residual_pullback
    f (R.pointAt s).reading W i a ((R.pointAt s).evaluation W)

/-- Evaluation is the pullback of the universal represented section. -/
theorem evaluation_eq_pullback
    (hR : IsEquationObservableRealization R)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) (W : S.category)
    (x : E.Observable W) :
    R.evaluation s W x = s.appTop (R.sectionMap W x) := by
  change (R.pointAt s).evaluation W x =
    s.appTop
      ((R.pointAt (𝟙 X.underlying)).evaluation W x)
  have hp := R.pointAt_comp hR (𝟙 X.underlying) s
  simp only [Category.comp_id] at hp
  rw [hp]
  rfl

/-- The universal maps preserve the equation presheaf's context restrictions. -/
theorem sectionMap_natural
    {source target : S.category} (f : source ⟶ target)
    (x : E.Observable target) :
    R.sectionMap source (E.restrict f x) =
      R.sectionMap target x :=
  (R.pointAt (𝟙 X.underlying)).evaluation_natural f x

/-- The ambient global section represented by one symbolic coordinate. -/
noncomputable def violationSection
    (W : S.category) (i : E.Index) (a : U.Atom) :
    Γ(X.underlying, ⊤) :=
  R.sectionMap W (E.violationCoordinate W i a)

/-- The regular residual section generated from the universal represented point. -/
noncomputable def ambientResidualSection
    (W : S.category) (i : E.Index) (a : U.Atom) :
    Γ(X.underlying, ⊤) :=
  R.residualSection W i a

/-- Context restriction preserves every universal symbolic section. -/
theorem violationSection_natural
    {source target : S.category} (f : source ⟶ target)
    (i : E.Index) (a : U.Atom) :
    R.violationSection source i a =
      R.violationSection target i a := by
  rw [violationSection, violationSection,
    ← E.violationCoordinate_restrict f i a,
    R.sectionMap_natural f]

/-- The regular equalizer equation generated at one context and Atom. -/
noncomputable def realizationRelation
    (g : GeneratorIndex E) : Γ(X.underlying, ⊤) :=
  R.violationSection g.1 g.2.1 g.2.2 -
    R.ambientResidualSection g.1 g.2.1 g.2.2

/-- The ideal generated by all symbolic-residual equalizer equations. -/
noncomputable def realizationIdeal : Ideal Γ(X.underlying, ⊤) :=
  Ideal.span (Set.range R.realizationRelation)

/-- One equalizer relation restricted to an actual affine chart. -/
noncomputable def chartRealizationRelation
    (j : X.atlas.Index) (g : GeneratorIndex E) :
    Γ((X.atlas.chart j).domain, ⊤) :=
  (X.atlas.chart j).map.appTop (R.realizationRelation g)

/-- The local equalizer ideal generated on an actual affine chart. -/
noncomputable def chartRealizationIdeal
    (j : X.atlas.Index) :
    Ideal Γ((X.atlas.chart j).domain, ⊤) :=
  Ideal.span (Set.range (R.chartRealizationRelation j))

/-- Restriction of the global equalizer ideal is the generated chart ideal. -/
theorem chartRealizationIdeal_eq_map
    (j : X.atlas.Index) :
    R.chartRealizationIdeal j =
      Ideal.map (X.atlas.chart j).map.appTop.hom
        R.realizationIdeal := by
  rw [chartRealizationIdeal, realizationIdeal, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨R.realizationRelation g, ⟨g, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩

/-- The ideal sheaf generated by all symbolic-residual equalizer equations. -/
noncomputable def realizationIdealSheaf : X.underlying.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop R.realizationIdeal

/--
Part III, Definition 5.2B's single equation-generated scheme.  It is the
closed equalizer on which every symbolic coordinate specializes to the
regular residual function of the section-dependent reading.
-/
noncomputable def realizationScheme : AlgebraicGeometry.Scheme :=
  R.realizationIdealSheaf.subscheme

/-- The canonical closed immersion of the equation-generated realization. -/
noncomputable def realizationImmersion :
    R.realizationScheme ⟶ X.underlying :=
  R.realizationIdealSheaf.subschemeι

/-- The equation-generated realization map is a closed immersion. -/
theorem realizationImmersion_isClosedImmersion :
    IsClosedImmersion R.realizationImmersion := by
  change IsClosedImmersion R.realizationIdealSheaf.subschemeι
  infer_instance

/-- The realization immersion has the generated equalizer ideal as kernel. -/
@[simp] theorem realizationImmersion_ker :
    R.realizationImmersion.ker = R.realizationIdealSheaf := by
  change R.realizationIdealSheaf.subschemeι.ker =
    R.realizationIdealSheaf
  exact R.realizationIdealSheaf.ker_subschemeι

/--
The selected affine atlas, viewed as an actual open cover of the ambient
standard architecture scheme.
-/
noncomputable def ambientChartCover : X.underlying.OpenCover :=
  let _ := R
  (X.affineOpenCover raw).openCover

/--
The actual affine-chart cover pulled back to the equation-generated
realization.
-/
noncomputable def realizationChartCover :
    R.realizationScheme.OpenCover :=
  R.ambientChartCover.pullback₁ R.realizationImmersion

/-- The realization chart lying over one selected ambient chart. -/
noncomputable abbrev realizationChart
    (j : X.atlas.Index) : AlgebraicGeometry.Scheme :=
  R.realizationChartCover.X j

/-- The actual open immersion from a realization chart to the realization. -/
noncomputable def realizationChartMap
    (j : X.atlas.Index) :
    R.realizationChart j ⟶ R.realizationScheme :=
  R.realizationChartCover.f j

/-- The pullback projection from a realization chart to its ambient chart. -/
noncomputable def realizationChartToAmbient
    (j : X.atlas.Index) :
    R.realizationChart j ⟶ (X.atlas.chart j).domain :=
  R.ambientChartCover.pullbackHom R.realizationImmersion j

/--
For a test section `s`, the actual chart cover
`T_j = T ×_{X_E} X_{E,j}`.
-/
noncomputable def testChartCover
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) : T.OpenCover :=
  R.realizationChartCover.pullback₁ s

/-- One actual test chart `T_j`. -/
noncomputable abbrev testChart
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (j : X.atlas.Index) :
    AlgebraicGeometry.Scheme :=
  (R.testChartCover s).X j

/-- The actual open immersion `T_j ⟶ T`. -/
noncomputable def testChartMap
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (j : X.atlas.Index) :
    R.testChart s j ⟶ T :=
  (R.testChartCover s).f j

/-- The pullback projection `T_j ⟶ X_{E,j}`. -/
noncomputable def testChartToRealization
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (j : X.atlas.Index) :
    R.testChart s j ⟶ R.realizationChart j :=
  R.realizationChartCover.pullbackHom s j

/-- Evaluation of one observable on the selected ambient chart. -/
noncomputable def chartEvaluation
  (j : X.atlas.Index) (W : S.category) :
    E.Observable W →+*
      Γ((X.atlas.chart j).domain, ⊤) :=
  (X.atlas.chart j).map.appTop.hom.comp
    (R.evaluation (𝟙 X.underlying) W)

/-- Evaluation after restriction to the realization chart. -/
noncomputable def realizationChartEvaluation
    (j : X.atlas.Index) (W : S.category) :
    E.Observable W →+* Γ(R.realizationChart j, ⊤) :=
  (R.realizationChartToAmbient j).appTop.hom.comp
    (R.chartEvaluation j W)

/-- Evaluation on the actual test chart `T_j`. -/
noncomputable def testChartEvaluation
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (j : X.atlas.Index) (W : S.category) :
    E.Observable W →+* Γ(R.testChart s j, ⊤) :=
  (R.testChartToRealization s j).appTop.hom.comp
    (R.realizationChartEvaluation j W)

/-- The realization chart square is the defining pullback square. -/
theorem realizationChart_commutes
    (j : X.atlas.Index) :
    R.realizationChartToAmbient j ≫ (X.atlas.chart j).map =
      R.realizationChartMap j ≫ R.realizationImmersion :=
  R.ambientChartCover.pullbackHom_map R.realizationImmersion j

/-- The test chart square is the defining pullback square. -/
theorem testChart_commutes
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (j : X.atlas.Index) :
    R.testChartToRealization s j ≫ R.realizationChartMap j =
      R.testChartMap s j ≫ s :=
  R.realizationChartCover.pullbackHom_map s j

/--
Chart evaluation is the restriction of the represented global evaluation to
the actual pullback chart `T_j`.
-/
theorem testChartEvaluation_eq_restrict
    (hR : IsEquationObservableRealization R)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (j : X.atlas.Index) (W : S.category)
    (x : E.Observable W) :
    R.testChartEvaluation s j W x =
      (R.testChartMap s j).appTop
        (R.evaluation (s ≫ R.realizationImmersion) W x) := by
  have hpath :
      R.testChartToRealization s j ≫
          R.realizationChartToAmbient j ≫
          (X.atlas.chart j).map =
        R.testChartMap s j ≫ s ≫ R.realizationImmersion := by
    rw [R.realizationChart_commutes j, ← Category.assoc,
      R.testChart_commutes s j, Category.assoc]
  have htop := congrArg AlgebraicGeometry.Scheme.Hom.appTop hpath
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at htop
  change
    (R.testChartToRealization s j).appTop
        ((R.realizationChartToAmbient j).appTop
          ((X.atlas.chart j).map.appTop
            (R.evaluation (𝟙 X.underlying) W x))) =
      (R.testChartMap s j).appTop
        (R.evaluation (s ≫ R.realizationImmersion) W x)
  rw [R.evaluation_eq_pullback hR (𝟙 X.underlying) W x,
    R.evaluation_eq_pullback hR
      (s ≫ R.realizationImmersion) W x]
  simp only [Category.id_comp, AlgebraicGeometry.Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply] at htop ⊢
  exact congrArg
    (fun q : Γ(X.underlying, ⊤) ⟶
        Γ(R.testChart s j, ⊤) =>
      q (R.sectionMap W x)) htop

/-- Chart evaluation commutes with every equation-context restriction. -/
theorem testChartEvaluation_natural
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (j : X.atlas.Index)
    {source target : S.category} (f : source ⟶ target)
    (x : E.Observable target) :
    R.testChartEvaluation s j source (E.restrict f x) =
      R.testChartEvaluation s j target x := by
  change
    (R.testChartToRealization s j).appTop
        ((R.realizationChartToAmbient j).appTop
          ((X.atlas.chart j).map.appTop
            (R.sectionMap source (E.restrict f x)))) =
      (R.testChartToRealization s j).appTop
        ((R.realizationChartToAmbient j).appTop
          ((X.atlas.chart j).map.appTop
            (R.sectionMap target x)))
  rw [R.sectionMap_natural f x]

/-! ### Context-indexed realization charts -/

/--
An actual affine open cover whose index is identified with every equation
context and whose transition maps preserve the context-category functor.
-/
abbrev EquationContextCharts :=
  EquationContextChartCover S X.underlying

/--
The universal observable map on the affine chart selected by `W`.

It is derived by restricting the represented universal point; no chart
evaluation is supplied independently.
-/
noncomputable def contextChartEvaluation
    (C : EquationContextCharts (X := X))
    (W : S.category) :
    E.Observable W →+* Γ(C.chart W, ⊤) :=
  (C.chartMap W).appTop.hom.comp (R.sectionMap W)

/-- Context-chart evaluation commutes with every equation restriction. -/
theorem contextChartEvaluation_natural
    (C : EquationContextCharts (X := X))
    {source target : S.category} (f : source ⟶ target)
    (x : E.Observable target) :
    (C.transition f).appTop
        (R.contextChartEvaluation C target x) =
      R.contextChartEvaluation C source (E.restrict f x) := by
  have hmap := congrArg AlgebraicGeometry.Scheme.Hom.appTop
    (C.transition_to_base f)
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at hmap
  change
    (C.transition f).appTop
        ((C.chartMap target).appTop (R.sectionMap target x)) =
      (C.chartMap source).appTop
        (R.sectionMap source (E.restrict f x))
  rw [R.sectionMap_natural f x]
  exact congrArg (fun q => q (R.sectionMap target x)) hmap

/--
The equation-generated context cover
`X_{E,W} = X_E ×_X X_W`.
-/
noncomputable def contextRealizationCover
    (C : EquationContextCharts (X := X)) :
    R.realizationScheme.OpenCover :=
  (C.cover.pullback₁ R.realizationImmersion).reindex C.contextIndex

/-- The generated realization chart selected by an equation context. -/
noncomputable abbrev contextRealizationChart
    (C : EquationContextCharts (X := X))
    (W : S.category) : AlgebraicGeometry.Scheme :=
  (R.contextRealizationCover C).X W

/-- The actual open immersion `X_{E,W} ⟶ X_E`. -/
noncomputable def contextRealizationChartMap
    (C : EquationContextCharts (X := X))
    (W : S.category) :
    R.contextRealizationChart C W ⟶ R.realizationScheme :=
  (R.contextRealizationCover C).f W

/-- The pullback projection `X_{E,W} ⟶ X_W`. -/
noncomputable def contextRealizationToAmbientChart
    (C : EquationContextCharts (X := X))
    (W : S.category) :
    R.contextRealizationChart C W ⟶ C.chart W :=
  C.cover.pullbackHom R.realizationImmersion (C.contextIndex W)

/-- The context realization square is the defining pullback square. -/
theorem contextRealizationChart_commutes
    (C : EquationContextCharts (X := X))
    (W : S.category) :
    R.contextRealizationToAmbientChart C W ≫ C.chartMap W =
      R.contextRealizationChartMap C W ≫ R.realizationImmersion :=
  C.cover.pullbackHom_map R.realizationImmersion (C.contextIndex W)

/--
For a section `s : T ⟶ X_E`, the context chart
`T_W = T ×_{X_E} X_{E,W}`.
-/
noncomputable def contextTestCover
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) : T.OpenCover :=
  (R.contextRealizationCover C).pullback₁ s

/-- The actual test chart `T_W`. -/
noncomputable abbrev contextTestChart
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (W : S.category) : AlgebraicGeometry.Scheme :=
  (R.contextTestCover C s).X W

/-- The actual open immersion `T_W ⟶ T`. -/
noncomputable def contextTestChartMap
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (W : S.category) :
    R.contextTestChart C s W ⟶ T :=
  (R.contextTestCover C s).f W

/-- The pullback projection `T_W ⟶ X_{E,W}`. -/
noncomputable def contextTestToRealizationChart
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (W : S.category) :
    R.contextTestChart C s W ⟶ R.contextRealizationChart C W :=
  (R.contextRealizationCover C).pullbackHom s W

/-- The context test-chart square is the defining pullback square. -/
theorem contextTestChart_commutes
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (W : S.category) :
    R.contextTestToRealizationChart C s W ≫
        R.contextRealizationChartMap C W =
      R.contextTestChartMap C s W ≫ s :=
  (R.contextRealizationCover C).pullbackHom_map s W

/-- The sheafification/representation map on `X_{E,W}`. -/
noncomputable def contextRealizationEvaluation
    (C : EquationContextCharts (X := X))
    (W : S.category) :
    E.Observable W →+* Γ(R.contextRealizationChart C W, ⊤) :=
  (R.contextRealizationToAmbientChart C W).appTop.hom.comp
    (R.contextChartEvaluation C W)

/--
Definition 5.2A's primary local evaluation
`ev_{s,W} : O_E(W) ⟶ Γ(T_W)`.
-/
noncomputable def contextTestEvaluation
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (W : S.category) :
    E.Observable W →+* Γ(R.contextTestChart C s W, ⊤) :=
  (R.contextTestToRealizationChart C s W).appTop.hom.comp
    (R.contextRealizationEvaluation C W)

/-- Primary local evaluation is the actual restriction of represented evaluation. -/
theorem contextTestEvaluation_eq_restrict
    (hR : IsEquationObservableRealization R)
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (W : S.category) (x : E.Observable W) :
    R.contextTestEvaluation C s W x =
      (R.contextTestChartMap C s W).appTop
        (R.evaluation (s ≫ R.realizationImmersion) W x) := by
  have hpath :
      R.contextTestToRealizationChart C s W ≫
          R.contextRealizationToAmbientChart C W ≫ C.chartMap W =
        R.contextTestChartMap C s W ≫ s ≫
          R.realizationImmersion := by
    rw [R.contextRealizationChart_commutes C W, ← Category.assoc,
      R.contextTestChart_commutes C s W, Category.assoc]
  have htop := congrArg AlgebraicGeometry.Scheme.Hom.appTop hpath
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at htop
  change
    (R.contextTestToRealizationChart C s W).appTop
        ((R.contextRealizationToAmbientChart C W).appTop
          ((C.chartMap W).appTop (R.sectionMap W x))) =
      (R.contextTestChartMap C s W).appTop
        (R.evaluation (s ≫ R.realizationImmersion) W x)
  rw [R.evaluation_eq_pullback hR
    (s ≫ R.realizationImmersion) W x]
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply] at htop ⊢
  exact congrArg (fun q => q (R.sectionMap W x)) htop

/-- Every generated equalizer relation vanishes on the realization scheme. -/
theorem realizationImmersion_relation_zero
    (g : GeneratorIndex E) :
    R.realizationImmersion.appTop (R.realizationRelation g) = 0 := by
  rw [RingHom.mem_ker.symm]
  have hle :
      R.realizationIdealSheaf ≤ R.realizationImmersion.ker := by
    rw [R.realizationImmersion_ker]
  have hideal :
      R.realizationIdeal ≤
        RingHom.ker R.realizationImmersion.appTop.hom :=
    (ofIdealTop_le_schemeKernel_iff raw X
      R.realizationIdeal R.realizationImmersion).mp hle
  exact hideal (Ideal.subset_span ⟨g, rfl⟩)

/--
The architecture reading selected by a test section of the generated scheme.
-/
noncomputable def sectionArchitecture
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ R.realizationScheme) :
    ArchitectureObject U :=
  R.architectureAt (s ≫ R.realizationImmersion)

/-- The actual residual evaluated at one context by a realization section. -/
noncomputable def residualValue
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ R.realizationScheme)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    Γ(T, ⊤) :=
  R.evaluation (s ≫ R.realizationImmersion) W
    (E.equationResidual W (R.sectionArchitecture s) i a)

/--
The equation residual on the actual test chart
`T_j = T ×_{X_E} X_{E,j}`.
-/
noncomputable def testChartResidualValue
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ R.realizationScheme)
    (j : X.atlas.Index) (W : S.category)
    (i : E.Index) (a : U.Atom) :
    Γ(R.testChart s j, ⊤) :=
  R.testChartEvaluation s j W
    (E.equationResidual W (R.sectionArchitecture s) i a)

/-- A chart residual is the actual restriction of its global residual. -/
theorem testChartResidualValue_eq_restrict
    (hR : IsEquationObservableRealization R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ R.realizationScheme)
    (j : X.atlas.Index) (W : S.category)
    (i : E.Index) (a : U.Atom) :
    R.testChartResidualValue s j W i a =
      (R.testChartMap s j).appTop (R.residualValue s W i a) :=
  R.testChartEvaluation_eq_restrict hR s j W
    (E.equationResidual W (R.sectionArchitecture s) i a)

/-- The object residual evaluated on the actual context chart `T_W`. -/
noncomputable def contextTestResidualValue
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    Γ(R.contextTestChart C s W, ⊤) :=
  R.contextTestEvaluation C s W
    (E.equationResidual W (R.sectionArchitecture s) i a)

/-- A context residual is the actual restriction of the represented residual. -/
theorem contextTestResidualValue_eq_restrict
    (hR : IsEquationObservableRealization R)
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    R.contextTestResidualValue C s W i a =
      (R.contextTestChartMap C s W).appTop
        (R.residualValue s W i a) :=
  R.contextTestEvaluation_eq_restrict hR C s W
    (E.equationResidual W (R.sectionArchitecture s) i a)

/--
Part III, Definition 5.2B's named regularity producer.  The regular function
is generated by evaluating the equation residual at the universal represented
point; it is not supplied independently.
-/
theorem residualRegular
    (hR : IsEquationObservableRealization R)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    s.appTop (R.ambientResidualSection W i a) =
      R.evaluation s W
        (E.equationResidual W (R.architectureAt s) i a) := by
  have h :=
    R.residualEvaluation_comp hR (𝟙 X.underlying) s W i a
  simpa only [Category.comp_id, ambientResidualSection,
    EquationObservableRealization.residualSection,
    EquationObservableRealization.sectionMap,
    EquationObservableRealization.evaluation] using h.symm

/--
The standard equalizer constructor proves residual representability by
pulling back its generated relation and the regularity producer.  This is a
theorem, not a separate truth predicate or certificate.
-/
theorem residualRepresentable
    (hR : IsEquationObservableRealization R)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    R.evaluation (s ≫ R.realizationImmersion) W
        (E.violationCoordinate W i a) =
      R.residualValue s W i a := by
  let g : GeneratorIndex E := ⟨W, i, a⟩
  have hzero :
      (s ≫ R.realizationImmersion).appTop
          (R.realizationRelation g) = 0 := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      R.realizationImmersion_relation_zero g, map_zero]
  change
    (s ≫ R.realizationImmersion).appTop
        (R.violationSection W i a -
          R.ambientResidualSection W i a) = 0 at hzero
  rw [map_sub, sub_eq_zero] at hzero
  calc
    R.evaluation (s ≫ R.realizationImmersion) W
        (E.violationCoordinate W i a) =
      (s ≫ R.realizationImmersion).appTop
        (R.violationSection W i a) :=
      R.evaluation_eq_pullback hR
        (s ≫ R.realizationImmersion) W
        (E.violationCoordinate W i a)
    _ = (s ≫ R.realizationImmersion).appTop
        (R.ambientResidualSection W i a) := hzero
    _ = R.residualValue s W i a := by
      exact R.residualRegular hR
        (s ≫ R.realizationImmersion) W i a

/--
Definition 5.2B's residual representability on the actual context pullback
`T_W`.  It is obtained by pulling the universal equalizer equality through
the two defining pullback squares.
-/
theorem contextResidualRepresentable
    (hR : IsEquationObservableRealization R)
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    R.contextTestEvaluation C s W
        (E.violationCoordinate W i a) =
      R.contextTestResidualValue C s W i a := by
  rw [R.contextTestEvaluation_eq_restrict hR C s W,
    R.contextTestResidualValue_eq_restrict hR C s W i a]
  exact congrArg (R.contextTestChartMap C s W).appTop
    (R.residualRepresentable hR s W i a)

/-- The witness ideal generated on one context by the represented universal map. -/
noncomputable def contextWitnessIdeal
    (W : S.category) (i : E.Index) :
    Ideal Γ(X.underlying, ⊤) :=
  Ideal.map (R.sectionMap W) (E.witnessIdeal W i)

/-- A context witness ideal is generated by the mapped symbolic coordinates. -/
theorem contextWitnessIdeal_eq_span
    (W : S.category) (i : E.Index) :
    R.contextWitnessIdeal W i =
      Ideal.span (Set.range (fun a : U.Atom =>
        R.violationSection W i a)) := by
  rw [contextWitnessIdeal, E.witnessIdeal_eq_span, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, rfl⟩

/-- Context restriction identifies the two generated universal ideals. -/
theorem contextWitnessIdeal_eq_of_hom
    {source target : S.category} (f : source ⟶ target)
    (i : E.Index) :
    R.contextWitnessIdeal target i =
      R.contextWitnessIdeal source i := by
  rw [R.contextWitnessIdeal_eq_span target i,
    R.contextWitnessIdeal_eq_span source i]
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, R.violationSection_natural f i a⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, (R.violationSection_natural f i a).symm⟩

/-- The ambient witness ideal generated from every equation-system context. -/
noncomputable def globalWitnessIdeal (i : E.Index) :
    Ideal Γ(X.underlying, ⊤) :=
  ⨆ W : S.category, R.contextWitnessIdeal W i

/-- The ambient witness ideal is the span of all contextual generators. -/
theorem globalWitnessIdeal_eq_span (i : E.Index) :
    R.globalWitnessIdeal i =
      Ideal.span (Set.range (fun wa : WitnessIndex S =>
        R.violationSection wa.1 i wa.2)) := by
  apply le_antisymm
  · rw [globalWitnessIdeal]
    apply iSup_le
    intro W
    rw [R.contextWitnessIdeal_eq_span W i]
    apply Ideal.span_mono
    rintro x ⟨a, rfl⟩
    exact ⟨(W, a), rfl⟩
  · apply Ideal.span_le.mpr
    rintro x ⟨wa, rfl⟩
    have hmem :
        R.violationSection wa.1 i wa.2 ∈
          R.contextWitnessIdeal wa.1 i := by
      rw [R.contextWitnessIdeal_eq_span wa.1 i]
      exact Ideal.subset_span ⟨wa.2, rfl⟩
    exact le_iSup (fun W => R.contextWitnessIdeal W i) wa.1
      hmem

/--
Generator-level provenance for a context-indexed chart cover.

Every global symbolic section restricts to the symbolic coordinate owned by
the selected chart context.  This is the material producer equality used to
identify the sheafified ideal on charts; it contains no residual-vanishing or
factorization conclusion.
-/
structure EquationContextChartProducer
    (C : EquationContextCharts (X := X)) : Prop where
  violation_on_chart :
    ∀ (W V : S.category) (i : E.Index) (a : U.Atom),
      (C.chartMap W).appTop (R.violationSection V i a) =
        R.contextChartEvaluation C W
          (E.violationCoordinate W i a)

/-- The witness ideal generated directly in the context chart ring. -/
noncomputable def contextChartWitnessIdeal
    (C : EquationContextCharts (X := X))
    (W : S.category) (i : E.Index) :
    Ideal Γ(C.chart W, ⊤) :=
  Ideal.map (R.contextChartEvaluation C W) (E.witnessIdeal W i)

/-- The context-chart witness ideal is the span of the represented coordinates. -/
theorem contextChartWitnessIdeal_eq_span
    (C : EquationContextCharts (X := X))
    (W : S.category) (i : E.Index) :
    R.contextChartWitnessIdeal C W i =
      Ideal.span (Set.range (fun a : U.Atom =>
        R.contextChartEvaluation C W
          (E.violationCoordinate W i a))) := by
  rw [contextChartWitnessIdeal, E.witnessIdeal_eq_span, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, rfl⟩

/--
The generator producer identifies the global generated ideal with the ideal
generated in each actual context chart ring.
-/
theorem globalWitnessIdeal_on_contextChart
    (C : EquationContextCharts (X := X))
    (P : EquationContextChartProducer R C)
    (W : S.category) (i : E.Index) :
    Ideal.map (C.chartMap W).appTop.hom (R.globalWitnessIdeal i) =
      R.contextChartWitnessIdeal C W i := by
  rw [R.globalWitnessIdeal_eq_span i,
    R.contextChartWitnessIdeal_eq_span C W i, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨⟨V, a⟩, rfl⟩, rfl⟩
    exact ⟨a, (P.violation_on_chart W V i a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨R.violationSection W i a, ⟨⟨W, a⟩, rfl⟩,
      P.violation_on_chart W W i a⟩

/-- Context restriction carries the target chart ideal onto the source chart ideal. -/
theorem contextChartWitnessIdeal_map_transition
    (C : EquationContextCharts (X := X))
    {source target : S.category} (f : source ⟶ target)
    (i : E.Index) :
    Ideal.map (C.transition f).appTop.hom
        (R.contextChartWitnessIdeal C target i) =
      R.contextChartWitnessIdeal C source i := by
  rw [R.contextChartWitnessIdeal_eq_span C target i,
    R.contextChartWitnessIdeal_eq_span C source i, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    rw [R.contextChartEvaluation_natural C f,
      E.violationCoordinate_restrict f i a]
  · rintro ⟨a, rfl⟩
    refine ⟨R.contextChartEvaluation C target
      (E.violationCoordinate target i a), ⟨a, rfl⟩, ?_⟩
    rw [R.contextChartEvaluation_natural C f,
      E.violationCoordinate_restrict f i a]

/--
The actual context transition ring maps are localizations.

The multiplicative sets and localization instances are the primitive cover
data.  Tensor comparison for generated ideals is derived below.
-/
structure EquationContextChartLocalization
    (C : EquationContextCharts (X := X)) where
  /-- The multiplicative subset inverted by a context transition. -/
  submonoid :
    ∀ {source target : S.category} (f : source ⟶ target),
      Submonoid Γ(C.chart target, ⊤)
  /-- The actual transition map on chart sections is a localization. -/
  isLocalization :
    ∀ {source target : S.category} (f : source ⟶ target),
      letI := (C.transition f).appTop.hom.toAlgebra
      IsLocalization (submonoid f) Γ(C.chart source, ⊤)

/--
Definition 5.2B's context-transition localization producer for the generated
witness ideal.
-/
noncomputable def contextWitnessIdealLocalizes
    (C : EquationContextCharts (X := X))
    (L : EquationContextChartLocalization C)
    {source target : S.category} (f : source ⟶ target)
    (i : E.Index) :
    letI := (C.transition f).appTop.hom.toAlgebra
    Γ(C.chart source, ⊤) ⊗[Γ(C.chart target, ⊤)]
        (R.contextChartWitnessIdeal C target i) ≃ₗ[Γ(C.chart source, ⊤)]
      (R.contextChartWitnessIdeal C source i) := by
  classical
  let g := C.transition f
  letI := g.appTop.hom.toAlgebra
  letI : IsLocalization (L.submonoid f) Γ(C.chart source, ⊤) :=
    L.isLocalization f
  let hbase := IsLocalizedModule.isBaseChange
    (L.submonoid f) Γ(C.chart source, ⊤)
    (Submodule.toLocalized'
      Γ(C.chart source, ⊤) (L.submonoid f)
      (Algebra.linearMap Γ(C.chart target, ⊤) Γ(C.chart source, ⊤))
      (R.contextChartWitnessIdeal C target i))
  exact hbase.equiv.trans
    (LinearEquiv.ofEq _ _
      (by
        exact
          (Ideal.localized'_eq_map
            Γ(C.chart source, ⊤) (L.submonoid f)
            (R.contextChartWitnessIdeal C target i)).trans
              (R.contextChartWitnessIdeal_map_transition C f i)))

/--
All material chart producers required by the standard equation-scheme route.

The fields are actual chart maps, generator equality, and localization data;
no fulfillment/ideal/factorization equivalence is stored.
-/
structure EquationSchemeChartProducer
    (C : EquationContextCharts (X := X)) where
  /-- Generator-level comparison on each context chart. -/
  coordinate : EquationContextChartProducer R C
  /-- Actual context-transition localization. -/
  localization : EquationContextChartLocalization C

/--
Pulling a universal violation section to the actual test chart gives the
represented coordinate owned by that chart context.
-/
theorem contextTest_violation_eq_evaluation
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (W V : S.category) (i : E.Index) (a : U.Atom) :
    (R.contextTestChartMap C s W).appTop
        ((s ≫ R.realizationImmersion).appTop
          (R.violationSection V i a)) =
      R.contextTestEvaluation C s W
        (E.violationCoordinate W i a) := by
  have hpath :
      R.contextTestToRealizationChart C s W ≫
          R.contextRealizationToAmbientChart C W ≫ C.chartMap W =
        R.contextTestChartMap C s W ≫ s ≫
          R.realizationImmersion := by
    rw [R.contextRealizationChart_commutes C W, ← Category.assoc,
      R.contextTestChart_commutes C s W, Category.assoc]
  have htop := congrArg AlgebraicGeometry.Scheme.Hom.appTop hpath
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply] at htop
  change
    (R.contextTestChartMap C s W).appTop
        ((s ≫ R.realizationImmersion).appTop
          (R.violationSection V i a)) =
      (R.contextTestToRealizationChart C s W).appTop
        ((R.contextRealizationToAmbientChart C W).appTop
          (R.contextChartEvaluation C W
            (E.violationCoordinate W i a)))
  rw [← P.coordinate.violation_on_chart W V i a]
  exact congrArg (fun q => q (R.violationSection V i a)) htop.symm

/--
The selected affine chart's witness ideal in its actual global-section ring,
generated directly by the chart evaluation at the context carried by that
chart.
-/
noncomputable def chartWitnessIdeal
    (j : X.atlas.Index) (i : E.Index) :
    Ideal Γ((X.atlas.chart j).domain, ⊤) :=
  Ideal.span (Set.range (fun a : U.Atom =>
    R.chartEvaluation j (X.atlas.chart j).context
      (E.violationCoordinate (X.atlas.chart j).context i a)))

/--
The chart-generated witness ideal is exactly the image of the witness ideal
at the chart's own equation context.
-/
theorem chartWitnessIdeal_eq_map_context
    (j : X.atlas.Index) (i : E.Index) :
    R.chartWitnessIdeal j i =
      Ideal.map (X.atlas.chart j).map.appTop.hom
        (R.contextWitnessIdeal (X.atlas.chart j).context i) := by
  rw [chartWitnessIdeal,
    R.contextWitnessIdeal_eq_span (X.atlas.chart j).context i,
    Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨R.violationSection (X.atlas.chart j).context i a,
      ⟨a, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

/-- The actual Scheme pullback of two selected affine charts. -/
noncomputable abbrev overlapChart
    (R : EquationObservableRealization raw X E)
    (j l : X.atlas.Index) : AlgebraicGeometry.Scheme :=
  X.atlas.actualOverlap raw j l

/-- The actual pullback projection to the left chart. -/
noncomputable def overlapToLeft
    (j l : X.atlas.Index) :
    R.overlapChart j l ⟶ (X.atlas.chart j).domain :=
  pullback.fst (X.atlas.chart j).map (X.atlas.chart l).map

/-- The actual pullback projection to the right chart. -/
noncomputable def overlapToRight
    (j l : X.atlas.Index) :
    R.overlapChart j l ⟶ (X.atlas.chart l).domain :=
  pullback.snd (X.atlas.chart j).map (X.atlas.chart l).map

/-- The left-chart witness ideal after restriction to the actual pair-context ring. -/
noncomputable def overlapWitnessIdealLeft
    (j l : X.atlas.Index) (i : E.Index) :
    Ideal Γ(R.overlapChart j l, ⊤) :=
  Ideal.map (R.overlapToLeft j l).appTop.hom
    (R.chartWitnessIdeal j i)

/-- The right-chart witness ideal after restriction to the actual pair-context ring. -/
noncomputable def overlapWitnessIdealRight
    (j l : X.atlas.Index) (i : E.Index) :
    Ideal Γ(R.overlapChart j l, ⊤) :=
  Ideal.map (R.overlapToRight j l).appTop.hom
    (R.chartWitnessIdeal l i)

/--
Named localization property for the selected chart transitions.  Its ring map
is the actual `appTop` map of `overlapToLeft`; the submonoid is selected cover
data, while the witness-ideal tensor comparison is derived below.
-/
structure EquationChartLocalization
    (R : EquationObservableRealization raw X E) where
  /-- The multiplicative subset inverted by each selected left transition. -/
  submonoid :
    ∀ j l : X.atlas.Index,
      Submonoid Γ((X.atlas.chart j).domain, ⊤)
  /-- Each actual selected left-transition ring map is a localization. -/
  isLocalization :
    ∀ j l : X.atlas.Index,
      letI := (R.overlapToLeft j l).appTop.hom.toAlgebra
      IsLocalization (submonoid j l) Γ(R.overlapChart j l, ⊤)
  /--
  Restriction of the global generated ideal is generated by the equation
  coordinates at the selected chart context.
  -/
  globalWitnessIdeal_restricts :
    ∀ (j : X.atlas.Index) (i : E.Index),
      Ideal.map (X.atlas.chart j).map.appTop.hom
          (R.globalWitnessIdeal i) =
        R.chartWitnessIdeal j i

/-- The chart generator formula exposed in the global-to-local orientation. -/
theorem chartWitnessIdeal_eq_map_global
    (L : EquationChartLocalization R)
    (j : X.atlas.Index) (i : E.Index) :
    R.chartWitnessIdeal j i =
      Ideal.map (X.atlas.chart j).map.appTop.hom
        (R.globalWitnessIdeal i) :=
  (L.globalWitnessIdeal_restricts j i).symm

/--
Part III, Definition 5.2B's localization producer on actual, generally
different chart rings.
-/
noncomputable def witnessIdealLocalizes
    (L : EquationChartLocalization R)
    (j l : X.atlas.Index) (i : E.Index) :
    letI := (R.overlapToLeft j l).appTop.hom.toAlgebra
    Γ(R.overlapChart j l, ⊤) ⊗[Γ((X.atlas.chart j).domain, ⊤)]
        (R.chartWitnessIdeal j i) ≃ₗ[Γ(R.overlapChart j l, ⊤)]
      (R.overlapWitnessIdealLeft j l i) := by
  classical
  let g := R.overlapToLeft j l
  letI := g.appTop.hom.toAlgebra
  letI : IsLocalization (L.submonoid j l)
      Γ(R.overlapChart j l, ⊤) :=
    L.isLocalization j l
  let hbase := IsLocalizedModule.isBaseChange
    (L.submonoid j l) Γ(R.overlapChart j l, ⊤)
    (Submodule.toLocalized'
      Γ(R.overlapChart j l, ⊤) (L.submonoid j l)
      (Algebra.linearMap
        Γ((X.atlas.chart j).domain, ⊤)
        Γ(R.overlapChart j l, ⊤))
      (R.chartWitnessIdeal j i))
  exact hbase.equiv.trans
    (LinearEquiv.ofEq _ _
      (by
        simpa only [overlapWitnessIdealLeft, g] using
          (Ideal.localized'_eq_map
            Γ(R.overlapChart j l, ⊤) (L.submonoid j l)
            (R.chartWitnessIdeal j i))))

/-- Compatibility name exposing the actual chart localization equivalence. -/
noncomputable def witnessIdealLocalizationEquiv
    (L : EquationChartLocalization R)
    (j l : X.atlas.Index) (i : E.Index) :
    letI := (R.overlapToLeft j l).appTop.hom.toAlgebra
    Γ(R.overlapChart j l, ⊤) ⊗[Γ((X.atlas.chart j).domain, ⊤)]
        (R.chartWitnessIdeal j i) ≃ₗ[Γ(R.overlapChart j l, ⊤)]
      (R.overlapWitnessIdealLeft j l i) :=
  R.witnessIdealLocalizes L j l i

/-- The two actual overlap restrictions generate the same witness ideal. -/
theorem overlapWitnessIdeal_left_eq_right
    (L : EquationChartLocalization R)
    (j l : X.atlas.Index) (i : E.Index) :
    R.overlapWitnessIdealLeft j l i =
      R.overlapWitnessIdealRight j l i := by
  rw [overlapWitnessIdealLeft, overlapWitnessIdealRight,
    R.chartWitnessIdeal_eq_map_global L,
    R.chartWitnessIdeal_eq_map_global L,
    Ideal.map_map, Ideal.map_map]
  have hscheme :
      R.overlapToLeft j l ≫ (X.atlas.chart j).map =
        R.overlapToRight j l ≫ (X.atlas.chart l).map :=
    pullback.condition
  have h := congrArg AlgebraicGeometry.Scheme.Hom.appTop hscheme
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at h
  exact congrArg
    (fun q : Γ(X.underlying, ⊤) →+* Γ(R.overlapChart j l, ⊤) =>
      Ideal.map q (R.globalWitnessIdeal i))
    (congrArg CommRingCat.Hom.hom h)

/-- The ambient obstruction ideal is generated from every context. -/
noncomputable def globalObstructionIdeal :
    Ideal Γ(X.underlying, ⊤) :=
  ⨆ W : S.category,
    Ideal.map (R.sectionMap W) (E.obstructionIdeal W)

/-- The global obstruction ideal is the sum of the required global witness ideals. -/
theorem globalObstructionIdeal_eq_iSup_required :
    R.globalObstructionIdeal =
      ⨆ i : E.RequiredIndex, R.globalWitnessIdeal i.1 := by
  simp only [globalObstructionIdeal,
    E.obstructionIdeal_eq_iSup_required, Ideal.map_iSup,
    globalWitnessIdeal, contextWitnessIdeal]
  rw [iSup_comm]

/-- The ambient ideal sheaf generated from all contextual witness ideals. -/
noncomputable def globalWitnessIdealSheaf
    (i : E.Index) : X.underlying.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (R.globalWitnessIdeal i)

/-- The ambient ideal sheaf generated from the global obstruction ideal. -/
noncomputable def globalObstructionIdealSheaf :
    X.underlying.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop R.globalObstructionIdeal

/-- The witness ideal sheaf on the generated realization scheme. -/
noncomputable def witnessIdealSheaf
    (i : E.Index) :
    R.realizationScheme.IdealSheafData :=
  (R.globalWitnessIdealSheaf i).comap
    R.realizationImmersion

/-- The required generated ideal sheaf on the realization scheme. -/
noncomputable def generatedIdealSheaf :
    R.realizationScheme.IdealSheafData :=
  ⨆ i : E.RequiredIndex, R.witnessIdealSheaf i.1

/--
The required generated ideal sheaf is the pullback of the sheaf generated by
the equation system's contextual obstruction ideals.
-/
theorem generatedIdealSheaf_eq_globalObstructionIdealSheaf :
    R.generatedIdealSheaf =
      R.globalObstructionIdealSheaf.comap
        R.realizationImmersion := by
  rw [generatedIdealSheaf, globalObstructionIdealSheaf,
    R.globalObstructionIdeal_eq_iSup_required,
    ofIdealTop_iSup raw X,
    (Scheme.IdealSheafData.map_gc
      R.realizationImmersion).l_iSup]
  rfl

/--
Pullback of an `ofIdealTop` sheaf along an affine open immersion is generated
by the induced map on global sections.
-/
theorem ofIdealTop_comap_of_isOpenImmersion
    {Y Z : AlgebraicGeometry.Scheme} [IsAffine Y]
    (I : Ideal Γ(Z, ⊤)) (g : Y ⟶ Z) [IsOpenImmersion g] :
    (Scheme.IdealSheafData.ofIdealTop I).comap g =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map g.appTop.hom I) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
  let e := g.appIso ⊤
  have comap_inv (J : Ideal Γ(Z,
      g ''ᵁ (⊤ : Y.Opens))) :
      Ideal.comap e.inv.hom J = Ideal.map e.hom.hom J := by
    ext x
    constructor
    · intro hx
      change e.inv x ∈ J at hx
      simpa using Ideal.mem_map_of_mem e.hom.hom hx
    · intro hx
      rw [Ideal.mem_map_iff_of_surjective e.hom.hom
        e.commRingCatIsoToRingEquiv.surjective] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      change e.inv x ∈ J
      rw [← hxy]
      simpa using hy
  rw [comap_inv, Ideal.map_map]
  have appTop_eq :
      e.hom.hom.comp
          (Z.presheaf.map (homOfLE le_top).op).hom =
        g.appTop.hom := by
    apply RingHom.ext
    intro z
    change
      ((Z.presheaf.map (homOfLE le_top).op) ≫ e.hom) z =
        g.appTop z
    simp only [e, Scheme.Hom.appIso_hom]
    rw [← Category.assoc, g.naturality, Category.assoc,
      ← Functor.map_comp]
    simp
  rw [appTop_eq]
  have top_res :
      (Y.presheaf.map (homOfLE le_top).op).hom =
        RingHom.id Γ(Y, ⊤) := by
    apply RingHom.ext
    intro z
    have h := Y.presheaf.map_id (Opposite.op (⊤ : Y.Opens))
    exact congrArg (fun q => q z) h
  rw [top_res, Ideal.map_id]

/--
Definition 5.2B's chart theorem, derived from generator provenance rather than
accepted as an ideal equality field.
-/
theorem contextWitnessIdealChart
    (C : EquationContextCharts (X := X))
    (P : EquationContextChartProducer R C)
    (W : S.category) (i : E.Index) :
    (R.globalWitnessIdealSheaf i).comap (C.chartMap W) =
      Scheme.IdealSheafData.ofIdealTop
        (R.contextChartWitnessIdeal C W i) := by
  letI : IsOpenImmersion (C.chartMap W) :=
    C.cover.map_prop (C.contextIndex W)
  letI : IsAffine (C.chart W) := C.chartAffine W
  rw [globalWitnessIdealSheaf,
    ofIdealTop_comap_of_isOpenImmersion]
  exact congrArg Scheme.IdealSheafData.ofIdealTop
    (R.globalWitnessIdeal_on_contextChart C P W i)

/--
The equalizer ideal sheaf restricts on every actual ambient chart to the
locally generated equalizer ideal.
-/
theorem realizationIdealChart
    (j : X.atlas.Index) :
    R.realizationIdealSheaf.comap (X.atlas.chart j).map =
      Scheme.IdealSheafData.ofIdealTop
        (R.chartRealizationIdeal j) := by
  letI : IsOpenImmersion (X.atlas.chart j).map :=
    (X.atlasValid.chart_valid j).isOpenImmersion
  letI : IsAffine (X.atlas.chart j).domain :=
    (X.atlas.chart j).domain_isAffine
  rw [realizationIdealSheaf,
    ofIdealTop_comap_of_isOpenImmersion]
  exact congrArg Scheme.IdealSheafData.ofIdealTop
    (R.chartRealizationIdeal_eq_map j).symm

/--
Part III, Definition 5.2B's chart producer: the ambient witness ideal sheaf
restricts to the ideal sheaf associated to all represented contextual
generators on every selected affine chart.
-/
theorem witnessIdealChart
    (L : EquationChartLocalization R)
    (j : X.atlas.Index) (i : E.Index) :
    (R.globalWitnessIdealSheaf i).comap
        (X.atlas.chart j).map =
      Scheme.IdealSheafData.ofIdealTop
        (R.chartWitnessIdeal j i) := by
  letI : IsOpenImmersion (X.atlas.chart j).map :=
    (X.atlasValid.chart_valid j).isOpenImmersion
  letI : IsAffine (X.atlas.chart j).domain :=
    (X.atlas.chart j).domain_isAffine
  rw [globalWitnessIdealSheaf,
    ofIdealTop_comap_of_isOpenImmersion]
  exact congrArg Scheme.IdealSheafData.ofIdealTop
    (L.globalWitnessIdeal_restricts j i)

/--
Part III, Definition 5.2B's quasi-coherence producer, expressed by Mathlib's
defining affine-basic-open localization criterion for ideal sheaves.
-/
theorem witnessIdealQuasiCoherent
    (i : E.Index) :
    ∀ (V : R.realizationScheme.affineOpens)
      (f : Γ(R.realizationScheme, V)),
      Ideal.map
          (R.realizationScheme.presheaf.map
            (homOfLE (R.realizationScheme.basicOpen_le f)).op).hom
          ((R.witnessIdealSheaf i).ideal V) =
        (R.witnessIdealSheaf i).ideal
          (R.realizationScheme.affineBasicOpen f) :=
  (R.witnessIdealSheaf i).map_ideal_basicOpen

/--
Derived chart package for one equation: actual chart ideals, equality on
pair-context overlaps, localization of the ideal module, and Mathlib
quasi-coherence.
-/
def EquationWitnessChartRealized
    (L : EquationChartLocalization R) (i : E.Index) : Prop :=
  (∀ j : X.atlas.Index,
    (R.globalWitnessIdealSheaf i).comap (X.atlas.chart j).map =
      Scheme.IdealSheafData.ofIdealTop (R.chartWitnessIdeal j i)) ∧
  (∀ j l : X.atlas.Index,
    R.overlapWitnessIdealLeft j l i =
      R.overlapWitnessIdealRight j l i) ∧
  (∀ j l : X.atlas.Index,
    Function.Bijective
      (R.witnessIdealLocalizes L j l i)) ∧
  ∀ (V : R.realizationScheme.affineOpens)
    (f : Γ(R.realizationScheme, V)),
    Ideal.map
        (R.realizationScheme.presheaf.map
          (homOfLE (R.realizationScheme.basicOpen_le f)).op).hom
        ((R.witnessIdealSheaf i).ideal V) =
      (R.witnessIdealSheaf i).ideal
        (R.realizationScheme.affineBasicOpen f)

/-- All chart clauses are generated from the selected localization property. -/
theorem equationWitnessChartRealized
    (L : EquationChartLocalization R) (i : E.Index) :
    R.EquationWitnessChartRealized L i := by
  refine ⟨fun j => R.witnessIdealChart L j i,
    fun j l => R.overlapWitnessIdeal_left_eq_right L j l i,
    ?_, R.witnessIdealQuasiCoherent i⟩
  intro j l
  exact (R.witnessIdealLocalizes L j l i).bijective

/--
The chart-generated geometric condition for one equation along a section.
It combines vanishing of the glued ideal sheaf with the concrete localization
and overlap data that identify its chart generators.
-/
def EquationIdealChartCondition
    (L : EquationChartLocalization R)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (i : E.Index) : Prop :=
  (R.witnessIdealSheaf i).comap s = ⊥ ∧
    R.EquationWitnessChartRealized L i

/-- The context transition induced on generated realization charts. -/
noncomputable def contextRealizationTransition
    (C : EquationContextCharts (X := X))
    {source target : S.category} (f : source ⟶ target) :
    R.contextRealizationChart C source ⟶
      R.contextRealizationChart C target :=
  pullback.lift
    (R.contextRealizationChartMap C source)
    (R.contextRealizationToAmbientChart C source ≫ C.transition f)
    (by
      calc
        R.contextRealizationChartMap C source ≫
            R.realizationImmersion =
          R.contextRealizationToAmbientChart C source ≫
            C.chartMap source :=
          (R.contextRealizationChart_commutes C source).symm
        _ =
          R.contextRealizationToAmbientChart C source ≫
            (C.transition f ≫ C.chartMap target) := by
          rw [C.transition_to_base f]
        _ =
          (R.contextRealizationToAmbientChart C source ≫
            C.transition f) ≫ C.chartMap target :=
          (Category.assoc _ _ _).symm)

/-- A realization-chart transition preserves the map to `X_E`. -/
@[reassoc] theorem contextRealizationTransition_to_realization
    (C : EquationContextCharts (X := X))
    {source target : S.category} (f : source ⟶ target) :
    R.contextRealizationTransition C f ≫
        R.contextRealizationChartMap C target =
      R.contextRealizationChartMap C source :=
  pullback.lift_fst _ _ _

/-- A realization-chart transition is induced by the ambient context transition. -/
@[reassoc] theorem contextRealizationTransition_to_ambient
    (C : EquationContextCharts (X := X))
    {source target : S.category} (f : source ⟶ target) :
    R.contextRealizationTransition C f ≫
        R.contextRealizationToAmbientChart C target =
      R.contextRealizationToAmbientChart C source ≫ C.transition f :=
  pullback.lift_snd _ _ _

/-- The context transition induced on actual test charts. -/
noncomputable def contextTestTransition
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    {source target : S.category} (f : source ⟶ target) :
    R.contextTestChart C s source ⟶
      R.contextTestChart C s target :=
  pullback.lift
    (R.contextTestChartMap C s source)
    (R.contextTestToRealizationChart C s source ≫
      R.contextRealizationTransition C f)
    (by
      calc
        R.contextTestChartMap C s source ≫ s =
            R.contextTestToRealizationChart C s source ≫
              R.contextRealizationChartMap C source :=
          (R.contextTestChart_commutes C s source).symm
        _ = R.contextTestToRealizationChart C s source ≫
              (R.contextRealizationTransition C f ≫
                R.contextRealizationChartMap C target) := by
          rw [R.contextRealizationTransition_to_realization C f])

/-- A test-chart transition preserves the map to the test Scheme. -/
@[reassoc] theorem contextTestTransition_to_test
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    {source target : S.category} (f : source ⟶ target) :
    R.contextTestTransition C s f ≫
        R.contextTestChartMap C s target =
      R.contextTestChartMap C s source :=
  pullback.lift_fst _ _ _

/-- A test-chart transition is induced by the realization-chart transition. -/
@[reassoc] theorem contextTestTransition_to_realization
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    {source target : S.category} (f : source ⟶ target) :
    R.contextTestTransition C s f ≫
        R.contextTestToRealizationChart C s target =
      R.contextTestToRealizationChart C s source ≫
        R.contextRealizationTransition C f :=
  pullback.lift_snd _ _ _

/-- The primary local evaluations commute with actual context transitions. -/
theorem contextTestEvaluation_natural
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    {source target : S.category} (f : source ⟶ target)
    (x : E.Observable target) :
    (R.contextTestTransition C s f).appTop
        (R.contextTestEvaluation C s target x) =
      R.contextTestEvaluation C s source (E.restrict f x) := by
  have hpath :
      R.contextTestTransition C s f ≫
          R.contextTestToRealizationChart C s target ≫
          R.contextRealizationToAmbientChart C target =
        R.contextTestToRealizationChart C s source ≫
          R.contextRealizationToAmbientChart C source ≫
          C.transition f := by
    rw [← Category.assoc,
      R.contextTestTransition_to_realization C s f,
      Category.assoc,
      R.contextRealizationTransition_to_ambient C f]
  have htop := congrArg AlgebraicGeometry.Scheme.Hom.appTop hpath
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at htop
  change
    (R.contextTestTransition C s f).appTop
        ((R.contextTestToRealizationChart C s target).appTop
          ((R.contextRealizationToAmbientChart C target).appTop
            (R.contextChartEvaluation C target x))) =
      (R.contextTestToRealizationChart C s source).appTop
        ((R.contextRealizationToAmbientChart C source).appTop
          (R.contextChartEvaluation C source (E.restrict f x)))
  rw [← R.contextChartEvaluation_natural C f x]
  exact congrArg (fun q => q (R.contextChartEvaluation C target x)) htop

/-- Global residual fulfillment, used as the affine-cover comparison target. -/
def GlobalEquationHoldsAlong
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (i : E.Index) : Prop :=
  ∀ (W : S.category) (a : U.Atom),
    R.residualValue s W i a = 0

/--
Definition 5.2A fulfillment: each context residual vanishes on its own actual
pullback chart `T_W`.
-/
def EquationHoldsAlong
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (i : E.Index) : Prop :=
  ∀ (W : S.category) (a : U.Atom),
    R.contextTestResidualValue C s W i a = 0

/--
The representing component condition for a selected architecture point.

The local evaluation itself is already generated from the representing
equivalence and the context-chart pullback.  This proposition only records
that the selected component is invertible; `κ` is constructed below.
-/
def IsEquationPointComponent
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) : Prop :=
  ∀ W : S.category,
    Function.Bijective (R.contextTestEvaluation C s W)

namespace EquationPointComponent

/--
Part III, Definition 5.2A's `κ_{A,W}`, constructed from the generated
architecture-evaluation component.
-/
noncomputable def kappa
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    {s : T ⟶ R.realizationScheme}
    (hK : R.IsEquationPointComponent C s)
    (W : S.category) :
    Γ(R.contextTestChart C s W, ⊤) ≃+* E.Observable W :=
  (RingEquiv.ofBijective
    (R.contextTestEvaluation C s W) (hK W)).symm

/-- `κ` sends the generated local evaluation back to its observable. -/
@[simp] theorem kappa_contextTestEvaluation
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    {s : T ⟶ R.realizationScheme}
    (hK : R.IsEquationPointComponent C s)
    (W : S.category) (x : E.Observable W) :
    (EquationPointComponent.kappa (R := R) C hK W)
        (R.contextTestEvaluation C s W x) = x :=
  (RingEquiv.ofBijective
    (R.contextTestEvaluation C s W) (hK W)).symm_apply_apply x

/-- The generated `κ` components are natural for context restriction. -/
theorem kappa_natural
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    {s : T ⟶ R.realizationScheme}
    (hK : R.IsEquationPointComponent C s)
    {source target : S.category} (f : source ⟶ target)
    (y : Γ(R.contextTestChart C s target, ⊤)) :
    (EquationPointComponent.kappa (R := R) C hK source)
        ((R.contextTestTransition C s f).appTop y) =
      E.restrict f
        ((EquationPointComponent.kappa (R := R) C hK target) y) := by
  let eTarget :=
    RingEquiv.ofBijective
      (R.contextTestEvaluation C s target) (hK target)
  have hy :
      R.contextTestEvaluation C s target
          ((EquationPointComponent.kappa (R := R) C hK target) y) = y :=
    eTarget.apply_symm_apply y
  conv_lhs => rw [← hy]
  rw [R.contextTestEvaluation_natural C s f]
  exact EquationPointComponent.kappa_contextTestEvaluation
    (R := R) C hK source
      (E.restrict f
        ((EquationPointComponent.kappa (R := R) C hK target) y))

/-- `κ` identifies the actual context residual with the object residual. -/
theorem kappa_contextTestResidualValue
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    {s : T ⟶ R.realizationScheme}
    (hK : R.IsEquationPointComponent C s)
    (W : S.category) (i : E.Index) (a : U.Atom) :
    (EquationPointComponent.kappa (R := R) C hK W)
        (R.contextTestResidualValue C s W i a) =
      E.equationResidual W (R.sectionArchitecture s) i a :=
  EquationPointComponent.kappa_contextTestEvaluation
    (R := R) C hK W
      (E.equationResidual W (R.sectionArchitecture s) i a)

end EquationPointComponent

/-- Required section-level lawfulness is generated from actual context residuals. -/
def EquationLawfulAlong
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) : Prop :=
  ∀ i : E.Index, E.Required i →
    R.EquationHoldsAlong C s i

/-- Object-level fulfillment transfers to every actual context chart. -/
theorem equationHoldsAlong_of_equationHolds
    (C : EquationContextCharts (X := X))
    (Obj : ArchitectureObject U)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (i : E.Index)
    (hObj : R.sectionArchitecture s = Obj)
    (h : E.EquationHolds i Obj) :
    R.EquationHoldsAlong C s i := by
  intro W a
  simp only [contextTestResidualValue, hObj, h W a, map_zero]

/--
At a selected representing component, scheme-chart fulfillment is equivalent
to object fulfillment.
-/
theorem equationHoldsAlong_iff_equationHolds
    (C : EquationContextCharts (X := X))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (hK : R.IsEquationPointComponent C s)
    (i : E.Index) :
    R.EquationHoldsAlong C s i ↔
      E.EquationHolds i (R.sectionArchitecture s) := by
  constructor
  · intro h W a
    have hκ := congrArg
      (EquationPointComponent.kappa (R := R) C hK W) (h W a)
    rw [EquationPointComponent.kappa_contextTestResidualValue
      (R := R) C hK W i a, map_zero] at hκ
    exact hκ
  · intro h
    exact R.equationHoldsAlong_of_equationHolds
      C (R.sectionArchitecture s) s i rfl h

/-- An identified object reading transfers object-level required lawfulness. -/
theorem equationLawfulAlong_of_equationLawful
    (C : EquationContextCharts (X := X))
    (Obj : ArchitectureObject U)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme)
    (hObj : R.sectionArchitecture s = Obj)
    (h : E.EquationLawful Obj) :
    R.EquationLawfulAlong C s := by
  intro i hi
  exact R.equationHoldsAlong_of_equationHolds
    C Obj s i hObj (h i hi)

theorem vanish_iff_ofIdealTop_span_comap_eq_bot
    {ι : Type w} (equation : ι → Γ(X.underlying, ⊤))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) :
    (∀ j, s.appTop (equation j) = 0) ↔
      (Scheme.IdealSheafData.ofIdealTop
        (X := X.underlying)
        (Ideal.span (Set.range equation))).comap s = ⊥ := by
  constructor
  · intro h
    apply le_antisymm
    · apply (Scheme.IdealSheafData.map_gc s _ _).mpr
      change Scheme.IdealSheafData.ofIdealTop
        (X := X.underlying)
        (Ideal.span (Set.range equation)) ≤
          (⊥ : T.IdealSheafData).map s
      rw [Scheme.IdealSheafData.map_bot]
      apply (ofIdealTop_le_schemeKernel_iff raw X _ s).mpr
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact h j
    · exact bot_le
  · intro h j
    have hcomap :
        (Scheme.IdealSheafData.ofIdealTop
          (X := X.underlying)
          (Ideal.span (Set.range equation))).comap s ≤ ⊥ :=
      h.le
    have hle := (Scheme.IdealSheafData.map_gc s _ _).mp hcomap
    change Scheme.IdealSheafData.ofIdealTop
      (X := X.underlying)
      (Ideal.span (Set.range equation)) ≤
        (⊥ : T.IdealSheafData).map s at hle
    rw [Scheme.IdealSheafData.map_bot] at hle
    have hideal :
        Ideal.span (Set.range equation) ≤
          RingHom.ker s.appTop.hom :=
      (ofIdealTop_le_schemeKernel_iff raw X _ s).mp hle
    exact hideal (Ideal.subset_span ⟨j, rfl⟩)

/-- Equalizer-relation vanishing is exactly the generated realization ideal. -/
theorem realizationRelationsVanishAlong_iff_ideal
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) :
    (∀ g : GeneratorIndex E,
      s.appTop (R.realizationRelation g) = 0) ↔
      R.realizationIdealSheaf.comap s = ⊥ := by
  rw [realizationIdealSheaf, realizationIdeal]
  exact vanish_iff_ofIdealTop_span_comap_eq_bot
    (raw := raw) (X := X) R.realizationRelation s

/-- Factorizations through the generated symbolic-residual equalizer. -/
def FactorsThroughRealization
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) :=
  {t : T ⟶ R.realizationScheme //
    t ≫ R.realizationImmersion = s}

/-- Equalizer-ideal vanishing is exactly factorization through the realization. -/
theorem realizationIdeal_iff_nonempty_factorsThrough
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ X.underlying) :
    R.realizationIdealSheaf.comap s = ⊥ ↔
      Nonempty (R.FactorsThroughRealization s) := by
  constructor
  · intro hs
    have hle : R.realizationIdealSheaf ≤ s.ker := by
      rw [← Scheme.IdealSheafData.map_bot,
        ← Scheme.IdealSheafData.map_gc]
      exact hs.le
    letI : IsClosedImmersion R.realizationImmersion :=
      R.realizationImmersion_isClosedImmersion
    let lift :=
      IsClosedImmersion.lift R.realizationImmersion s (by
        rw [R.realizationImmersion_ker]
        exact hle)
    exact ⟨⟨lift, IsClosedImmersion.lift_fac _ _ _⟩⟩
  · rintro ⟨t⟩
    rw [eq_bot_iff]
    apply (Scheme.IdealSheafData.map_gc s _ ⊥).mpr
    change R.realizationIdealSheaf ≤
      (⊥ : T.IdealSheafData).map s
    rw [Scheme.IdealSheafData.map_bot, ← t.2]
    exact R.realizationImmersion_ker.symm.le.trans
      (Scheme.Hom.le_ker_comp t.1 R.realizationImmersion)

/--
Actual context residuals vanish exactly when every universal violation
generator vanishes after pullback to the test scheme.

This is private so the public correspondence cannot bypass the required chart
producer package.
-/
private theorem equationHoldsAlong_iff_violationVanishes
    (hR : IsEquationObservableRealization R)
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (i : E.Index) :
    R.EquationHoldsAlong C s i ↔
      ∀ (V : S.category) (a : U.Atom),
        (s ≫ R.realizationImmersion).appTop
          (R.violationSection V i a) = 0 := by
  constructor
  · intro h V a
    apply AlgebraicGeometry.Scheme.zero_of_zero_cover
      ((s ≫ R.realizationImmersion).appTop
        (R.violationSection V i a))
      (R.contextTestCover C s)
    intro W
    have hlocal :
        R.contextTestEvaluation C s W
            (E.violationCoordinate W i a) = 0 := by
      rw [R.contextResidualRepresentable hR C s W i a]
      exact h W a
    have hchart :=
      (R.contextTest_violation_eq_evaluation C P s W V i a).trans hlocal
    exact hchart
  · intro h W a
    rw [← R.contextResidualRepresentable hR C s W i a,
      ← R.contextTest_violation_eq_evaluation C P s W W i a,
      h W a, map_zero]

/--
Part III, Theorem 5.2C: actual context residual fulfillment is exactly
vanishing of the generated witness-ideal sheaf.

The theorem requires the complete chart producer, including actual transition
localizations; callers cannot apply the correspondence from residual
predicates or manually supplied ideal equalities.
-/
theorem equationHoldsAlong_iff_witnessIdeal
    (hR : IsEquationObservableRealization R)
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (i : E.Index) :
    R.EquationHoldsAlong C s i ↔
      (R.witnessIdealSheaf i).comap s = ⊥ := by
  have hviolation :
      (∀ (W : S.category) (a : U.Atom),
        (s ≫ R.realizationImmersion).appTop
          (R.violationSection W i a) = 0) ↔
        (R.globalWitnessIdealSheaf i).comap
          (s ≫ R.realizationImmersion) = ⊥ := by
    rw [globalWitnessIdealSheaf, R.globalWitnessIdeal_eq_span i]
    constructor
    · intro h
      apply (vanish_iff_ofIdealTop_span_comap_eq_bot
        (raw := raw) (X := X)
        (fun wa : WitnessIndex S =>
          R.violationSection wa.1 i wa.2)
        (s ≫ R.realizationImmersion)).mp
      intro wa
      exact h wa.1 wa.2
    · intro h W a
      exact (vanish_iff_ofIdealTop_span_comap_eq_bot
        (raw := raw) (X := X)
        (fun wa : WitnessIndex S =>
          R.violationSection wa.1 i wa.2)
        (s ≫ R.realizationImmersion)).mpr h (W, a)
  rw [R.equationHoldsAlong_iff_violationVanishes hR C P s i,
    witnessIdealSheaf, ← Scheme.IdealSheafData.comap_comp]
  exact hviolation

/-- Actual context-chart fulfillment is preserved by test-scheme base change. -/
theorem equationHoldsAlong_comp
    (hR : IsEquationObservableRealization R)
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    {T T' : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (f : T' ⟶ T)
    (i : E.Index) (h : R.EquationHoldsAlong C s i) :
    R.EquationHoldsAlong C (f ≫ s) i := by
  apply (R.equationHoldsAlong_iff_witnessIdeal hR C P (f ≫ s) i).mpr
  rw [Scheme.IdealSheafData.comap_comp,
    (R.equationHoldsAlong_iff_witnessIdeal hR C P s i).mp h,
    Scheme.IdealSheafData.comap_bot]

/-- The closed zero locus of one equation's generated witness ideal sheaf. -/
noncomputable def equationClosedSubscheme
    (i : E.Index) : AlgebraicGeometry.Scheme :=
  (R.witnessIdealSheaf i).subscheme

/-- The canonical immersion of one equation's generated zero locus. -/
noncomputable def equationClosedImmersion
    (i : E.Index) :
    R.equationClosedSubscheme i ⟶ R.realizationScheme :=
  (R.witnessIdealSheaf i).subschemeι

/-- A single-equation zero locus is a closed subscheme. -/
theorem equationClosedImmersion_isClosedImmersion
    (i : E.Index) :
    IsClosedImmersion (R.equationClosedImmersion i) := by
  change IsClosedImmersion (R.witnessIdealSheaf i).subschemeι
  infer_instance

/-- The single-equation immersion has its generated witness ideal as kernel. -/
@[simp] theorem equationClosedImmersion_ker
    (i : E.Index) :
    (R.equationClosedImmersion i).ker =
      R.witnessIdealSheaf i := by
  change (R.witnessIdealSheaf i).subschemeι.ker =
    R.witnessIdealSheaf i
  exact (R.witnessIdealSheaf i).ker_subschemeι

/-- Factorizations through one equation's generated zero locus. -/
def FactorsThroughEquationClosedSubscheme
    (i : E.Index)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) :=
  {t : T ⟶ R.equationClosedSubscheme i //
    t ≫ R.equationClosedImmersion i = s}

/-- One generated witness ideal vanishes exactly along its closed zero locus. -/
theorem witnessIdeal_iff_nonempty_factorsThrough
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (i : E.Index) :
    (R.witnessIdealSheaf i).comap s = ⊥ ↔
      Nonempty (R.FactorsThroughEquationClosedSubscheme i s) := by
  constructor
  · intro hs
    have hle : R.witnessIdealSheaf i ≤ s.ker := by
      rw [← Scheme.IdealSheafData.map_bot,
        ← Scheme.IdealSheafData.map_gc]
      exact hs.le
    letI : IsClosedImmersion (R.equationClosedImmersion i) :=
      R.equationClosedImmersion_isClosedImmersion i
    let lift :=
      IsClosedImmersion.lift (R.equationClosedImmersion i) s (by
        rw [R.equationClosedImmersion_ker i]
        exact hle)
    exact ⟨⟨lift, IsClosedImmersion.lift_fac _ _ _⟩⟩
  · rintro ⟨t⟩
    rw [eq_bot_iff]
    apply (Scheme.IdealSheafData.map_gc s _ ⊥).mpr
    change R.witnessIdealSheaf i ≤
      (⊥ : T.IdealSheafData).map s
    rw [Scheme.IdealSheafData.map_bot, ← t.2]
    exact (R.equationClosedImmersion_ker i).symm.le.trans
      (Scheme.Hom.le_ker_comp t.1 (R.equationClosedImmersion i))

/--
Part III, Theorem 5.2C: one equation holds exactly when the section factors
through its generated closed zero locus.
-/
theorem equationHoldsAlong_iff_nonempty_factorsThrough
    (hR : IsEquationObservableRealization R)
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (i : E.Index) :
    R.EquationHoldsAlong C s i ↔
      Nonempty (R.FactorsThroughEquationClosedSubscheme i s) :=
  (R.equationHoldsAlong_iff_witnessIdeal hR C P s i).trans
    (R.witnessIdeal_iff_nonempty_factorsThrough s i)

/--
Part III, Theorem 5.2C: one equation holds exactly when its generated ideal
vanishes and exactly when the section factors through the associated closed
zero locus.
-/
theorem equationIdealFactorizationCorrespondence
    (hR : IsEquationObservableRealization R)
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) (i : E.Index) :
    (R.EquationHoldsAlong C s i ↔
      (R.witnessIdealSheaf i).comap s = ⊥) ∧
    ((R.witnessIdealSheaf i).comap s = ⊥ ↔
      Nonempty (R.FactorsThroughEquationClosedSubscheme i s)) := by
  exact ⟨R.equationHoldsAlong_iff_witnessIdeal hR C P s i,
    R.witnessIdeal_iff_nonempty_factorsThrough s i⟩

/-- Required residual lawfulness is exactly generated-ideal vanishing. -/
theorem equationLawfulAlong_iff_generatedIdeal
    (hR : IsEquationObservableRealization R)
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) :
    R.EquationLawfulAlong C s ↔
      R.generatedIdealSheaf.comap s = ⊥ := by
  rw [EquationLawfulAlong, generatedIdealSheaf,
    (Scheme.IdealSheafData.map_gc s).l_iSup]
  constructor
  · intro h
    rw [iSup_eq_bot]
    intro i
    exact (R.equationHoldsAlong_iff_witnessIdeal hR C P s i.1).mp
      (h i.1 i.2)
  · intro h i hi
    apply (R.equationHoldsAlong_iff_witnessIdeal hR C P s i).mpr
    rw [iSup_eq_bot] at h
    exact h ⟨i, hi⟩

/-- The lawful closed subscheme inside the equation-generated realization. -/
noncomputable def lawfulClosedSubscheme : AlgebraicGeometry.Scheme :=
  R.generatedIdealSheaf.subscheme

/-- The canonical closed immersion of the generated lawful subscheme. -/
noncomputable def lawfulClosedImmersion :
    R.lawfulClosedSubscheme ⟶ R.realizationScheme :=
  R.generatedIdealSheaf.subschemeι

/-- The generated lawful map is a closed immersion. -/
theorem lawfulClosedImmersion_isClosedImmersion :
    IsClosedImmersion R.lawfulClosedImmersion := by
  change IsClosedImmersion R.generatedIdealSheaf.subschemeι
  infer_instance

/-- The generated lawful immersion has the generated ideal sheaf as kernel. -/
@[simp] theorem lawfulClosedImmersion_ker :
    R.lawfulClosedImmersion.ker = R.generatedIdealSheaf := by
  change R.generatedIdealSheaf.subschemeι.ker =
    R.generatedIdealSheaf
  exact R.generatedIdealSheaf.ker_subschemeι

/-- Factorizations through the generated lawful closed subscheme. -/
def FactorsThroughLawfulClosedSubscheme
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) :=
  {t : T ⟶ R.lawfulClosedSubscheme //
    t ≫ R.lawfulClosedImmersion = s}

/-- Generated-ideal vanishing is exactly actual factorization. -/
theorem generatedIdeal_iff_nonempty_factorsThrough
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) :
    R.generatedIdealSheaf.comap s = ⊥ ↔
      Nonempty (R.FactorsThroughLawfulClosedSubscheme s) := by
  constructor
  · intro hs
    have hle : R.generatedIdealSheaf ≤ s.ker := by
      rw [← Scheme.IdealSheafData.map_bot,
        ← Scheme.IdealSheafData.map_gc]
      exact hs.le
    letI : IsClosedImmersion R.lawfulClosedImmersion :=
      R.lawfulClosedImmersion_isClosedImmersion
    let lift :=
      IsClosedImmersion.lift R.lawfulClosedImmersion s (by
        rw [R.lawfulClosedImmersion_ker]
        exact hle)
    exact ⟨⟨lift, IsClosedImmersion.lift_fac _ _ _⟩⟩
  · rintro ⟨t⟩
    rw [eq_bot_iff]
    apply (Scheme.IdealSheafData.map_gc s _ ⊥).mpr
    change R.generatedIdealSheaf ≤
      (⊥ : T.IdealSheafData).map s
    rw [Scheme.IdealSheafData.map_bot, ← t.2]
    exact R.lawfulClosedImmersion_ker.symm.le.trans
      (Scheme.Hom.le_ker_comp t.1 R.lawfulClosedImmersion)

/--
Actual required residual lawfulness, generated-ideal vanishing, and
factorization through the generated lawful closed subscheme agree.
-/
theorem lawfulnessIdealFactorizationCorrespondence
    (hR : IsEquationObservableRealization R)
    (C : EquationContextCharts (X := X))
    (P : EquationSchemeChartProducer R C)
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ R.realizationScheme) :
    (R.EquationLawfulAlong C s ↔
      R.generatedIdealSheaf.comap s = ⊥) ∧
    (R.generatedIdealSheaf.comap s = ⊥ ↔
      Nonempty (R.FactorsThroughLawfulClosedSubscheme s)) := by
  exact ⟨R.equationLawfulAlong_iff_generatedIdeal hR C P s,
    R.generatedIdeal_iff_nonempty_factorsThrough s⟩

end EquationObservableRealization

/-- Chartwise realization of the core ideal sheaves in canonical affine presentations. -/
def SemanticCoreIdealSheafRealized
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E) : Prop :=
  (∀ W : S.category,
    AffineChart.AffineAATChart.SheafifiedChartPresentation raw W) ∧
  ∀ (j : X.atlas.Index) (i : E.Index),
    let R := ClosedEquationalLawReading.ofSemanticCore raw X E B
    let hR := ClosedEquationalLawReading.ofSemanticCore_witnessCompatible raw X E B
    ((lawWitnessIdealSheaf raw X R hR i (Set.mem_univ i)).comap
        (X.atlas.chart j).map) =
      Scheme.IdealSheafData.ofIdealTop
        (X := (X.atlas.chart j).domain)
        (Ideal.map
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing raw (X.atlas.chart j).context)).inv.hom
          (Ideal.map
            (B.toSheafifiedSection (X.atlas.chart j).context)
            (E.witnessIdeal (X.atlas.chart j).context i)))

/-- A valid core bridge realizes its witness ideal sheaves on every atlas chart. -/
theorem semanticCoreIdealSheaf_realized
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (hB : IsSemanticLawEquationSchemeBridge raw E B) :
    SemanticCoreIdealSheafRealized raw X E B := by
  refine ⟨hB.presentation_stable, ?_⟩
  intro j i
  dsimp only
  let R := ClosedEquationalLawReading.ofSemanticCore raw X E B
  let hR := ClosedEquationalLawReading.ofSemanticCore_witnessCompatible raw X E B
  rw [lawWitnessIdealSheaf_ofGlobalSections raw X R hR i (Set.mem_univ i)
    (semanticCoreGlobalEquation raw X E B i) rfl]
  letI : IsOpenImmersion (X.atlas.chart j).map :=
    (X.atlasValid.chart_valid j).isOpenImmersion
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
  let e := (X.atlas.chart j).map.appIso ⊤
  have comap_inv (J : Ideal Γ(X.underlying,
      (X.atlas.chart j).map ''ᵁ (⊤ : (X.atlas.chart j).domain.Opens))) :
      Ideal.comap e.inv.hom J = Ideal.map e.hom.hom J := by
    ext x
    constructor
    · intro hx
      change e.inv x ∈ J at hx
      simpa using Ideal.mem_map_of_mem e.hom.hom hx
    · intro hx
      rw [Ideal.mem_map_iff_of_surjective e.hom.hom
        e.commRingCatIsoToRingEquiv.surjective] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      change e.inv x ∈ J
      rw [← hxy]
      simpa using hy
  rw [comap_inv, Ideal.map_map]
  have appTop_eq :
      e.hom.hom.comp
          (X.underlying.presheaf.map (homOfLE le_top).op).hom =
        (X.atlas.chart j).map.appTop.hom := by
    apply RingHom.ext
    intro z
    change
      ((X.underlying.presheaf.map (homOfLE le_top).op) ≫ e.hom) z =
        (X.atlas.chart j).map.appTop z
    simp only [e, Scheme.Hom.appIso_hom]
    rw [← Category.assoc]
    rw [(X.atlas.chart j).map.naturality]
    rw [Category.assoc, ← Functor.map_comp]
    rfl
  rw [appTop_eq]
  simp only [Ideal.map_span, semanticCoreLawWitnessIdeal_map]
  have top_res_apply (z : Γ((X.atlas.chart j).domain, ⊤)) :
      (X.atlas.chart j).domain.presheaf.map
          (homOfLE le_top).op z = z := by
    have h := (X.atlas.chart j).domain.presheaf.map_id
      (op (⊤ : (X.atlas.chart j).domain.Opens))
    exact congrArg (fun q => q z) h
  have chart_eq (a : U.Atom) :
      (X.atlas.chart j).map.appTop
          (semanticCoreGlobalEquation raw X E B i a) =
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw (X.atlas.chart j).context)).inv
            (B.toSheafifiedSection (X.atlas.chart j).context
              (E.violationCoordinate (X.atlas.chart j).context i a)) := by
    apply (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing raw
        (X.atlas.chart j).context)).commRingCatIsoToRingEquiv.eq_symm_apply.mpr
    simpa only [CommRingCat.comp_apply] using
      semanticCoreGlobalEquation_on_chart raw X E B hB j i a
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨eqsec, ⟨a, ha⟩, hx⟩
    refine ⟨_, ⟨_, ⟨⟨a, rfl⟩, rfl⟩⟩, ?_⟩
    calc
      (X.atlas.chart j).domain.presheaf.map (homOfLE le_top).op
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing raw
              (X.atlas.chart j).context)).inv
            (B.toSheafifiedSection (X.atlas.chart j).context
              (E.violationCoordinate (X.atlas.chart j).context i a))) =
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing raw
              (X.atlas.chart j).context)).inv
            (B.toSheafifiedSection (X.atlas.chart j).context
              (E.violationCoordinate (X.atlas.chart j).context i a)) := top_res_apply _
      _ = (X.atlas.chart j).map.appTop
          (semanticCoreGlobalEquation raw X E B i a) := (chart_eq a).symm
      _ = (X.atlas.chart j).map.appTop eqsec := by rw [ha]
      _ = x := hx
  · rintro ⟨x₁, ⟨x₀, ⟨a, ha⟩, hx₁⟩, hx⟩
    refine ⟨_, ⟨a, rfl⟩, ?_⟩
    calc
      (X.atlas.chart j).map.appTop
          (semanticCoreGlobalEquation raw X E B i a) =
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing raw
              (X.atlas.chart j).context)).inv
            (B.toSheafifiedSection (X.atlas.chart j).context
              (E.violationCoordinate (X.atlas.chart j).context i a)) := chart_eq a
      _ = (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing raw
              (X.atlas.chart j).context)).inv x₀ := by rw [ha]
      _ = x₁ := hx₁
      _ = (X.atlas.chart j).domain.presheaf.map
          (homOfLE le_top).op x₁ := (top_res_apply x₁).symm
      _ = x := hx

/-- Required selected local suprema commute exactly with basic-open restriction. -/
theorem requiredLocalLawIdeal_map_basicOpen
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) (f : Γ(X.underlying, V)) :
    Ideal.map
        (X.underlying.presheaf.map
          (homOfLE (X.underlying.basicOpen_le f)).op).hom
        (⨆ i : {i : E.Index //
            E.Required i ∧ R.selected V i},
          localLawWitnessIdeal raw X
            (R.witness i.1 (hclosed.closed i.1 i.2.1)) V) =
      ⨆ i : {i : E.Index //
          E.Required i ∧
            R.selected (X.underlying.affineBasicOpen f) i},
        localLawWitnessIdeal raw X
            (R.witness i.1 (hclosed.closed i.1 i.2.1))
            (X.underlying.affineBasicOpen f) := by
  rw [Ideal.map_iSup]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rw [localLawWitnessIdeal_map_basicOpen raw X _
      (hR.witness_compatible i.1 (hclosed.closed i.1 i.2.1))]
    let j : {q : E.Index //
        E.Required q ∧
          R.selected (X.underlying.affineBasicOpen f) q} :=
      ⟨i.1, i.2.1, (hR.selected_basicOpen V f i.1).mp i.2.2⟩
    simpa only [j, Subtype.coe_mk] using
      (le_iSup (fun q : {q : E.Index //
        E.Required q ∧
          R.selected (X.underlying.affineBasicOpen f) q} =>
          localLawWitnessIdeal raw X
            (R.witness q.1 (hclosed.closed q.1 q.2.1))
            (X.underlying.affineBasicOpen f)) j)
  · refine iSup_le fun i => ?_
    let j : {q : E.Index //
        E.Required q ∧ R.selected V q} :=
      ⟨i.1, i.2.1, (hR.selected_basicOpen V f i.1).mpr i.2.2⟩
    have hj := le_iSup (fun q : {q : E.Index //
        E.Required q ∧ R.selected V q} =>
      Ideal.map
        (X.underlying.presheaf.map
          (homOfLE (X.underlying.basicOpen_le f)).op).hom
        (localLawWitnessIdeal raw X
          (R.witness q.1 (hclosed.closed q.1 q.2.1)) V)) j
    rw [localLawWitnessIdeal_map_basicOpen raw X _
      (hR.witness_compatible j.1 (hclosed.closed j.1 j.2.1))] at hj
    simpa only [j, Subtype.coe_mk] using hj

/-- All selected local suprema commute exactly with basic-open restriction. -/
theorem allSelectedLocalLawIdeal_map_basicOpen
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (V : X.underlying.affineOpens) (f : Γ(X.underlying, V)) :
    Ideal.map
        (X.underlying.presheaf.map
          (homOfLE (X.underlying.basicOpen_le f)).op).hom
        (⨆ i : {i : E.Index // R.selected V i},
          localLawWitnessIdeal raw X
            (R.witness i.1 (hR.selected_closed V i.1 i.2)) V) =
      ⨆ i : {i : E.Index //
          R.selected (X.underlying.affineBasicOpen f) i},
          localLawWitnessIdeal raw X
            (R.witness i.1
              (hR.selected_closed
                (X.underlying.affineBasicOpen f) i.1 i.2))
            (X.underlying.affineBasicOpen f) := by
  rw [Ideal.map_iSup]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rw [localLawWitnessIdeal_map_basicOpen raw X _
      (hR.witness_compatible i.1 (hR.selected_closed V i.1 i.2))]
    let j : {q : E.Index //
        R.selected (X.underlying.affineBasicOpen f) q} :=
      ⟨i.1, (hR.selected_basicOpen V f i.1).mp i.2⟩
    simpa only [j, Subtype.coe_mk] using
      (le_iSup (fun q : {q : E.Index //
          R.selected (X.underlying.affineBasicOpen f) q} =>
        localLawWitnessIdeal raw X
          (R.witness q.1 (hR.selected_closed
            (X.underlying.affineBasicOpen f) q.1 q.2))
          (X.underlying.affineBasicOpen f)) j)
  · refine iSup_le fun i => ?_
    let j : {q : E.Index // R.selected V q} :=
      ⟨i.1, (hR.selected_basicOpen V f i.1).mpr i.2⟩
    have hj := le_iSup (fun q : {q : E.Index // R.selected V q} =>
      Ideal.map
        (X.underlying.presheaf.map
          (homOfLE (X.underlying.basicOpen_le f)).op).hom
        (localLawWitnessIdeal raw X
          (R.witness q.1 (hR.selected_closed V q.1 q.2)) V)) j
    rw [localLawWitnessIdeal_map_basicOpen raw X _
      (hR.witness_compatible j.1 (hR.selected_closed V j.1 j.2))] at hj
    simpa only [j, Subtype.coe_mk] using hj

/-- The required selected obstruction ideal sheaf. -/
noncomputable def lawGeneratedIdealSheaf
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    X.underlying.IdealSheafData where
  ideal V :=
    ⨆ i : {i : E.Index //
        E.Required i ∧ R.selected V i},
      localLawWitnessIdeal raw X
        (R.witness i.1 (hclosed.closed i.1 i.2.1)) V
  map_ideal_basicOpen :=
    requiredLocalLawIdeal_map_basicOpen raw X R hR hclosed

/-- The obstruction ideal sheaf generated by all selected laws. -/
noncomputable def allLawGeneratedIdealSheaf
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R) :
    X.underlying.IdealSheafData where
  ideal V :=
    ⨆ i : {i : E.Index // R.selected V i},
      localLawWitnessIdeal raw X
        (R.witness i.1 (hR.selected_closed V i.1 i.2)) V
  map_ideal_basicOpen := allSelectedLocalLawIdeal_map_basicOpen raw X R hR

/-- The component of the required generated ideal sheaf is its selected supremum. -/
@[simp] theorem lawGeneratedIdealSheaf_ideal
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) :
    (lawGeneratedIdealSheaf raw X R hR hclosed).ideal V =
      ⨆ i : {i : E.Index //
          E.Required i ∧ R.selected V i},
        localLawWitnessIdeal raw X
          (R.witness i.1 (hclosed.closed i.1 i.2.1)) V :=
  rfl

/-- The component of the all-law generated ideal sheaf is its selected supremum. -/
@[simp] theorem allLawGeneratedIdealSheaf_ideal
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (V : X.underlying.affineOpens) :
    (allLawGeneratedIdealSheaf raw X R hR).ideal V =
      ⨆ i : {i : E.Index // R.selected V i},
        localLawWitnessIdeal raw X
          (R.witness i.1 (hR.selected_closed V i.1 i.2)) V :=
  rfl

/--
The required generated ideal sheaf is the supremum of the required
per-equation witness ideal sheaves.
-/
theorem lawGeneratedIdealSheaf_eq_iSup_required
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    lawGeneratedIdealSheaf raw X R hR hclosed =
      ⨆ i : E.RequiredIndex,
        lawWitnessIdealSheaf raw X R hR.witness_compatible
          i.1 (hclosed.closed i.1 i.2) := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [lawGeneratedIdealSheaf_ideal,
    Scheme.IdealSheafData.ideal_iSup, iSup_apply]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    let j : E.RequiredIndex := ⟨i.1, i.2.1⟩
    simpa only [lawWitnessIdealSheaf_ideal, j, Subtype.coe_mk] using
      (le_iSup (fun q : E.RequiredIndex =>
        (lawWitnessIdealSheaf raw X R hR.witness_compatible q.1
          (hclosed.closed q.1 q.2)).ideal V) j)
  · refine iSup_le fun i => ?_
    let j : {q : E.Index //
        E.Required q ∧ R.selected V q} :=
      ⟨i.1, i.2, hclosed.selected V i.1 i.2⟩
    simpa only [lawWitnessIdealSheaf_ideal, j, Subtype.coe_mk] using
      (le_iSup (fun q : {q : E.Index //
          E.Required q ∧ R.selected V q} =>
        localLawWitnessIdeal raw X
          (R.witness q.1 (hclosed.closed q.1 q.2.1)) V) j)

/--
When every equation is selected, the all-equation generated ideal sheaf is
the supremum of the per-equation witness ideal sheaves.
-/
theorem allLawGeneratedIdealSheaf_eq_iSup
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hall : AllLawsSelected raw X R) :
    allLawGeneratedIdealSheaf raw X R hR =
      ⨆ i : E.Index,
        lawWitnessIdealSheaf raw X R hR.witness_compatible
          i (hall.closed i) := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [allLawGeneratedIdealSheaf_ideal,
    Scheme.IdealSheafData.ideal_iSup, iSup_apply]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    simpa only [lawWitnessIdealSheaf_ideal] using
      (le_iSup (fun q : E.Index =>
        (lawWitnessIdealSheaf raw X R hR.witness_compatible q
          (hall.closed q)).ideal V) i.1)
  · refine iSup_le fun i => ?_
    let j : {q : E.Index // R.selected V q} :=
      ⟨i, hall.selected V i⟩
    simpa only [lawWitnessIdealSheaf_ideal, j, Subtype.coe_mk] using
      (le_iSup (fun q : {q : E.Index // R.selected V q} =>
        localLawWitnessIdeal raw X
          (R.witness q.1 (hR.selected_closed V q.1 q.2)) V) j)

/-- The required generated ideal sheaf is contained in the all-law generated ideal sheaf. -/
theorem lawGeneratedIdealSheaf_le_all
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    lawGeneratedIdealSheaf raw X R hR hclosed ≤
      allLawGeneratedIdealSheaf raw X R hR := by
  intro V
  refine iSup_le fun i => ?_
  let j : {q : E.Index // R.selected V q} := ⟨i.1, i.2.2⟩
  simpa only [j, Subtype.coe_mk] using
    (le_iSup (fun q : {q : E.Index // R.selected V q} =>
      localLawWitnessIdeal raw X
        (R.witness q.1 (hR.selected_closed V q.1 q.2)) V) j)

/-! ## Actual closed subschemes and their quotient charts -/

/-- The required-law closed subscheme cut out by the generated ideal sheaf. -/
noncomputable def lawfulClosedSubscheme
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) : AlgebraicGeometry.Scheme :=
  (lawGeneratedIdealSheaf raw X R hR hclosed).subscheme

/-- The canonical closed immersion of the required-law closed subscheme. -/
noncomputable def lawfulClosedImmersion
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    lawfulClosedSubscheme raw X R hR hclosed ⟶ X.underlying :=
  (lawGeneratedIdealSheaf raw X R hR hclosed).subschemeι

/-- The closed subscheme cut out by all selected laws. -/
noncomputable def allLawfulClosedSubscheme
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R) : AlgebraicGeometry.Scheme :=
  (allLawGeneratedIdealSheaf raw X R hR).subscheme

/-- The canonical closed immersion of the all-law closed subscheme. -/
noncomputable def allLawfulClosedImmersion
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R) :
    allLawfulClosedSubscheme raw X R hR ⟶ X.underlying :=
  (allLawGeneratedIdealSheaf raw X R hR).subschemeι

/-- The required-law subscheme map is an actual closed immersion. -/
theorem lawfulClosedImmersion_isClosedImmersion
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    IsClosedImmersion (lawfulClosedImmersion raw X R hR hclosed) := by
  change IsClosedImmersion
    (lawGeneratedIdealSheaf raw X R hR hclosed).subschemeι
  infer_instance

/-- The kernel of the required-law closed immersion is the generated ideal sheaf. -/
@[simp] theorem lawfulClosedImmersion_ker
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedImmersion raw X R hR hclosed).ker =
      lawGeneratedIdealSheaf raw X R hR hclosed :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- The range of the required-law closed immersion is the ideal-sheaf support. -/
@[simp] theorem lawfulClosedImmersion_range
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    Set.range (lawfulClosedImmersion raw X R hR hclosed) =
      (lawGeneratedIdealSheaf raw X R hR hclosed).support :=
  Scheme.IdealSheafData.range_subschemeι _

/-- Mathlib's quotient affine cover of the required-law closed subscheme. -/
noncomputable def lawfulClosedSubschemeCover
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedSubscheme raw X R hR hclosed).AffineOpenCover :=
  (lawGeneratedIdealSheaf raw X R hR hclosed).subschemeCover

/-- Each chart algebra in the closed-subscheme cover is the corresponding quotient ring. -/
@[simp] theorem lawfulClosedSubschemeCover_X
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) :
    (lawfulClosedSubschemeCover raw X R hR hclosed).X V =
      CommRingCat.of
        (Γ(X.underlying, V) ⧸
          (lawGeneratedIdealSheaf raw X R hR hclosed).ideal V) :=
  rfl

/-- Global sections on a pulled affine open are identified with its quotient chart algebra. -/
noncomputable def lawfulClosedSubschemeObjIso
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) :
    Γ(lawfulClosedSubscheme raw X R hR hclosed,
        lawfulClosedImmersion raw X R hR hclosed ⁻¹ᵁ V) ≅
      CommRingCat.of
        (Γ(X.underlying, V) ⧸
          (lawGeneratedIdealSheaf raw X R hR hclosed).ideal V) :=
  (lawGeneratedIdealSheaf raw X R hR hclosed).subschemeObjIso V

/-- Pull the ambient AAT reading decoration back to the required-law closed subscheme. -/
noncomputable def lawfulClosedDecoration
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    AATReadingDecoration raw (lawfulClosedSubscheme raw X R hR hclosed) :=
  AATReadingDecoration.pullback raw
    (lawfulClosedImmersion raw X R hR hclosed) X.decoration

/-- Pullback of the decoration preserves the selected context. -/
@[simp] theorem lawfulClosedDecoration_context
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedDecoration raw X R hR hclosed).context = X.decoration.context :=
  rfl

/-- Pullback of the decoration preserves the site equation system. -/
@[simp] theorem lawfulClosedDecoration_equationSystem
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedDecoration raw X R hR hclosed).equationSystem raw =
      X.decoration.equationSystem raw :=
  rfl

/-- Pullback of the decoration preserves the architecture signature. -/
@[simp] theorem lawfulClosedDecoration_signature
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedDecoration raw X R hR hclosed).signature raw =
      X.decoration.signature raw :=
  rfl

/-- Pullback transports each coordinate section through the closed immersion on global sections. -/
@[simp] theorem lawfulClosedDecoration_coordinateSection
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (c : (X.decoration.coordinateFamily raw).CoordX) :
    (lawfulClosedDecoration raw X R hR hclosed).coordinateSection raw c =
      (lawfulClosedImmersion raw X R hR hclosed).appTop
        (X.decoration.coordinateSection raw c) :=
  rfl

/-- Inclusion of all-law equations induces a map to the required-law closed subscheme. -/
noncomputable def fullToRequiredLawfulMap
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    allLawfulClosedSubscheme raw X R hR ⟶
      lawfulClosedSubscheme raw X R hR hclosed :=
  Scheme.IdealSheafData.inclusion
    (lawGeneratedIdealSheaf_le_all raw X R hR hclosed)

/-- The all-law to required-law comparison map is a closed immersion. -/
theorem fullToRequiredLawfulMap_isClosedImmersion
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    IsClosedImmersion (fullToRequiredLawfulMap raw X R hR hclosed) := by
  change IsClosedImmersion (Scheme.IdealSheafData.inclusion
    (lawGeneratedIdealSheaf_le_all raw X R hR hclosed))
  infer_instance

/-- The comparison map followed by the required immersion is the all-law immersion. -/
@[reassoc] theorem fullToRequiredLawfulMap_immersion
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    fullToRequiredLawfulMap raw X R hR hclosed ≫
        lawfulClosedImmersion raw X R hR hclosed =
      allLawfulClosedImmersion raw X R hR :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-! ## Exact law ideals and actual factorization -/

/-- Semantic truth of one closed law implies vanishing of its pulled witness ideal. -/
def LawIdealSound
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : E.Index) (hi : R.closed i) : Prop :=
  ∀ {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying),
    R.geometric.HoldsOn s i →
      (lawWitnessIdealSheaf raw X R hR i hi).comap s = ⊥

/-- Vanishing of one pulled witness ideal implies its semantic law truth. -/
def LawIdealComplete
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : E.Index) (hi : R.closed i) : Prop :=
  ∀ {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying),
    (lawWitnessIdealSheaf raw X R hR i hi).comap s = ⊥ →
      R.geometric.HoldsOn s i

/-- Law-by-law equivalence between semantic truth and pulled ideal vanishing. -/
def LawIdealExact
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : E.Index) (hi : R.closed i) : Prop :=
  ∀ {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying),
    R.geometric.HoldsOn s i ↔
      (lawWitnessIdealSheaf raw X R hR i hi).comap s = ⊥

/-- Exactness is equivalent to its soundness and completeness directions. -/
theorem lawIdealExact_iff_sound_and_complete
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : E.Index) (hi : R.closed i) :
    LawIdealExact raw X R hR i hi ↔
      LawIdealSound raw X R hR i hi ∧
        LawIdealComplete raw X R hR i hi := by
  constructor
  · intro h
    exact ⟨fun s => (h s).mp, fun s => (h s).mpr⟩
  · rintro ⟨hsound, hcomplete⟩ T s
    exact ⟨hsound s, hcomplete s⟩

/-- Law-ideal exactness for every required law. -/
def RequiredLawIdealExact
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) : Prop :=
  ∀ i (hi : E.Required i),
    LawIdealExact raw X R hR.witness_compatible i (hclosed.closed i hi)

/-- Law-ideal exactness for every selected law index. -/
def AllLawIdealExact
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hall : AllLawsSelected raw X R) : Prop :=
  ∀ i, LawIdealExact raw X R hR.witness_compatible i (hall.closed i)

/-- Vanishing of every required law witness ideal along a section. -/
def WitnessVanishes
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  ∀ i (hi : E.Required i),
    (lawWitnessIdealSheaf raw X R hR.witness_compatible i
      (hclosed.closed i hi)).comap s = ⊥

/-- Vanishing of the required generated ideal sheaf along a section. -/
def IdealLawfulAlong
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  (lawGeneratedIdealSheaf raw X R hR hclosed).comap s = ⊥

/-- Vanishing of the all-law generated ideal sheaf along a section. -/
def FullIdealLawfulAlong
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  (allLawGeneratedIdealSheaf raw X R hR).comap s = ⊥

/-- Actual factorizations of a section through the required-law closed subscheme. -/
def FactorsThroughLawfulClosedSubscheme
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :=
  {t : T ⟶ lawfulClosedSubscheme raw X R hR hclosed //
    t ≫ lawfulClosedImmersion raw X R hR hclosed = s}

/-- Actual factorizations of a section through the all-law closed subscheme. -/
def FactorsThroughAllLawfulClosedSubscheme
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :=
  {t : T ⟶ allLawfulClosedSubscheme raw X R hR //
    t ≫ allLawfulClosedImmersion raw X R hR = s}

/-- Required ideal lawfulness is containment in the kernel ideal sheaf. -/
theorem idealLawfulAlong_iff_le_ker
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    IdealLawfulAlong raw X R hR hclosed s ↔
      lawGeneratedIdealSheaf raw X R hR hclosed ≤ s.ker := by
  change (lawGeneratedIdealSheaf raw X R hR hclosed).comap s = ⊥ ↔ _
  rw [eq_bot_iff]
  simpa only [Scheme.IdealSheafData.map_bot] using
    (Scheme.IdealSheafData.map_gc s
      (lawGeneratedIdealSheaf raw X R hR hclosed) ⊥)

/-- The canonical Mathlib lift through the required-law closed immersion. -/
noncomputable def factorizationLift
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : IdealLawfulAlong raw X R hR hclosed s) :
    T ⟶ lawfulClosedSubscheme raw X R hR hclosed := by
  letI : IsClosedImmersion (lawfulClosedImmersion raw X R hR hclosed) :=
    lawfulClosedImmersion_isClosedImmersion raw X R hR hclosed
  exact IsClosedImmersion.lift
    (lawfulClosedImmersion raw X R hR hclosed) s
    (by
      rw [lawfulClosedImmersion_ker]
      exact (idealLawfulAlong_iff_le_ker raw X R hR hclosed s).mp hs)

/-- The canonical factorization lift composes to the original section. -/
@[reassoc] theorem factorizationLift_fac
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : IdealLawfulAlong raw X R hR hclosed s) :
    factorizationLift raw X R hR hclosed s hs ≫
        lawfulClosedImmersion raw X R hR hclosed = s := by
  letI : IsClosedImmersion (lawfulClosedImmersion raw X R hR hclosed) :=
    lawfulClosedImmersion_isClosedImmersion raw X R hR hclosed
  exact IsClosedImmersion.lift_fac _ _ _

/-- Factorizations through the required-law closed immersion are unique. -/
theorem factorization_unique
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (a b : FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s) :
    a.1 = b.1 := by
  letI : IsClosedImmersion (lawfulClosedImmersion raw X R hR hclosed) :=
    lawfulClosedImmersion_isClosedImmersion raw X R hR hclosed
  apply (cancel_mono (lawfulClosedImmersion raw X R hR hclosed)).mp
  exact a.2.trans b.2.symm

/-- Required ideal lawfulness is equivalent to existence of an actual factorization. -/
theorem idealLawfulAlong_iff_nonempty_factorsThrough
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    IdealLawfulAlong raw X R hR hclosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s) := by
  constructor
  · intro hs
    exact ⟨⟨factorizationLift raw X R hR hclosed s hs,
      factorizationLift_fac raw X R hR hclosed s hs⟩⟩
  · rintro ⟨t⟩
    apply (idealLawfulAlong_iff_le_ker raw X R hR hclosed s).mpr
    rw [← t.2]
    calc
      lawGeneratedIdealSheaf raw X R hR hclosed =
          (lawfulClosedImmersion raw X R hR hclosed).ker :=
        (lawfulClosedImmersion_ker raw X R hR hclosed).symm
      _ ≤ (t.1 ≫ lawfulClosedImmersion raw X R hR hclosed).ker :=
        Scheme.Hom.le_ker_comp _ _

/-- The canonical Mathlib lift through the all-law closed immersion. -/
noncomputable def allLawFactorizationLift
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : FullIdealLawfulAlong raw X R hR s) :
    T ⟶ allLawfulClosedSubscheme raw X R hR := by
  letI : IsClosedImmersion (allLawfulClosedImmersion raw X R hR) := by
    change IsClosedImmersion (allLawGeneratedIdealSheaf raw X R hR).subschemeι
    infer_instance
  exact IsClosedImmersion.lift (allLawfulClosedImmersion raw X R hR) s
    (by
      change (allLawGeneratedIdealSheaf raw X R hR).subschemeι.ker ≤ s.ker
      rw [Scheme.IdealSheafData.ker_subschemeι]
      change (allLawGeneratedIdealSheaf raw X R hR).comap s = ⊥ at hs
      rw [eq_bot_iff] at hs
      simpa only [Scheme.IdealSheafData.map_bot] using
        (Scheme.IdealSheafData.map_gc s _ ⊥).mp hs)

/-- The all-law factorization lift composes to the original section. -/
@[reassoc] theorem allLawFactorizationLift_fac
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : FullIdealLawfulAlong raw X R hR s) :
    allLawFactorizationLift raw X R hR s hs ≫
        allLawfulClosedImmersion raw X R hR = s := by
  letI : IsClosedImmersion (allLawfulClosedImmersion raw X R hR) := by
    change IsClosedImmersion (allLawGeneratedIdealSheaf raw X R hR).subschemeι
    infer_instance
  exact IsClosedImmersion.lift_fac _ _ _

/-- Factorizations through the all-law closed immersion are unique. -/
theorem allLawFactorization_unique
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (a b : FactorsThroughAllLawfulClosedSubscheme raw X R hR s) :
    a.1 = b.1 := by
  letI : IsClosedImmersion (allLawfulClosedImmersion raw X R hR) := by
    change IsClosedImmersion (allLawGeneratedIdealSheaf raw X R hR).subschemeι
    infer_instance
  apply (cancel_mono (allLawfulClosedImmersion raw X R hR)).mp
  exact a.2.trans b.2.symm

/-- Full ideal lawfulness is equivalent to existence of an all-law factorization. -/
theorem fullIdealLawfulAlong_iff_nonempty_factorsThrough
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    FullIdealLawfulAlong raw X R hR s ↔
      Nonempty (FactorsThroughAllLawfulClosedSubscheme raw X R hR s) := by
  constructor
  · intro hs
    exact ⟨⟨allLawFactorizationLift raw X R hR s hs,
      allLawFactorizationLift_fac raw X R hR s hs⟩⟩
  · rintro ⟨t⟩
    change (allLawGeneratedIdealSheaf raw X R hR).comap s = ⊥
    rw [eq_bot_iff]
    apply (Scheme.IdealSheafData.map_gc s _ ⊥).mpr
    simpa only [Scheme.IdealSheafData.map_bot] using
      (show allLawGeneratedIdealSheaf raw X R hR ≤ s.ker from by
        rw [← t.2]
        calc
          allLawGeneratedIdealSheaf raw X R hR =
              (allLawfulClosedImmersion raw X R hR).ker :=
            (Scheme.IdealSheafData.ker_subschemeι _).symm
          _ ≤ (t.1 ≫ allLawfulClosedImmersion raw X R hR).ker :=
            Scheme.Hom.le_ker_comp _ _)

/-! ## Lawfulness, ideal vanishing, and factorization correspondence -/

/-- Required semantic lawfulness is equivalent to vanishing of every required witness ideal. -/
theorem semanticLawfulAlong_iff_witnessVanishes
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (hexact : RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    SemanticLawfulAlong raw X R s ↔
      WitnessVanishes raw X R hR hclosed s := by
  constructor
  · intro h i hi
    exact (hexact i hi s).mp (h i hi)
  · intro h i hi
    exact (hexact i hi s).mpr (h i hi)

/-- Required witnesswise vanishing is equivalent to vanishing of their generated supremum. -/
theorem witnessVanishes_iff_idealLawfulAlong
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    WitnessVanishes raw X R hR hclosed s ↔
      IdealLawfulAlong raw X R hR hclosed s := by
  constructor
  · intro h
    apply (idealLawfulAlong_iff_le_ker raw X R hR hclosed s).mpr
    intro V
    refine iSup_le fun i => ?_
    have hi := h i.1 i.2.1
    have hle :
        lawWitnessIdealSheaf raw X R hR.witness_compatible i.1
            (hclosed.closed i.1 i.2.1) ≤ s.ker := by
      rw [eq_bot_iff] at hi
      simpa only [Scheme.IdealSheafData.map_bot] using
        (Scheme.IdealSheafData.map_gc s _ ⊥).mp hi
    simpa only [lawWitnessIdealSheaf_ideal] using hle V
  · intro h i hi
    have hagg :=
      (idealLawfulAlong_iff_le_ker raw X R hR hclosed s).mp h
    have hind :
        lawWitnessIdealSheaf raw X R hR.witness_compatible i
            (hclosed.closed i hi) ≤
          lawGeneratedIdealSheaf raw X R hR hclosed := by
      intro V
      let j : {q : E.Index //
          E.Required q ∧ R.selected V q} :=
        ⟨i, hi, hclosed.selected V i hi⟩
      simpa only [lawWitnessIdealSheaf_ideal, j, Subtype.coe_mk] using
        (le_iSup (fun q : {q : E.Index //
            E.Required q ∧ R.selected V q} =>
          localLawWitnessIdeal raw X
            (R.witness q.1 (hclosed.closed q.1 q.2.1)) V) j)
    rw [eq_bot_iff]
    apply (Scheme.IdealSheafData.map_gc s _ ⊥).mpr
    simpa only [Scheme.IdealSheafData.map_bot] using hind.trans hagg

/-- The required closed-equational core correspondence. -/
theorem lawfulnessIdealFactorizationCorrespondence
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (hexact : RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    (SemanticLawfulAlong raw X R s ↔
      WitnessVanishes raw X R hR hclosed s) ∧
    (WitnessVanishes raw X R hR hclosed s ↔
      IdealLawfulAlong raw X R hR hclosed s) ∧
    (IdealLawfulAlong raw X R hR hclosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s)) :=
  ⟨semanticLawfulAlong_iff_witnessVanishes raw X R hR hclosed hexact s,
    witnessVanishes_iff_idealLawfulAlong raw X R hR hclosed s,
    idealLawfulAlong_iff_nonempty_factorsThrough raw X R hR hclosed s⟩

/-- The existing semantic core realizes the required correspondence through actual ideal sheaves. -/
theorem semanticCoreLawfulnessIdealFactorizationCorrespondence
    (E : ArchitecturalEquationSystem S.contextPreorder)
    (B : SemanticLawEquationSchemeBridge raw E)
    (hB : IsSemanticLawEquationSchemeBridge raw E B)
    (hexact : RequiredLawIdealExact raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X E B)
      (ClosedEquationalLawReading.ofSemanticCore_valid raw X E B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X E B))
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    let R := ClosedEquationalLawReading.ofSemanticCore raw X E B
    let hR := ClosedEquationalLawReading.ofSemanticCore_valid raw X E B
    let hclosed := ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X E B
    SemanticCoreIdealSheafRealized raw X E B ∧
    (SemanticLawfulAlong raw X R s ↔
      WitnessVanishes raw X R hR hclosed s) ∧
    (WitnessVanishes raw X R hR hclosed s ↔
      IdealLawfulAlong raw X R hR hclosed s) ∧
    (IdealLawfulAlong raw X R hR hclosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s)) := by
  dsimp only
  refine ⟨semanticCoreIdealSheaf_realized raw X E B hB, ?_⟩
  exact lawfulnessIdealFactorizationCorrespondence raw X
    (ClosedEquationalLawReading.ofSemanticCore raw X E B)
    (ClosedEquationalLawReading.ofSemanticCore_valid raw X E B)
    (ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X E B)
    hexact s

/-- Full semantic lawfulness is equivalent to vanishing of the all-law ideal sheaf. -/
theorem fullySemanticLawfulAlong_iff_fullIdealLawfulAlong
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hall : AllLawsSelected raw X R)
    (hexact : AllLawIdealExact raw X R hR hall)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    FullySemanticLawfulAlong raw X R s ↔
      FullIdealLawfulAlong raw X R hR s := by
  constructor
  · intro h
    change (allLawGeneratedIdealSheaf raw X R hR).comap s = ⊥
    rw [eq_bot_iff]
    apply (Scheme.IdealSheafData.map_gc s _ ⊥).mpr
    simpa only [Scheme.IdealSheafData.map_bot] using
      (show allLawGeneratedIdealSheaf raw X R hR ≤ s.ker from by
        intro V
        refine iSup_le fun i => ?_
        have hi := (hexact i.1 s).mp (h i.1)
        rw [eq_bot_iff] at hi
        have hle := (Scheme.IdealSheafData.map_gc s _ ⊥).mp hi
        have hle' :
            lawWitnessIdealSheaf raw X R hR.witness_compatible i.1
                (hall.closed i.1) ≤ s.ker := by
          simpa only [Scheme.IdealSheafData.map_bot] using hle
        simpa only [lawWitnessIdealSheaf_ideal] using hle' V)
  · intro h i
    apply (hexact i s).mpr
    rw [eq_bot_iff]
    apply (Scheme.IdealSheafData.map_gc s _ ⊥).mpr
    simpa only [Scheme.IdealSheafData.map_bot] using
      (show lawWitnessIdealSheaf raw X R hR.witness_compatible i
          (hall.closed i) ≤ s.ker from by
        have hagg : allLawGeneratedIdealSheaf raw X R hR ≤ s.ker := by
          change (allLawGeneratedIdealSheaf raw X R hR).comap s = ⊥ at h
          rw [eq_bot_iff] at h
          simpa only [Scheme.IdealSheafData.map_bot] using
            (Scheme.IdealSheafData.map_gc s _ ⊥).mp h
        apply le_trans ?_ hagg
        intro V
        let j : {q : E.Index // R.selected V q} :=
          ⟨i, hall.selected V i⟩
        simpa only [lawWitnessIdealSheaf_ideal, j, Subtype.coe_mk] using
          (le_iSup (fun q : {q : E.Index // R.selected V q} =>
            localLawWitnessIdeal raw X
              (R.witness q.1 (hR.selected_closed V q.1 q.2)) V) j))

/-- Full semantic lawfulness corresponds to all-law ideal vanishing and actual factorization. -/
theorem fullLawfulnessIdealFactorizationCorrespondence
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hall : AllLawsSelected raw X R)
    (hexact : AllLawIdealExact raw X R hR hall)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    (FullySemanticLawfulAlong raw X R s ↔
      FullIdealLawfulAlong raw X R hR s) ∧
    (FullIdealLawfulAlong raw X R hR s ↔
      Nonempty (FactorsThroughAllLawfulClosedSubscheme raw X R hR s)) :=
  ⟨fullySemanticLawfulAlong_iff_fullIdealLawfulAlong raw X R hR hall hexact s,
    fullIdealLawfulAlong_iff_nonempty_factorsThrough raw X R hR s⟩

/-! ## Object, valuation, and signature comparisons -/

/-- Comparison of required section-level law truth with one architecture object. -/
def RequiredObjectPointComparison
    (R : ClosedEquationalLawReading raw X E)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) : Prop :=
  ∀ i, E.Required i →
    (R.geometric.HoldsOn s i ↔ E.EquationHolds i Obj)

/-- Required semantic lawfulness agrees with object-level lawfulness under point comparison. -/
theorem semanticLawfulAlong_iff_lawfulness
    (R : ClosedEquationalLawReading raw X E)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U)
    (hpoint : RequiredObjectPointComparison raw X R s Obj) :
    SemanticLawfulAlong raw X R s ↔ E.EquationLawful Obj := by
  constructor
  · intro h i hi
    exact (hpoint i hi).mp (h i hi)
  · intro h i hi
    exact (hpoint i hi).mpr (h i hi)

/-- Required semantic lawfulness is equivalent to vanishing of required signature axes. -/
theorem semanticLawfulAlong_iff_requiredSignatureAxesZero
    (R : ClosedEquationalLawReading raw X E)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) (Sig : SignatureAxes U)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (haxis : E.EquationLawful Obj ↔
      RequiredSignatureAxesZero Obj Sig) :
    SemanticLawfulAlong raw X R s ↔ RequiredSignatureAxesZero Obj Sig :=
  (semanticLawfulAlong_iff_lawfulness raw X R s Obj hpoint).trans haxis

/-- Actual factorization through the required closed subscheme is equivalent to signature-axis vanishing. -/
theorem factorsThroughLawfulClosedSubscheme_iff_requiredSignatureAxesZero
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (hexact : RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) (Sig : SignatureAxes U)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (haxis : E.EquationLawful Obj ↔
      RequiredSignatureAxesZero Obj Sig) :
    Nonempty (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s) ↔
      RequiredSignatureAxesZero Obj Sig := by
  have hcorr := lawfulnessIdealFactorizationCorrespondence raw X R hR hclosed hexact s
  exact (hcorr.1.trans (hcorr.2.1.trans hcorr.2.2)).symm.trans
    (semanticLawfulAlong_iff_requiredSignatureAxesZero raw X R s Obj Sig hpoint haxis)

/-! ## Law inclusions and contravariant closed geometry -/

/-- Primitive inclusion data consisting of a law-index map and indexed atom maps. -/
structure ClosedEquationalLawInclusion
    (R : ClosedEquationalLawReading raw X E)
    (Q : ClosedEquationalLawReading raw X F) where
  /-- The map from source laws to target laws. -/
  lawMap : E.Index → F.Index
  /-- The atom map associated to each source law. -/
  atomMap : ∀ i : E.Index, U.Atom → U.Atom

/-- Primitive law inclusions are determined by their two maps. -/
@[ext] theorem ClosedEquationalLawInclusion.ext
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (e f : ClosedEquationalLawInclusion raw X R Q)
    (hlawMap : e.lawMap = f.lawMap)
    (hatomMap : e.atomMap = f.atomMap) : e = f := by
  cases e
  cases f
  cases hlawMap
  cases hatomMap
  rfl

/-- Preservation and semantic monotonicity required of a primitive law inclusion. -/
structure IsClosedEquationalLawInclusion
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (e : ClosedEquationalLawInclusion raw X R Q) : Prop where
  required_map : ∀ i, E.Required i →
    F.Required (e.lawMap i)
  closed_map : ∀ i, R.closed i → Q.closed (e.lawMap i)
  selected_map :
    ∀ V i, R.selected V i → Q.selected V (e.lawMap i)
  coordinate_eq :
    ∀ i (hi : R.closed i) (V : X.underlying.affineOpens) (a : U.Atom),
      (R.witness i hi).coordinate V a =
        (Q.witness (e.lawMap i) (closed_map i hi)).coordinate V (e.atomMap i a)
  semantic_monotone :
    ∀ {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) i,
      Q.geometric.HoldsOn s (e.lawMap i) → R.geometric.HoldsOn s i

/-- The identity primitive law inclusion. -/
def ClosedEquationalLawInclusion.refl
    (R : ClosedEquationalLawReading raw X E) :
    ClosedEquationalLawInclusion raw X R R where
  lawMap := id
  atomMap := fun _ => id

/-- The identity primitive law inclusion is valid. -/
theorem ClosedEquationalLawInclusion.refl_valid
    (R : ClosedEquationalLawReading raw X E) :
    IsClosedEquationalLawInclusion raw X
      (ClosedEquationalLawInclusion.refl raw X R) where
  required_map := fun _ h => h
  closed_map := fun _ h => h
  selected_map := fun _ _ h => h
  coordinate_eq := by intros; rfl
  semantic_monotone := fun _ _ h => h

/-- Composition of primitive law inclusions. -/
def ClosedEquationalLawInclusion.comp
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    {P : ClosedEquationalLawReading raw X H}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (f : ClosedEquationalLawInclusion raw X Q P) :
    ClosedEquationalLawInclusion raw X R P where
  lawMap i := f.lawMap (e.lawMap i)
  atomMap i a := f.atomMap (e.lawMap i) (e.atomMap i a)

/-- Composition preserves validity of primitive law inclusions. -/
theorem ClosedEquationalLawInclusion.comp_valid
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    {P : ClosedEquationalLawReading raw X H}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (f : ClosedEquationalLawInclusion raw X Q P)
    (he : IsClosedEquationalLawInclusion raw X e)
    (hf : IsClosedEquationalLawInclusion raw X f) :
    IsClosedEquationalLawInclusion raw X (e.comp raw X f) where
  required_map i hi := hf.required_map _ (he.required_map i hi)
  closed_map i hi := hf.closed_map _ (he.closed_map i hi)
  selected_map V i hi := hf.selected_map V _ (he.selected_map V i hi)
  coordinate_eq i hi V a := by
    calc
      (R.witness i hi).coordinate V a =
          (Q.witness (e.lawMap i) (he.closed_map i hi)).coordinate V
            (e.atomMap i a) := he.coordinate_eq i hi V a
      _ = (P.witness (f.lawMap (e.lawMap i))
            (hf.closed_map (e.lawMap i) (he.closed_map i hi))).coordinate V
            (f.atomMap (e.lawMap i) (e.atomMap i a)) :=
        hf.coordinate_eq (e.lawMap i) (he.closed_map i hi) V (e.atomMap i a)
  semantic_monotone s i h := he.semantic_monotone s i (hf.semantic_monotone s _ h)

/-- Coordinate preservation makes each source law witness ideal sheaf smaller. -/
theorem lawWitnessIdealSheaf_le
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e)
    (i : E.Index) (hi : R.closed i) :
    lawWitnessIdealSheaf raw X R hR.witness_compatible i hi ≤
      lawWitnessIdealSheaf raw X Q hQ.witness_compatible
        (e.lawMap i) (he.closed_map i hi) := by
  intro V
  simp only [lawWitnessIdealSheaf_ideal, localLawWitnessIdeal]
  apply Ideal.span_mono
  rintro x ⟨a, rfl⟩
  exact ⟨e.atomMap i a, (he.coordinate_eq i hi V a).symm⟩

/-- Required generated ideal sheaves are monotone under a valid law inclusion. -/
theorem lawGeneratedIdealSheaf_mono
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    lawGeneratedIdealSheaf raw X R hR hRclosed ≤
      lawGeneratedIdealSheaf raw X Q hQ hQclosed := by
  intro V
  refine iSup_le fun i => ?_
  let j : {q : F.Index //
      F.Required q ∧ Q.selected V q} :=
    ⟨e.lawMap i.1, he.required_map i.1 i.2.1, he.selected_map V i.1 i.2.2⟩
  apply le_trans ?_ (le_iSup (fun q : {q : F.Index //
      F.Required q ∧ Q.selected V q} =>
    localLawWitnessIdeal raw X
      (Q.witness q.1 (hQclosed.closed q.1 q.2.1)) V) j)
  simpa only [lawWitnessIdealSheaf_ideal, j, Subtype.coe_mk] using
    (lawWitnessIdealSheaf_le raw X hR hQ e he i.1
      (hRclosed.closed i.1 i.2.1)) V

/-- All-law generated ideal sheaves are monotone under a valid law inclusion. -/
theorem allLawGeneratedIdealSheaf_mono
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    allLawGeneratedIdealSheaf raw X R hR ≤
      allLawGeneratedIdealSheaf raw X Q hQ := by
  intro V
  refine iSup_le fun i => ?_
  let j : {q : F.Index // Q.selected V q} :=
    ⟨e.lawMap i.1, he.selected_map V i.1 i.2⟩
  apply le_trans ?_ (le_iSup (fun q : {q : F.Index // Q.selected V q} =>
    localLawWitnessIdeal raw X
      (Q.witness q.1 (hQ.selected_closed V q.1 q.2)) V) j)
  simpa only [lawWitnessIdealSheaf_ideal, j, Subtype.coe_mk] using
    (lawWitnessIdealSheaf_le raw X hR hQ e he i.1
      (hR.selected_closed V i.1 i.2)) V

/-- Required semantic lawfulness is contravariantly monotone under law inclusion. -/
theorem semanticLawfulAlong_mono
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    SemanticLawfulAlong raw X Q s → SemanticLawfulAlong raw X R s := by
  intro h i hi
  exact he.semantic_monotone s i (h (e.lawMap i) (he.required_map i hi))

/-- Full semantic lawfulness is contravariantly monotone under law inclusion. -/
theorem fullySemanticLawfulAlong_mono
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    FullySemanticLawfulAlong raw X Q s →
      FullySemanticLawfulAlong raw X R s := by
  intro h i
  exact he.semantic_monotone s i (h (e.lawMap i))

/-- A valid law inclusion induces the contravariant map of required closed subschemes. -/
noncomputable def lawfulClosedSubschemeMap
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    lawfulClosedSubscheme raw X Q hQ hQclosed ⟶
      lawfulClosedSubscheme raw X R hR hRclosed :=
  Scheme.IdealSheafData.inclusion
    (lawGeneratedIdealSheaf_mono raw X hR hQ hRclosed hQclosed e he)

/-- The induced required closed-subscheme map is a closed immersion. -/
theorem lawfulClosedSubschemeMap_isClosedImmersion
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    IsClosedImmersion
      (lawfulClosedSubschemeMap raw X hR hQ hRclosed hQclosed e he) := by
  change IsClosedImmersion (Scheme.IdealSheafData.inclusion
    (lawGeneratedIdealSheaf_mono raw X hR hQ hRclosed hQclosed e he))
  infer_instance

/-- The induced required map commutes with the two ambient closed immersions. -/
@[reassoc] theorem lawfulClosedSubschemeMap_immersion
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    lawfulClosedSubschemeMap raw X hR hQ hRclosed hQclosed e he ≫
        lawfulClosedImmersion raw X R hR hRclosed =
      lawfulClosedImmersion raw X Q hQ hQclosed :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The required closed-subscheme map of the identity inclusion is the identity. -/
@[simp] theorem lawfulClosedSubschemeMap_id
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    lawfulClosedSubschemeMap raw X hR hR hclosed hclosed
        (ClosedEquationalLawInclusion.refl raw X R)
        (ClosedEquationalLawInclusion.refl_valid raw X R) = 𝟙 _ := by
  change Scheme.IdealSheafData.inclusion _ = 𝟙 _
  exact Scheme.IdealSheafData.inclusion_id _

/-- Required closed-subscheme maps compose contravariantly. -/
@[reassoc] theorem lawfulClosedSubschemeMap_comp
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    {P : ClosedEquationalLawReading raw X H}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hP : IsClosedEquationalLawReading raw X P)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (hPclosed : RequiredClosed raw X P)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (f : ClosedEquationalLawInclusion raw X Q P)
    (he : IsClosedEquationalLawInclusion raw X e)
    (hf : IsClosedEquationalLawInclusion raw X f) :
    lawfulClosedSubschemeMap raw X hQ hP hQclosed hPclosed f hf ≫
        lawfulClosedSubschemeMap raw X hR hQ hRclosed hQclosed e he =
      lawfulClosedSubschemeMap raw X hR hP hRclosed hPclosed
        (e.comp raw X f) (ClosedEquationalLawInclusion.comp_valid raw X e f he hf) := by
  change Scheme.IdealSheafData.inclusion _ ≫
      Scheme.IdealSheafData.inclusion _ = Scheme.IdealSheafData.inclusion _
  exact Scheme.IdealSheafData.inclusion_comp _ _

/-- A valid law inclusion induces the contravariant map of all-law closed subschemes. -/
noncomputable def allLawfulClosedSubschemeMap
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    allLawfulClosedSubscheme raw X Q hQ ⟶
      allLawfulClosedSubscheme raw X R hR :=
  Scheme.IdealSheafData.inclusion
    (allLawGeneratedIdealSheaf_mono raw X hR hQ e he)

/-- The induced all-law closed-subscheme map is a closed immersion. -/
theorem allLawfulClosedSubschemeMap_isClosedImmersion
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    IsClosedImmersion (allLawfulClosedSubschemeMap raw X hR hQ e he) := by
  change IsClosedImmersion (Scheme.IdealSheafData.inclusion
    (allLawGeneratedIdealSheaf_mono raw X hR hQ e he))
  infer_instance

/-- The induced all-law map commutes with the ambient closed immersions. -/
@[reassoc] theorem allLawfulClosedSubschemeMap_immersion
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    allLawfulClosedSubschemeMap raw X hR hQ e he ≫
        allLawfulClosedImmersion raw X R hR =
      allLawfulClosedImmersion raw X Q hQ :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The all-law closed-subscheme map of the identity inclusion is the identity. -/
@[simp] theorem allLawfulClosedSubschemeMap_id
    (R : ClosedEquationalLawReading raw X E)
    (hR : IsClosedEquationalLawReading raw X R) :
    allLawfulClosedSubschemeMap raw X hR hR
        (ClosedEquationalLawInclusion.refl raw X R)
        (ClosedEquationalLawInclusion.refl_valid raw X R) = 𝟙 _ := by
  change Scheme.IdealSheafData.inclusion _ = 𝟙 _
  exact Scheme.IdealSheafData.inclusion_id _

/-- All-law closed-subscheme maps compose contravariantly. -/
@[reassoc] theorem allLawfulClosedSubschemeMap_comp
    {R : ClosedEquationalLawReading raw X E}
    {Q : ClosedEquationalLawReading raw X F}
    {P : ClosedEquationalLawReading raw X H}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hP : IsClosedEquationalLawReading raw X P)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (f : ClosedEquationalLawInclusion raw X Q P)
    (he : IsClosedEquationalLawInclusion raw X e)
    (hf : IsClosedEquationalLawInclusion raw X f) :
    allLawfulClosedSubschemeMap raw X hQ hP f hf ≫
        allLawfulClosedSubschemeMap raw X hR hQ e he =
      allLawfulClosedSubschemeMap raw X hR hP
        (e.comp raw X f) (ClosedEquationalLawInclusion.comp_valid raw X e f he hf) := by
  change Scheme.IdealSheafData.inclusion _ ≫
      Scheme.IdealSheafData.inclusion _ = Scheme.IdealSheafData.inclusion _
  exact Scheme.IdealSheafData.inclusion_comp _ _
