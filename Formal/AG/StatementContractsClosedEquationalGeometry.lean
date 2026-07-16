import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Formal.AG.LawAlgebra.ClosedEquationalGeometryFiniteExample

/-!
Executable statement contracts for closed-equational geometry.

This file checks the approved closed-equational geometry signatures directly
against the implementation declarations. It contains elaboration examples only
and introduces no new mathematical declarations.
-/

noncomputable section

namespace AAT.AG.LawAlgebra

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable (raw : RawAmbientRestrictionSystem S k)
variable [HasSheafify S.topology (AATCommAlgCat k)]
variable (X : StandardArchitectureScheme raw)

/-! ### SD0: geometric law reading and closed-equational witnesses -/

example
    (HoldsOn : ∀ {T : AlgebraicGeometry.Scheme},
      (T ⟶ X.underlying) → S.lawUniverse.Index → Prop) :
    GeometricLawReading raw X :=
  GeometricLawReading.mk HoldsOn

example (R : GeometricLawReading raw X) :
    ∀ {T : AlgebraicGeometry.Scheme},
      (T ⟶ X.underlying) → S.lawUniverse.Index → Prop :=
  @R.HoldsOn

example
    (R Q : GeometricLawReading raw X)
    (h : @R.HoldsOn = @Q.HoldsOn) : R = Q :=
  GeometricLawReading.ext raw X R Q h

example (R : GeometricLawReading raw X) : Prop :=
  IsGeometricLawReading raw X R

example {i : S.lawUniverse.Index}
    (coordinate : ∀ V : X.underlying.affineOpens,
      U.Atom → Γ(X.underlying, V)) :
    ClosedEquationalLawWitness raw X i :=
  ClosedEquationalLawWitness.mk coordinate

example {i : S.lawUniverse.Index}
    (W : ClosedEquationalLawWitness raw X i) :
    ∀ V : X.underlying.affineOpens, U.Atom → Γ(X.underlying, V) :=
  W.coordinate

example {i : S.lawUniverse.Index}
    (W Z : ClosedEquationalLawWitness raw X i)
    (h : W.coordinate = Z.coordinate) : W = Z :=
  ClosedEquationalLawWitness.ext raw X W Z h

example {i : S.lawUniverse.Index}
    (W : ClosedEquationalLawWitness raw X i) : Prop :=
  IsClosedEquationalLawWitness raw X W

example {i : S.lawUniverse.Index}
    (W : ClosedEquationalLawWitness raw X i)
    (V : X.underlying.affineOpens) : Ideal Γ(X.underlying, V) :=
  localLawWitnessIdeal raw X W V

example {i : S.lawUniverse.Index}
    (W : ClosedEquationalLawWitness raw X i)
    (hW : IsClosedEquationalLawWitness raw X W)
    (V : X.underlying.affineOpens) (f : Γ(X.underlying, V)) :
    Ideal.map
        (X.underlying.presheaf.map
          (homOfLE (X.underlying.basicOpen_le f)).op).hom
        (localLawWitnessIdeal raw X W V) =
      localLawWitnessIdeal raw X W (X.underlying.affineBasicOpen f) :=
  localLawWitnessIdeal_map_basicOpen raw X W hW V f

example
    (i : S.lawUniverse.Index)
    (equation : U.Atom → Γ(X.underlying, ⊤)) :
    ClosedEquationalLawWitness raw X i :=
  ClosedEquationalLawWitness.ofGlobalSections raw X i equation

example
    (i : S.lawUniverse.Index)
    (equation : U.Atom → Γ(X.underlying, ⊤)) :
    IsClosedEquationalLawWitness raw X
      (ClosedEquationalLawWitness.ofGlobalSections raw X i equation) :=
  ClosedEquationalLawWitness.ofGlobalSections_valid raw X i equation

example
    (i : S.lawUniverse.Index)
    (equation : U.Atom → Γ(X.underlying, ⊤))
    (V : X.underlying.affineOpens) (a : U.Atom) :
    (ClosedEquationalLawWitness.ofGlobalSections raw X i equation).coordinate V a =
      X.underlying.presheaf.map (homOfLE le_top).op (equation a) :=
  ClosedEquationalLawWitness.ofGlobalSections_coordinate raw X i equation V a

example (G : SemanticLawEquationWitnessIdealCore S)
    (toRawPresentation : ∀ W : S.category,
      G.Observable W ≃+* raw.rawAlgebra W) :
    SemanticLawEquationSchemeBridge raw G :=
  SemanticLawEquationSchemeBridge.mk toRawPresentation

example (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    ∀ W : S.category, G.Observable W ≃+* raw.rawAlgebra W :=
  B.toRawPresentation

example {raw : RawAmbientRestrictionSystem S k}
    {G : SemanticLawEquationWitnessIdealCore S}
    (B : SemanticLawEquationSchemeBridge raw G)
    (W : S.category) : G.Observable W →+* SheafifiedSectionRing raw W :=
  B.toSheafifiedSection W

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B C : SemanticLawEquationSchemeBridge raw G)
    (h : B.toRawPresentation = C.toRawPresentation) : B = C :=
  SemanticLawEquationSchemeBridge.ext raw G B C h

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (restriction_natural :
      ∀ {source target : S.category} (f : source ⟶ target)
        (x : G.Observable target),
        B.toSheafifiedSection source (G.restrict f x) =
          sheafifiedRestriction raw f (B.toSheafifiedSection target x))
    (presentation_stable :
      ∀ W : S.category,
        AffineChart.AffineAATChart.SheafifiedChartPresentation raw W) :
    IsSemanticLawEquationSchemeBridge raw G B :=
  IsSemanticLawEquationSchemeBridge.mk restriction_natural presentation_stable

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B) :
    ∀ {source target : S.category} (f : source ⟶ target)
      (x : G.Observable target),
      B.toSheafifiedSection source (G.restrict f x) =
        sheafifiedRestriction raw f (B.toSheafifiedSection target x) :=
  hB.restriction_natural

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B) :
    ∀ W : S.category,
      AffineChart.AffineAATChart.SheafifiedChartPresentation raw W :=
  hB.presentation_stable

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    (W : S.category) :
    Function.Bijective (B.toSheafifiedSection W) :=
  SemanticLawEquationSchemeBridge.toSheafifiedSection_bijective raw G B hB W

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (i : S.lawUniverse.Index) (a : U.Atom) : Γ(X.underlying, ⊤) :=
  semanticCoreGlobalEquation raw X G B i a

example
    (equation : U.Atom → Γ(X.underlying, ⊤))
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  GlobalEquationsVanishAlong raw X equation s

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    GeometricLawReading raw X :=
  GeometricLawReading.ofSemanticCore raw X G B

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    IsGeometricLawReading raw X
      (GeometricLawReading.ofSemanticCore raw X G B) :=
  GeometricLawReading.ofSemanticCore_valid raw X G B

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (i : S.lawUniverse.Index) :
    (GeometricLawReading.ofSemanticCore raw X G B).HoldsOn s i ↔
      ∀ a, s.appTop (semanticCoreGlobalEquation raw X G B i a) = 0 :=
  GeometricLawReading.ofSemanticCore_holdsOn raw X G B s i

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    {source target : S.category} (f : source ⟶ target)
    (i : S.lawUniverse.Index) (a : U.Atom) :
    B.toSheafifiedSection source (G.violationWitness source i a) =
      sheafifiedRestriction raw f
        (B.toSheafifiedSection target (G.violationWitness target i a)) :=
  semanticCoreWitness_restrict raw G B hB f i a

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (W : S.category) (i : S.lawUniverse.Index) :
    Ideal.map (B.toSheafifiedSection W) (G.lawWitnessIdeal W i) =
      Ideal.span (Set.range (fun a =>
        B.toSheafifiedSection W (G.violationWitness W i a))) :=
  semanticCoreLawWitnessIdeal_map raw G B W i

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    (W : S.category) (i : S.lawUniverse.Index) :
    Ideal.comap (B.toSheafifiedSection W)
        (Ideal.map (B.toSheafifiedSection W) (G.lawWitnessIdeal W i)) =
      G.lawWitnessIdeal W i :=
  semanticCoreLawWitnessIdeal_comap_map raw G B hB W i

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    (j : X.atlas.Index) (i : S.lawUniverse.Index) (a : U.Atom) :
    ((X.atlas.chart j).map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing raw (X.atlas.chart j).context)).hom)
        (semanticCoreGlobalEquation raw X G B i a) =
      B.toSheafifiedSection (X.atlas.chart j).context
        (G.violationWitness (X.atlas.chart j).context i a) :=
  semanticCoreGlobalEquation_on_chart raw X G B hB j i a

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (i : S.lawUniverse.Index) : ClosedEquationalLawWitness raw X i :=
  ClosedEquationalLawWitness.ofSemanticCore raw X G B i

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (i : S.lawUniverse.Index) :
    IsClosedEquationalLawWitness raw X
      (ClosedEquationalLawWitness.ofSemanticCore raw X G B i) :=
  ClosedEquationalLawWitness.ofSemanticCore_valid raw X G B i

/-! ### SD1: reading validity and required/all selection -/

example
    (geometric : GeometricLawReading raw X)
    (closed : Set S.lawUniverse.Index)
    (selected : X.underlying.affineOpens → Set S.lawUniverse.Index)
    (witness : ∀ i, closed i → ClosedEquationalLawWitness raw X i) :
    ClosedEquationalLawReading raw X :=
  ClosedEquationalLawReading.mk geometric closed selected witness

example (R : ClosedEquationalLawReading raw X) :
    GeometricLawReading raw X :=
  R.geometric

example (R : ClosedEquationalLawReading raw X) :
    Set S.lawUniverse.Index :=
  R.closed

example (R : ClosedEquationalLawReading raw X) :
    X.underlying.affineOpens → Set S.lawUniverse.Index :=
  R.selected

example (R : ClosedEquationalLawReading raw X) :
    ∀ i, R.closed i → ClosedEquationalLawWitness raw X i :=
  R.witness

example
    (R Q : ClosedEquationalLawReading raw X)
    (hgeometric : R.geometric = Q.geometric)
    (hclosed : R.closed = Q.closed)
    (hselected : R.selected = Q.selected)
    (hwitness : HEq R.witness Q.witness) : R = Q :=
  ClosedEquationalLawReading.ext raw X R Q hgeometric hclosed hselected hwitness

example (R : ClosedEquationalLawReading raw X) : Prop :=
  IsClosedEquationalWitnessReading raw X R

example
    (R : ClosedEquationalLawReading raw X)
    (geometric_stable : IsGeometricLawReading raw X R.geometric)
    (witness_compatible : IsClosedEquationalWitnessReading raw X R)
    (selected_closed : ∀ V i, R.selected V i → R.closed i)
    (selected_basicOpen :
      ∀ (V : X.underlying.affineOpens)
        (f : Γ(X.underlying, V)) (i : S.lawUniverse.Index),
        R.selected V i ↔
          R.selected (X.underlying.affineBasicOpen f) i) :
    IsClosedEquationalLawReading raw X R :=
  IsClosedEquationalLawReading.mk geometric_stable witness_compatible
    selected_closed selected_basicOpen

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) :
    IsGeometricLawReading raw X R.geometric :=
  hR.geometric_stable

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) :
    IsClosedEquationalWitnessReading raw X R :=
  hR.witness_compatible

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) :
    ∀ V i, R.selected V i → R.closed i :=
  hR.selected_closed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) :
    ∀ (V : X.underlying.affineOpens)
      (f : Γ(X.underlying, V)) (i : S.lawUniverse.Index),
      R.selected V i ↔
        R.selected (X.underlying.affineBasicOpen f) i :=
  hR.selected_basicOpen

example
    (R : ClosedEquationalLawReading raw X)
    (closed : ∀ i, S.lawUniverse.Required i → R.closed i)
    (selected :
      ∀ V i, S.lawUniverse.Required i → R.selected V i) :
    RequiredClosed raw X R :=
  RequiredClosed.mk closed selected

example
    (R : ClosedEquationalLawReading raw X)
    (hR : RequiredClosed raw X R) :
    ∀ i, S.lawUniverse.Required i → R.closed i :=
  hR.closed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : RequiredClosed raw X R) :
    ∀ V i, S.lawUniverse.Required i → R.selected V i :=
  hR.selected

example
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  SemanticLawfulAlong raw X R s

example
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  FullySemanticLawfulAlong raw X R s

example
    (R : ClosedEquationalLawReading raw X)
    (closed : ∀ i, R.closed i)
    (selected : ∀ V i, R.selected V i) :
    AllLawsSelected raw X R :=
  AllLawsSelected.mk closed selected

example
    (R : ClosedEquationalLawReading raw X)
    (hR : AllLawsSelected raw X R) : ∀ i, R.closed i :=
  hR.closed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : AllLawsSelected raw X R) : ∀ V i, R.selected V i :=
  hR.selected

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    ClosedEquationalLawReading raw X :=
  ClosedEquationalLawReading.ofSemanticCore raw X G B

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (i : S.lawUniverse.Index)
    (hi : (ClosedEquationalLawReading.ofSemanticCore raw X G B).closed i) :
    (ClosedEquationalLawReading.ofSemanticCore raw X G B).witness i hi =
      ClosedEquationalLawWitness.ofSemanticCore raw X G B i :=
  ClosedEquationalLawReading.ofSemanticCore_witness raw X G B i hi

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    IsClosedEquationalWitnessReading raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B) :=
  ClosedEquationalLawReading.ofSemanticCore_witnessCompatible raw X G B

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    IsClosedEquationalLawReading raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B) :=
  ClosedEquationalLawReading.ofSemanticCore_valid raw X G B

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    RequiredClosed raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B) :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (V : X.underlying.affineOpens) (i : S.lawUniverse.Index) :
    (ClosedEquationalLawReading.ofSemanticCore raw X G B).selected V i :=
  ClosedEquationalLawReading.ofSemanticCore_selected raw X G B V i

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    AllLawsSelected raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B) :=
  ClosedEquationalLawReading.ofSemanticCore_allLawsSelected raw X G B

/-! ### SD2: actual ideal sheaves and required/all obstruction ideals -/

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i) :
    X.underlying.IdealSheafData :=
  lawWitnessIdealSheaf raw X R hR i hi

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i)
    (V : X.underlying.affineOpens) :
    (lawWitnessIdealSheaf raw X R hR i hi).ideal V =
      localLawWitnessIdeal raw X (R.witness i hi) V :=
  lawWitnessIdealSheaf_ideal raw X R hR i hi V

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i)
    (equation : U.Atom → Γ(X.underlying, ⊤))
    (hw : R.witness i hi =
      ClosedEquationalLawWitness.ofGlobalSections raw X i equation) :
    lawWitnessIdealSheaf raw X R hR i hi =
      Scheme.IdealSheafData.ofIdealTop (X := X.underlying)
        (Ideal.span (Set.range equation)) :=
  lawWitnessIdealSheaf_ofGlobalSections raw X R hR i hi equation hw

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) : Prop :=
  SemanticCoreIdealSheafRealized raw X G B

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G) :
    SemanticCoreIdealSheafRealized raw X G B ↔
      ((∀ W : S.category,
          AffineChart.AffineAATChart.SheafifiedChartPresentation raw W) ∧
        ∀ (j : X.atlas.Index) (i : S.lawUniverse.Index),
          let R := ClosedEquationalLawReading.ofSemanticCore raw X G B
          let hR :=
            ClosedEquationalLawReading.ofSemanticCore_witnessCompatible raw X G B
          ((lawWitnessIdealSheaf raw X R hR i (Set.mem_univ i)).comap
              (X.atlas.chart j).map) =
            Scheme.IdealSheafData.ofIdealTop
              (X := (X.atlas.chart j).domain)
              (Ideal.map
                (AlgebraicGeometry.Scheme.ΓSpecIso
                  (SheafifiedSectionRing raw
                    (X.atlas.chart j).context)).inv.hom
                (Ideal.map
                  (B.toSheafifiedSection (X.atlas.chart j).context)
                  (G.lawWitnessIdeal (X.atlas.chart j).context i)))) :=
  Iff.rfl

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B) :
    SemanticCoreIdealSheafRealized raw X G B :=
  semanticCoreIdealSheaf_realized raw X G B hB

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) (f : Γ(X.underlying, V)) :
    Ideal.map
        (X.underlying.presheaf.map
          (homOfLE (X.underlying.basicOpen_le f)).op).hom
        (⨆ i : {i : S.lawUniverse.Index //
            S.lawUniverse.Required i ∧ R.selected V i},
          localLawWitnessIdeal raw X
            (R.witness i.1 (hclosed.closed i.1 i.2.1)) V) =
      ⨆ i : {i : S.lawUniverse.Index //
          S.lawUniverse.Required i ∧
            R.selected (X.underlying.affineBasicOpen f) i},
        localLawWitnessIdeal raw X
            (R.witness i.1 (hclosed.closed i.1 i.2.1))
            (X.underlying.affineBasicOpen f) :=
  requiredLocalLawIdeal_map_basicOpen raw X R hR hclosed V f

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (V : X.underlying.affineOpens) (f : Γ(X.underlying, V)) :
    Ideal.map
        (X.underlying.presheaf.map
          (homOfLE (X.underlying.basicOpen_le f)).op).hom
        (⨆ i : {i : S.lawUniverse.Index // R.selected V i},
          localLawWitnessIdeal raw X
            (R.witness i.1 (hR.selected_closed V i.1 i.2)) V) =
      ⨆ i : {i : S.lawUniverse.Index //
          R.selected (X.underlying.affineBasicOpen f) i},
          localLawWitnessIdeal raw X
            (R.witness i.1
              (hR.selected_closed
                (X.underlying.affineBasicOpen f) i.1 i.2))
            (X.underlying.affineBasicOpen f) :=
  allSelectedLocalLawIdeal_map_basicOpen raw X R hR V f

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    X.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) :
    X.underlying.IdealSheafData :=
  allLawGeneratedIdealSheaf raw X R hR

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) :
    (lawGeneratedIdealSheaf raw X R hR hclosed).ideal V =
      ⨆ i : {i : S.lawUniverse.Index //
          S.lawUniverse.Required i ∧ R.selected V i},
        localLawWitnessIdeal raw X
          (R.witness i.1 (hclosed.closed i.1 i.2.1)) V :=
  lawGeneratedIdealSheaf_ideal raw X R hR hclosed V

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (V : X.underlying.affineOpens) :
    (allLawGeneratedIdealSheaf raw X R hR).ideal V =
      ⨆ i : {i : S.lawUniverse.Index // R.selected V i},
        localLawWitnessIdeal raw X
          (R.witness i.1 (hR.selected_closed V i.1 i.2)) V :=
  allLawGeneratedIdealSheaf_ideal raw X R hR V

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    lawGeneratedIdealSheaf raw X R hR hclosed ≤
      allLawGeneratedIdealSheaf raw X R hR :=
  lawGeneratedIdealSheaf_le_all raw X R hR hclosed

/-! ### SD3: actual closed geometry and pulled decoration -/

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) : AlgebraicGeometry.Scheme :=
  lawfulClosedSubscheme raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    lawfulClosedSubscheme raw X R hR hclosed ⟶ X.underlying :=
  lawfulClosedImmersion raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) : AlgebraicGeometry.Scheme :=
  allLawfulClosedSubscheme raw X R hR

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) :
    allLawfulClosedSubscheme raw X R hR ⟶ X.underlying :=
  allLawfulClosedImmersion raw X R hR

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    IsClosedImmersion (lawfulClosedImmersion raw X R hR hclosed) :=
  lawfulClosedImmersion_isClosedImmersion raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedImmersion raw X R hR hclosed).ker =
      lawGeneratedIdealSheaf raw X R hR hclosed :=
  lawfulClosedImmersion_ker raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    Set.range (lawfulClosedImmersion raw X R hR hclosed) =
      (lawGeneratedIdealSheaf raw X R hR hclosed).support :=
  lawfulClosedImmersion_range raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedSubscheme raw X R hR hclosed).AffineOpenCover :=
  lawfulClosedSubschemeCover raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) :
    (lawfulClosedSubschemeCover raw X R hR hclosed).X V =
      CommRingCat.of
        (Γ(X.underlying, V) ⧸
          (lawGeneratedIdealSheaf raw X R hR hclosed).ideal V) :=
  lawfulClosedSubschemeCover_X raw X R hR hclosed V

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (V : X.underlying.affineOpens) :
    Γ(lawfulClosedSubscheme raw X R hR hclosed,
        lawfulClosedImmersion raw X R hR hclosed ⁻¹ᵁ V) ≅
      CommRingCat.of
        (Γ(X.underlying, V) ⧸
          (lawGeneratedIdealSheaf raw X R hR hclosed).ideal V) :=
  lawfulClosedSubschemeObjIso raw X R hR hclosed V

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    AATReadingDecoration raw (lawfulClosedSubscheme raw X R hR hclosed) :=
  lawfulClosedDecoration raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedDecoration raw X R hR hclosed).context = X.decoration.context :=
  lawfulClosedDecoration_context raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedDecoration raw X R hR hclosed).lawUniverse raw =
      X.decoration.lawUniverse raw :=
  lawfulClosedDecoration_lawUniverse raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    (lawfulClosedDecoration raw X R hR hclosed).signature raw =
      X.decoration.signature raw :=
  lawfulClosedDecoration_signature raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (c : (X.decoration.coordinateFamily raw).CoordX) :
    (lawfulClosedDecoration raw X R hR hclosed).coordinateSection raw c =
      (lawfulClosedImmersion raw X R hR hclosed).appTop
        (X.decoration.coordinateSection raw c) :=
  lawfulClosedDecoration_coordinateSection raw X R hR hclosed c

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    allLawfulClosedSubscheme raw X R hR ⟶
      lawfulClosedSubscheme raw X R hR hclosed :=
  fullToRequiredLawfulMap raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    IsClosedImmersion (fullToRequiredLawfulMap raw X R hR hclosed) :=
  fullToRequiredLawfulMap_isClosedImmersion raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    fullToRequiredLawfulMap raw X R hR hclosed ≫
        lawfulClosedImmersion raw X R hR hclosed =
      allLawfulClosedImmersion raw X R hR :=
  fullToRequiredLawfulMap_immersion raw X R hR hclosed

/-! ### SD4: exactness, ideal lawfulness, and actual factorization -/

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i) : Prop :=
  LawIdealSound raw X R hR i hi

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i) : Prop :=
  LawIdealComplete raw X R hR i hi

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i) : Prop :=
  LawIdealExact raw X R hR i hi

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalWitnessReading raw X R)
    (i : S.lawUniverse.Index) (hi : R.closed i) :
    LawIdealExact raw X R hR i hi ↔
      LawIdealSound raw X R hR i hi ∧
        LawIdealComplete raw X R hR i hi :=
  lawIdealExact_iff_sound_and_complete raw X R hR i hi

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) : Prop :=
  RequiredLawIdealExact raw X R hR hclosed

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hall : AllLawsSelected raw X R) : Prop :=
  AllLawIdealExact raw X R hR hall

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  WitnessVanishes raw X R hR hclosed s

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  IdealLawfulAlong raw X R hR hclosed s

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Prop :=
  FullIdealLawfulAlong raw X R hR s

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Type _ :=
  FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s =
      {t : T ⟶ lawfulClosedSubscheme raw X R hR hclosed //
        t ≫ lawfulClosedImmersion raw X R hR hclosed = s} :=
  rfl

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) : Type _ :=
  FactorsThroughAllLawfulClosedSubscheme raw X R hR s

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    FactorsThroughAllLawfulClosedSubscheme raw X R hR s =
      {t : T ⟶ allLawfulClosedSubscheme raw X R hR //
        t ≫ allLawfulClosedImmersion raw X R hR = s} :=
  rfl

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    IdealLawfulAlong raw X R hR hclosed s ↔
      lawGeneratedIdealSheaf raw X R hR hclosed ≤ s.ker :=
  idealLawfulAlong_iff_le_ker raw X R hR hclosed s

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : IdealLawfulAlong raw X R hR hclosed s) :
    T ⟶ lawfulClosedSubscheme raw X R hR hclosed :=
  factorizationLift raw X R hR hclosed s hs

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : IdealLawfulAlong raw X R hR hclosed s) :
    factorizationLift raw X R hR hclosed s hs ≫
        lawfulClosedImmersion raw X R hR hclosed = s :=
  factorizationLift_fac raw X R hR hclosed s hs

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (a b : FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s) :
    a.1 = b.1 :=
  factorization_unique raw X R hR hclosed s a b

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    IdealLawfulAlong raw X R hR hclosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s) :=
  idealLawfulAlong_iff_nonempty_factorsThrough raw X R hR hclosed s

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : FullIdealLawfulAlong raw X R hR s) :
    T ⟶ allLawfulClosedSubscheme raw X R hR :=
  allLawFactorizationLift raw X R hR s hs

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (hs : FullIdealLawfulAlong raw X R hR s) :
    allLawFactorizationLift raw X R hR s hs ≫
        allLawfulClosedImmersion raw X R hR = s :=
  allLawFactorizationLift_fac raw X R hR s hs

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (a b : FactorsThroughAllLawfulClosedSubscheme raw X R hR s) :
    a.1 = b.1 :=
  allLawFactorization_unique raw X R hR s a b

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    FullIdealLawfulAlong raw X R hR s ↔
      Nonempty (FactorsThroughAllLawfulClosedSubscheme raw X R hR s) :=
  fullIdealLawfulAlong_iff_nonempty_factorsThrough raw X R hR s

/-! ### SD5: required and full lawfulness correspondences -/

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (hexact : RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    SemanticLawfulAlong raw X R s ↔
      WitnessVanishes raw X R hR hclosed s :=
  semanticLawfulAlong_iff_witnessVanishes raw X R hR hclosed hexact s

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    WitnessVanishes raw X R hR hclosed s ↔
      IdealLawfulAlong raw X R hR hclosed s :=
  witnessVanishes_iff_idealLawfulAlong raw X R hR hclosed s

example
    (R : ClosedEquationalLawReading raw X)
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
  lawfulnessIdealFactorizationCorrespondence raw X R hR hclosed hexact s

example
    (G : SemanticLawEquationWitnessIdealCore S)
    (B : SemanticLawEquationSchemeBridge raw G)
    (hB : IsSemanticLawEquationSchemeBridge raw G B)
    (hexact : RequiredLawIdealExact raw X
      (ClosedEquationalLawReading.ofSemanticCore raw X G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid raw X G B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B))
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    let R := ClosedEquationalLawReading.ofSemanticCore raw X G B
    let hR := ClosedEquationalLawReading.ofSemanticCore_valid raw X G B
    let hclosed :=
      ClosedEquationalLawReading.ofSemanticCore_requiredClosed raw X G B
    SemanticCoreIdealSheafRealized raw X G B ∧
    (SemanticLawfulAlong raw X R s ↔
      WitnessVanishes raw X R hR hclosed s) ∧
    (WitnessVanishes raw X R hR hclosed s ↔
      IdealLawfulAlong raw X R hR hclosed s) ∧
    (IdealLawfulAlong raw X R hR hclosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s)) :=
  semanticCoreLawfulnessIdealFactorizationCorrespondence
    raw X G B hB hexact s

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hall : AllLawsSelected raw X R)
    (hexact : AllLawIdealExact raw X R hR hall)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    FullySemanticLawfulAlong raw X R s ↔
      FullIdealLawfulAlong raw X R hR s :=
  fullySemanticLawfulAlong_iff_fullIdealLawfulAlong
    raw X R hR hall hexact s

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hall : AllLawsSelected raw X R)
    (hexact : AllLawIdealExact raw X R hR hall)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    (FullySemanticLawfulAlong raw X R s ↔
      FullIdealLawfulAlong raw X R hR s) ∧
    (FullIdealLawfulAlong raw X R hR s ↔
      Nonempty (FactorsThroughAllLawfulClosedSubscheme raw X R hR s)) :=
  fullLawfulnessIdealFactorizationCorrespondence
    raw X R hR hall hexact s

/-! ### SD6: object, valuation, and signature-axis comparisons -/

example
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) : Prop :=
  RequiredObjectPointComparison raw X R s Obj

example
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) :
    RequiredObjectPointComparison raw X R s Obj ↔
      ∀ i, S.lawUniverse.Required i →
        (R.geometric.HoldsOn s i ↔ (S.lawUniverse.law i).holds Obj) :=
  Iff.rfl

example
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U)
    (hpoint : RequiredObjectPointComparison raw X R s Obj) :
    SemanticLawfulAlong raw X R s ↔ Lawfulness Obj S.lawUniverse :=
  semanticLawfulAlong_iff_lawfulness raw X R s Obj hpoint

example
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U)
    {Value : Type u}
    (valuation : ObstructionValuation U Value)
    (aggregation : ZeroReflectingAggregation Value valuation.domain
      S.lawUniverse.RequiredIndex)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (hsound : ∀ i : S.lawUniverse.RequiredIndex,
      ObstructionSound valuation (S.lawUniverse.law i.1))
    (hcomplete : ∀ i : S.lawUniverse.RequiredIndex,
      ObstructionComplete valuation (S.lawUniverse.law i.1)) :
    SemanticLawfulAlong raw X R s ↔
      omegaU valuation S.lawUniverse aggregation Obj = valuation.domain.zero :=
  semanticLawfulAlong_iff_omegaU_zero raw X R s Obj valuation aggregation
    hpoint hsound hcomplete

example
    (R : ClosedEquationalLawReading raw X)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) (Sig : SignatureAxes U)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (haxis : Lawfulness Obj S.lawUniverse ↔
      RequiredSignatureAxesZero Obj Sig) :
    SemanticLawfulAlong raw X R s ↔ RequiredSignatureAxesZero Obj Sig :=
  semanticLawfulAlong_iff_requiredSignatureAxesZero
    raw X R s Obj Sig hpoint haxis

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (hexact : RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U)
    {Value : Type u}
    (valuation : ObstructionValuation U Value)
    (aggregation : ZeroReflectingAggregation Value valuation.domain
      S.lawUniverse.RequiredIndex)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (hsound : ∀ i : S.lawUniverse.RequiredIndex,
      ObstructionSound valuation (S.lawUniverse.law i.1))
    (hcomplete : ∀ i : S.lawUniverse.RequiredIndex,
      ObstructionComplete valuation (S.lawUniverse.law i.1)) :
    Nonempty (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s) ↔
      omegaU valuation S.lawUniverse aggregation Obj = valuation.domain.zero :=
  factorsThroughLawfulClosedSubscheme_iff_omegaU_zero
    raw X R hR hclosed hexact s Obj valuation aggregation
      hpoint hsound hcomplete

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R)
    (hexact : RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) (Sig : SignatureAxes U)
    (hpoint : RequiredObjectPointComparison raw X R s Obj)
    (haxis : Lawfulness Obj S.lawUniverse ↔
      RequiredSignatureAxesZero Obj Sig) :
    Nonempty (FactorsThroughLawfulClosedSubscheme raw X R hR hclosed s) ↔
      RequiredSignatureAxesZero Obj Sig :=
  factorsThroughLawfulClosedSubscheme_iff_requiredSignatureAxesZero
    raw X R hR hclosed hexact s Obj Sig hpoint haxis

/-! ### SD7: law inclusion and contravariant closed geometry -/

example
    (R Q : ClosedEquationalLawReading raw X)
    (lawMap : S.lawUniverse.Index → S.lawUniverse.Index)
    (atomMap : ∀ _i : S.lawUniverse.Index, U.Atom → U.Atom) :
    ClosedEquationalLawInclusion raw X R Q :=
  ClosedEquationalLawInclusion.mk lawMap atomMap

example
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q) :
    S.lawUniverse.Index → S.lawUniverse.Index :=
  e.lawMap

example
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q) :
    ∀ _i : S.lawUniverse.Index, U.Atom → U.Atom :=
  e.atomMap

example
    {R Q : ClosedEquationalLawReading raw X}
    (e f : ClosedEquationalLawInclusion raw X R Q)
    (hlawMap : e.lawMap = f.lawMap)
    (hatomMap : e.atomMap = f.atomMap) : e = f :=
  ClosedEquationalLawInclusion.ext raw X e f hlawMap hatomMap

example
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (required_map : ∀ i, S.lawUniverse.Required i →
      S.lawUniverse.Required (e.lawMap i))
    (closed_map : ∀ i, R.closed i → Q.closed (e.lawMap i))
    (selected_map :
      ∀ V i, R.selected V i → Q.selected V (e.lawMap i))
    (coordinate_eq :
      ∀ i (hi : R.closed i) (V : X.underlying.affineOpens) (a : U.Atom),
        (R.witness i hi).coordinate V a =
          (Q.witness (e.lawMap i) (closed_map i hi)).coordinate V
            (e.atomMap i a))
    (semantic_monotone :
      ∀ {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) i,
        Q.geometric.HoldsOn s (e.lawMap i) → R.geometric.HoldsOn s i) :
    IsClosedEquationalLawInclusion raw X e :=
  IsClosedEquationalLawInclusion.mk required_map closed_map selected_map
    coordinate_eq semantic_monotone

example
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    ∀ i, S.lawUniverse.Required i →
      S.lawUniverse.Required (e.lawMap i) :=
  he.required_map

example
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    ∀ i, R.closed i → Q.closed (e.lawMap i) :=
  he.closed_map

example
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    ∀ V i, R.selected V i → Q.selected V (e.lawMap i) :=
  he.selected_map

example
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    ∀ i (hi : R.closed i) (V : X.underlying.affineOpens) (a : U.Atom),
      (R.witness i hi).coordinate V a =
        (Q.witness (e.lawMap i) (he.closed_map i hi)).coordinate V
          (e.atomMap i a) :=
  he.coordinate_eq

example
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    ∀ {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) i,
      Q.geometric.HoldsOn s (e.lawMap i) → R.geometric.HoldsOn s i :=
  he.semantic_monotone

example
    (R : ClosedEquationalLawReading raw X) :
    ClosedEquationalLawInclusion raw X R R :=
  ClosedEquationalLawInclusion.refl raw X R

example
    (R : ClosedEquationalLawReading raw X) :
    IsClosedEquationalLawInclusion raw X
      (ClosedEquationalLawInclusion.refl raw X R) :=
  ClosedEquationalLawInclusion.refl_valid raw X R

example
    {R Q P : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (f : ClosedEquationalLawInclusion raw X Q P) :
    ClosedEquationalLawInclusion raw X R P :=
  ClosedEquationalLawInclusion.comp raw X e f

example
    {R Q P : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (f : ClosedEquationalLawInclusion raw X Q P)
    (he : IsClosedEquationalLawInclusion raw X e)
    (hf : IsClosedEquationalLawInclusion raw X f) :
    IsClosedEquationalLawInclusion raw X (e.comp raw X f) :=
  ClosedEquationalLawInclusion.comp_valid raw X e f he hf

example
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e)
    (i : S.lawUniverse.Index) (hi : R.closed i) :
    lawWitnessIdealSheaf raw X R hR.witness_compatible i hi ≤
      lawWitnessIdealSheaf raw X Q hQ.witness_compatible
        (e.lawMap i) (he.closed_map i hi) :=
  lawWitnessIdealSheaf_le raw X hR hQ e he i hi

example
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    lawGeneratedIdealSheaf raw X R hR hRclosed ≤
      lawGeneratedIdealSheaf raw X Q hQ hQclosed :=
  lawGeneratedIdealSheaf_mono raw X hR hQ hRclosed hQclosed e he

example
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    allLawGeneratedIdealSheaf raw X R hR ≤
      allLawGeneratedIdealSheaf raw X Q hQ :=
  allLawGeneratedIdealSheaf_mono raw X hR hQ e he

example
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    SemanticLawfulAlong raw X Q s → SemanticLawfulAlong raw X R s :=
  semanticLawfulAlong_mono raw X e he s

example
    {R Q : ClosedEquationalLawReading raw X}
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying) :
    FullySemanticLawfulAlong raw X Q s →
      FullySemanticLawfulAlong raw X R s :=
  fullySemanticLawfulAlong_mono raw X e he s

example
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    lawfulClosedSubscheme raw X Q hQ hQclosed ⟶
      lawfulClosedSubscheme raw X R hR hRclosed :=
  lawfulClosedSubschemeMap raw X hR hQ hRclosed hQclosed e he

example
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    IsClosedImmersion
      (lawfulClosedSubschemeMap raw X hR hQ hRclosed hQclosed e he) :=
  lawfulClosedSubschemeMap_isClosedImmersion
    raw X hR hQ hRclosed hQclosed e he

example
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (hRclosed : RequiredClosed raw X R)
    (hQclosed : RequiredClosed raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    lawfulClosedSubschemeMap raw X hR hQ hRclosed hQclosed e he ≫
        lawfulClosedImmersion raw X R hR hRclosed =
      lawfulClosedImmersion raw X Q hQ hQclosed :=
  lawfulClosedSubschemeMap_immersion
    raw X hR hQ hRclosed hQclosed e he

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R)
    (hclosed : RequiredClosed raw X R) :
    lawfulClosedSubschemeMap raw X hR hR hclosed hclosed
        (ClosedEquationalLawInclusion.refl raw X R)
        (ClosedEquationalLawInclusion.refl_valid raw X R) = 𝟙 _ :=
  lawfulClosedSubschemeMap_id raw X R hR hclosed

example
    {R Q P : ClosedEquationalLawReading raw X}
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
        (e.comp raw X f)
        (ClosedEquationalLawInclusion.comp_valid raw X e f he hf) :=
  lawfulClosedSubschemeMap_comp
    raw X hR hQ hP hRclosed hQclosed hPclosed e f he hf

example
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    allLawfulClosedSubscheme raw X Q hQ ⟶
      allLawfulClosedSubscheme raw X R hR :=
  allLawfulClosedSubschemeMap raw X hR hQ e he

example
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    IsClosedImmersion (allLawfulClosedSubschemeMap raw X hR hQ e he) :=
  allLawfulClosedSubschemeMap_isClosedImmersion raw X hR hQ e he

example
    {R Q : ClosedEquationalLawReading raw X}
    (hR : IsClosedEquationalLawReading raw X R)
    (hQ : IsClosedEquationalLawReading raw X Q)
    (e : ClosedEquationalLawInclusion raw X R Q)
    (he : IsClosedEquationalLawInclusion raw X e) :
    allLawfulClosedSubschemeMap raw X hR hQ e he ≫
        allLawfulClosedImmersion raw X R hR =
      allLawfulClosedImmersion raw X Q hQ :=
  allLawfulClosedSubschemeMap_immersion raw X hR hQ e he

example
    (R : ClosedEquationalLawReading raw X)
    (hR : IsClosedEquationalLawReading raw X R) :
    allLawfulClosedSubschemeMap raw X hR hR
        (ClosedEquationalLawInclusion.refl raw X R)
        (ClosedEquationalLawInclusion.refl_valid raw X R) = 𝟙 _ :=
  allLawfulClosedSubschemeMap_id raw X R hR

example
    {R Q P : ClosedEquationalLawReading raw X}
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
        (e.comp raw X f)
        (ClosedEquationalLawInclusion.comp_valid raw X e f he hf) :=
  allLawfulClosedSubschemeMap_comp raw X hR hQ hP e f he hf

end AAT.AG.LawAlgebra

namespace AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry
open AAT.AG.FiniteModel
open AAT.AG.LawAlgebra.FiniteExamples.RingedSite.FiniteModel
open AAT.AG.LawAlgebra.FiniteExamples.StandardArchitectureScheme

/-! ### SD9: weak/strong semantic-core fixtures -/

example :
    SemanticLawEquationWitnessIdealCore
      AAT.AG.LawAlgebra.FiniteExamples.RingedSite.FiniteModel.site :=
  weakLawEquationCore

example :
    SemanticLawEquationWitnessIdealCore
      AAT.AG.LawAlgebra.FiniteExamples.RingedSite.FiniteModel.site :=
  strongLawEquationCore

example : SemanticLawEquationSchemeBridge rawSystem weakLawEquationCore :=
  weakSchemeBridge

example : SemanticLawEquationSchemeBridge rawSystem strongLawEquationCore :=
  strongSchemeBridge

example :
    IsSemanticLawEquationSchemeBridge rawSystem
      weakLawEquationCore weakSchemeBridge :=
  weakSchemeBridge_valid

example :
    IsSemanticLawEquationSchemeBridge rawSystem
      strongLawEquationCore strongSchemeBridge :=
  strongSchemeBridge_valid

example (W : RingedSite.FiniteModel.site.category) :
    AffineChart.AffineAATChart.SheafifiedChartPresentation rawSystem W :=
  weakSchemeBridge_presentationStable W

example (W : RingedSite.FiniteModel.site.category) :
    Function.Bijective (weakSchemeBridge.toSheafifiedSection W) :=
  weakSchemeBridge_toSheafifiedSection_bijective W

example (W : RingedSite.FiniteModel.site.category) (i : lawUniverse.Index) :
    Ideal.comap (weakSchemeBridge.toSheafifiedSection W)
        (Ideal.map (weakSchemeBridge.toSheafifiedSection W)
          (weakLawEquationCore.lawWitnessIdeal W i)) =
      weakLawEquationCore.lawWitnessIdeal W i :=
  weakCore_witnessIdeal_reflected W i

example : Γ(twoChartReferenceModel.underlying, ⊤) :=
  baseGlobalCoordinate

example :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge PUnit.unit FiniteAtom.componentA =
      baseGlobalCoordinate - 1 :=
  weakCore_componentA_equation

example (a : carrier.Atom) (ha : a ≠ FiniteAtom.componentA) :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge PUnit.unit a = 0 :=
  weakCore_other_equation a ha

example :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit FiniteAtom.componentA =
      baseGlobalCoordinate - 1 :=
  strongCore_componentA_equation

example :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit FiniteAtom.componentB =
      baseGlobalCoordinate + 1 :=
  strongCore_componentB_equation

example
    (a : carrier.Atom)
    (ha : a ≠ FiniteAtom.componentA) (hb : a ≠ FiniteAtom.componentB) :
    semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit a = 0 :=
  strongCore_other_equation a ha hb

example (a : carrier.Atom) :
    ((twoChartReferenceModel.atlas.chart leftIndex).map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem
            (twoChartReferenceModel.atlas.chart leftIndex).context)).hom)
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          weakLawEquationCore weakSchemeBridge PUnit.unit a) =
      weakSchemeBridge.toSheafifiedSection
        (twoChartReferenceModel.atlas.chart leftIndex).context
        (weakLawEquationCore.violationWitness
          (twoChartReferenceModel.atlas.chart leftIndex).context PUnit.unit a) :=
  weakCore_leftChart_provenance_fires a

example :
    Ideal.map
        (weakSchemeBridge.toSheafifiedSection
          (twoChartReferenceModel.atlas.chart leftIndex).context)
        (weakLawEquationCore.lawWitnessIdeal
          (twoChartReferenceModel.atlas.chart leftIndex).context PUnit.unit) =
      Ideal.span (Set.range (fun a =>
        weakSchemeBridge.toSheafifiedSection
          (twoChartReferenceModel.atlas.chart leftIndex).context
          (weakLawEquationCore.violationWitness
            (twoChartReferenceModel.atlas.chart leftIndex).context
            PUnit.unit a))) :=
  weakCore_leftChart_witnessIdeal_realization_fires

example : ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  weakReading

example : ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  strongReading

example
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) (i : lawUniverse.Index) :
    weakReading.geometric.HoldsOn s i ↔
      ∀ a, s.appTop
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          weakLawEquationCore weakSchemeBridge i a) = 0 :=
  weakReading_holdsOn_iff s i

example
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) (i : lawUniverse.Index) :
    strongReading.geometric.HoldsOn s i ↔
      ∀ a, s.appTop
        (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
          strongLawEquationCore strongSchemeBridge i a) = 0 :=
  strongReading_holdsOn_iff s i

example (i : lawUniverse.Index) (hi : weakReading.closed i) :
    weakReading.witness i hi =
      ClosedEquationalLawWitness.ofSemanticCore rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge i :=
  weakReading_witness_eq_ofSemanticCore i hi

example (i : lawUniverse.Index) (hi : strongReading.closed i) :
    strongReading.witness i hi =
      ClosedEquationalLawWitness.ofSemanticCore rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge i :=
  strongReading_witness_eq_ofSemanticCore i hi

example :
    IsGeometricLawReading rawSystem twoChartReferenceModel weakReading.geometric :=
  weakGeometricReading_valid

example :
    IsGeometricLawReading rawSystem twoChartReferenceModel strongReading.geometric :=
  strongGeometricReading_valid

example :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel weakReading :=
  weakReading_witnessCompatible

example :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel strongReading :=
  strongReading_witnessCompatible

example :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel weakReading :=
  weakReading_valid

example :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel strongReading :=
  strongReading_valid

example : weakReading.closed PUnit.unit :=
  weakReading_closed_unit

example
    (V : twoChartReferenceModel.underlying.affineOpens)
    (i : lawUniverse.Index) : weakReading.selected V i :=
  weakReading_selected V i

example
    (V : twoChartReferenceModel.underlying.affineOpens)
    (i : lawUniverse.Index) : strongReading.selected V i :=
  strongReading_selected V i

example :
    ((lawWitnessIdealSheaf rawSystem twoChartReferenceModel weakReading
        weakReading_witnessCompatible PUnit.unit weakReading_closed_unit).comap
        (twoChartReferenceModel.atlas.chart leftIndex).map) =
      Scheme.IdealSheafData.ofIdealTop
        (X := (twoChartReferenceModel.atlas.chart leftIndex).domain)
        (Ideal.map
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing rawSystem
              (twoChartReferenceModel.atlas.chart leftIndex).context)).inv.hom
          (Ideal.map
            (weakSchemeBridge.toSheafifiedSection
              (twoChartReferenceModel.atlas.chart leftIndex).context)
            (weakLawEquationCore.lawWitnessIdeal
              (twoChartReferenceModel.atlas.chart leftIndex).context PUnit.unit))) :=
  weakCore_leftChart_idealSheaf_realization_fires

example :
    IsClosedEquationalLawWitness rawSystem twoChartReferenceModel
      (weakReading.witness PUnit.unit weakReading_closed_unit) :=
  weakWitness_valid

example : RequiredClosed rawSystem twoChartReferenceModel weakReading :=
  weakReading_requiredClosed

example : RequiredClosed rawSystem twoChartReferenceModel strongReading :=
  strongReading_requiredClosed

example : AllLawsSelected rawSystem twoChartReferenceModel weakReading :=
  weakReading_allLawsSelected

example : AllLawsSelected rawSystem twoChartReferenceModel strongReading :=
  strongReading_allLawsSelected

example :
    RequiredLawIdealExact rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed :=
  weakReading_requiredLawIdealExact

example :
    RequiredLawIdealExact rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed :=
  strongReading_requiredLawIdealExact

example :
    LawIdealSound rawSystem twoChartReferenceModel weakReading
      weakReading_witnessCompatible PUnit.unit
      (weakReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit)) :=
  weakReading_lawIdealSound

example :
    LawIdealComplete rawSystem twoChartReferenceModel weakReading
      weakReading_witnessCompatible PUnit.unit
      (weakReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit)) :=
  weakReading_lawIdealComplete

example :
    LawIdealExact rawSystem twoChartReferenceModel weakReading
      weakReading_witnessCompatible PUnit.unit
      (weakReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit)) :=
  weakReading_lawIdealExact

example :
    AllLawIdealExact rawSystem twoChartReferenceModel weakReading
      weakReading_valid weakReading_allLawsSelected :=
  weakReading_allLawIdealExact

example :
    AllLawIdealExact rawSystem twoChartReferenceModel strongReading
      strongReading_valid strongReading_allLawsSelected :=
  strongReading_allLawIdealExact

example :
    ClosedEquationalLawInclusion rawSystem twoChartReferenceModel
      weakReading strongReading :=
  weakToStrong

example :
    IsClosedEquationalLawInclusion rawSystem twoChartReferenceModel weakToStrong :=
  weakToStrong_valid

example :
    lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
        weakReading weakReading_valid weakReading_requiredClosed <
      lawGeneratedIdealSheaf rawSystem twoChartReferenceModel
        strongReading strongReading_valid strongReading_requiredClosed :=
  weak_ideal_lt_strong

example :
    Nonempty (lawfulClosedSubscheme rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed) :=
  weakSubscheme_nonempty

example :
    Nonempty (lawfulClosedSubscheme rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed) :=
  strongSubscheme_nonempty

example :
    ¬ IsIso (lawfulClosedImmersion rawSystem twoChartReferenceModel
      weakReading weakReading_valid weakReading_requiredClosed) :=
  weakImmersion_not_isIso

example :
    ¬ IsIso (lawfulClosedImmersion rawSystem twoChartReferenceModel
      strongReading strongReading_valid strongReading_requiredClosed) :=
  strongImmersion_not_isIso

example :
    ¬ IsIso (lawfulClosedSubschemeMap rawSystem twoChartReferenceModel
      weakReading_valid strongReading_valid
      weakReading_requiredClosed strongReading_requiredClosed
      weakToStrong weakToStrong_valid) :=
  weakToStrongMap_not_isIso

example :
    ¬ IsIso (allLawfulClosedSubschemeMap rawSystem twoChartReferenceModel
      weakReading_valid strongReading_valid
      weakToStrong weakToStrong_valid) :=
  weakToStrongAllMap_not_isIso

example : Type :=
  RequiredAllLawIndex

example : RequiredAllLawIndex :=
  RequiredAllLawIndex.base

example : RequiredAllLawIndex :=
  RequiredAllLawIndex.strengthening

example : LawUniverse carrier :=
  requiredAllLawUniverse

example (i : RequiredAllLawIndex) :
    requiredAllLawUniverse.Required i ↔ i = .base :=
  requiredAllLawUniverse_required_iff i

example : requiredAllLawUniverse.Optional .strengthening :=
  requiredAllLawUniverse_optional_strengthening

example : Site.AATSite corePackage.object :=
  requiredAllSite

example : requiredAllSite.lawUniverse = requiredAllLawUniverse :=
  requiredAllSite_lawUniverse

example : RawAmbientRestrictionSystem requiredAllSite Int :=
  requiredAllRawSystem

example : HasSheafify requiredAllSite.topology (AATCommAlgCat Int) :=
  requiredAllHasSheafify

example : StandardArchitectureScheme requiredAllRawSystem :=
  requiredAllReferenceModel

example :
    requiredAllReferenceModel.underlying = twoChartReferenceModel.underlying :=
  requiredAllReferenceModel_underlying

example : SemanticLawEquationWitnessIdealCore requiredAllSite :=
  requiredAllLawEquationCore

example :
    SemanticLawEquationSchemeBridge requiredAllRawSystem
      requiredAllLawEquationCore :=
  requiredAllSchemeBridge

example :
    IsSemanticLawEquationSchemeBridge requiredAllRawSystem
      requiredAllLawEquationCore requiredAllSchemeBridge :=
  requiredAllSchemeBridge_valid

example : Γ(requiredAllReferenceModel.underlying, ⊤) :=
  requiredAllBaseGlobalCoordinate

example :
    semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
        requiredAllLawEquationCore requiredAllSchemeBridge
        .base FiniteAtom.componentA =
      requiredAllBaseGlobalCoordinate - 1 :=
  requiredLaw_componentA_equation

example :
    semanticCoreGlobalEquation requiredAllRawSystem requiredAllReferenceModel
        requiredAllLawEquationCore requiredAllSchemeBridge
        .strengthening FiniteAtom.componentB =
      requiredAllBaseGlobalCoordinate + 1 :=
  strengtheningLaw_componentB_equation

example :
    ClosedEquationalLawReading requiredAllRawSystem requiredAllReferenceModel :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReading

example :
    IsClosedEquationalWitnessReading requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReading_witnessCompatible

example :
    IsClosedEquationalLawReading requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReading_valid

example :
    RequiredClosed requiredAllRawSystem requiredAllReferenceModel
      requiredAllReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReading_requiredClosed

example :
    AllLawsSelected requiredAllRawSystem requiredAllReferenceModel
      requiredAllReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReading_allLawsSelected

example :
    {i | requiredAllSite.lawUniverse.Required i} ⊂ requiredAllReading.closed :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.required_indices_ssubset_closed

example
    (V : requiredAllReferenceModel.underlying.affineOpens)
    (i : RequiredAllLawIndex) :
    requiredAllReading.selected V i :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.requiredAllReading_selected
    V i

example
    (V : requiredAllReferenceModel.underlying.affineOpens) :
    {i | requiredAllSite.lawUniverse.Required i} ⊂
      {i | requiredAllReading.selected V i} :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.required_indices_ssubset_selected
    V

example :
    lawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid
        requiredAllReading_requiredClosed <
      allLawGeneratedIdealSheaf requiredAllRawSystem requiredAllReferenceModel
        requiredAllReading requiredAllReading_valid :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.required_ideal_lt_all_ideal

example :
    ¬ IsIso (fullToRequiredLawfulMap requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid requiredAllReading_requiredClosed) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.fullToRequiredLawfulMap_not_isIso

example :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of Int)) ⟶
      requiredAllReferenceModel.underlying :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.selectedRequiredPoint

example :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of (ZMod 2))) ⟶
      requiredAllReferenceModel.underlying :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.selectedModTwoPoint

example :
    Nonempty (FactorsThroughLawfulClosedSubscheme requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid requiredAllReading_requiredClosed
      selectedRequiredPoint) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.selected_point_factors_required

example :
    ¬ Nonempty (FactorsThroughAllLawfulClosedSubscheme requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid selectedRequiredPoint) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.selected_point_not_factors_all

example :
    Nonempty (FactorsThroughAllLawfulClosedSubscheme requiredAllRawSystem
      requiredAllReferenceModel requiredAllReading
      requiredAllReading_valid selectedModTwoPoint) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.selected_modTwo_point_factors_all

example :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of Int)) ⟶
      twoChartReferenceModel.underlying :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint

example :
    AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of (ZMod 2))) ⟶
      twoChartReferenceModel.underlying :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.modTwoPoint

example :
    RequiredObjectPointComparison rawSystem twoChartReferenceModel
      weakReading integerPoint
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_objectComparison

example :
    ¬ RequiredObjectPointComparison rawSystem twoChartReferenceModel
      weakReading integerPoint
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.cyclicObject :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_objectComparison_fails_for_cyclic

example :
    SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading integerPoint ↔
      omegaU noCycleValuation lawUniverse singletonRequiredAggregation
          AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject =
        noCycleValuation.domain.zero :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_omega_fires

example :
    SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading integerPoint ↔
      RequiredSignatureAxesZero
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.acyclicObject
        AAT.AG.LawAlgebra.FiniteExamples.CycleCorrespondenceExample.signatureAxes :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_axis_fires

example :
    GlobalEquationsVanishAlong rawSystem twoChartReferenceModel
      (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        weakLawEquationCore weakSchemeBridge PUnit.unit) integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_globalEquationsVanish_weak

example :
    ¬ GlobalEquationsVanishAlong rawSystem twoChartReferenceModel
      (semanticCoreGlobalEquation rawSystem twoChartReferenceModel
        strongLawEquationCore strongSchemeBridge PUnit.unit) integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_globalEquationsVanish_strong

example :
    SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_semanticLawful_weak

example :
    ¬ SemanticLawfulAlong rawSystem twoChartReferenceModel
      strongReading integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_semanticLawful_strong

example :
    FullySemanticLawfulAlong rawSystem twoChartReferenceModel
      weakReading integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_fullySemanticLawful_weak

example :
    ¬ FullySemanticLawfulAlong rawSystem twoChartReferenceModel
      strongReading integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_fullySemanticLawful_strong

example :
    WitnessVanishes rawSystem twoChartReferenceModel weakReading
      weakReading_valid weakReading_requiredClosed integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_witnessVanishes_weak

example :
    ¬ WitnessVanishes rawSystem twoChartReferenceModel strongReading
      strongReading_valid strongReading_requiredClosed integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_witnessVanishes_strong

example :
    IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
      weakReading_valid weakReading_requiredClosed integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_idealLawful_weak

example :
    ¬ IdealLawfulAlong rawSystem twoChartReferenceModel strongReading
      strongReading_valid strongReading_requiredClosed integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_idealLawful_strong

example :
    FullIdealLawfulAlong rawSystem twoChartReferenceModel weakReading
      weakReading_valid integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_fullIdealLawful_weak

example :
    ¬ FullIdealLawfulAlong rawSystem twoChartReferenceModel strongReading
      strongReading_valid integerPoint :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_fullIdealLawful_strong

example :
    Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel weakReading weakReading_valid
      weakReading_requiredClosed integerPoint) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_factors_weak

example :
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel strongReading strongReading_valid
      strongReading_requiredClosed integerPoint) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_factors_strong

example :
    Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel weakReading weakReading_valid
      weakReading_requiredClosed modTwoPoint) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.modTwoPoint_factors_weak

example :
    Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
      twoChartReferenceModel strongReading strongReading_valid
      strongReading_requiredClosed modTwoPoint) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.modTwoPoint_factors_strong

example :
    Nonempty (FactorsThroughAllLawfulClosedSubscheme rawSystem
      twoChartReferenceModel weakReading weakReading_valid integerPoint) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_factorsAll_weak

example :
    ¬ Nonempty (FactorsThroughAllLawfulClosedSubscheme rawSystem
      twoChartReferenceModel strongReading strongReading_valid integerPoint) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.integerPoint_not_factorsAll_strong

example
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) :
    (SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading s ↔
      WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
        twoChartReferenceModel weakReading weakReading_valid
        weakReading_requiredClosed s)) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weak_correspondence_fires
    s

example
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) :
    SemanticCoreIdealSheafRealized rawSystem twoChartReferenceModel
      weakLawEquationCore weakSchemeBridge ∧
    (SemanticLawfulAlong rawSystem twoChartReferenceModel weakReading s ↔
      WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (WitnessVanishes rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s) ∧
    (IdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid weakReading_requiredClosed s ↔
      Nonempty (FactorsThroughLawfulClosedSubscheme rawSystem
        twoChartReferenceModel weakReading weakReading_valid
        weakReading_requiredClosed s)) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weak_semanticCore_correspondence_fires
    s

example
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ twoChartReferenceModel.underlying) :
    (FullySemanticLawfulAlong rawSystem twoChartReferenceModel weakReading s ↔
      FullIdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid s) ∧
    (FullIdealLawfulAlong rawSystem twoChartReferenceModel weakReading
        weakReading_valid s ↔
      Nonempty (FactorsThroughAllLawfulClosedSubscheme rawSystem
        twoChartReferenceModel weakReading weakReading_valid s)) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.weak_full_correspondence_fires
    s

example :
    SemanticLawEquationSchemeBridge rawSystem weakLawEquationCore :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenSchemeBridge

example :
    ¬ IsSemanticLawEquationSchemeBridge rawSystem
      weakLawEquationCore restrictionBrokenSchemeBridge :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenSchemeBridge_not_valid

example :
    ¬ SemanticCoreIdealSheafRealized rawSystem twoChartReferenceModel
      weakLawEquationCore restrictionBrokenSchemeBridge :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenSchemeBridge_not_realized

example :
    GeometricLawReading rawSystem twoChartReferenceModel :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.baseChangeBrokenGeometricReading

example :
    ¬ IsGeometricLawReading rawSystem twoChartReferenceModel
      baseChangeBrokenGeometricReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.baseChangeBrokenGeometricReading_not_valid

example :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.baseChangeBrokenReading

example :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      baseChangeBrokenReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.baseChangeBrokenReading_witnessCompatible

example :
    ¬ IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      baseChangeBrokenReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.baseChangeBrokenReading_not_valid

example :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredReading

example :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      missingRequiredReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredReading_valid

example :
    ¬ RequiredClosed rawSystem twoChartReferenceModel missingRequiredReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredReading_not_requiredClosed

example :
    ¬ AllLawsSelected rawSystem twoChartReferenceModel
      missingRequiredReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredReading_not_allLawsSelected

example :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenSelectionReading

example :
    ¬ IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      restrictionBrokenSelectionReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenSelectionReading_not_valid

example :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredSelectionReading

example :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      missingRequiredSelectionReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredSelectionReading_valid

example :
    ¬ RequiredClosed rawSystem twoChartReferenceModel
      missingRequiredSelectionReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.missingRequiredSelectionReading_not_requiredClosed

example :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading

example :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      semanticMismatchReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_valid

example :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      semanticMismatchReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_witnessCompatible

example :
    RequiredClosed rawSystem twoChartReferenceModel semanticMismatchReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_requiredClosed

example :
    AllLawsSelected rawSystem twoChartReferenceModel
      semanticMismatchReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_allLawsSelected

example :
    ¬ RequiredLawIdealExact rawSystem twoChartReferenceModel
      semanticMismatchReading semanticMismatchReading_valid
      semanticMismatchReading_requiredClosed :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_not_exact

example :
    ¬ LawIdealExact rawSystem twoChartReferenceModel
      semanticMismatchReading semanticMismatchReading_witnessCompatible
      PUnit.unit
      (semanticMismatchReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit)) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_not_lawIdealExact

example :
    ¬ LawIdealComplete rawSystem twoChartReferenceModel
      semanticMismatchReading semanticMismatchReading_witnessCompatible
      PUnit.unit
      (semanticMismatchReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit)) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_not_complete

example :
    ¬ AllLawIdealExact rawSystem twoChartReferenceModel semanticMismatchReading
      semanticMismatchReading_valid
      semanticMismatchReading_allLawsSelected :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatchReading_not_allLawIdealExact

example :
    ¬ (FullySemanticLawfulAlong rawSystem twoChartReferenceModel
          semanticMismatchReading integerPoint ↔
        FullIdealLawfulAlong rawSystem twoChartReferenceModel
          semanticMismatchReading semanticMismatchReading_valid
          integerPoint) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticMismatch_full_correspondence_fails

example :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticOverclaimReading

example :
    IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      semanticOverclaimReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticOverclaimReading_valid

example :
    IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      semanticOverclaimReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticOverclaimReading_witnessCompatible

example :
    RequiredClosed rawSystem twoChartReferenceModel semanticOverclaimReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticOverclaimReading_requiredClosed

example :
    ¬ LawIdealSound rawSystem twoChartReferenceModel semanticOverclaimReading
      semanticOverclaimReading_witnessCompatible PUnit.unit
      (semanticOverclaimReading_requiredClosed.closed PUnit.unit
        (lawUniverse_required PUnit.unit)) :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.semanticOverclaimReading_not_sound

example :
    ClosedEquationalLawWitness rawSystem twoChartReferenceModel PUnit.unit :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenWitness

example :
    ¬ IsClosedEquationalLawWitness rawSystem twoChartReferenceModel
      restrictionBrokenWitness :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenWitness_not_valid

example :
    ClosedEquationalLawReading rawSystem twoChartReferenceModel :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenReading

example :
    ¬ IsClosedEquationalWitnessReading rawSystem twoChartReferenceModel
      restrictionBrokenReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenReading_not_witnessCompatible

example :
    ¬ IsClosedEquationalLawReading rawSystem twoChartReferenceModel
      restrictionBrokenReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.restrictionBrokenReading_not_valid

example :
    ClosedEquationalLawInclusion rawSystem twoChartReferenceModel
      weakReading strongReading :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.coordinateBrokenInclusion

example :
    ¬ IsClosedEquationalLawInclusion rawSystem twoChartReferenceModel
      coordinateBrokenInclusion :=
  AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry.coordinateBrokenInclusion_not_valid

end AAT.AG.LawAlgebra.FiniteExamples.ClosedEquationalGeometry
